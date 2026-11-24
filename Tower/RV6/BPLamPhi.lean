import Mathlib
import Tower.RV6.BPMellin

/-!
# RungBP, step 8 closed: `Λ(0) + Λ(-s) = Φ(s)`

`R(x) = x j(x) = exp(ℓ(x) - a₀ x)` (`sjS_eq_exp`).  With `w(u) = ℓ(u) + ℓ(s-u) - ℓ(s)` the Mellin identity
(`jS_mul_jS`) reads `e^{w(u)} - 1 = -(u(s-u)/s)(Λ(-u) + Λ(u-s))` (`exp_w_sub_one`).  Divided by `u` and taken to
`u → 0+` (`tendsto_ellQ_slope`, `continuousOn_lamS`) it gives `Λ(0) + Λ(-s) = Φ(s)` (`lamS_zero_add_neg`), and so
`2Λ(0) = Φ(s) - s T₁ - E(s)` (`two_lamS_zero`).
-/

namespace Tower.RV6

open Real Set Filter Topology

theorem sjS_eq_exp {x : ℝ} (hx0 : 0 < x) (hx2 : x < 2) : x * jS x = Real.exp (ellQ x - a0 * x) := by
  rw [Real.exp_sub, ← expQ_eq hx0 hx2, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

theorem jS_pos {x : ℝ} (hx0 : 0 < x) (hx2 : x < 2) : 0 < jS x := by
  have h : 0 < x * jS x := by
    rw [sjS_eq_exp hx0 hx2]
    exact Real.exp_pos _
  exact pos_of_mul_pos_right h hx0.le

/-- `e^{w(u)} - 1 = -(u(s-u)/s)(Λ(-u) + Λ(u-s))` for `0 < u < s ≤ 1`. -/
theorem exp_w_sub_one {s u : ℝ} (hu0 : 0 < u) (hus : u < s) (hs1 : s ≤ 1) :
    Real.exp (ellQ u + ellQ (s - u) - ellQ s) - 1
      = -(u * (s - u) / s) * (lamS s (-u) + lamS s (u - s)) := by
  have hs0 : 0 < s := by linarith
  have hsu : 0 < s - u := by linarith
  have e1 : Real.exp (ellQ u + ellQ (s - u) - ellQ s)
      = Real.exp (ellQ u - a0 * u) * Real.exp (ellQ (s - u) - a0 * (s - u))
        / Real.exp (ellQ s - a0 * s) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  have hJ := jS_mul_jS hu0 hus hs1
  have hjs : jS s ≠ 0 := (jS_pos hs0 (by linarith)).ne'
  have hu : u ≠ 0 := hu0.ne'
  have hsu' : s - u ≠ 0 := hsu.ne'
  have hs : s ≠ 0 := hs0.ne'
  rw [e1, ← sjS_eq_exp hu0 (by linarith), ← sjS_eq_exp hsu (by linarith),
    ← sjS_eq_exp hs0 (by linarith)]
  calc u * jS u * ((s - u) * jS (s - u)) / (s * jS s) - 1
      = u * (s - u) * (jS u * jS (s - u)) / (s * jS s) - 1 := by ring
    _ = u * (s - u) * (jS s * (s / (u * (s - u)) - lamS s (-u) - lamS s (u - s)))
          / (s * jS s) - 1 := by rw [hJ]
    _ = -(u * (s - u) / s) * (lamS s (-u) + lamS s (u - s)) := by
          field_simp
          all_goals ring

/-- **`Λ(0) + Λ(-s) = Φ(s)`** for `0 < s ≤ 1`. -/
theorem lamS_zero_add_neg {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    lamS s 0 + lamS s (-s) = phiS s := by
  have hw := tendsto_ellQ_slope hs0 (by linarith : s < 2)
  -- `w(u) → 0`
  have hw0 : Tendsto (fun u : ℝ => ellQ u + ellQ (s - u) - ellQ s) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (a := 0))).mul hw
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := (show (0 : ℝ) < u from hu).ne'
    simp only [id]
    field_simp
  -- `(e^{w(u)} - 1)/u → -Φ(s)`
  have hsmall : ∀ᶠ u in 𝓝[>] (0 : ℝ), |ellQ u + ellQ (s - u) - ellQ s| ≤ 1 := by
    have h := hw0.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [h] with u hu
    simpa [Metric.mem_closedBall, Real.dist_eq] using hu
  have hrem : Tendsto (fun u : ℝ => (Real.exp (ellQ u + ellQ (s - u) - ellQ s) - 1
      - (ellQ u + ellQ (s - u) - ellQ s)) / u) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun u : ℝ => |ellQ u + ellQ (s - u) - ellQ s|
        * |(ellQ u + ellQ (s - u) - ellQ s) / u|) (𝓝[>] 0) (𝓝 0) := by
      have h := hw0.abs.mul hw.abs
      rw [abs_zero, zero_mul] at h
      exact h
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hsmall, self_mem_nhdsWithin] with u h1 hu
    have hu0 : (0 : ℝ) < u := hu
    have he := Real.abs_exp_sub_one_sub_id_le h1
    have hu0' : u ≠ 0 := hu0.ne'
    rw [Real.norm_eq_abs, abs_div, abs_div, abs_of_pos hu0]
    rw [div_le_iff₀ hu0]
    calc |Real.exp (ellQ u + ellQ (s - u) - ellQ s) - 1 - (ellQ u + ellQ (s - u) - ellQ s)|
        ≤ |ellQ u + ellQ (s - u) - ellQ s| ^ 2 := by rw [sq_abs]; exact he
      _ = |ellQ u + ellQ (s - u) - ellQ s| * (|ellQ u + ellQ (s - u) - ellQ s| / u) * u := by
          field_simp
          all_goals ring
  have hE : Tendsto (fun u : ℝ => (Real.exp (ellQ u + ellQ (s - u) - ellQ s) - 1) / u)
      (𝓝[>] 0) (𝓝 (-phiS s)) := by
    have h := hw.add hrem
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    ring
  -- the right side
  have hc := continuousOn_lamS hs0.le (by linarith : s ≤ 2)
  have hL1 : Tendsto (fun u : ℝ => lamS s (-u)) (𝓝[>] 0) (𝓝 (lamS s 0)) := by
    have hcw : ContinuousWithinAt (lamS s) (Ici (-1)) 0 := hc 0 (by norm_num)
    have hg : Tendsto (fun u : ℝ => -u) (𝓝[>] 0) (𝓝[Ici (-1)] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h := (continuous_neg.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using h
      · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with u hu
        show (-1 : ℝ) ≤ -u
        linarith [hu.2]
    exact hcw.tendsto.comp hg
  have hL2 : Tendsto (fun u : ℝ => lamS s (u - s)) (𝓝[>] 0) (𝓝 (lamS s (-s))) := by
    have hcw : ContinuousWithinAt (lamS s) (Ici (-1)) (-s) := hc (-s) (by
      show (-1 : ℝ) ≤ -s
      linarith)
    have hg : Tendsto (fun u : ℝ => u - s) (𝓝[>] 0) (𝓝[Ici (-1)] (-s)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h := ((continuous_sub_right s).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using h
      · filter_upwards [self_mem_nhdsWithin] with u hu
        show (-1 : ℝ) ≤ u - s
        have : (0 : ℝ) < u := hu
        linarith
    exact hcw.tendsto.comp hg
  have hq : Tendsto (fun u : ℝ => (s - u) / s) (𝓝[>] 0) (𝓝 ((s - 0) / s)) :=
    (((continuous_sub_left s).div_const s).tendsto (0 : ℝ)).mono_left
      nhdsWithin_le_nhds
  have hRS := (hq.mul (hL1.add hL2)).neg
  have hval : -((s - 0) / s * (lamS s 0 + lamS s (-s))) = -(lamS s 0 + lamS s (-s)) := by
    rw [sub_zero, div_self hs0.ne', one_mul]
  rw [hval] at hRS
  have hRS' : Tendsto (fun u : ℝ => (Real.exp (ellQ u + ellQ (s - u) - ellQ s) - 1) / u)
      (𝓝[>] 0) (𝓝 (-(lamS s 0 + lamS s (-s)))) := by
    refine hRS.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hs0] with u hu
    have hu0 : u ≠ 0 := hu.1.ne'
    have hs' : s ≠ 0 := hs0.ne'
    rw [exp_w_sub_one hu.1 hu.2 hs1]
    field_simp
    all_goals ring
  have := tendsto_nhds_unique hE hRS'
  linarith

/-- `2Λ(0) = Φ(s) - s T₁ - E(s)` for `0 < s ≤ 1`. -/
theorem two_lamS_zero {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    2 * lamS s 0 = phiS s - s * t1S s - eS s := by
  have h := lamS_zero_add_neg hs0 hs1
  rw [eS]
  linarith

end Tower.RV6
