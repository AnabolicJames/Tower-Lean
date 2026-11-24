import Mathlib
import Tower.RV6.BPQexp

/-!
# RungBP, step 5: `Φ(s) = ℓ'(s)`

`dφ_k(u) = 1/(K + u) + 1/(K - u) - 2/K` (`K = k + 1`) is the derivative of `φ_k` on `|u| < 1`, and
`Φ(s) = ∑_k dφ_k(s/2)/2 = ∑_k s²/(K(4K² - s²))` (`phiS`).

* `HasDerivAt ℓ (Φ s) s` for `|s| < 2` (termwise, `hasDerivAt_tsum_of_isPreconnected`).
* `dφ_k(u) = 2u²/K³ + 2u⁴/K⁵ + 2u⁶/(K⁵(K + u)(K - u))`, so on `0 ≤ s ≤ 1`:
  `0 ≤ Φ(s) - s² zN 3/4 - s⁴ zN 5/16 ≤ s⁶ zN 7/48` (`phiS_expansion`).
* `(ℓ(u) + ℓ(s - u) - ℓ(s))/u → -Φ(s)` as `u → 0+`, `0 < s < 2` (`tendsto_ellQ_slope`).
-/

namespace Tower.RV6

open Real Set Filter Topology

/-- `dφ_k(u) = 1/(k + 1 + u) + 1/(k + 1 - u) - 2/(k + 1)`. -/
noncomputable def dphiK (u : ℝ) (k : ℕ) : ℝ :=
  1 / ((k : ℝ) + 1 + u) + 1 / ((k : ℝ) + 1 - u) - 2 / ((k : ℝ) + 1)

/-- `Φ(s) = ∑_k dφ_k(s/2)/2`. -/
noncomputable def phiS (s : ℝ) : ℝ := ∑' k : ℕ, dphiK (s / 2) k / 2

theorem recip_sum_eq {K u : ℝ} (hK : K ≠ 0) (h1 : K + u ≠ 0) (h2 : K - u ≠ 0) :
    1 / (K + u) + 1 / (K - u) - 2 / K = 2 * u ^ 2 / (K * ((K + u) * (K - u))) := by
  field_simp
  ring

theorem recip_sum_expand {K u : ℝ} (hK : K ≠ 0) (h1 : K + u ≠ 0) (h2 : K - u ≠ 0) :
    1 / (K + u) + 1 / (K - u) - 2 / K
      = 2 * u ^ 2 * (1 / K ^ 3) + 2 * u ^ 4 * (1 / K ^ 5)
        + 2 * u ^ 6 / (K ^ 5 * ((K + u) * (K - u))) := by
  field_simp
  ring

theorem recip_rem_le {K u : ℝ} (hK : 1 ≤ K) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    0 ≤ 2 * u ^ 6 / (K ^ 5 * ((K + u) * (K - u)))
      ∧ 2 * u ^ 6 / (K ^ 5 * ((K + u) * (K - u))) ≤ 8 / 3 * u ^ 6 * (1 / K ^ 7) := by
  have hK0 : 0 < K := by linarith
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith
  have hP : 3 / 4 * K ^ 2 ≤ (K + u) * (K - u) := by nlinarith
  have hP0 : 0 < (K + u) * (K - u) := by nlinarith
  have hD : 0 < K ^ 5 * ((K + u) * (K - u)) := mul_pos (pow_pos hK0 5) hP0
  refine ⟨div_nonneg (by positivity) hD.le, ?_⟩
  rw [mul_one_div, div_le_div_iff₀ hD (pow_pos hK0 7)]
  have h := mul_le_mul_of_nonneg_left hP (mul_nonneg (by positivity) (pow_nonneg hK0.le 5) :
    (0 : ℝ) ≤ u ^ 6 * K ^ 5)
  nlinarith [h]

theorem recip_bound {K u b : ℝ} (hK : 1 ≤ K) (hu : |u| ≤ b / 2) (hb : b < 2) :
    |2 * u ^ 2 / (K * ((K + u) * (K - u))) / 2| ≤ b ^ 2 / (4 - b ^ 2) * (1 / K ^ 3) := by
  have hK0 : 0 < K := by linarith
  have hb0 : 0 ≤ b := by have := abs_nonneg u; linarith
  have hu2 : u ^ 2 ≤ b ^ 2 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
    rw [sq_abs] at h
    nlinarith [h]
  have h4 : 0 < 4 - b ^ 2 := by nlinarith
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hP0 : 0 < (K + u) * (K - u) := by nlinarith
  have hD : 0 < K * ((K + u) * (K - u)) := mul_pos hK0 hP0
  rw [abs_of_nonneg (div_nonneg (div_nonneg (by positivity) hD.le) (by norm_num))]
  rw [div_mul_div_comm, mul_one,
    show 2 * u ^ 2 / (K * ((K + u) * (K - u))) / 2 = u ^ 2 / (K * ((K + u) * (K - u))) by ring,
    div_le_div_iff₀ hD (mul_pos h4 (pow_pos hK0 3))]
  have p1 : 0 ≤ K ^ 3 * (b ^ 2 - 4 * u ^ 2) := mul_nonneg (pow_nonneg hK0.le 3) (by linarith)
  have p2 : 0 ≤ u ^ 2 * b ^ 2 * K * (K ^ 2 - 1) :=
    mul_nonneg (mul_nonneg (by positivity) hK0.le) (by nlinarith)
  nlinarith [p1, p2]

theorem hasDerivAt_phiK {u : ℝ} (hu : |u| < 1) (k : ℕ) :
    HasDerivAt (fun v : ℝ => phiK v k) (dphiK u k) u := by
  have hK : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hu1 := abs_lt.1 hu
  have hA : 0 < (k : ℝ) + 1 + u := by linarith
  have hB : 0 < (k : ℝ) + 1 - u := by linarith
  have dA : HasDerivAt (fun v : ℝ => (k : ℝ) + 1 + v) 1 u := (hasDerivAt_id' u).const_add _
  have dB : HasDerivAt (fun v : ℝ => (k : ℝ) + 1 - v) (-1) u := (hasDerivAt_id' u).const_sub _
  have dM : HasDerivAt (fun v : ℝ => 2 * v / ((k : ℝ) + 1)) (2 * 1 / ((k : ℝ) + 1)) u :=
    ((hasDerivAt_id' u).const_mul 2).div_const _
  have h := ((dA.log hA.ne').sub (dB.log hB.ne')).sub dM
  have hev : (fun v : ℝ => phiK v k) =ᶠ[𝓝 u]
      (fun v : ℝ => Real.log ((k : ℝ) + 1 + v) - Real.log ((k : ℝ) + 1 - v)
        - 2 * v / ((k : ℝ) + 1)) := by
    filter_upwards [Ioo_mem_nhds hu1.1 hu1.2] with v hv
    have hA' : 0 < (k : ℝ) + 1 + v := by linarith [hv.1]
    have hB' : 0 < (k : ℝ) + 1 - v := by linarith [hv.2]
    rw [phiK, Real.log_div hA'.ne' hB'.ne']
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [dphiK]
  ring

theorem dphiK_half_bound {b y : ℝ} (hb : b < 2) (hy : y ∈ Ioo (-b) b) (n : ℕ) :
    ‖dphiK (y / 2) n / 2‖ ≤ b ^ 2 / (4 - b ^ 2) * (1 / ((n : ℝ) + 1) ^ 3) := by
  have hK : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hy2 : |y / 2| ≤ b / 2 := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have hy1 : |y / 2| < 1 := by linarith
  have hu := abs_lt.1 hy1
  have hK0 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h1 : (n : ℝ) + 1 + y / 2 ≠ 0 := (show (0 : ℝ) < (n : ℝ) + 1 + y / 2 by linarith).ne'
  have h2 : (n : ℝ) + 1 - y / 2 ≠ 0 := (show (0 : ℝ) < (n : ℝ) + 1 - y / 2 by linarith).ne'
  rw [Real.norm_eq_abs, dphiK, recip_sum_eq hK0 h1 h2]
  exact recip_bound hK hy2 hb

/-- **`ℓ'(s) = Φ(s)`** for `|s| < 2`. -/
theorem hasDerivAt_ellQ {s : ℝ} (hs : |s| < 2) : HasDerivAt ellQ (phiS s) s := by
  have hb2 : (|s| + 2) / 2 < 2 := by linarith
  have hsb := abs_lt.1 (show |s| < (|s| + 2) / 2 by linarith)
  have hu : Summable (fun n : ℕ => ((|s| + 2) / 2) ^ 2 / (4 - ((|s| + 2) / 2) ^ 2)
      * (1 / ((n : ℝ) + 1) ^ 3)) :=
    (summable_zN (by norm_num : 2 ≤ 3)).mul_left _
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Ioo (-((|s| + 2) / 2)) ((|s| + 2) / 2) →
      HasDerivAt (fun z : ℝ => phiK (z / 2) n) (dphiK (y / 2) n / 2) y := by
    intro n y hy
    have hy2 : |y / 2| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have h := (hasDerivAt_phiK hy2 n).comp y ((hasDerivAt_id' y).div_const 2)
    have h2 := h.congr_deriv (show dphiK (y / 2) n * (1 / 2) = dphiK (y / 2) n / 2 by ring)
    exact h2
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Ioo (-((|s| + 2) / 2)) ((|s| + 2) / 2) →
      ‖dphiK (y / 2) n / 2‖ ≤ ((|s| + 2) / 2) ^ 2 / (4 - ((|s| + 2) / 2) ^ 2)
        * (1 / ((n : ℝ) + 1) ^ 3) :=
    fun n y hy => dphiK_half_bound hb2 hy n
  have h0 : (0 : ℝ) ∈ Ioo (-((|s| + 2) / 2)) ((|s| + 2) / 2) := by
    have := abs_nonneg s
    constructor <;> linarith
  have hg0 : Summable (fun n : ℕ => phiK (0 / 2) n) := by
    rw [zero_div]
    exact summable_phiK le_rfl one_pos
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hderiv hbound h0 hg0
    ⟨hsb.1, hsb.2⟩

theorem ellQ_zero : ellQ 0 = 0 := by
  have h : ∀ k : ℕ, phiK (0 / 2) k = 0 := fun k => by
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [zero_div, phiK, add_zero, sub_zero, div_self hk, Real.log_one, mul_zero, zero_div,
      sub_zero]
  simp only [ellQ, h, tsum_zero]

theorem phiS_zero : phiS 0 = 0 := by
  have h : ∀ k : ℕ, dphiK (0 / 2) k / 2 = 0 := fun k => by
    rw [zero_div, dphiK, add_zero, sub_zero]
    ring
  simp only [phiS, h, tsum_zero]

/-- `0 ≤ Φ(s) - s² zN 3/4 - s⁴ zN 5/16 ≤ s⁶ zN 7/48` for `0 ≤ s ≤ 1`. -/
theorem phiS_expansion {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ phiS s - s ^ 2 / 4 * zN 3 - s ^ 4 / 16 * zN 5
      ∧ phiS s - s ^ 2 / 4 * zN 3 - s ^ 4 / 16 * zN 5 ≤ s ^ 6 / 48 * zN 7 := by
  have hu0 : 0 ≤ s / 2 := by linarith
  have hu1 : s / 2 ≤ 1 / 2 := by linarith
  have hK : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hexp : ∀ k : ℕ, dphiK (s / 2) k / 2
      = (s / 2) ^ 2 * (1 / ((k : ℝ) + 1) ^ 3) + (s / 2) ^ 4 * (1 / ((k : ℝ) + 1) ^ 5)
        + 2 * (s / 2) ^ 6 / (((k : ℝ) + 1) ^ 5 * (((k : ℝ) + 1 + s / 2) * ((k : ℝ) + 1 - s / 2)))
          / 2 := fun k => by
    have hK0 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h1 : (k : ℝ) + 1 + s / 2 ≠ 0 :=
      (show (0 : ℝ) < (k : ℝ) + 1 + s / 2 by linarith [hK k]).ne'
    have h2 : (k : ℝ) + 1 - s / 2 ≠ 0 :=
      (show (0 : ℝ) < (k : ℝ) + 1 - s / 2 by linarith [hK k]).ne'
    rw [dphiK, recip_sum_expand hK0 h1 h2]
    ring
  have hr := fun k => recip_rem_le (hK k) hu0 hu1
  have hA := (summable_zN (by norm_num : 2 ≤ 3)).mul_left ((s / 2) ^ 2)
  have hB := (summable_zN (by norm_num : 2 ≤ 5)).mul_left ((s / 2) ^ 4)
  have hC := (summable_zN (by norm_num : 2 ≤ 7)).mul_left (8 / 3 * (s / 2) ^ 6 / 2)
  have hR : Summable (fun k : ℕ => 2 * (s / 2) ^ 6
      / (((k : ℝ) + 1) ^ 5 * (((k : ℝ) + 1 + s / 2) * ((k : ℝ) + 1 - s / 2))) / 2) := by
    refine Summable.of_nonneg_of_le (fun k => div_nonneg (hr k).1 (by norm_num))
      (fun k => ?_) hC
    have h := (hr k).2
    calc 2 * (s / 2) ^ 6 / (((k : ℝ) + 1) ^ 5 * (((k : ℝ) + 1 + s / 2) * ((k : ℝ) + 1 - s / 2)))
          / 2 ≤ 8 / 3 * (s / 2) ^ 6 * (1 / ((k : ℝ) + 1) ^ 7) / 2 := by linarith
      _ = 8 / 3 * (s / 2) ^ 6 / 2 * (1 / ((k : ℝ) + 1) ^ 7) := by ring
  have hsum : phiS s = (s / 2) ^ 2 * zN 3 + (s / 2) ^ 4 * zN 5
      + ∑' k : ℕ, 2 * (s / 2) ^ 6
          / (((k : ℝ) + 1) ^ 5 * (((k : ℝ) + 1 + s / 2) * ((k : ℝ) + 1 - s / 2))) / 2 := by
    rw [phiS, tsum_congr hexp, (hA.add hB).tsum_add hR, hA.tsum_add hB, tsum_mul_left,
      tsum_mul_left, zN, zN]
  have hRle : ∑' k : ℕ, 2 * (s / 2) ^ 6
      / (((k : ℝ) + 1) ^ 5 * (((k : ℝ) + 1 + s / 2) * ((k : ℝ) + 1 - s / 2))) / 2
      ≤ 8 / 3 * (s / 2) ^ 6 / 2 * zN 7 := by
    rw [zN, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) hR hC
    have h := (hr k).2
    calc 2 * (s / 2) ^ 6 / (((k : ℝ) + 1) ^ 5 * (((k : ℝ) + 1 + s / 2) * ((k : ℝ) + 1 - s / 2)))
          / 2 ≤ 8 / 3 * (s / 2) ^ 6 * (1 / ((k : ℝ) + 1) ^ 7) / 2 := by linarith
      _ = 8 / 3 * (s / 2) ^ 6 / 2 * (1 / ((k : ℝ) + 1) ^ 7) := by ring
  have hR0 := tsum_nonneg (fun k => div_nonneg (hr k).1 (by norm_num : (0 : ℝ) ≤ 2))
  rw [hsum]
  constructor
  · nlinarith [hR0]
  · nlinarith [hRle]

/-- `(ℓ(u) + ℓ(s - u) - ℓ(s))/u → -Φ(s)` as `u → 0+`, for `0 < s < 2`. -/
theorem tendsto_ellQ_slope {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    Tendsto (fun u : ℝ => (ellQ u + ellQ (s - u) - ellQ s) / u) (𝓝[>] 0) (𝓝 (-phiS s)) := by
  have h0 : HasDerivAt ellQ (phiS 0) 0 := hasDerivAt_ellQ (by norm_num)
  have hs : HasDerivAt ellQ (phiS s) s := hasDerivAt_ellQ (by rw [abs_of_pos hs0]; exact hs2)
  have hA := h0.tendsto_slope_zero_right
  have hB := hs.tendsto_slope_zero_left
  have hneg : Tendsto (fun u : ℝ => -u) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa using (tendsto_neg_nhdsGT_neg (a := (0 : ℝ)))
  have hlim := hA.sub (hB.comp hneg)
  rw [phiS_zero, zero_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp only [Function.comp_apply, smul_eq_mul, zero_add, ellQ_zero, sub_zero, inv_neg,
    ← sub_eq_add_neg]
  ring

end Tower.RV6
