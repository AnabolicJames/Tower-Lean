import Mathlib
import Tower.RV6.BPFubini
import Tower.RV6.RungA2P
import Tower.RV6.MellinU
import Tower.RV6.BesselW

/-!
# RungBP, step 4: `∫_τ F₂ ∫_t G min(τ,t)^s = s B(s)` and `B(s) = (4/5) P(s) + (3/5) s M₃₅(s)`

`f = I₀K₀³` (`θf = thF1`, `θ²f = thF2`), `g = I₀²K₀² = thG0` (`θg = thG1`), `Γ(τ) = ∫₀^τ g(y) y^{s-1} dy` (`gamG`).

* Inner (`inner_min_integral`): `∫₀^∞ G(t) min(τ,t)^s dt = s Γ(τ)`, since `(g t^s)' = θg t^{s-1} + s g t^{s-1}` on `(0, τ)`
  and `∫_τ^∞ G = g(τ)`.
* Outer (`outer_min_integral`): `F = θf · Γ` has `F' = F₂ Γ + θf g τ^{s-1}`, `F → 0` at `0+` and `∞`, so
  `∫ F₂ Γ = -∫ θf g τ^{s-1} = B(s)` (`bB`).
* `θf g = 4t I₀²I₁K₀⁵ - 3 I₀²K₀⁴` (the Wronskian), so `B = 3 M₂₄ - 4 P = (4/5) P + (3/5) s M₃₅` (`bB_eq`).
-/

namespace Tower.RV6

open Real MeasureTheory Set Filter Topology

/-- `B(s) = -∫₀^∞ θf(y) g(y) y^{s-1} dy`. -/
noncomputable def bB (s : ℝ) : ℝ := -∫ y in Ioi (0 : ℝ), thF1 y * thG0 y * y ^ (s - 1)

/-- `Γ(τ) = ∫₀^τ g(y) y^{s-1} dy`. -/
noncomputable def gamG (s τ : ℝ) : ℝ := ∫ y in (0 : ℝ)..τ, thG0 y * y ^ (s - 1)

theorem mellU_eq_integral (h : ℝ → ℝ) (s : ℝ) :
    mellU h s = ∫ y in Ioi (0 : ℝ), h y * y ^ (s - 1) := by
  rw [← integral_comp_exp]
  unfold mellU
  congr 1
  funext u
  show h (Real.exp u) * Real.exp (s * u) = Real.exp u • (h (Real.exp u) * Real.exp u ^ (s - 1))
  rw [smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp,
    show Real.exp u * (h (Real.exp u) * Real.exp (u * (s - 1)))
      = h (Real.exp u) * (Real.exp u * Real.exp (u * (s - 1))) by ring, ← Real.exp_add]
  congr 2
  ring

theorem thF1_mul_thG0 {t : ℝ} (ht : 0 < t) :
    thF1 t * thG0 t = 4 * t * (besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5)
      - 3 * (besselI0 t ^ 2 * besselK0 t ^ 4) := by
  have hw := wronskian ht
  have hw' : t * (besselI0 t * besselK1 t) + t * (besselI1 t * besselK0 t) = 1 := by
    rw [← mul_add, hw, mul_one_div_cancel ht.ne']
  unfold thF1 ldF1 thG0 ldG0
  linear_combination (-3 * besselI0 t ^ 2 * besselK0 t ^ 4) * hw'

/-- `B(s) = 3 M₂₄(s) - 4 P(s)`. -/
theorem bB_eq_mell {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : bB s = 3 * mellM 2 4 s - 4 * mellP s := by
  have h1 : bB s = -mellU (fun y => thF1 y * thG0 y) s := by
    rw [bB, mellU_eq_integral]
  have iP : Integrable (fun u : ℝ => besselI0 (Real.exp u) ^ 2 * besselI1 (Real.exp u)
      * besselK0 (Real.exp u) ^ 5 * Real.exp ((s + 1) * u)) :=
    integrable_besselP_exp (by linarith) (by linarith)
  have iM : Integrable (fun u : ℝ => besselI0 (Real.exp u) ^ 2 * besselK0 (Real.exp u) ^ 4
      * Real.exp (s * u)) := integrable_besselIK_exp 2 0 hs0 (by linarith)
  have e : (fun u : ℝ => thF1 (Real.exp u) * thG0 (Real.exp u) * Real.exp (s * u))
      = fun u : ℝ => 4 * (besselI0 (Real.exp u) ^ 2 * besselI1 (Real.exp u)
          * besselK0 (Real.exp u) ^ 5 * Real.exp ((s + 1) * u))
        - 3 * (besselI0 (Real.exp u) ^ 2 * besselK0 (Real.exp u) ^ 4 * Real.exp (s * u)) := by
    funext u
    rw [thF1_mul_thG0 (Real.exp_pos u), show (s + 1) * u = u + s * u by ring, Real.exp_add]
    ring
  rw [h1, mellM, mellP]
  show -(∫ u : ℝ, thF1 (Real.exp u) * thG0 (Real.exp u) * Real.exp (s * u))
    = 3 * (∫ u : ℝ, besselI0 (Real.exp u) ^ 2 * besselK0 (Real.exp u) ^ 4 * Real.exp (s * u))
      - 4 * (∫ u : ℝ, besselI0 (Real.exp u) ^ 2 * besselI1 (Real.exp u)
          * besselK0 (Real.exp u) ^ 5 * Real.exp ((s + 1) * u))
  rw [e, integral_sub (iP.const_mul 4) (iM.const_mul 3), integral_const_mul, integral_const_mul]
  ring

/-- **`B(s) = (4/5) P(s) + (3/5) s M₃₅(s)`** for `0 < s ≤ 1`. -/
theorem bB_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    bB s = 4 / 5 * mellP s + 3 / 5 * s * mellM 3 5 s := by
  rw [bB_eq_mell hs0 hs1, mellM24_eq hs0 hs1]
  ring

theorem abs_thF1_le_log : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → |thF1 t| ≤ C * Eb t ^ 3 := by
  refine ⟨Bser 1 + 3 * Real.exp 1, fun t ht ht1 => ?_⟩
  have hE := one_le_Eb ht ht1
  have hK : |besselK0 t| ≤ Eb t := kty_besselK0.2.1 t ht ht1
  have hK2 : |besselK0 t ^ 2| ≤ Eb t ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hK 2
  have hK3 : |besselK0 t ^ 3| ≤ Eb t ^ 3 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hK 3
  have a1 : |(t * besselI1 t) * besselK0 t ^ 3| ≤ Bser 1 * t * Eb t ^ 3 :=
    abs_mul_le_of (abs_mul_besselI1_le ht ht1) hK3
  have a2 : |besselI0 t * besselK0 t ^ 2 * (t * besselK1 t)| ≤ Real.exp 1 * Eb t ^ 2 * 1 :=
    abs_mul_le_of (abs_mul_le_of (ity_besselI0.2.1 t ht ht1) hK2) (abs_mul_besselK1_le_one ht)
  have hE3 : Eb t ^ 2 ≤ Eb t ^ 3 := pow_le_pow_right₀ hE (by norm_num)
  have hB := Bser_one_nonneg
  have s1 := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hB (pow_nonneg (by linarith) 3))
  have s2 := mul_le_mul_of_nonneg_left hE3 (Real.exp_pos 1).le
  show |(t * besselI1 t) * besselK0 t ^ 3 + (-3) * (besselI0 t * besselK0 t ^ 2 * (t * besselK1 t))|
    ≤ (Bser 1 + 3 * Real.exp 1) * Eb t ^ 3
  rw [abs_le] at a1 a2 ⊢
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, s1, s2]

theorem abs_thG0_le_log {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |thG0 t| ≤ Real.exp 1 ^ 2 * Eb t ^ 2 := by
  have hK : |besselK0 t| ≤ Eb t := kty_besselK0.2.1 t ht ht1
  have hI := ity_besselI0.2.1 t ht ht1
  have hK2 : |besselK0 t ^ 2| ≤ Eb t ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hK 2
  have hI2 : |besselI0 t ^ 2| ≤ Real.exp 1 ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hI 2
  exact abs_mul_le_of hI2 hK2

/-- Integrability on `(0, ∞)` from a log bound on `(0, 1]` and a majorant beyond `1`. -/
theorem integrableOn_Ioi0_split {φ ψ : ℝ → ℝ} (hc : ContinuousOn φ (Ioi 0)) {k : ℕ} {a C1 : ℝ}
    (ha : -1 < a) (h1 : ∀ t : ℝ, 0 < t → t ≤ 1 → |φ t| ≤ C1 * (Eb t ^ k * t ^ a))
    (hψ : IntegrableOn ψ (Ioi 1)) (h2 : ∀ t : ℝ, 1 < t → |φ t| ≤ ψ t) :
    IntegrableOn φ (Ioi 0) := by
  have i1 : IntegrableOn φ (Ioc 0 1) :=
    Integrable.mono' ((integrableOn_Eb_pow_rpow (k := k) ha).const_mul C1)
      ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => by
        rw [Real.norm_eq_abs]; exact h1 t ht.1 ht.2))
  have i2 : IntegrableOn φ (Ioi 1) :=
    Integrable.mono' hψ ((hc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
        rw [Real.norm_eq_abs]; exact h2 t ht))
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact i1.union i2

theorem continuousOn_rpow_Ioi (a : ℝ) : ContinuousOn (fun t : ℝ => t ^ a) (Ioi 0) :=
  ContinuousOn.rpow_const (continuousOn_id (s := Ioi (0 : ℝ)))
    (fun t ht => Or.inl (show (0 : ℝ) < t from ht).ne')

theorem pdom_far_le {ψ : ℝ → ℝ} (hψ : PDom ψ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 < t → |ψ t| ≤ C * t ^ (-2 : ℝ) := by
  obtain ⟨_, C, hC, _, hfar⟩ := hψ
  refine ⟨C, hC, fun t ht => ?_⟩
  have ht0 : (0 : ℝ) < t := by linarith
  have h := hfar t ht.le
  have e : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
    rw [Real.rpow_neg ht0.le, Real.rpow_two]
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith [mul_comm (t ^ 2) |ψ t|]

theorem integrableOn_thG0_rpow {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    IntegrableOn (fun y : ℝ => thG0 y * y ^ (s - 1)) (Ioi 0) := by
  obtain ⟨C, hC, hfar⟩ := pdom_far_le pdom_thG0
  refine integrableOn_Ioi0_split (k := 2) (a := s - 1) (C1 := Real.exp 1 ^ 2)
    (continuousOn_thG0.mul (continuousOn_rpow_Ioi _)) (by linarith)
    (fun t ht ht1 => ?_) ((integrableOn_Ioi_rpow_of_lt (by linarith : s - 3 < -1) one_pos).const_mul C)
    (fun t ht => ?_)
  · have hp : 0 < t ^ (s - 1) := Real.rpow_pos_of_pos ht _
    rw [abs_mul, abs_of_pos hp]
    calc |thG0 t| * t ^ (s - 1) ≤ Real.exp 1 ^ 2 * Eb t ^ 2 * t ^ (s - 1) :=
          mul_le_mul_of_nonneg_right (abs_thG0_le_log ht ht1) hp.le
      _ = Real.exp 1 ^ 2 * (Eb t ^ 2 * t ^ (s - 1)) := by ring
  · have ht0 : (0 : ℝ) < t := by linarith
    have hp : 0 < t ^ (s - 1) := Real.rpow_pos_of_pos ht0 _
    rw [abs_mul, abs_of_pos hp]
    have e : t ^ (-2 : ℝ) * t ^ (s - 1) = t ^ (s - 3) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    calc |thG0 t| * t ^ (s - 1) ≤ C * t ^ (-2 : ℝ) * t ^ (s - 1) :=
          mul_le_mul_of_nonneg_right (hfar t ht) hp.le
      _ = C * t ^ (s - 3) := by rw [mul_assoc, e]

theorem integrableOn_thG1_rpow {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    IntegrableOn (fun y : ℝ => thG1 y * y ^ (s - 1)) (Ioi 0) := by
  obtain ⟨C1, hC1⟩ := abs_thG1_le_log
  refine integrableOn_Ioi0_split (k := 2) (a := s - 1) (C1 := |C1|)
    (continuousOn_thG1.mul (continuousOn_rpow_Ioi _)) (by linarith)
    (fun t ht ht1 => ?_) ((integrableOn_Ioi_rpow_of_lt (by linarith : s - 3 < -1) one_pos).const_mul 16)
    (fun t ht => ?_)
  · have hp : 0 < t ^ (s - 1) := Real.rpow_pos_of_pos ht _
    rw [abs_mul, abs_of_pos hp]
    have hC : C1 * Eb t ^ 2 ≤ |C1| * Eb t ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self C1) (sq_nonneg _)
    calc |thG1 t| * t ^ (s - 1) ≤ |C1| * Eb t ^ 2 * t ^ (s - 1) :=
          mul_le_mul_of_nonneg_right ((hC1 t ht ht1).trans hC) hp.le
      _ = |C1| * (Eb t ^ 2 * t ^ (s - 1)) := by ring
  · have ht0 : (0 : ℝ) < t := by linarith
    have hp : 0 < t ^ (s - 3) := Real.rpow_pos_of_pos ht0 _
    have h1 := abs_tsq_thG1_le ht0
    rw [abs_mul, abs_of_pos (pow_pos ht0 2)] at h1
    have e : t ^ (s - 1) = t ^ 2 * t ^ (s - 3) := by
      rw [show (s - 1) = (2 : ℝ) + (s - 3) by ring, Real.rpow_add ht0, Real.rpow_two]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _), e]
    calc |thG1 t| * (t ^ 2 * t ^ (s - 3)) = (t ^ 2 * |thG1 t|) * t ^ (s - 3) := by ring
      _ ≤ 16 * t ^ (s - 3) := mul_le_mul_of_nonneg_right h1 hp.le

theorem integrableOn_thF1_thG0 {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    IntegrableOn (fun y : ℝ => thF1 y * thG0 y * y ^ (s - 1)) (Ioi 0) := by
  obtain ⟨C1, hC1⟩ := abs_thF1_le_log
  obtain ⟨_, CF, hCF, N, _, hN⟩ := hdom_thF1
  obtain ⟨CG, hCG, hfar⟩ := pdom_far_le pdom_thG0
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine integrableOn_Ioi0_split (k := 5) (a := s - 1) (C1 := |C1| * Real.exp 1 ^ 2)
    ((hdom_thF1.1.mul continuousOn_thG0).mul (continuousOn_rpow_Ioi _)) (by linarith)
    (fun t ht ht1 => ?_)
    (((Real.GammaIntegral_convergent (by linarith : (0 : ℝ) < (N : ℝ) + s)).mono_set
      (Ioi_subset_Ioi zero_le_one)).const_mul (CF * CG)) (fun t ht => ?_)
  · have hp : 0 < t ^ (s - 1) := Real.rpow_pos_of_pos ht _
    have hE := one_le_Eb ht ht1
    rw [abs_mul, abs_mul, abs_of_pos hp]
    have hC : C1 * Eb t ^ 3 ≤ |C1| * Eb t ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self C1) (pow_nonneg (by linarith) 3)
    have h1 := (hC1 t ht ht1).trans hC
    have h2 := abs_thG0_le_log ht ht1
    calc |thF1 t| * |thG0 t| * t ^ (s - 1)
        ≤ (|C1| * Eb t ^ 3) * (Real.exp 1 ^ 2 * Eb t ^ 2) * t ^ (s - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) 3))) hp.le
      _ = |C1| * Real.exp 1 ^ 2 * (Eb t ^ 5 * t ^ (s - 1)) := by ring
  · have ht0 : (0 : ℝ) < t := by linarith
    have hp : 0 < t ^ (s - 1) := Real.rpow_pos_of_pos ht0 _
    have h1 := hN t ht.le
    have h2 := hfar t ht
    have hm : t ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht.le (by norm_num)
    have h2' : |thG0 t| ≤ CG := h2.trans (mul_le_of_le_one_right hCG hm)
    rw [abs_mul, abs_mul, abs_of_pos hp]
    have e : t ^ N * t ^ (s - 1) = t ^ ((N : ℝ) + s - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
      congr 1
      ring
    calc |thF1 t| * |thG0 t| * t ^ (s - 1)
        ≤ (CF * t ^ N * Real.exp (-t)) * CG * t ^ (s - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2' (abs_nonneg _)
            (le_trans (abs_nonneg _) h1)) hp.le
      _ = CF * CG * (Real.exp (-t) * t ^ ((N : ℝ) + s - 1)) := by
          rw [← e]
          ring

theorem tendsto_thG0_atTop : Tendsto thG0 atTop (𝓝 0) := by
  obtain ⟨C, hC, hfar⟩ := pdom_far_le pdom_thG0
  have hlim : Tendsto (fun t : ℝ => C * t ^ (-2 : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul C
    rw [mul_zero] at h
    exact h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [Real.norm_eq_abs]
  exact hfar t ht

/-- `E(t)^k t^a ≤ C t^{a - b}` on `(0, 1]` for `b > 0`. -/
theorem Eb_pow_le_rpow (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → Eb t ^ k ≤ C * t ^ (-b) := by
  set δ : ℝ := b / ((k : ℝ) + 1) with hδdef
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hδ : 0 < δ := div_pos hb hk1
  have hA : 0 < (1 + 1 / δ) * (2 : ℝ) ^ δ :=
    mul_pos (by have := one_div_pos.mpr hδ; linarith) (Real.rpow_pos_of_pos two_pos _)
  refine ⟨((1 + 1 / δ) * (2 : ℝ) ^ δ) ^ k, pow_nonneg hA.le k, fun t ht ht1 => ?_⟩
  have hE1 := one_le_Eb ht ht1
  have hE := Eb_le_rpow hδ ht ht1
  have hd : (2 / t) ^ δ = (2 : ℝ) ^ δ * t ^ (-δ) := by
    rw [Real.div_rpow zero_le_two ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
  have hE' : Eb t ≤ (1 + 1 / δ) * (2 : ℝ) ^ δ * t ^ (-δ) := by
    rw [hd] at hE
    exact hE.trans (le_of_eq (by ring))
  have h1 := pow_le_pow_left₀ (by linarith) hE' k
  rw [mul_pow, ← Real.rpow_natCast (t ^ (-δ)) k, ← Real.rpow_mul ht.le] at h1
  have hδk : δ * k ≤ b := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hk1]
    nlinarith
  have h3 : t ^ (-δ * (k : ℝ)) ≤ t ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  exact h1.trans (mul_le_mul_of_nonneg_left h3 (pow_nonneg hA.le k))

/-- **The inner integral**: `∫₀^∞ G(t) min(τ,t)^s dt = s Γ(τ)` for `0 < s ≤ 1`, `τ > 0`. -/
theorem inner_min_integral {s τ : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hτ : 0 < τ) :
    ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * min τ t ^ s = s * gamG s τ := by
  have hs2 : s < 2 := by linarith
  have iG1 := integrableOn_thG1_rpow hs0 hs2
  have iG0 := integrableOn_thG0_rpow hs0 hs2
  -- the two pieces
  have hA : EqOn (fun t : ℝ => (-thG1 t / t) * min τ t ^ s) (fun t : ℝ => -(thG1 t * t ^ (s - 1)))
      (Ioc 0 τ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht.1
    show (-thG1 t / t) * min τ t ^ s = -(thG1 t * t ^ (s - 1))
    rw [min_eq_right ht.2, Real.rpow_sub_one ht0.ne']
    field_simp
    all_goals ring
  have hB : EqOn (fun t : ℝ => (-thG1 t / t) * min τ t ^ s) (fun t : ℝ => τ ^ s * (-(thG1 t / t)))
      (Ioi τ) := by
    intro t ht
    show (-thG1 t / t) * min τ t ^ s = τ ^ s * (-(thG1 t / t))
    rw [min_eq_left (le_of_lt ht)]
    ring
  have iA : IntegrableOn (fun t : ℝ => -(thG1 t * t ^ (s - 1))) (Ioc 0 τ) :=
    (iG1.mono_set Ioc_subset_Ioi_self).neg
  have iB0 : IntegrableOn (fun t : ℝ => thG1 t / t) (Ioi τ) := by
    refine Integrable.mono' ((iG1.mono_set (Ioi_subset_Ioi hτ.le)).norm.const_mul (τ ^ (-s)))
      ((continuousOn_thG1.div continuousOn_id (fun t ht => (show (0 : ℝ) < t from ht).ne')).mono
        (Ioi_subset_Ioi hτ.le) |>.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := lt_trans hτ ht
    have e : thG1 t / t = thG1 t * t ^ (s - 1) * t ^ (-s) := by
      rw [mul_assoc, ← Real.rpow_add ht0, show s - 1 + -s = -1 by ring, Real.rpow_neg_one,
        div_eq_mul_inv]
    have h3 : t ^ (-s) ≤ τ ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hτ (le_of_lt ht) (by linarith)
    simp only [Real.norm_eq_abs]
    rw [e, abs_mul (thG1 t * t ^ (s - 1)) (t ^ (-s)), abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc |thG1 t * t ^ (s - 1)| * t ^ (-s) ≤ |thG1 t * t ^ (s - 1)| * τ ^ (-s) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = τ ^ (-s) * |thG1 t * t ^ (s - 1)| := by ring
  have iB : IntegrableOn (fun t : ℝ => τ ^ s * (-(thG1 t / t))) (Ioi τ) := iB0.neg.const_mul _
  have iAA := IntegrableOn.congr_fun iA hA.symm measurableSet_Ioc
  have iBB := IntegrableOn.congr_fun iB hB.symm measurableSet_Ioi
  -- the integral on (0, τ]
  have hftc : ∫ t in (0 : ℝ)..τ, (thG1 t * t ^ (s - 1) + s * (thG0 t * t ^ (s - 1)))
      = thG0 τ * τ ^ s := by
    have hderiv : ∀ x ∈ Ioo (0 : ℝ) τ, HasDerivAt (fun t : ℝ => thG0 t * t ^ s)
        (thG1 x * x ^ (s - 1) + s * (thG0 x * x ^ (s - 1))) x := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx.1
      have h := (hasDerivAt_thG0 hx0).mul (Real.hasDerivAt_rpow_const (p := s) (Or.inl hx0.ne'))
      convert h using 1
      rw [Real.rpow_sub_one hx0.ne']
      field_simp
      all_goals ring
    have hint : IntervalIntegrable (fun t : ℝ => thG1 t * t ^ (s - 1) + s * (thG0 t * t ^ (s - 1)))
        volume 0 τ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le]
      exact (iG1.mono_set Ioc_subset_Ioi_self).add ((iG0.mono_set Ioc_subset_Ioi_self).const_mul s)
    have ha : Tendsto (fun t : ℝ => thG0 t * t ^ s) (𝓝[>] 0) (𝓝 0) := by
      obtain ⟨C, hC, hCb⟩ := Eb_pow_le_rpow 2 (by linarith : (0 : ℝ) < s / 2)
      have hlim : Tendsto (fun t : ℝ => Real.exp 1 ^ 2 * C * t ^ (s / 2)) (𝓝[>] 0) (𝓝 0) := by
        have h := ((Real.continuousAt_rpow_const 0 (s / 2) (Or.inr (by linarith))).tendsto).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        rw [Real.zero_rpow (by linarith : s / 2 ≠ 0)] at h
        have h2 := h.const_mul (Real.exp 1 ^ 2 * C)
        rw [mul_zero] at h2
        exact h2
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
      have ht0 : (0 : ℝ) < t := ht.1
      have hp : 0 < t ^ s := Real.rpow_pos_of_pos ht0 _
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
      have h1 := abs_thG0_le_log ht0 ht.2.le
      have h2 := hCb t ht0 ht.2.le
      have e : t ^ (-(s / 2)) * t ^ s = t ^ (s / 2) := by
        rw [← Real.rpow_add ht0]
        congr 1
        ring
      calc |thG0 t| * t ^ s ≤ Real.exp 1 ^ 2 * Eb t ^ 2 * t ^ s :=
            mul_le_mul_of_nonneg_right h1 hp.le
        _ ≤ Real.exp 1 ^ 2 * (C * t ^ (-(s / 2))) * t ^ s :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hp.le
        _ = Real.exp 1 ^ 2 * C * t ^ (s / 2) := by rw [← e]; ring
    have hb : Tendsto (fun t : ℝ => thG0 t * t ^ s) (𝓝[<] τ) (𝓝 (thG0 τ * τ ^ s)) := by
      have hc : ContinuousAt (fun t : ℝ => thG0 t * t ^ s) τ :=
        (continuousOn_thG0.continuousAt (Ioi_mem_nhds hτ)).mul
          (Real.continuousAt_rpow_const τ s (Or.inl hτ.ne'))
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hτ hderiv hint ha hb
    rw [h, sub_zero]
  have hA_val : ∫ t in Ioc (0 : ℝ) τ, -(thG1 t * t ^ (s - 1)) = s * gamG s τ - thG0 τ * τ ^ s := by
    have hi1 : IntervalIntegrable (fun t : ℝ => thG1 t * t ^ (s - 1)) volume 0 τ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le]
      exact iG1.mono_set Ioc_subset_Ioi_self
    have hi2 : IntervalIntegrable (fun t : ℝ => s * (thG0 t * t ^ (s - 1))) volume 0 τ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le]
      exact (iG0.mono_set Ioc_subset_Ioi_self).const_mul s
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul] at hftc
    rw [integral_neg, ← intervalIntegral.integral_of_le hτ.le, gamG]
    linarith
  -- the integral on (τ, ∞)
  have hB_val : ∫ t in Ioi τ, τ ^ s * (-(thG1 t / t)) = τ ^ s * thG0 τ := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (f := thG0) (f' := fun t => thG1 t / t)
      (a := τ) (fun x hx => hasDerivAt_thG0 (lt_of_lt_of_le hτ hx)) iB0 tendsto_thG0_atTop
    rw [integral_const_mul, integral_neg, h]
    ring
  rw [← Set.Ioc_union_Ioi_eq_Ioi hτ.le, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    iAA iBB, setIntegral_congr_fun measurableSet_Ioc hA, setIntegral_congr_fun measurableSet_Ioi hB,
    hA_val, hB_val]
  ring

theorem hasDerivAt_gamG {s τ : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hτ : 0 < τ) :
    HasDerivAt (gamG s) (thG0 τ * τ ^ (s - 1)) τ := by
  have iG0 := integrableOn_thG0_rpow hs0 hs2
  have hc : ContinuousOn (fun y : ℝ => thG0 y * y ^ (s - 1)) (Ioi 0) :=
    continuousOn_thG0.mul (continuousOn_rpow_Ioi _)
  have hi : IntervalIntegrable (fun y : ℝ => thG0 y * y ^ (s - 1)) volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le]
    exact iG0.mono_set Ioc_subset_Ioi_self
  exact intervalIntegral.integral_hasDerivAt_right hi
    (hc.stronglyMeasurableAtFilter isOpen_Ioi τ hτ) (hc.continuousAt (Ioi_mem_nhds hτ))

theorem abs_gamG_le_tot {s τ : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hτ : 0 ≤ τ) :
    |gamG s τ| ≤ ∫ y in Ioi (0 : ℝ), |thG0 y * y ^ (s - 1)| := by
  have iG0 := integrableOn_thG0_rpow hs0 hs2
  rw [gamG, intervalIntegral.integral_of_le hτ]
  calc |∫ y in Ioc (0 : ℝ) τ, thG0 y * y ^ (s - 1)|
      ≤ ∫ y in Ioc (0 : ℝ) τ, |thG0 y * y ^ (s - 1)| := abs_integral_le_integral_abs
    _ ≤ ∫ y in Ioi (0 : ℝ), |thG0 y * y ^ (s - 1)| :=
        setIntegral_mono_set iG0.abs (Eventually.of_forall fun y => abs_nonneg _)
          (Ioc_subset_Ioi_self.eventuallyLE)

theorem abs_gamG_le_small {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → |gamG s τ| ≤ K * τ ^ (s / 2) := by
  obtain ⟨C, hC, hCb⟩ := Eb_pow_le_rpow 2 (by linarith : (0 : ℝ) < s / 2)
  refine ⟨Real.exp 1 ^ 2 * C * (2 / s), mul_nonneg (mul_nonneg (by positivity) hC)
    (div_nonneg zero_le_two hs0.le), fun τ hτ hτ1 => ?_⟩
  have iG0 := integrableOn_thG0_rpow hs0 hs2
  have hr : IntervalIntegrable (fun y : ℝ => Real.exp 1 ^ 2 * C * y ^ (s / 2 - 1)) volume 0 τ :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s / 2 - 1)).const_mul _
  have hval : ∫ y in (0 : ℝ)..τ, Real.exp 1 ^ 2 * C * y ^ (s / 2 - 1)
      = Real.exp 1 ^ 2 * C * (2 / s) * τ ^ (s / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      Real.zero_rpow (by linarith : s / 2 - 1 + 1 ≠ 0), sub_zero,
      show s / 2 - 1 + 1 = s / 2 by ring]
    ring
  rw [← hval, gamG, intervalIntegral.integral_of_le hτ.le, intervalIntegral.integral_of_le hτ.le]
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on (iG0.mono_set Ioc_subset_Ioi_self).abs
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).1 hr) measurableSet_Ioc (fun y hy => ?_))
  have hy0 : (0 : ℝ) < y := hy.1
  have hp : 0 < y ^ (s - 1) := Real.rpow_pos_of_pos hy0 _
  have hy1 : y ≤ 1 := le_trans hy.2 hτ1
  rw [abs_mul, abs_of_pos hp]
  have h1 := abs_thG0_le_log hy0 hy1
  have h2 := hCb y hy0 hy1
  have e : y ^ (-(s / 2)) * y ^ (s - 1) = y ^ (s / 2 - 1) := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  calc |thG0 y| * y ^ (s - 1) ≤ Real.exp 1 ^ 2 * Eb y ^ 2 * y ^ (s - 1) :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ ≤ Real.exp 1 ^ 2 * (C * y ^ (-(s / 2))) * y ^ (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hp.le
    _ = Real.exp 1 ^ 2 * C * y ^ (s / 2 - 1) := by rw [← e]; ring

theorem continuousOn_gamG {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) : ContinuousOn (gamG s) (Ioi 0) :=
  fun τ hτ => (hasDerivAt_gamG hs0 hs2 hτ).continuousAt.continuousWithinAt

theorem abs_gamG_le_const {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ τ : ℝ, 0 ≤ τ → |gamG s τ| ≤ T :=
  ⟨_, setIntegral_nonneg measurableSet_Ioi (fun y _ => abs_nonneg (thG0 y * y ^ (s - 1))),
    fun τ hτ => abs_gamG_le_tot hs0 hs2 hτ⟩

theorem abs_gamG_le_rpow {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, 0 < τ → |gamG s τ| ≤ M * τ ^ (s / 2) := by
  obtain ⟨K, hK, hKb⟩ := abs_gamG_le_small hs0 hs2
  obtain ⟨T, hT0, hTb⟩ := abs_gamG_le_const hs0 hs2
  refine ⟨K + T, add_nonneg hK hT0, fun τ hτ => ?_⟩
  have hp : 0 < τ ^ (s / 2) := Real.rpow_pos_of_pos hτ _
  rcases le_or_lt τ 1 with hτ1 | hτ1
  · have h := hKb τ hτ hτ1
    nlinarith
  · have h := hTb τ hτ.le
    have h1 : 1 ≤ τ ^ (s / 2) := Real.one_le_rpow hτ1.le (by linarith)
    nlinarith

/-- **The outer integral**: `∫₀^∞ F₂(τ) Γ(τ) dτ = B(s)` for `0 < s ≤ 1`. -/
theorem outer_min_integral {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∫ τ in Ioi (0 : ℝ), thF2 τ / τ * gamG s τ = bB s := by
  have hs2 : s < 2 := by linarith
  obtain ⟨M, hM, hMb⟩ := abs_gamG_le_rpow hs0 hs2
  have i1 : IntegrableOn (fun τ : ℝ => thF2 τ / τ * gamG s τ) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_F2_rpow hs0).const_mul M)
      (((hdom_thF2.1.div continuousOn_id (fun τ hτ => (show (0 : ℝ) < τ from hτ).ne')).mul
        (continuousOn_gamG hs0 hs2)).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun τ hτ => ?_))
    have hτ0 : (0 : ℝ) < τ := hτ
    rw [Real.norm_eq_abs, abs_mul]
    calc |thF2 τ / τ| * |gamG s τ| ≤ |thF2 τ / τ| * (M * τ ^ (s / 2)) :=
          mul_le_mul_of_nonneg_left (hMb τ hτ0) (abs_nonneg _)
      _ = M * (|thF2 τ / τ| * τ ^ (s / 2)) := by ring
  have i2 := integrableOn_thF1_thG0 hs0 hs2
  have hF0 : thF1 0 * gamG s 0 = 0 := by
    rw [gamG, intervalIntegral.integral_same, mul_zero]
  have hd : ∀ τ : ℝ, 0 < τ → HasDerivAt (fun x : ℝ => thF1 x * gamG s x)
      (thF2 τ / τ * gamG s τ + thF1 τ * thG0 τ * τ ^ (s - 1)) τ := by
    intro τ hτ
    have h := (hasDerivAt_thF1 hτ).mul (hasDerivAt_gamG hs0 hs2 hτ)
    convert h using 1
    ring
  -- `F → 0` at `0+`
  have h0 : Tendsto (fun x : ℝ => thF1 x * gamG s x) (𝓝[>] 0) (𝓝 0) := by
    obtain ⟨C1, hC1⟩ := abs_thF1_le_log
    obtain ⟨C, hC, hCb⟩ := Eb_pow_le_rpow 3 (by linarith : (0 : ℝ) < s / 4)
    have hlim : Tendsto (fun x : ℝ => |C1| * C * M * x ^ (s / 4)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuousAt_rpow_const 0 (s / 4) (Or.inr (by linarith))).tendsto).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rw [Real.zero_rpow (by linarith : s / 4 ≠ 0)] at h
      have h2 := h.const_mul (|C1| * C * M)
      rw [mul_zero] at h2
      exact h2
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hx1 : x ≤ 1 := hx.2.le
    have hE := one_le_Eb hx0 hx1
    rw [Real.norm_eq_abs, abs_mul]
    have a1 : |thF1 x| ≤ |C1| * Eb x ^ 3 :=
      (hC1 x hx0 hx1).trans (mul_le_mul_of_nonneg_right (le_abs_self C1) (pow_nonneg (by linarith) 3))
    have a2 := hMb x hx0
    have a3 := hCb x hx0 hx1
    have e : x ^ (-(s / 4)) * x ^ (s / 2) = x ^ (s / 4) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    calc |thF1 x| * |gamG s x| ≤ (|C1| * Eb x ^ 3) * (M * x ^ (s / 2)) :=
          mul_le_mul a1 a2 (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) 3))
      _ ≤ (|C1| * (C * x ^ (-(s / 4)))) * (M * x ^ (s / 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a3 (abs_nonneg _))
            (mul_nonneg hM (Real.rpow_pos_of_pos hx0 _).le)
      _ = |C1| * C * M * x ^ (s / 4) := by rw [← e]; ring
  -- `F → 0` at `∞`
  have hinf : Tendsto (fun x : ℝ => thF1 x * gamG s x) atTop (𝓝 0) := by
    obtain ⟨_, CF, hCF, N, _, hN⟩ := hdom_thF1
    obtain ⟨T, hT0, hTb⟩ := abs_gamG_le_const hs0 hs2
    have hlim : Tendsto (fun x : ℝ => CF * T * (x ^ N * Real.exp (-x))) atTop (𝓝 0) := by
      have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero N).const_mul (CF * T)
      rw [mul_zero] at h
      exact h
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    rw [Real.norm_eq_abs, abs_mul]
    have a1 := hN x hx
    have a2 : |gamG s x| ≤ T := hTb x hx0.le
    calc |thF1 x| * |gamG s x| ≤ (CF * x ^ N * Real.exp (-x)) * T :=
          mul_le_mul a1 a2 (abs_nonneg _) ((abs_nonneg _).trans a1)
      _ = CF * T * (x ^ N * Real.exp (-x)) := by ring
  have hz := integral_Ioi_deriv_eq_zero (F := fun x : ℝ => thF1 x * gamG s x)
    (F' := fun τ : ℝ => thF2 τ / τ * gamG s τ + thF1 τ * thG0 τ * τ ^ (s - 1)) hF0 hd h0 hinf
    (i1.add i2)
  rw [integral_add i1 i2] at hz
  rw [bB]
  linarith

/-- **The `min^s` part of the iterated integral**: `∫_τ F₂ ∫_t G min(τ,t)^s = s B(s)`. -/
theorem fubini_min {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∫ τ in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), thF2 τ / τ * (-thG1 t / t) * min τ t ^ s
      = s * bB s := by
  have hin : EqOn (fun τ : ℝ => ∫ t in Ioi (0 : ℝ), thF2 τ / τ * (-thG1 t / t) * min τ t ^ s)
      (fun τ : ℝ => s * (thF2 τ / τ * gamG s τ)) (Ioi 0) := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have e : (fun t : ℝ => thF2 τ / τ * (-thG1 t / t) * min τ t ^ s)
        = fun t : ℝ => thF2 τ / τ * ((-thG1 t / t) * min τ t ^ s) := by
      funext t
      ring
    show ∫ t in Ioi (0 : ℝ), thF2 τ / τ * (-thG1 t / t) * min τ t ^ s = s * (thF2 τ / τ * gamG s τ)
    rw [e, integral_const_mul, inner_min_integral hs0 hs1 hτ0]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_const_mul, outer_min_integral hs0 hs1]

end Tower.RV6
