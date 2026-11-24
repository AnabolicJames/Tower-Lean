import Mathlib
import Tower.RV6.BPMin

/-!
# RungBP, step 4: `pairS(s) = j(s) (s B(s) - H(s))`

`H(s) = ∫_τ F₂(τ) ∫_t G(t) k_H(τ,t)` (`hH`), `F₂ = θ²f/τ`, `G = -θg/t`.

* `k_H` is continuous on `ℝ²` (`continuous_kerH`, from the joint continuity of `M_s`).
* `0 ≤ h_s(w) ≤ (s²/2) w` on `[0, 1]` (`hS_le_sq`), so `k_H ≤ (s²/2)(min/max)² max^s` (`kerH_le_left`, `kerH_le_right`).
* If `|φ(t)| ≤ C t^{-p}` with `s - 1 < p < 3`, then `t ↦ φ(t) k_H(τ,t)` is integrable and
  `∫ |φ k_H| ≤ (s²/2) C (1/(3-p) + 1/(p+1-s)) τ^{1+s-p}` (`integrableOn_kerH_mul`, `integral_abs_kerH_le`).
* `|G(t)| ≤ C_b t^{-1-b}` (`abs_G_le_rpow`); with `p = 1 + s/2` the inner integral is `O(τ^{s/2})`, and the inner integral
  of wave 60 splits into `s Γ(τ) - ∫ G k_H` (`pairS_eq_sB_sub_H`).
-/

namespace Tower.RV6

open Real MeasureTheory Set Filter Topology

theorem continuous_angM2 {s : ℝ} (hs : 0 ≤ s) : Continuous (fun p : ℝ × ℝ => angM s p.1 p.2) := by
  have h : Continuous (Function.uncurry fun (p : ℝ × ℝ) (θ : ℝ) => rhoN p.1 p.2 θ ^ s) := by
    have hc : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.1 : ℝ) : ℂ) + (q.1.2 : ℂ) * cexpR (2 * π * q.2)) :=
      (Complex.continuous_ofReal.comp (continuous_fst.fst)).add
        ((Complex.continuous_ofReal.comp continuous_fst.snd).mul
          (continuous_cexpR_two_pi.comp continuous_snd))
    exact (continuous_norm.comp hc).rpow_const (fun _ => Or.inr hs)
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := (volume : Measure ℝ)) h 0 1
  refine h2.congr fun p => ?_
  show ∫ θ in (0 : ℝ)..1, rhoN p.1 p.2 θ ^ s = angM s p.1 p.2
  rw [angM, intervalIntegral.integral_of_le zero_le_one]

theorem continuous_kerH {s : ℝ} (hs : 0 ≤ s) : Continuous (fun p : ℝ × ℝ => kerH s p.1 p.2) := by
  have h := ((continuous_fst.min continuous_snd).rpow_const (fun _ => Or.inr hs)).sub
    (((continuous_fst.rpow_const (fun _ => Or.inr hs)).add
      (continuous_snd.rpow_const (fun _ => Or.inr hs))).sub (continuous_angM2 hs))
  exact h

/-- `0 ≤ h_s(w) ≤ (s²/2) w` on `[0, 1]`, the endpoint by continuity. -/
theorem hS_le_sq {s w : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    hS s w ≤ s ^ 2 / 2 * w := by
  rcases hw1.lt_or_eq with h | h
  · exact hS_le hs0 hs2 hw0 h
  · subst h
    have hf : Tendsto (hS s) (𝓝[<] 1) (𝓝 (hS s 1)) :=
      (continuous_hS hs0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hg : Tendsto (fun w : ℝ => s ^ 2 / 2 * w) (𝓝[<] 1) (𝓝 (s ^ 2 / 2 * 1)) :=
      ((continuous_const.mul continuous_id).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hf hg ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with w hw
    exact hS_le hs0 hs2 hw.1.le hw.2

theorem kerH_le_left {s τ t : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (ht : 0 < t) (htτ : t ≤ τ) :
    kerH s τ t ≤ s ^ 2 / 2 * (t / τ) ^ 2 * τ ^ s := by
  have hτ : 0 < τ := lt_of_lt_of_le ht htτ
  rw [kerH_eq_le ht htτ]
  have hw1 : (t / τ) ^ 2 ≤ 1 :=
    pow_le_one₀ (div_nonneg ht.le hτ.le) ((div_le_one hτ).2 htτ)
  have h := hS_le_sq hs0 hs2 (sq_nonneg (t / τ)) hw1
  calc τ ^ s * hS s ((t / τ) ^ 2) ≤ τ ^ s * (s ^ 2 / 2 * (t / τ) ^ 2) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hτ.le s)
    _ = s ^ 2 / 2 * (t / τ) ^ 2 * τ ^ s := by ring

theorem kerH_le_right {s τ t : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ) (hτt : τ ≤ t) :
    kerH s τ t ≤ s ^ 2 / 2 * (τ / t) ^ 2 * t ^ s := by
  rw [kerH_symm]
  exact kerH_le_left hs0 hs2 hτ hτt

theorem continuousOn_mul_kerH {s τ : ℝ} {φ : ℝ → ℝ} (hs : 0 ≤ s) (hφ : ContinuousOn φ (Ioi 0)) :
    ContinuousOn (fun t : ℝ => φ t * kerH s τ t) (Ioi 0) :=
  hφ.mul ((continuous_kerH hs).comp
    ((continuous_const : Continuous fun _ : ℝ => τ).prodMk continuous_id)).continuousOn

theorem rpow_alg_left {τ t p s : ℝ} (hτ : 0 < τ) (ht : 0 < t) :
    t ^ (-p) * ((t / τ) ^ 2 * τ ^ s) = τ ^ (s - 2) * t ^ (2 - p) := by
  rw [Real.rpow_sub hτ, Real.rpow_sub ht, Real.rpow_two, Real.rpow_two, Real.rpow_neg ht.le, div_pow]
  have h1 : t ^ p ≠ 0 := (Real.rpow_pos_of_pos ht p).ne'
  have h2 : τ ≠ 0 := hτ.ne'
  have h3 : t ≠ 0 := ht.ne'
  field_simp
  all_goals ring

theorem rpow_alg_right {τ t p s : ℝ} (ht : 0 < t) :
    t ^ (-p) * ((τ / t) ^ 2 * t ^ s) = τ ^ 2 * t ^ (s - 2 - p) := by
  rw [Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_two, Real.rpow_neg ht.le, div_pow]
  have h1 : t ^ p ≠ 0 := (Real.rpow_pos_of_pos ht p).ne'
  have h3 : t ≠ 0 := ht.ne'
  field_simp
  all_goals ring

theorem abs_mul_kerH_le_left {s τ t p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) (ht : 0 < t) (htτ : t ≤ τ) :
    |φ t * kerH s τ t| ≤ s ^ 2 / 2 * C * τ ^ (s - 2) * t ^ (2 - p) := by
  have hτ : 0 < τ := lt_of_lt_of_le ht htτ
  have hk0 := kerH_nonneg hs0 hs2 hτ ht
  have hk := kerH_le_left hs0 hs2 ht htτ
  rw [abs_mul, abs_of_nonneg hk0]
  have hp := Real.rpow_pos_of_pos ht (-p)
  calc |φ t| * kerH s τ t ≤ (C * t ^ (-p)) * (s ^ 2 / 2 * (t / τ) ^ 2 * τ ^ s) :=
        mul_le_mul (hC t ht) hk hk0 (mul_nonneg hC0 hp.le)
    _ = s ^ 2 / 2 * C * (t ^ (-p) * ((t / τ) ^ 2 * τ ^ s)) := by ring
    _ = s ^ 2 / 2 * C * τ ^ (s - 2) * t ^ (2 - p) := by rw [rpow_alg_left hτ ht]; ring

theorem abs_mul_kerH_le_right {s τ t p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) (hτ : 0 < τ) (hτt : τ ≤ t) :
    |φ t * kerH s τ t| ≤ s ^ 2 / 2 * C * τ ^ 2 * t ^ (s - 2 - p) := by
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  have hk0 := kerH_nonneg hs0 hs2 hτ ht
  have hk := kerH_le_right hs0 hs2 hτ hτt
  rw [abs_mul, abs_of_nonneg hk0]
  have hp := Real.rpow_pos_of_pos ht (-p)
  calc |φ t| * kerH s τ t ≤ (C * t ^ (-p)) * (s ^ 2 / 2 * (τ / t) ^ 2 * t ^ s) :=
        mul_le_mul (hC t ht) hk hk0 (mul_nonneg hC0 hp.le)
    _ = s ^ 2 / 2 * C * (t ^ (-p) * ((τ / t) ^ 2 * t ^ s)) := by ring
    _ = s ^ 2 / 2 * C * τ ^ 2 * t ^ (s - 2 - p) := by rw [rpow_alg_right ht]; ring

theorem integrableOn_kerH_left {s τ p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ)
    (hp3 : p < 3) (hφ : ContinuousOn φ (Ioi 0)) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) :
    IntegrableOn (fun t : ℝ => φ t * kerH s τ t) (Ioc 0 τ) := by
  have hr : IntegrableOn (fun t : ℝ => t ^ (2 - p)) (Ioc 0 τ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 2 - p))
  refine Integrable.mono' (hr.const_mul (s ^ 2 / 2 * C * τ ^ (s - 2)))
    (((continuousOn_mul_kerH hs0 hφ).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))
  rw [Real.norm_eq_abs]
  exact abs_mul_kerH_le_left hs0 hs2 hC0 hC ht.1 ht.2

theorem integrableOn_kerH_right {s τ p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ)
    (hp1 : s - 1 < p) (hφ : ContinuousOn φ (Ioi 0)) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) :
    IntegrableOn (fun t : ℝ => φ t * kerH s τ t) (Ioi τ) := by
  have hr : IntegrableOn (fun t : ℝ => t ^ (s - 2 - p)) (Ioi τ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hτ
  refine Integrable.mono' (hr.const_mul (s ^ 2 / 2 * C * τ ^ 2))
    (((continuousOn_mul_kerH hs0 hφ).mono (Ioi_subset_Ioi hτ.le)).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
  rw [Real.norm_eq_abs]
  exact abs_mul_kerH_le_right hs0 hs2 hC0 hC hτ (le_of_lt ht)

theorem integrableOn_kerH_mul {s τ p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ)
    (hp1 : s - 1 < p) (hp3 : p < 3) (hφ : ContinuousOn φ (Ioi 0)) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) :
    IntegrableOn (fun t : ℝ => φ t * kerH s τ t) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hτ.le]
  exact (integrableOn_kerH_left hs0 hs2 hτ hp3 hφ hC0 hC).union
    (integrableOn_kerH_right hs0 hs2 hτ hp1 hφ hC0 hC)

/-- **The inner bound** `∫ |φ k_H| ≤ (s²/2) C (1/(3-p) + 1/(p+1-s)) τ^{1+s-p}`. -/
theorem integral_abs_kerH_le {s τ p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ)
    (hp1 : s - 1 < p) (hp3 : p < 3) (hφ : ContinuousOn φ (Ioi 0)) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) :
    ∫ t in Ioi (0 : ℝ), |φ t * kerH s τ t|
      ≤ s ^ 2 / 2 * C * (1 / (3 - p) + 1 / (p + 1 - s)) * τ ^ (1 + s - p) := by
  have iL := (integrableOn_kerH_left hs0 hs2 hτ hp3 hφ hC0 hC).abs
  have iR := (integrableOn_kerH_right hs0 hs2 hτ hp1 hφ hC0 hC).abs
  have hrL : IntegrableOn (fun t : ℝ => t ^ (2 - p)) (Ioc 0 τ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 2 - p))
  have hrR : IntegrableOn (fun t : ℝ => t ^ (s - 2 - p)) (Ioi τ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hτ
  have vL : ∫ t in Ioc (0 : ℝ) τ, t ^ (2 - p) = τ ^ (3 - p) / (3 - p) := by
    rw [← intervalIntegral.integral_of_le hτ.le, integral_rpow (r := 2 - p) (Or.inl (by linarith)),
      Real.zero_rpow (by linarith : 2 - p + 1 ≠ 0), sub_zero, show 2 - p + 1 = 3 - p by ring]
  have vR : ∫ t in Ioi τ, t ^ (s - 2 - p) = τ ^ (s - 1 - p) / (p + 1 - s) := by
    rw [integral_Ioi_rpow_of_lt (a := s - 2 - p) (by linarith) hτ, show s - 2 - p + 1 = s - 1 - p by ring]
    have : p + 1 - s = -(s - 1 - p) := by ring
    rw [this, div_neg, neg_div]
  have bL : ∫ t in Ioc (0 : ℝ) τ, |φ t * kerH s τ t|
      ≤ ∫ t in Ioc (0 : ℝ) τ, s ^ 2 / 2 * C * τ ^ (s - 2) * t ^ (2 - p) := by
    refine setIntegral_mono_on iL ?_ measurableSet_Ioc (fun t ht => ?_)
    · exact hrL.const_mul (s ^ 2 / 2 * C * τ ^ (s - 2))
    · exact abs_mul_kerH_le_left hs0 hs2 hC0 hC ht.1 ht.2
  have bR : ∫ t in Ioi τ, |φ t * kerH s τ t| ≤ ∫ t in Ioi τ, s ^ 2 / 2 * C * τ ^ 2 * t ^ (s - 2 - p) := by
    refine setIntegral_mono_on iR ?_ measurableSet_Ioi (fun t ht => ?_)
    · exact hrR.const_mul (s ^ 2 / 2 * C * τ ^ 2)
    · exact abs_mul_kerH_le_right hs0 hs2 hC0 hC hτ (le_of_lt ht)
  rw [integral_const_mul, vL] at bL
  rw [integral_const_mul, vR] at bR
  rw [← Set.Ioc_union_Ioi_eq_Ioi hτ.le, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi iL iR]
  have e1 : τ ^ (s - 2) * τ ^ (3 - p) = τ ^ (1 + s - p) := by
    rw [← Real.rpow_add hτ]; congr 1; ring
  have e2 : τ ^ 2 * τ ^ (s - 1 - p) = τ ^ (1 + s - p) := by
    rw [← Real.rpow_two, ← Real.rpow_add hτ]; congr 1; ring
  have h3 : 0 < 3 - p := by linarith
  have h4 : 0 < p + 1 - s := by linarith
  calc (∫ t in Ioc (0 : ℝ) τ, |φ t * kerH s τ t|) + ∫ t in Ioi τ, |φ t * kerH s τ t|
      ≤ s ^ 2 / 2 * C * τ ^ (s - 2) * (τ ^ (3 - p) / (3 - p))
        + s ^ 2 / 2 * C * τ ^ 2 * (τ ^ (s - 1 - p) / (p + 1 - s)) := add_le_add bL bR
    _ = s ^ 2 / 2 * C * ((τ ^ (s - 2) * τ ^ (3 - p)) / (3 - p) + (τ ^ 2 * τ ^ (s - 1 - p)) / (p + 1 - s)) := by
        ring
    _ = s ^ 2 / 2 * C * (τ ^ (1 + s - p) / (3 - p) + τ ^ (1 + s - p) / (p + 1 - s)) := by rw [e1, e2]
    _ = s ^ 2 / 2 * C * (1 / (3 - p) + 1 / (p + 1 - s)) * τ ^ (1 + s - p) := by ring

/-- `|G(t)| ≤ C_b t^{-1-b}` on `(0, ∞)` for `0 < b ≤ 2`. -/
theorem abs_G_le_rpow {b : ℝ} (hb0 : 0 < b) (hb2 : b ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → |-thG1 t / t| ≤ C * t ^ (-(1 + b)) := by
  obtain ⟨C1, hC1⟩ := abs_thG1_le_log
  obtain ⟨C2, hC2, hC2b⟩ := Eb_pow_le_rpow 2 hb0
  refine ⟨|C1| * C2 + 16, by positivity, fun t ht => ?_⟩
  have e : t ^ (-(1 + b)) = t ^ (-b) / t := by
    rw [show -(1 + b) = -b + -1 by ring, Real.rpow_add ht, Real.rpow_neg_one, div_eq_mul_inv]
  have hq : 0 < t ^ (-b) := Real.rpow_pos_of_pos ht _
  rw [abs_div, abs_neg, abs_of_pos ht, e, mul_div_assoc', div_le_div_iff_of_pos_right ht]
  rcases le_or_gt t 1 with ht1 | ht1
  · have a1 : |thG1 t| ≤ |C1| * Eb t ^ 2 :=
      (hC1 t ht ht1).trans (mul_le_mul_of_nonneg_right (le_abs_self C1) (sq_nonneg _))
    have a2 := hC2b t ht ht1
    calc |thG1 t| ≤ |C1| * Eb t ^ 2 := a1
      _ ≤ |C1| * (C2 * t ^ (-b)) := mul_le_mul_of_nonneg_left a2 (abs_nonneg _)
      _ ≤ (|C1| * C2 + 16) * t ^ (-b) := by nlinarith
  · have h1 := abs_tsq_thG1_le ht
    rw [abs_mul, abs_of_pos (pow_pos ht 2)] at h1
    have hm : t ^ (-(2 : ℝ)) ≤ t ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    have e2 : t ^ (-(2 : ℝ)) = (t ^ 2)⁻¹ := by rw [Real.rpow_neg ht.le, Real.rpow_two]
    have h2 : |thG1 t| ≤ 16 * t ^ (-(2 : ℝ)) := by
      rw [e2, ← div_eq_mul_inv, le_div_iff₀ (pow_pos ht 2)]
      linarith [mul_comm (t ^ 2) |thG1 t|]
    have hC : 0 ≤ |C1| * C2 := mul_nonneg (abs_nonneg _) hC2
    calc |thG1 t| ≤ 16 * t ^ (-(2 : ℝ)) := h2
      _ ≤ 16 * t ^ (-b) := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ ≤ (|C1| * C2 + 16) * t ^ (-b) := by nlinarith

/-- `H(s) = ∫_τ F₂(τ) ∫_t G(t) k_H(τ,t)`. -/
noncomputable def hH (s : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), thF2 τ / τ * (-thG1 t / t) * kerH s τ t

theorem integrableOn_F2_gamG {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    IntegrableOn (fun τ : ℝ => thF2 τ / τ * gamG s τ) (Ioi 0) := by
  obtain ⟨M, hM, hMb⟩ := abs_gamG_le_rpow hs0 hs2
  refine Integrable.mono' ((integrableOn_F2_rpow hs0).const_mul M)
    (((hdom_thF2.1.div continuousOn_id (fun τ hτ => (show (0 : ℝ) < τ from hτ).ne')).mul
      (continuousOn_gamG hs0 hs2)).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun τ hτ => ?_))
  have hτ0 : (0 : ℝ) < τ := hτ
  rw [Real.norm_eq_abs, abs_mul]
  calc |thF2 τ / τ| * |gamG s τ| ≤ |thF2 τ / τ| * (M * τ ^ (s / 2)) :=
        mul_le_mul_of_nonneg_left (hMb τ hτ0) (abs_nonneg _)
    _ = M * (|thF2 τ / τ| * τ ^ (s / 2)) := by ring

theorem integrableOn_G_min {s τ : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hτ : 0 < τ) :
    IntegrableOn (fun t : ℝ => (-thG1 t / t) * min τ t ^ s) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => (-thG1 t / t) * min τ t ^ s) (Ioi 0) :=
    (continuousOn_thG1.neg.div continuousOn_id (fun t ht => (show (0 : ℝ) < t from ht).ne')).mul
      (((continuous_const : Continuous fun _ : ℝ => τ).min continuous_id).rpow_const
        (fun _ => Or.inr hs0.le)).continuousOn
  refine Integrable.mono' ((integrableOn_G_rpow hs0 (by linarith)).const_mul (τ ^ (s / 2)))
    (hc.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
  have ht0 : (0 : ℝ) < t := ht
  have hm0 : 0 ≤ min τ t ^ s := Real.rpow_nonneg (le_min hτ.le ht0.le) s
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm0]
  calc |-thG1 t / t| * min τ t ^ s ≤ |-thG1 t / t| * (τ ^ (s / 2) * t ^ (s / 2)) :=
        mul_le_mul_of_nonneg_left (min_rpow_le hs0 hτ.le ht0.le) (abs_nonneg _)
    _ = τ ^ (s / 2) * (|-thG1 t / t| * t ^ (s / 2)) := by ring

/-- **`pairS(s) = j(s) (s B(s) - H(s))`** for `0 < s ≤ 1`. -/
theorem pairS_eq_sB_sub_H {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    pairS s = jS s * (s * bB s - hH s) := by
  have hs2 : s < 2 := by linarith
  obtain ⟨C, hC0, hC⟩ := abs_G_le_rpow (b := s / 2) (by linarith) (by linarith)
  have hC' : ∀ t : ℝ, 0 < t → |-thG1 t / t| ≤ C * t ^ (-(1 + s / 2)) := hC
  have cG : ContinuousOn (fun t : ℝ => -thG1 t / t) (Ioi 0) :=
    continuousOn_thG1.neg.div continuousOn_id (fun t ht => (show (0 : ℝ) < t from ht).ne')
  have hp1 : s - 1 < 1 + s / 2 := by linarith
  have hp3 : 1 + s / 2 < 3 := by linarith
  have hexp : 1 + s - (1 + s / 2) = s / 2 := by ring
  -- the inner integral of `G k_H`
  have iK : ∀ τ : ℝ, 0 < τ → IntegrableOn (fun t : ℝ => (-thG1 t / t) * kerH s τ t) (Ioi 0) :=
    fun τ hτ => integrableOn_kerH_mul hs0.le hs2.le hτ hp1 hp3 cG hC0 hC'
  have h1 : 0 < 3 - (1 + s / 2) := by linarith
  have h2 : 0 < 1 + s / 2 + 1 - s := by linarith
  obtain ⟨K, hK0, bK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, 0 < τ →
      |∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t| ≤ K * τ ^ (s / 2) := by
    refine ⟨s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s)),
      mul_nonneg (mul_nonneg (by positivity) hC0)
        (add_nonneg (one_div_nonneg.2 h1.le) (one_div_nonneg.2 h2.le)), fun τ hτ => ?_⟩
    have h := integral_abs_kerH_le hs0.le hs2.le hτ hp1 hp3 cG hC0 hC'
    rw [hexp] at h
    exact (abs_integral_le_integral_abs).trans h
  -- measurability of the inner integral
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t)
      ((volume : Measure ℝ).restrict (Ioi 0)) := by
    have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => (-thG1 p.2 / p.2) * kerH s p.1 p.2)
        (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))) := by
      rw [Measure.prod_restrict]
      refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioi)
      have m2 : MapsTo (fun q : ℝ × ℝ => q.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (Ioi 0) := fun q hq => hq.2
      exact (cG.comp continuous_snd.continuousOn m2).mul (continuous_kerH hs0.le).continuousOn
    exact hprod.integral_prod_right'
  have iOut : IntegrableOn (fun τ : ℝ => thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t)
      (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_F2_rpow hs0).const_mul K)
      (((hdom_thF2.1.div continuousOn_id (fun τ hτ => (show (0 : ℝ) < τ from hτ).ne')).aestronglyMeasurable
        measurableSet_Ioi).mul hmeas)
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun τ hτ => ?_))
    have hτ0 : (0 : ℝ) < τ := hτ
    rw [Real.norm_eq_abs, abs_mul]
    calc |thF2 τ / τ| * |∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t|
        ≤ |thF2 τ / τ| * (K * τ ^ (s / 2)) := mul_le_mul_of_nonneg_left (bK τ hτ0) (abs_nonneg _)
      _ = K * (|thF2 τ / τ| * τ ^ (s / 2)) := by ring
  have hHe : hH s = ∫ τ in Ioi (0 : ℝ), thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t := by
    unfold hH
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ _ => ?_)
    show ∫ t in Ioi (0 : ℝ), thF2 τ / τ * (-thG1 t / t) * kerH s τ t
      = thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  have hin : EqOn (fun τ : ℝ => ∫ t in Ioi (0 : ℝ),
        thF2 τ / τ * (-thG1 t / t) * (min τ t ^ s - kerH s τ t))
      (fun τ : ℝ => s * (thF2 τ / τ * gamG s τ)
        - thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t) (Ioi 0) := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have e : (fun t : ℝ => thF2 τ / τ * (-thG1 t / t) * (min τ t ^ s - kerH s τ t))
        = fun t : ℝ => thF2 τ / τ * ((-thG1 t / t) * min τ t ^ s)
          - thF2 τ / τ * ((-thG1 t / t) * kerH s τ t) := by
      funext t
      ring
    show ∫ t in Ioi (0 : ℝ), thF2 τ / τ * (-thG1 t / t) * (min τ t ^ s - kerH s τ t)
      = s * (thF2 τ / τ * gamG s τ) - thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t
    rw [e, integral_sub ((integrableOn_G_min hs0 hs2 hτ0).const_mul _) ((iK τ hτ0).const_mul _),
      integral_const_mul, integral_const_mul, inner_min_integral hs0 hs1 hτ0]
    ring
  rw [pairS_eq_fubini hs0 hs1, setIntegral_congr_fun measurableSet_Ioi hin,
    integral_sub ((integrableOn_F2_gamG hs0 hs2).const_mul s) iOut, integral_const_mul,
    outer_min_integral hs0 hs1, ← hHe]

end Tower.RV6
