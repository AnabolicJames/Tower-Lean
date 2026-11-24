import Mathlib
import Tower.RV6.BPHm

/-!
# RungBP (b6): `|H(s) - H_m(s)| ≤ K s²` on `0 < s ≤ 1`

`I_G(τ) = ∫_{t>0} G k_H`, `I_M(τ) = ∫_{t∈(0,1]} g_L k_H`.  `H = ∫_{τ>0} F₂ I_G` and `H_m = ∫_{(0,1]} 3 g_L I_M`, so
`H - H_m = ∫_{(0,1]} ((F₂ - 3 g_L) I_G + 3 g_L (I_G - I_M)) + ∫_{τ>1} F₂ I_G`.
With the inner bound of wave 62 (here for measurable `φ`) at `p = 5/4` and `p = 1/4`:
`|I_G| ≤ s² K_G τ^{s-1/4}`, `|I_G - I_M| ≤ s² K_D τ^{3/4+s}`, and `|F₂ - 3 g_L| ≤ C τ^{-1/4}` on `(0,1]`.
-/

namespace Tower.RV6

open Real MeasureTheory Set Filter Topology

/-! ## The inner bound for measurable `φ` -/

theorem aesm_mul_kerH {s τ : ℝ} {φ : ℝ → ℝ} {S : Set ℝ} (hs : 0 ≤ s)
    (hφ : AEStronglyMeasurable φ (volume.restrict (Ioi 0))) (hS : S ⊆ Ioi 0) :
    AEStronglyMeasurable (fun t : ℝ => φ t * kerH s τ t) (volume.restrict S) :=
  (hφ.mono_measure (Measure.restrict_mono hS le_rfl)).mul
    ((continuous_kerH hs).comp ((continuous_const : Continuous fun _ : ℝ => τ).prodMk
      continuous_id)).aestronglyMeasurable

theorem integrableOn_kerH_left_m {s τ p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ)
    (hp3 : p < 3) (hφ : AEStronglyMeasurable φ (volume.restrict (Ioi 0))) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) :
    IntegrableOn (fun t : ℝ => φ t * kerH s τ t) (Ioc 0 τ) := by
  have hr : IntegrableOn (fun t : ℝ => t ^ (2 - p)) (Ioc 0 τ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 2 - p))
  refine Integrable.mono' (hr.const_mul (s ^ 2 / 2 * C * τ ^ (s - 2)))
    (aesm_mul_kerH hs0 hφ Ioc_subset_Ioi_self)
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))
  rw [Real.norm_eq_abs]
  exact abs_mul_kerH_le_left hs0 hs2 hC0 hC ht.1 ht.2

theorem integrableOn_kerH_right_m {s τ p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ)
    (hp1 : s - 1 < p) (hφ : AEStronglyMeasurable φ (volume.restrict (Ioi 0))) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) :
    IntegrableOn (fun t : ℝ => φ t * kerH s τ t) (Ioi τ) := by
  have hr : IntegrableOn (fun t : ℝ => t ^ (s - 2 - p)) (Ioi τ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hτ
  refine Integrable.mono' (hr.const_mul (s ^ 2 / 2 * C * τ ^ 2))
    (aesm_mul_kerH hs0 hφ (Ioi_subset_Ioi hτ.le))
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
  rw [Real.norm_eq_abs]
  exact abs_mul_kerH_le_right hs0 hs2 hC0 hC hτ (le_of_lt ht)

theorem integrableOn_kerH_mul_m {s τ p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ)
    (hp1 : s - 1 < p) (hp3 : p < 3) (hφ : AEStronglyMeasurable φ (volume.restrict (Ioi 0)))
    (hC0 : 0 ≤ C) (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) :
    IntegrableOn (fun t : ℝ => φ t * kerH s τ t) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hτ.le]
  exact (integrableOn_kerH_left_m hs0 hs2 hτ hp3 hφ hC0 hC).union
    (integrableOn_kerH_right_m hs0 hs2 hτ hp1 hφ hC0 hC)

theorem integral_abs_kerH_le_m {s τ p C : ℝ} {φ : ℝ → ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ)
    (hp1 : s - 1 < p) (hp3 : p < 3) (hφ : AEStronglyMeasurable φ (volume.restrict (Ioi 0)))
    (hC0 : 0 ≤ C) (hC : ∀ t : ℝ, 0 < t → |φ t| ≤ C * t ^ (-p)) :
    ∫ t in Ioi (0 : ℝ), |φ t * kerH s τ t|
      ≤ s ^ 2 / 2 * C * (1 / (3 - p) + 1 / (p + 1 - s)) * τ ^ (1 + s - p) := by
  have iL := (integrableOn_kerH_left_m hs0 hs2 hτ hp3 hφ hC0 hC).abs
  have iR := (integrableOn_kerH_right_m hs0 hs2 hτ hp1 hφ hC0 hC).abs
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
      ≤ ∫ t in Ioc (0 : ℝ) τ, s ^ 2 / 2 * C * τ ^ (s - 2) * t ^ (2 - p) :=
    setIntegral_mono_on iL (hrL.const_mul _) measurableSet_Ioc
      (fun t ht => abs_mul_kerH_le_left hs0 hs2 hC0 hC ht.1 ht.2)
  have bR : ∫ t in Ioi τ, |φ t * kerH s τ t| ≤ ∫ t in Ioi τ, s ^ 2 / 2 * C * τ ^ 2 * t ^ (s - 2 - p) :=
    setIntegral_mono_on iR (hrR.const_mul _) measurableSet_Ioi
      (fun t ht => abs_mul_kerH_le_right hs0 hs2 hC0 hC hτ (le_of_lt ht))
  rw [integral_const_mul, vL] at bL
  rw [integral_const_mul, vR] at bR
  rw [← Set.Ioc_union_Ioi_eq_Ioi hτ.le, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi iL iR]
  have e1 : τ ^ (s - 2) * τ ^ (3 - p) = τ ^ (1 + s - p) := by
    rw [← Real.rpow_add hτ]; congr 1; ring
  have e2 : τ ^ 2 * τ ^ (s - 1 - p) = τ ^ (1 + s - p) := by
    rw [← Real.rpow_two, ← Real.rpow_add hτ]; congr 1; ring
  calc (∫ t in Ioc (0 : ℝ) τ, |φ t * kerH s τ t|) + ∫ t in Ioi τ, |φ t * kerH s τ t|
      ≤ s ^ 2 / 2 * C * τ ^ (s - 2) * (τ ^ (3 - p) / (3 - p))
        + s ^ 2 / 2 * C * τ ^ 2 * (τ ^ (s - 1 - p) / (p + 1 - s)) := add_le_add bL bR
    _ = s ^ 2 / 2 * C * ((τ ^ (s - 2) * τ ^ (3 - p)) / (3 - p) + (τ ^ 2 * τ ^ (s - 1 - p)) / (p + 1 - s)) := by
        ring
    _ = s ^ 2 / 2 * C * (τ ^ (1 + s - p) / (3 - p) + τ ^ (1 + s - p) / (p + 1 - s)) := by rw [e1, e2]
    _ = s ^ 2 / 2 * C * (1 / (3 - p) + 1 / (p + 1 - s)) * τ ^ (1 + s - p) := by ring

/-! ## The pointwise bounds -/

theorem abs_ind_gL_le {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → |(Iic (1 : ℝ)).indicator gL t| ≤ C * t ^ (-(1 + b)) := by
  obtain ⟨C2, hC2, hC2b⟩ := Eb_pow_le_rpow 1 hb
  refine ⟨2 * C2, mul_nonneg zero_le_two hC2, fun t ht => ?_⟩
  have hp : 0 < t ^ (-(1 + b)) := Real.rpow_pos_of_pos ht _
  by_cases h1 : t ∈ Iic (1 : ℝ)
  · have ht1 : t ≤ 1 := h1
    rw [Set.indicator_of_mem h1, abs_of_nonneg (gL_nonneg ht ht1)]
    have hL := Lc_le_Eb ht ht1
    have hE := hC2b t ht ht1
    rw [pow_one] at hE
    have e : t ^ (-(1 + b)) = t ^ (-b) / t := by
      rw [show -(1 + b) = -b + -1 by ring, Real.rpow_add ht, Real.rpow_neg_one, div_eq_mul_inv]
    rw [e, gL]
    have hq : 0 < t ^ (-b) := Real.rpow_pos_of_pos ht _
    rw [mul_div_assoc', div_le_div_iff_of_pos_right ht]
    nlinarith
  · rw [Set.indicator_of_notMem h1, abs_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hC2) hp.le

theorem abs_G_sub_ind_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      |(-thG1 t / t) - (Iic (1 : ℝ)).indicator gL t| ≤ C * t ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C1, hC1⟩ := thG1_model
  obtain ⟨C2, hC2, hC2b⟩ := Eb_pow_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨|C1| * C2 + 16, by positivity, fun t ht => ?_⟩
  have hq : 0 < t ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos ht _
  by_cases h1 : t ∈ Iic (1 : ℝ)
  · have ht1 : t ≤ 1 := h1
    rw [Set.indicator_of_mem h1, gL]
    have e : -thG1 t / t - 2 * Lc t / t = -((thG1 t + 2 * Lc t) / t) := by ring
    rw [e, abs_neg, abs_div, abs_of_pos ht, div_le_iff₀ ht]
    have a1 := hC1 t ht ht1
    have a2 := hC2b t ht ht1
    have hC : C1 * t * Eb t ^ 2 ≤ |C1| * t * Eb t ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C1) ht.le) (sq_nonneg _)
    have a3 : |C1| * t * Eb t ^ 2 ≤ |C1| * t * (C2 * t ^ (-(1 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left a2 (mul_nonneg (abs_nonneg _) ht.le)
    nlinarith
  · have ht1 : 1 < t := lt_of_not_ge h1
    rw [Set.indicator_of_notMem h1, sub_zero]
    have h2 := abs_tsq_thG1_le ht
    rw [abs_mul, abs_of_pos (pow_pos ht 2)] at h2
    have hm : t ^ (-(3 : ℝ)) ≤ t ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by norm_num)
    have e3 : t ^ (-(3 : ℝ)) = (t ^ 3)⁻¹ := by
      rw [Real.rpow_neg ht.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : |-thG1 t / t| ≤ 16 * t ^ (-(3 : ℝ)) := by
      rw [abs_div, abs_neg, abs_of_pos ht, div_le_iff₀ ht, e3]
      have : 16 * (t ^ 3)⁻¹ * t = 16 / t ^ 2 := by
        field_simp
        all_goals ring
      rw [this, le_div_iff₀ (pow_pos ht 2)]
      linarith [mul_comm (t ^ 2) |thG1 t|]
    have hC : 0 ≤ |C1| * C2 := mul_nonneg (abs_nonneg _) hC2
    calc |-thG1 t / t| ≤ 16 * t ^ (-(3 : ℝ)) := h3
      _ ≤ 16 * t ^ (-(1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ ≤ (|C1| * C2 + 16) * t ^ (-(1 / 4 : ℝ)) := by nlinarith

theorem abs_F2_sub_gL_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → |thF2 τ / τ - 3 * gL τ| ≤ C * τ ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C1, hC1⟩ := thF2_model
  obtain ⟨C2, hC2, hC2b⟩ := Eb_pow_le_rpow 3 (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨|C1| * C2, mul_nonneg (abs_nonneg _) hC2, fun τ hτ hτ1 => ?_⟩
  rw [gL, show thF2 τ / τ - 3 * (2 * Lc τ / τ) = (thF2 τ - 6 * Lc τ) / τ by ring, abs_div,
    abs_of_pos hτ, div_le_iff₀ hτ]
  have a1 := hC1 τ hτ hτ1
  have a2 := hC2b τ hτ hτ1
  have hE : 0 ≤ Eb τ ^ 3 := pow_nonneg (by linarith [one_le_Eb hτ hτ1]) 3
  have hC : C1 * τ * Eb τ ^ 3 ≤ |C1| * τ * Eb τ ^ 3 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C1) hτ.le) hE
  have a3 : |C1| * τ * Eb τ ^ 3 ≤ |C1| * τ * (C2 * τ ^ (-(1 / 4 : ℝ))) :=
    mul_le_mul_of_nonneg_left a2 (mul_nonneg (abs_nonneg _) hτ.le)
  nlinarith

/-! ## The outer integrands -/

theorem hH_eq_outer (s : ℝ) :
    hH s = ∫ τ in Ioi (0 : ℝ), thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t := by
  unfold hH
  refine setIntegral_congr_fun measurableSet_Ioi (fun τ _ => ?_)
  show ∫ t in Ioi (0 : ℝ), thF2 τ / τ * (-thG1 t / t) * kerH s τ t
    = thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

theorem integrableOn_F2_IG {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IntegrableOn (fun τ : ℝ => thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t) (Ioi 0) := by
  have hs2 : s < 2 := by linarith
  obtain ⟨C, hC0, hC⟩ := abs_G_le_rpow (b := s / 2) (by linarith) (by linarith)
  have cG : ContinuousOn (fun t : ℝ => -thG1 t / t) (Ioi 0) :=
    continuousOn_thG1.neg.div continuousOn_id (fun t ht => (show (0 : ℝ) < t from ht).ne')
  have hp1 : s - 1 < 1 + s / 2 := by linarith
  have hp3 : 1 + s / 2 < 3 := by linarith
  have h1 : 0 < 3 - (1 + s / 2) := by linarith
  have h2 : 0 < 1 + s / 2 + 1 - s := by linarith
  have hK0 : 0 ≤ s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s)) :=
    mul_nonneg (mul_nonneg (by positivity) hC0) (add_nonneg (one_div_nonneg.2 h1.le) (one_div_nonneg.2 h2.le))
  have bK : ∀ τ : ℝ, 0 < τ → |∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t|
      ≤ s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s)) * τ ^ (s / 2) := by
    intro τ hτ
    have h := integral_abs_kerH_le hs0.le hs2.le hτ hp1 hp3 cG hC0 hC
    rw [show 1 + s - (1 + s / 2) = s / 2 by ring] at h
    exact (abs_integral_le_integral_abs).trans h
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t)
      ((volume : Measure ℝ).restrict (Ioi 0)) := by
    have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => (-thG1 p.2 / p.2) * kerH s p.1 p.2)
        (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))) := by
      rw [Measure.prod_restrict]
      refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioi)
      have m2 : MapsTo (fun q : ℝ × ℝ => q.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (Ioi 0) := fun q hq => hq.2
      exact (cG.comp continuous_snd.continuousOn m2).mul (continuous_kerH hs0.le).continuousOn
    exact hprod.integral_prod_right'
  refine Integrable.mono' ((integrableOn_F2_rpow hs0).const_mul
      (s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s))))
    (((hdom_thF2.1.div continuousOn_id (fun τ hτ => (show (0 : ℝ) < τ from hτ).ne')).aestronglyMeasurable
      measurableSet_Ioi).mul hmeas)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun τ hτ => ?_))
  have hτ0 : (0 : ℝ) < τ := hτ
  rw [Real.norm_eq_abs, abs_mul]
  calc |thF2 τ / τ| * |∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t|
      ≤ |thF2 τ / τ| * (s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s)) * τ ^ (s / 2)) :=
        mul_le_mul_of_nonneg_left (bK τ hτ0) (abs_nonneg _)
    _ = s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s)) * (|thF2 τ / τ| * τ ^ (s / 2)) := by
        ring

theorem IM_eq_ind (s τ : ℝ) :
    ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t
      = ∫ t in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator gL t * kerH s τ t := by
  have e : (fun t : ℝ => (Iic (1 : ℝ)).indicator gL t * kerH s τ t)
      = (Iic (1 : ℝ)).indicator (fun t : ℝ => gL t * kerH s τ t) := by
    funext t
    by_cases h : t ∈ Iic (1 : ℝ)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [e, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]

theorem integrableOn_gL_IM {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IntegrableOn (fun τ : ℝ => 3 * gL τ * ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t) (Ioc 0 1) := by
  have hs2 : s < 2 := by linarith
  obtain ⟨C, hC0, hC⟩ := abs_ind_gL_le (b := s / 2) (by linarith)
  have hφ : AEStronglyMeasurable ((Iic (1 : ℝ)).indicator gL) (volume.restrict (Ioi (0 : ℝ))) :=
    (measurable_gL.indicator measurableSet_Iic).aestronglyMeasurable
  have hp1 : s - 1 < 1 + s / 2 := by linarith
  have hp3 : 1 + s / 2 < 3 := by linarith
  have h1 : 0 < 3 - (1 + s / 2) := by linarith
  have h2 : 0 < 1 + s / 2 + 1 - s := by linarith
  have hK0 : 0 ≤ s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s)) :=
    mul_nonneg (mul_nonneg (by positivity) hC0) (add_nonneg (one_div_nonneg.2 h1.le) (one_div_nonneg.2 h2.le))
  have bK : ∀ τ : ℝ, 0 < τ → |∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t|
      ≤ s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s)) * τ ^ (s / 2) := by
    intro τ hτ
    have h := integral_abs_kerH_le_m hs0.le hs2.le hτ hp1 hp3 hφ hC0 hC
    rw [show 1 + s - (1 + s / 2) = s / 2 by ring] at h
    rw [IM_eq_ind]
    exact (abs_integral_le_integral_abs).trans h
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t)
      ((volume : Measure ℝ).restrict (Ioc 0 1)) := by
    have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => gL p.2 * kerH s p.1 p.2)
        (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)).prod ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))) :=
      ((measurable_gL.comp measurable_snd).mul (continuous_kerH hs0.le).measurable).aestronglyMeasurable
    exact hprod.integral_prod_right'
  have hb : IntegrableOn (fun τ : ℝ => 6 * (s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s)))
      * (Eb τ ^ 1 * τ ^ (s / 2 - 1))) (Ioc 0 1) :=
    (integrableOn_Eb_pow_rpow (k := 1) (a := s / 2 - 1) (by linarith)).const_mul _
  refine Integrable.mono' hb
    (((measurable_const.mul measurable_gL).aestronglyMeasurable).mul hmeas)
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun τ hτ => ?_))
  have hτ0 : (0 : ℝ) < τ := hτ.1
  have hτ1 : τ ≤ 1 := hτ.2
  have hg := gL_nonneg hτ0 hτ1
  have hL := Lc_le_Eb hτ0 hτ1
  have hgE : gL τ * τ ^ (s / 2) ≤ 2 * (Eb τ * τ ^ (s / 2 - 1)) := by
    have e : gL τ * τ ^ (s / 2) = 2 * Lc τ * τ ^ (s / 2 - 1) := by
      have hτ' : τ ≠ 0 := hτ0.ne'
      rw [gL, Real.rpow_sub_one hτ']
      field_simp
      all_goals ring
    have hq : 0 ≤ τ ^ (s / 2 - 1) := Real.rpow_nonneg hτ0.le _
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hL hq]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * gL τ), pow_one]
  calc 3 * gL τ * |∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t|
      ≤ 3 * gL τ * (s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s)) * τ ^ (s / 2)) :=
        mul_le_mul_of_nonneg_left (bK τ hτ0) (by positivity)
    _ = 3 * (s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s))) * (gL τ * τ ^ (s / 2)) := by
        ring
    _ ≤ 3 * (s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s))) * (2 * (Eb τ * τ ^ (s / 2 - 1))) :=
        mul_le_mul_of_nonneg_left hgE (by positivity)
    _ = 6 * (s ^ 2 / 2 * C * (1 / (3 - (1 + s / 2)) + 1 / (1 + s / 2 + 1 - s))) * (Eb τ * τ ^ (s / 2 - 1)) := by
        ring

theorem hM_eq_outer (s : ℝ) :
    hM s = ∫ τ in Ioc (0 : ℝ) 1, 3 * gL τ * ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t := by
  unfold hM
  refine setIntegral_congr_fun measurableSet_Ioc (fun τ _ => ?_)
  show ∫ t in Ioc (0 : ℝ) 1, 3 * gL τ * gL t * kerH s τ t
    = 3 * gL τ * ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

/-! ## The bound -/

/-- **`|H(s) - H_m(s)| ≤ K s²`** on `0 < s ≤ 1`. -/
theorem hH_sub_hM_le : ∃ K : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → |hH s - hM s| ≤ K * s ^ 2 := by
  obtain ⟨CG, hCG0, hCG⟩ := abs_G_le_rpow (b := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨CD, hCD0, hCD⟩ := abs_G_sub_ind_le
  obtain ⟨CF, hCF0, hCF⟩ := abs_F2_sub_gL_le
  obtain ⟨CI, hCI0, hCI⟩ := abs_ind_gL_le (b := 1 / 4) (by norm_num)
  have cG : ContinuousOn (fun t : ℝ => -thG1 t / t) (Ioi 0) :=
    continuousOn_thG1.neg.div continuousOn_id (fun t ht => (show (0 : ℝ) < t from ht).ne')
  have mI : AEStronglyMeasurable ((Iic (1 : ℝ)).indicator gL) (volume.restrict (Ioi (0 : ℝ))) :=
    (measurable_gL.indicator measurableSet_Iic).aestronglyMeasurable
  have mD : AEStronglyMeasurable (fun t : ℝ => (-thG1 t / t) - (Iic (1 : ℝ)).indicator gL t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (cG.aestronglyMeasurable measurableSet_Ioi).sub mI
  set KG : ℝ := CG / 2 * (4 / 7 + 4 / 5) with hKG
  set KD : ℝ := CD / 2 * (4 / 11 + 4) with hKD
  have hKG0 : 0 ≤ KG := by rw [hKG]; positivity
  have hKD0 : 0 ≤ KD := by rw [hKD]; positivity
  -- the three fixed integrable majorants
  have m1 : IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := integrableOn_rpow_Ioc01 (by norm_num)
  have m2 : IntegrableOn (fun τ : ℝ => gL τ * τ ^ (3 / 4 : ℝ)) (Ioc 0 1) := by
    refine Integrable.mono' ((integrableOn_Eb_pow_rpow (k := 1) (a := -(1 / 4 : ℝ)) (by norm_num)).const_mul 2)
      ((continuousOn_gL.mul (continuousOn_rpow_Ioi _)).mono Ioc_subset_Ioi_self |>.aestronglyMeasurable
        measurableSet_Ioc)
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun τ hτ => ?_))
    have hτ0 : (0 : ℝ) < τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2
    have hg := gL_nonneg hτ0 hτ1
    have hL := Lc_le_Eb hτ0 hτ1
    have hp : 0 < τ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hτ0 _
    have e : gL τ * τ ^ (3 / 4 : ℝ) = 2 * Lc τ * τ ^ (-(1 / 4 : ℝ)) := by
      have hτ' : τ ≠ 0 := hτ0.ne'
      rw [show (-(1 / 4 : ℝ)) = 3 / 4 - 1 by norm_num, Real.rpow_sub_one hτ', gL]
      field_simp
      all_goals ring
    have hq : 0 ≤ τ ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hτ0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg hp.le), pow_one, e]
    nlinarith [mul_le_mul_of_nonneg_right hL hq]
  have m3 : IntegrableOn (fun τ : ℝ => |thF2 τ / τ| * τ ^ (3 / 4 : ℝ)) (Ioi 1) := by
    have h := (integrableOn_F2_rpow (s := 3 / 2) (by norm_num)).mono_set (Ioi_subset_Ioi zero_le_one)
    rw [show (3 / 2 : ℝ) / 2 = 3 / 4 by norm_num] at h
    exact h
  refine ⟨CF * KG * (∫ τ in Ioc (0 : ℝ) 1, τ ^ (-(1 / 2 : ℝ)))
      + 3 * KD * (∫ τ in Ioc (0 : ℝ) 1, gL τ * τ ^ (3 / 4 : ℝ))
      + KG * (∫ τ in Ioi (1 : ℝ), |thF2 τ / τ| * τ ^ (3 / 4 : ℝ)), fun s hs0 hs1 => ?_⟩
  have hs2 : s < 2 := by linarith
  -- the inner bounds
  have bG : ∀ τ : ℝ, 0 < τ → |∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t| ≤ s ^ 2 * KG * τ ^ (s - 1 / 4) := by
    intro τ hτ
    have h := integral_abs_kerH_le hs0.le hs2.le hτ (by linarith : s - 1 < 1 + 1 / 4) (by norm_num) cG hCG0 hCG
    have hq : 1 / (1 + 1 / 4 + 1 - s) ≤ 4 / 5 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hpow : 0 ≤ τ ^ (1 + s - (1 + 1 / 4)) := Real.rpow_nonneg hτ.le _
    have e : (1 : ℝ) + s - (1 + 1 / 4) = s - 1 / 4 := by ring
    rw [e] at h hpow
    refine (abs_integral_le_integral_abs).trans (h.trans ?_)
    rw [hKG]
    have h7 : (1 : ℝ) / (3 - (1 + 1 / 4)) = 4 / 7 := by norm_num
    rw [h7]
    have : s ^ 2 / 2 * CG * (4 / 7 + 1 / (1 + 1 / 4 + 1 - s)) ≤ s ^ 2 / 2 * CG * (4 / 7 + 4 / 5) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have bD : ∀ τ : ℝ, 0 < τ → |(∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t)
      - ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t| ≤ s ^ 2 * KD * τ ^ (3 / 4 + s) := by
    intro τ hτ
    have iG := integrableOn_kerH_mul hs0.le hs2.le hτ (by linarith : s - 1 < 1 + 1 / 4) (by norm_num) cG hCG0 hCG
    have iI := integrableOn_kerH_mul_m hs0.le hs2.le hτ (by linarith : s - 1 < 1 + 1 / 4) (by norm_num) mI hCI0 hCI
    have h := integral_abs_kerH_le_m hs0.le hs2.le hτ (by linarith : s - 1 < 1 / 4) (by norm_num) mD hCD0 hCD
    rw [IM_eq_ind, ← integral_sub iG iI]
    have ee : (fun t : ℝ => (-thG1 t / t) * kerH s τ t - (Iic (1 : ℝ)).indicator gL t * kerH s τ t)
        = fun t : ℝ => ((-thG1 t / t) - (Iic (1 : ℝ)).indicator gL t) * kerH s τ t := by
      funext t; ring
    rw [ee]
    have hq : 1 / (1 / 4 + 1 - s) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have e : (1 : ℝ) + s - 1 / 4 = 3 / 4 + s := by ring
    rw [e] at h
    have hpow : 0 ≤ τ ^ (3 / 4 + s) := Real.rpow_nonneg hτ.le _
    refine (abs_integral_le_integral_abs).trans (h.trans ?_)
    rw [hKD]
    have h11 : (1 : ℝ) / (3 - 1 / 4) = 4 / 11 := by norm_num
    rw [h11]
    have : s ^ 2 / 2 * CD * (4 / 11 + 1 / (1 / 4 + 1 - s)) ≤ s ^ 2 / 2 * CD * (4 / 11 + 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  -- the decomposition
  have iFG := integrableOn_F2_IG hs0 hs1
  have iGM := integrableOn_gL_IM hs0 hs1
  have hsplitH : hH s = (∫ τ in Ioc (0 : ℝ) 1, thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t)
      + ∫ τ in Ioi (1 : ℝ), thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t := by
    have hU := setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (iFG.mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0))
      (iFG.mono_set (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1)))
    rw [Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)] at hU
    rw [hH_eq_outer, hU]
  have hdiff : hH s - hM s = (∫ τ in Ioc (0 : ℝ) 1, (thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t)
        - 3 * gL τ * ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t)
      + ∫ τ in Ioi (1 : ℝ), thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t := by
    rw [hsplitH, hM_eq_outer, integral_sub (iFG.mono_set Ioc_subset_Ioi_self) iGM]
    ring
  -- the two estimates
  have est1 : |∫ τ in Ioc (0 : ℝ) 1, (thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t)
        - 3 * gL τ * ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t|
      ≤ ∫ τ in Ioc (0 : ℝ) 1, s ^ 2 * (CF * KG * τ ^ (-(1 / 2 : ℝ)) + 3 * KD * (gL τ * τ ^ (3 / 4 : ℝ))) := by
    rw [← Real.norm_eq_abs]
    have hmaj : IntegrableOn (fun τ : ℝ => s ^ 2 * (CF * KG * τ ^ (-(1 / 2 : ℝ))
        + 3 * KD * (gL τ * τ ^ (3 / 4 : ℝ)))) (Ioc 0 1) :=
      ((m1.const_mul (CF * KG)).add (m2.const_mul (3 * KD))).const_mul (s ^ 2)
    refine norm_integral_le_of_norm_le hmaj
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun τ hτ => ?_))
    have hτ0 : (0 : ℝ) < τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2
    have hg := gL_nonneg hτ0 hτ1
    have a1 : |thF2 τ / τ - 3 * gL τ| ≤ CF * τ ^ (-(1 / 4 : ℝ)) := hCF τ hτ0 hτ1
    have a2 := bG τ hτ0
    have a3 := bD τ hτ0
    generalize hIG : (∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t) = IG at a2 a3 ⊢
    generalize hIM : (∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t) = IM at a3 ⊢
    have r1 : τ ^ (s - 1 / 4) ≤ τ ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hτ0 hτ1 (by linarith)
    have r2 : τ ^ (3 / 4 + s) ≤ τ ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hτ0 hτ1 (by linarith)
    have r3 : τ ^ (-(1 / 4 : ℝ)) * τ ^ (-(1 / 4 : ℝ)) = τ ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hτ0]; congr 1; norm_num
    have p1 : 0 ≤ τ ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hτ0.le _
    have p2 : 0 ≤ τ ^ (s - 1 / 4) := Real.rpow_nonneg hτ0.le _
    have p3 : 0 ≤ τ ^ (3 / 4 + s) := Real.rpow_nonneg hτ0.le _
    have e : thF2 τ / τ * IG - 3 * gL τ * IM = (thF2 τ / τ - 3 * gL τ) * IG + 3 * gL τ * (IG - IM) := by ring
    rw [Real.norm_eq_abs, e]
    have b1 : |(thF2 τ / τ - 3 * gL τ) * IG| ≤ CF * KG * τ ^ (-(1 / 2 : ℝ)) * s ^ 2 := by
      rw [abs_mul, ← r3]
      calc |thF2 τ / τ - 3 * gL τ| * |IG| ≤ (CF * τ ^ (-(1 / 4 : ℝ))) * (s ^ 2 * KG * τ ^ (s - 1 / 4)) :=
            mul_le_mul a1 a2 (abs_nonneg _) (mul_nonneg hCF0 p1)
        _ ≤ (CF * τ ^ (-(1 / 4 : ℝ))) * (s ^ 2 * KG * τ ^ (-(1 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r1 (by positivity)) (mul_nonneg hCF0 p1)
        _ = CF * KG * (τ ^ (-(1 / 4 : ℝ)) * τ ^ (-(1 / 4 : ℝ))) * s ^ 2 := by ring
    have b2 : |3 * gL τ * (IG - IM)| ≤ 3 * KD * (gL τ * τ ^ (3 / 4 : ℝ)) * s ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * gL τ)]
      calc 3 * gL τ * |IG - IM| ≤ 3 * gL τ * (s ^ 2 * KD * τ ^ (3 / 4 + s)) :=
            mul_le_mul_of_nonneg_left a3 (by positivity)
        _ ≤ 3 * gL τ * (s ^ 2 * KD * τ ^ (3 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r2 (by positivity)) (by positivity)
        _ = 3 * KD * (gL τ * τ ^ (3 / 4 : ℝ)) * s ^ 2 := by ring
    calc |(thF2 τ / τ - 3 * gL τ) * IG + 3 * gL τ * (IG - IM)|
        ≤ |(thF2 τ / τ - 3 * gL τ) * IG| + |3 * gL τ * (IG - IM)| := abs_add_le _ _
      _ ≤ CF * KG * τ ^ (-(1 / 2 : ℝ)) * s ^ 2 + 3 * KD * (gL τ * τ ^ (3 / 4 : ℝ)) * s ^ 2 := add_le_add b1 b2
      _ = s ^ 2 * (CF * KG * τ ^ (-(1 / 2 : ℝ)) + 3 * KD * (gL τ * τ ^ (3 / 4 : ℝ))) := by ring
  have est2 : |∫ τ in Ioi (1 : ℝ), thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t|
      ≤ ∫ τ in Ioi (1 : ℝ), s ^ 2 * (KG * (|thF2 τ / τ| * τ ^ (3 / 4 : ℝ))) := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((m3.const_mul KG).const_mul (s ^ 2))
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun τ hτ => ?_))
    have hτ1 : (1 : ℝ) < τ := hτ
    have hτ0 : (0 : ℝ) < τ := by linarith
    have a2 := bG τ hτ0
    have r : τ ^ (s - 1 / 4) ≤ τ ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hτ1.le (by linarith)
    rw [Real.norm_eq_abs, abs_mul]
    calc |thF2 τ / τ| * |∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t|
        ≤ |thF2 τ / τ| * (s ^ 2 * KG * τ ^ (s - 1 / 4)) := mul_le_mul_of_nonneg_left a2 (abs_nonneg _)
      _ ≤ |thF2 τ / τ| * (s ^ 2 * KG * τ ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r (by positivity)) (abs_nonneg _)
      _ = s ^ 2 * (KG * (|thF2 τ / τ| * τ ^ (3 / 4 : ℝ))) := by ring
  have v1 : ∫ τ in Ioc (0 : ℝ) 1, s ^ 2 * (CF * KG * τ ^ (-(1 / 2 : ℝ)) + 3 * KD * (gL τ * τ ^ (3 / 4 : ℝ)))
      = s ^ 2 * (CF * KG * (∫ τ in Ioc (0 : ℝ) 1, τ ^ (-(1 / 2 : ℝ)))
        + 3 * KD * (∫ τ in Ioc (0 : ℝ) 1, gL τ * τ ^ (3 / 4 : ℝ))) := by
    rw [integral_const_mul, integral_add (m1.const_mul _) (m2.const_mul _), integral_const_mul, integral_const_mul]
  have v2 : ∫ τ in Ioi (1 : ℝ), s ^ 2 * (KG * (|thF2 τ / τ| * τ ^ (3 / 4 : ℝ)))
      = s ^ 2 * (KG * (∫ τ in Ioi (1 : ℝ), |thF2 τ / τ| * τ ^ (3 / 4 : ℝ))) := by
    rw [integral_const_mul, integral_const_mul]
  rw [hdiff]
  calc |(∫ τ in Ioc (0 : ℝ) 1, (thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t)
          - 3 * gL τ * ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t)
        + ∫ τ in Ioi (1 : ℝ), thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t|
      ≤ |∫ τ in Ioc (0 : ℝ) 1, (thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t)
          - 3 * gL τ * ∫ t in Ioc (0 : ℝ) 1, gL t * kerH s τ t|
        + |∫ τ in Ioi (1 : ℝ), thF2 τ / τ * ∫ t in Ioi (0 : ℝ), (-thG1 t / t) * kerH s τ t| := abs_add_le _ _
    _ ≤ _ := add_le_add est1 est2
    _ = _ := by rw [v1, v2]; ring

end Tower.RV6
