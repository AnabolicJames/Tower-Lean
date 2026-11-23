import Mathlib
import Tower.RV6.LadderB
import Tower.RV6.BesselJ
import Tower.RV6.LaplaceDecay

/-!
# The `J₁` transform `AJ ψ x = x ∫₀^∞ J₁(xt) ψ(t) dt` on a class with polynomial decay

`g = I₀² K₀²` decays only like `1/(4t²)`, so the Hankel machinery of `HankelDom.lean` (exponential decay)
does not apply to it.  This file works with `ajG = AJ gB` directly.

* `PDom ψ`: `ψ` continuous on `(0, ∞)`, `√t |ψ t| ≤ C` on `(0, 1]` and `t² |ψ t| ≤ C` on `[1, ∞)`.
* `AJ_eq_subst`: `AJ ψ x = ∫₀^∞ J₁(s) ψ(s/x) ds` for `x > 0` (`s = xt`).
* **`hasDerivAt_AJ`** (R1): for a chain `ψ, ψ₁ = θψ` in `PDom`, `(AJ ψ)'(x) = -AJ ψ₁ (x) / x`,
  i.e. `ϑ AJ[ψ] = -AJ[θψ]`.  The derivative falls on `ψ(s/x)`; `J₁` needs only `|J₁| ≤ 1`, and the
  domination is by `A s^{-1/2}` on `(0, 2x]` plus `B s^{-2}` on `(x/2, ∞)`.
* **`AJ_theta2`** (R2): for a chain `φ, φ₁, φ₂` in `PDom` with `t⁴ |φ t| ≤ C` on `[1, ∞)`,
  `AJ φ₂ + 2 AJ φ₁ = -x² AJ[t² φ]`, i.e. `AJ[θ(θ+2)φ] = -x² AJ[t²φ]`: differentiate `x J₁(xt)` twice
  (`(x J₁(xt))' = x t J₀(xt)`, `(x t J₀(xt))' = t J₀(xt) - x t² J₁(xt)`) and compare with R1 twice.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `AJ ψ x = x ∫₀^∞ J₁(xt) ψ(t) dt`. -/
noncomputable def AJ (ψ : ℝ → ℝ) (x : ℝ) : ℝ := x * ∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * ψ t

theorem ajG_eq_AJ : ajG = AJ gB := rfl

/-- The class with polynomial decay. -/
abbrev PDom (ψ : ℝ → ℝ) : Prop :=
  ContinuousOn ψ (Set.Ioi 0) ∧ ∃ C : ℝ, 0 ≤ C ∧
    (∀ t : ℝ, 0 < t → t ≤ 1 → Real.sqrt t * |ψ t| ≤ C) ∧ ∀ t : ℝ, 1 ≤ t → t ^ 2 * |ψ t| ≤ C

/-! ## Two integrable majorants -/

theorem integrableOn_inv_sqrt {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹) (Set.Ioc 0 c) := by
  have h := intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (by norm_num)
    (a := 0) (b := c)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc] at h
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioc
  show s ^ (-(1 / 2 : ℝ)) = (Real.sqrt s)⁻¹
  rw [Real.rpow_neg hs.1.le, Real.sqrt_eq_rpow]

theorem integrableOn_inv_sq_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => (s ^ 2)⁻¹) (Set.Ioi c) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -(2 : ℝ)) (by norm_num) hc
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  show s ^ (-(2 : ℝ)) = (s ^ 2)⁻¹
  rw [Real.rpow_neg (le_of_lt (lt_trans hc hs)), Real.rpow_two]

/-- A function bounded by `A/√t` on `(0, 1]` and by `B/t²` on `(1, ∞)` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_of_bounds {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0)) {A B : ℝ}
    (h1 : ∀ t : ℝ, 0 < t → t ≤ 1 → |f t| ≤ A * (Real.sqrt t)⁻¹)
    (h2 : ∀ t : ℝ, 1 < t → |f t| ≤ B * (t ^ 2)⁻¹) : IntegrableOn f (Set.Ioi 0) := by
  have i1 : IntegrableOn f (Set.Ioc 0 1) := by
    have hm : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (hf.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    refine Integrable.mono' ((integrableOn_inv_sqrt zero_le_one).const_mul A) hm
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))
    rw [Real.norm_eq_abs]
    exact h1 t ht.1 ht.2
  have i2 : IntegrableOn f (Set.Ioi 1) := by
    have hm : AEStronglyMeasurable f (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (hf.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    refine Integrable.mono' ((integrableOn_inv_sq_Ioi one_pos).const_mul B) hm
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    rw [Real.norm_eq_abs]
    exact h2 t ht
  have h := i1.union i2
  rw [Set.Ioc_union_Ioi_eq_Ioi zero_le_one] at h
  exact h

theorem abs_le_of_sqrt_mul_le {a C t : ℝ} (ht : 0 < t) (h : Real.sqrt t * |a| ≤ C) :
    |a| ≤ C * (Real.sqrt t)⁻¹ := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rw [← div_eq_mul_inv, le_div_iff₀ hs, mul_comm]
  exact h

theorem abs_le_of_sq_mul_le {a C t : ℝ} (ht : 0 < t) (h : t ^ 2 * |a| ≤ C) :
    |a| ≤ C * (t ^ 2)⁻¹ := by
  have hs : 0 < t ^ 2 := pow_pos ht 2
  rw [← div_eq_mul_inv, le_div_iff₀ hs, mul_comm]
  exact h

theorem pdom_integrableOn {ψ : ℝ → ℝ} (hψ : PDom ψ) : IntegrableOn ψ (Set.Ioi 0) := by
  obtain ⟨hc, C, _, hn, hf⟩ := hψ
  exact integrableOn_Ioi_of_bounds hc (fun t ht ht1 => abs_le_of_sqrt_mul_le ht (hn t ht ht1))
    (fun t ht => abs_le_of_sq_mul_le (by linarith) (hf t ht.le))

/-! ## The substitution `s = xt` and the domination -/

/-- `AJ ψ x = ∫₀^∞ J₁(s) ψ(s/x) ds` for `x > 0`. -/
theorem AJ_eq_subst (ψ : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    AJ ψ x = ∫ s in Set.Ioi (0 : ℝ), besselJ1 s * ψ (s / x) := by
  unfold AJ
  have h : (∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * ψ (x * t / x))
      = x⁻¹ • ∫ s in Set.Ioi (x * 0), besselJ1 s * ψ (s / x) :=
    integral_comp_mul_left_Ioi (fun s : ℝ => besselJ1 s * ψ (s / x)) 0 hx
  rw [mul_zero, smul_eq_mul] at h
  have h2 : (∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * ψ t)
      = ∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * ψ (x * t / x) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show besselJ1 (x * t) * ψ t = besselJ1 (x * t) * ψ (x * t / x)
    rw [mul_div_cancel_left₀ t hx.ne']
  rw [h2, h, ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]

/-- The majorant of `ψ(s/y)` for `y ∈ (x/2, 2x)`. -/
noncomputable def pbnd (C x s : ℝ) : ℝ :=
  (Set.Ioc 0 (2 * x)).indicator (fun s : ℝ => C * Real.sqrt (2 * x) * (Real.sqrt s)⁻¹) s
    + (Set.Ioi (x / 2)).indicator (fun s : ℝ => C * (4 * x ^ 2) * (s ^ 2)⁻¹) s

theorem integrable_pbnd {C x : ℝ} (hx : 0 < x) :
    Integrable (fun s : ℝ => pbnd C x s) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 : Integrable ((Set.Ioc 0 (2 * x)).indicator
      (fun s : ℝ => C * Real.sqrt (2 * x) * (Real.sqrt s)⁻¹)) :=
    ((integrableOn_inv_sqrt (by linarith : (0 : ℝ) ≤ 2 * x)).const_mul
      (C * Real.sqrt (2 * x))).integrable_indicator measurableSet_Ioc
  have h2 : Integrable ((Set.Ioi (x / 2)).indicator (fun s : ℝ => C * (4 * x ^ 2) * (s ^ 2)⁻¹)) :=
    ((integrableOn_inv_sq_Ioi (by linarith : (0 : ℝ) < x / 2)).const_mul
      (C * (4 * x ^ 2))).integrable_indicator measurableSet_Ioi
  exact (h1.add h2).restrict

theorem pdom_bound {ψ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hn : ∀ t : ℝ, 0 < t → t ≤ 1 → Real.sqrt t * |ψ t| ≤ C) (hf : ∀ t : ℝ, 1 ≤ t → t ^ 2 * |ψ t| ≤ C)
    {x y s : ℝ} (hx : 0 < x) (hy : y ∈ Set.Ioo (x / 2) (2 * x)) (hs : 0 < s) :
    |ψ (s / y)| ≤ pbnd C x s := by
  have hy0 : 0 < y := by linarith [hy.1]
  have hu : 0 < s / y := div_pos hs hy0
  have hI1 : 0 ≤ (Set.Ioc 0 (2 * x)).indicator
      (fun s : ℝ => C * Real.sqrt (2 * x) * (Real.sqrt s)⁻¹) s :=
    Set.indicator_nonneg (fun s _ => mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
      (inv_nonneg.mpr (Real.sqrt_nonneg _))) s
  have hI2 : 0 ≤ (Set.Ioi (x / 2)).indicator (fun s : ℝ => C * (4 * x ^ 2) * (s ^ 2)⁻¹) s :=
    Set.indicator_nonneg (fun s _ => mul_nonneg (mul_nonneg hC (by positivity))
      (inv_nonneg.mpr (sq_nonneg _))) s
  unfold pbnd
  rcases le_or_gt (s / y) 1 with h1 | h1
  · -- `s ≤ y < 2x`
    have hsy : s ≤ y := (div_le_one hy0).mp h1
    have hmem : s ∈ Set.Ioc 0 (2 * x) := ⟨hs, by linarith [hy.2]⟩
    rw [Set.indicator_of_mem hmem]
    have hb := abs_le_of_sqrt_mul_le hu (hn (s / y) hu h1)
    have hsq : Real.sqrt s = Real.sqrt (s / y) * Real.sqrt y := by
      rw [← Real.sqrt_mul hu.le, div_mul_cancel₀ s hy0.ne']
    have hpu : 0 < Real.sqrt (s / y) := Real.sqrt_pos.mpr hu
    have hpy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
    have hpyi : Real.sqrt y * (Real.sqrt y)⁻¹ = 1 := mul_inv_cancel₀ hpy.ne'
    have e : C * (Real.sqrt (s / y))⁻¹ = C * Real.sqrt y * (Real.sqrt s)⁻¹ := by
      rw [hsq, mul_inv]
      linear_combination (-(C * (Real.sqrt (s / y))⁻¹)) * hpyi
    have hyx : Real.sqrt y ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt (by linarith [hy.2])
    have h3 : C * Real.sqrt y * (Real.sqrt s)⁻¹ ≤ C * Real.sqrt (2 * x) * (Real.sqrt s)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyx hC) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    linarith
  · -- `s > y > x/2`
    have hsy : y < s := (one_lt_div hy0).mp h1
    have hmem : s ∈ Set.Ioi (x / 2) := by
      show x / 2 < s
      linarith [hy.1]
    rw [Set.indicator_of_mem hmem]
    have hb := abs_le_of_sq_mul_le hu (hf (s / y) h1.le)
    have hsi : s ^ 2 * (s ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hs.ne')
    have hyi : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
    have e : C * ((s / y) ^ 2)⁻¹ = C * y ^ 2 * (s ^ 2)⁻¹ := by
      rw [div_pow, inv_div]
      rw [div_eq_mul_inv]
      ring
    have hy2 : y ^ 2 ≤ 4 * x ^ 2 := by nlinarith [hy.2, hy0]
    have h3 : C * y ^ 2 * (s ^ 2)⁻¹ ≤ C * (4 * x ^ 2) * (s ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy2 hC) (inv_nonneg.mpr (sq_nonneg _))
    linarith

/-! ## R1: `ϑ AJ[ψ] = -AJ[θψ]` -/

/-- **R1.** For a chain `ψ, ψ₁` in `PDom` (`ψ' = ψ₁/t`), `(AJ ψ)'(x) = -AJ ψ₁ (x) / x`. -/
theorem hasDerivAt_AJ {ψ ψ1 : ℝ → ℝ} (hψ : PDom ψ) (hψ1 : PDom ψ1)
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt ψ (ψ1 t / t) t) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (AJ ψ) (-(AJ ψ1 x) / x) x := by
  obtain ⟨hc, C0, hC0, hn0, hf0⟩ := hψ
  obtain ⟨hc1, C1, hC1, hn1, hf1⟩ := hψ1
  have hs : Set.Ioo (x / 2) (2 * x) ∈ nhds x := Ioo_mem_nhds (by linarith) (by linarith)
  have hxB : x ∈ Set.Ioo (x / 2) (2 * x) := ⟨by linarith, by linarith⟩
  have hmeas : ∀ y ∈ Set.Ioo (x / 2) (2 * x), AEStronglyMeasurable
      (fun s : ℝ => besselJ1 s * ψ (s / y)) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hmap : Set.MapsTo (fun s : ℝ => s / y) (Set.Ioi 0) (Set.Ioi 0) :=
      fun s hs' => div_pos hs' hy0
    have hcomp : ContinuousOn (fun s : ℝ => ψ (s / y)) (Set.Ioi 0) :=
      hc.comp (continuousOn_id.div_const y) hmap
    exact (continuous_besselJ1.continuousOn.mul hcomp).aestronglyMeasurable measurableSet_Ioi
  have hint : Integrable (fun s : ℝ => besselJ1 s * ψ (s / x)) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (integrable_pbnd (C := C0) hx).mono' (hmeas x hxB)
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs' => ?_))
    have hs0 : (0 : ℝ) < s := hs'
    rw [Real.norm_eq_abs, abs_mul]
    have hJ := abs_besselJ1_le_one hs0.le
    have hb := pdom_bound hC0 hn0 hf0 hx hxB hs0
    calc |besselJ1 s| * |ψ (s / x)| ≤ 1 * |ψ (s / x)| :=
          mul_le_mul_of_nonneg_right hJ (abs_nonneg _)
      _ ≤ pbnd C0 x s := by linarith
  have hmeas' : AEStronglyMeasurable (fun s : ℝ => -(besselJ1 s * ψ1 (s / x) / x))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hmap : Set.MapsTo (fun s : ℝ => s / x) (Set.Ioi 0) (Set.Ioi 0) :=
      fun s hs' => div_pos hs' hx
    have hcomp : ContinuousOn (fun s : ℝ => ψ1 (s / x)) (Set.Ioi 0) :=
      hc1.comp (continuousOn_id.div_const x) hmap
    exact (((continuous_besselJ1.continuousOn.mul hcomp).div_const x).neg).aestronglyMeasurable
      measurableSet_Ioi
  have hbound : ∀ s ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      ‖-(besselJ1 s * ψ1 (s / y) / y)‖ ≤ 2 / x * pbnd C1 x s := by
    intro s hs' y hy
    have hs0 : (0 : ℝ) < s := hs'
    have hy0 : 0 < y := by linarith [hy.1]
    rw [norm_neg, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hy0]
    have hJ := abs_besselJ1_le_one hs0.le
    have hb := pdom_bound hC1 hn1 hf1 hx hy hs0
    have hpb : 0 ≤ pbnd C1 x s := le_trans (abs_nonneg _) hb
    have h1 : |besselJ1 s| * |ψ1 (s / y)| ≤ pbnd C1 x s := by
      calc |besselJ1 s| * |ψ1 (s / y)| ≤ 1 * |ψ1 (s / y)| :=
            mul_le_mul_of_nonneg_right hJ (abs_nonneg _)
        _ ≤ pbnd C1 x s := by linarith
    have hyx : 1 / y ≤ 2 / x := by
      rw [div_le_div_iff₀ hy0 hx]
      linarith [hy.1]
    calc |besselJ1 s| * |ψ1 (s / y)| / y = (|besselJ1 s| * |ψ1 (s / y)|) * (1 / y) := by ring
      _ ≤ pbnd C1 x s * (2 / x) :=
          mul_le_mul h1 hyx (one_div_pos.mpr hy0).le hpb
      _ = 2 / x * pbnd C1 x s := by ring
  have hbi : Integrable (fun s : ℝ => 2 / x * pbnd C1 x s) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrable_pbnd hx).const_mul _
  have hdiff : ∀ s ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      HasDerivAt (fun y : ℝ => besselJ1 s * ψ (s / y)) (-(besselJ1 s * ψ1 (s / y) / y)) y := by
    intro s hs' y hy
    have hs0 : (0 : ℝ) < s := hs'
    have hy0 : 0 < y := by linarith [hy.1]
    have h1 : HasDerivAt (fun y : ℝ => s / y) ((0 * y - s * 1) / y ^ 2) y :=
      (hasDerivAt_const y s).div (hasDerivAt_id y) hy0.ne'
    have h2 := hd (s / y) (div_pos hs0 hy0)
    have h3 : HasDerivAt (fun y : ℝ => ψ (s / y)) (ψ1 (s / y) / (s / y) * ((0 * y - s * 1) / y ^ 2)) y :=
      h2.comp y h1
    have h4 : HasDerivAt (fun y : ℝ => besselJ1 s * ψ (s / y))
        (besselJ1 s * (ψ1 (s / y) / (s / y) * ((0 * y - s * 1) / y ^ 2))) y := h3.const_mul _
    refine h4.congr_deriv ?_
    have hsi : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
    have hyi : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
    linear_combination (-(besselJ1 s * ψ1 (s / y) * y⁻¹) * (y * y⁻¹)) * hsi
      + (-(besselJ1 s * ψ1 (s / y) * y⁻¹)) * hyi
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun y s => besselJ1 s * ψ (s / y))
    (F' := fun y s => -(besselJ1 s * ψ1 (s / y) / y))
    (bound := fun s => 2 / x * pbnd C1 x s) hs
    (Filter.eventually_of_mem hs hmeas) hint hmeas'
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound) hbi
    (ae_restrict_of_forall_mem measurableSet_Ioi hdiff)
  have h5 : HasDerivAt (fun y : ℝ => ∫ s in Set.Ioi (0 : ℝ), besselJ1 s * ψ (s / y))
      (∫ s in Set.Ioi (0 : ℝ), -(besselJ1 s * ψ1 (s / x) / x)) x := key.2
  have hval : (∫ s in Set.Ioi (0 : ℝ), -(besselJ1 s * ψ1 (s / x) / x)) = -(AJ ψ1 x) / x := by
    rw [integral_neg, integral_div, AJ_eq_subst ψ1 hx, neg_div]
  rw [hval] at h5
  have he : AJ ψ =ᶠ[nhds x] fun y : ℝ => ∫ s in Set.Ioi (0 : ℝ), besselJ1 s * ψ (s / y) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) (fun y hy => AJ_eq_subst ψ hy)
  exact h5.congr_of_eventuallyEq he

/-! ## R2: `AJ[θ(θ+2)φ] = -x² AJ[t²φ]` -/

theorem hasDerivAt_mul_besselJ1_mul {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun x : ℝ => x * besselJ1 (x * t)) (y * t * besselJ0 (y * t)) y := by
  have h0 := (hasDerivAt_mul_besselJ1 (y * t)).comp y ((hasDerivAt_id y).mul_const t)
  have h1 : HasDerivAt (fun x : ℝ => (x * t) * besselJ1 (x * t)) (y * t * besselJ0 (y * t) * (1 * t)) y :=
    h0
  have h2 := h1.const_mul t⁻¹
  have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hfun : (fun x : ℝ => x * besselJ1 (x * t)) = fun x : ℝ => t⁻¹ * ((x * t) * besselJ1 (x * t)) := by
    funext x
    linear_combination (-(x * besselJ1 (x * t))) * hti
  rw [hfun]
  refine h2.congr_deriv ?_
  linear_combination (y * t * besselJ0 (y * t)) * hti

theorem hasDerivAt_mul_mul_besselJ0_mul (t y : ℝ) :
    HasDerivAt (fun x : ℝ => x * t * besselJ0 (x * t))
      (t * besselJ0 (y * t) - y * t ^ 2 * besselJ1 (y * t)) y := by
  have h0 := (hasDerivAt_besselJ0 (y * t)).comp y ((hasDerivAt_id y).mul_const t)
  have h1 : HasDerivAt (fun x : ℝ => besselJ0 (x * t)) (-besselJ1 (y * t) * (1 * t)) y := h0
  have h2 : HasDerivAt (fun x : ℝ => x * t) (1 * t) y := (hasDerivAt_id y).mul_const t
  have h3 : HasDerivAt (fun x : ℝ => x * t * besselJ0 (x * t))
      (1 * t * besselJ0 (y * t) + y * t * (-besselJ1 (y * t) * (1 * t))) y := h2.mul h1
  refine h3.congr_deriv ?_
  ring

/-- `t |φ|`, `t² |φ|` and `|φ|` are integrable for `φ ∈ PDom` with `t⁴|φ| ≤ C` on `[1, ∞)`. -/
theorem integrableOn_pow_mul_of_pdom4 {φ : ℝ → ℝ} (hφ : PDom φ) {C4 : ℝ}
    (h4 : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |φ t| ≤ C4) {j : ℕ} (hj : j ≤ 2) :
    IntegrableOn (fun t : ℝ => t ^ j * φ t) (Set.Ioi 0) := by
  obtain ⟨hc, C, hC, hn, _⟩ := hφ
  have hcont : ContinuousOn (fun t : ℝ => t ^ j * φ t) (Set.Ioi 0) :=
    ContinuousOn.mul (f := fun t : ℝ => t ^ j) (continuous_pow j).continuousOn hc
  refine integrableOn_Ioi_of_bounds hcont (A := C) (B := C4) (fun t ht ht1 => ?_) (fun t ht => ?_)
  · rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le j)]
    have hpj : t ^ j ≤ 1 := pow_le_one₀ ht.le ht1
    have hb := abs_le_of_sqrt_mul_le ht (hn t ht ht1)
    calc t ^ j * |φ t| ≤ 1 * |φ t| := mul_le_mul_of_nonneg_right hpj (abs_nonneg _)
      _ ≤ C * (Real.sqrt t)⁻¹ := by linarith
  · have ht0 : 0 < t := by linarith
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht0.le j)]
    have hb := h4 t ht.le
    have hpj : t ^ j ≤ t ^ 2 := pow_le_pow_right₀ ht.le hj
    have ht2 : 0 < t ^ 2 := pow_pos ht0 2
    have e : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [← div_eq_mul_inv, le_div_iff₀ ht2]
    calc t ^ j * |φ t| * t ^ 2 ≤ t ^ 2 * |φ t| * t ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpj (abs_nonneg _)) ht2.le
      _ = t ^ 4 * |φ t| := by ring
      _ ≤ C4 := hb

/-- `∫ y t J₀(yt) φ(t) dt`: the first `y`-derivative of `AJ φ`. -/
noncomputable def AJd1 (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), y * t * besselJ0 (y * t) * φ t

/-- `∫ (t J₀(yt) - y t² J₁(yt)) φ(t) dt`: the second `y`-derivative of `AJ φ`. -/
noncomputable def AJd2 (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), (t * besselJ0 (y * t) - y * t ^ 2 * besselJ1 (y * t)) * φ t

theorem continuous_besselJ0_mul' (y : ℝ) : Continuous (fun t : ℝ => besselJ0 (y * t)) :=
  continuous_besselJ0.comp (continuous_const.mul continuous_id)

theorem continuous_besselJ1_mul' (y : ℝ) : Continuous (fun t : ℝ => besselJ1 (y * t)) :=
  continuous_besselJ1.comp (continuous_const.mul continuous_id)

theorem AJ_eq_integral (φ : ℝ → ℝ) (y : ℝ) :
    AJ φ y = ∫ t in Set.Ioi (0 : ℝ), y * besselJ1 (y * t) * φ t := by
  unfold AJ
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  show y * (besselJ1 (y * t) * φ t) = y * besselJ1 (y * t) * φ t
  ring

theorem abs_d1_integrand_le {φ : ℝ → ℝ} {y t : ℝ} (hy : 0 ≤ y) (ht : 0 < t) {b : ℝ} (hyb : y ≤ b) :
    |y * t * besselJ0 (y * t) * φ t| ≤ b * (t * |φ t|) := by
  have hJ := abs_besselJ0_le_one (mul_nonneg hy ht.le)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hy, abs_of_pos ht]
  have h1 : y * t * |besselJ0 (y * t)| ≤ b * t := by
    have h2 := mul_le_mul_of_nonneg_left hJ (mul_nonneg hy ht.le)
    have h3 : y * t ≤ b * t := mul_le_mul_of_nonneg_right hyb ht.le
    linarith
  calc y * t * |besselJ0 (y * t)| * |φ t| ≤ b * t * |φ t| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = b * (t * |φ t|) := by ring

theorem abs_d2_integrand_le {φ : ℝ → ℝ} {y t : ℝ} (hy : 0 ≤ y) (ht : 0 < t) {b : ℝ} (hyb : y ≤ b) :
    |(t * besselJ0 (y * t) - y * t ^ 2 * besselJ1 (y * t)) * φ t|
      ≤ t * |φ t| + b * (t ^ 2 * |φ t|) := by
  have hJ0 := abs_besselJ0_le_one (mul_nonneg hy ht.le)
  have hJ1 := abs_besselJ1_le_one (mul_nonneg hy ht.le)
  have hp2 : 0 ≤ t ^ 2 := pow_nonneg ht.le 2
  have hA : |t * besselJ0 (y * t) - y * t ^ 2 * besselJ1 (y * t)| ≤ t + b * t ^ 2 := by
    have a1 := abs_add_le (t * besselJ0 (y * t)) (-(y * t ^ 2 * besselJ1 (y * t)))
    rw [abs_neg, ← sub_eq_add_neg, abs_mul, abs_mul, abs_mul, abs_of_pos ht, abs_of_nonneg hy,
      abs_of_nonneg hp2] at a1
    have b1 : t * |besselJ0 (y * t)| ≤ t := by
      have := mul_le_mul_of_nonneg_left hJ0 ht.le
      linarith
    have b2 : y * t ^ 2 * |besselJ1 (y * t)| ≤ b * t ^ 2 := by
      have h2 := mul_le_mul_of_nonneg_left hJ1 (mul_nonneg hy hp2)
      have h3 : y * t ^ 2 ≤ b * t ^ 2 := mul_le_mul_of_nonneg_right hyb hp2
      linarith
    linarith
  rw [abs_mul]
  calc |t * besselJ0 (y * t) - y * t ^ 2 * besselJ1 (y * t)| * |φ t|
      ≤ (t + b * t ^ 2) * |φ t| := mul_le_mul_of_nonneg_right hA (abs_nonneg _)
    _ = t * |φ t| + b * (t ^ 2 * |φ t|) := by ring

theorem hasDerivAt_AJ_d1 {φ : ℝ → ℝ} (hφ : PDom φ) {C4 : ℝ}
    (h4 : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |φ t| ≤ C4) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (AJ φ) (AJd1 φ x) x := by
  have hc : ContinuousOn φ (Set.Ioi 0) := hφ.1
  have i0 := integrableOn_pow_mul_of_pdom4 hφ h4 (j := 0) (by norm_num)
  have i1 := integrableOn_pow_mul_of_pdom4 hφ h4 (j := 1) (by norm_num)
  have hs : Set.Ioo (x / 2) (2 * x) ∈ nhds x := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable (fun t : ℝ => y * besselJ1 (y * t) * φ t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := fun y =>
    ((continuous_const.mul (continuous_besselJ1_mul' y)).continuousOn.mul hc).aestronglyMeasurable
      measurableSet_Ioi
  have hint : Integrable (fun t : ℝ => x * besselJ1 (x * t) * φ t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (i0.norm.const_mul x).mono' (hmeas x)
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := ht
    have hJ := abs_besselJ1_le_one (mul_nonneg hx.le ht0.le)
    show ‖x * besselJ1 (x * t) * φ t‖ ≤ x * ‖t ^ 0 * φ t‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, pow_zero, one_mul, abs_mul, abs_mul, abs_of_pos hx]
    have h1 : x * |besselJ1 (x * t)| ≤ x * 1 := mul_le_mul_of_nonneg_left hJ hx.le
    calc x * |besselJ1 (x * t)| * |φ t| ≤ x * 1 * |φ t| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = x * |φ t| := by ring
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => x * t * besselJ0 (x * t) * φ t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (((continuous_const.mul continuous_id).mul (continuous_besselJ0_mul' x)).continuousOn.mul
      hc).aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      ‖y * t * besselJ0 (y * t) * φ t‖ ≤ 2 * x * ‖t ^ 1 * φ t‖ := by
    intro t ht y hy
    have ht0 : (0 : ℝ) < t := ht
    have hy0 : 0 < y := by linarith [hy.1]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, pow_one, abs_mul t, abs_of_pos ht0]
    exact abs_d1_integrand_le hy0.le ht0 hy.2.le
  have hbi : Integrable (fun t : ℝ => 2 * x * ‖t ^ 1 * φ t‖) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    i1.norm.const_mul _
  have hdiff : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      HasDerivAt (fun y : ℝ => y * besselJ1 (y * t) * φ t) (y * t * besselJ0 (y * t) * φ t) y := by
    intro t ht y _
    exact (hasDerivAt_mul_besselJ1_mul ht y).mul_const (φ t)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun y t => y * besselJ1 (y * t) * φ t)
    (F' := fun y t => y * t * besselJ0 (y * t) * φ t)
    (bound := fun t => 2 * x * ‖t ^ 1 * φ t‖) hs
    (Filter.Eventually.of_forall hmeas) hint hmeas'
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound) hbi
    (ae_restrict_of_forall_mem measurableSet_Ioi hdiff)
  have h5 : HasDerivAt (fun y : ℝ => ∫ t in Set.Ioi (0 : ℝ), y * besselJ1 (y * t) * φ t)
      (AJd1 φ x) x := key.2
  have hfun : AJ φ = fun y : ℝ => ∫ t in Set.Ioi (0 : ℝ), y * besselJ1 (y * t) * φ t :=
    funext (AJ_eq_integral φ)
  rw [hfun]
  exact h5

theorem integrable_d2_integrand {φ : ℝ → ℝ} (hφ : PDom φ) {C4 : ℝ}
    (h4 : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |φ t| ≤ C4) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => (t * besselJ0 (x * t) - x * t ^ 2 * besselJ1 (x * t)) * φ t)
      (Set.Ioi 0) := by
  have hc : ContinuousOn φ (Set.Ioi 0) := hφ.1
  have i1 := integrableOn_pow_mul_of_pdom4 hφ h4 (j := 1) (by norm_num)
  have i2 := integrableOn_pow_mul_of_pdom4 hφ h4 (j := 2) (by norm_num)
  have hm : AEStronglyMeasurable
      (fun t : ℝ => (t * besselJ0 (x * t) - x * t ^ 2 * besselJ1 (x * t)) * φ t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((((continuous_id.mul (continuous_besselJ0_mul' x)).sub
      ((continuous_const.mul (continuous_pow 2)).mul (continuous_besselJ1_mul' x)))).continuousOn.mul
      hc).aestronglyMeasurable measurableSet_Ioi
  refine (i1.norm.add (i2.norm.const_mul x)).mono' hm
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
  have ht0 : (0 : ℝ) < t := ht
  show ‖(t * besselJ0 (x * t) - x * t ^ 2 * besselJ1 (x * t)) * φ t‖
    ≤ ‖t ^ 1 * φ t‖ + x * ‖t ^ 2 * φ t‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, pow_one, abs_mul t, abs_of_pos ht0,
    abs_mul (t ^ 2), abs_of_nonneg (pow_nonneg ht0.le 2)]
  exact abs_d2_integrand_le hx ht0 le_rfl

theorem integrable_d1_integrand {φ : ℝ → ℝ} (hφ : PDom φ) {C4 : ℝ}
    (h4 : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |φ t| ≤ C4) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => x * t * besselJ0 (x * t) * φ t) (Set.Ioi 0) := by
  have hc : ContinuousOn φ (Set.Ioi 0) := hφ.1
  have i1 := integrableOn_pow_mul_of_pdom4 hφ h4 (j := 1) (by norm_num)
  have hm : AEStronglyMeasurable (fun t : ℝ => x * t * besselJ0 (x * t) * φ t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (((continuous_const.mul continuous_id).mul (continuous_besselJ0_mul' x)).continuousOn.mul
      hc).aestronglyMeasurable measurableSet_Ioi
  refine (i1.norm.const_mul x).mono' hm (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
  have ht0 : (0 : ℝ) < t := ht
  show ‖x * t * besselJ0 (x * t) * φ t‖ ≤ x * ‖t ^ 1 * φ t‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, pow_one, abs_mul t, abs_of_pos ht0]
  exact abs_d1_integrand_le hx ht0 le_rfl

theorem hasDerivAt_AJd1 {φ : ℝ → ℝ} (hφ : PDom φ) {C4 : ℝ}
    (h4 : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |φ t| ≤ C4) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (AJd1 φ) (AJd2 φ x) x := by
  have hc : ContinuousOn φ (Set.Ioi 0) := hφ.1
  have i1 := integrableOn_pow_mul_of_pdom4 hφ h4 (j := 1) (by norm_num)
  have i2 := integrableOn_pow_mul_of_pdom4 hφ h4 (j := 2) (by norm_num)
  have hs : Set.Ioo (x / 2) (2 * x) ∈ nhds x := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable (fun t : ℝ => y * t * besselJ0 (y * t) * φ t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := fun y =>
    (((continuous_const.mul continuous_id).mul (continuous_besselJ0_mul' y)).continuousOn.mul
      hc).aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      ‖(t * besselJ0 (y * t) - y * t ^ 2 * besselJ1 (y * t)) * φ t‖
        ≤ ‖t ^ 1 * φ t‖ + 2 * x * ‖t ^ 2 * φ t‖ := by
    intro t ht y hy
    have ht0 : (0 : ℝ) < t := ht
    have hy0 : 0 < y := by linarith [hy.1]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, pow_one, abs_mul t, abs_of_pos ht0,
      abs_mul (t ^ 2), abs_of_nonneg (pow_nonneg ht0.le 2)]
    exact abs_d2_integrand_le hy0.le ht0 hy.2.le
  have hbi : Integrable (fun t : ℝ => ‖t ^ 1 * φ t‖ + 2 * x * ‖t ^ 2 * φ t‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    i1.norm.add (i2.norm.const_mul _)
  have hdiff : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      HasDerivAt (fun y : ℝ => y * t * besselJ0 (y * t) * φ t)
        ((t * besselJ0 (y * t) - y * t ^ 2 * besselJ1 (y * t)) * φ t) y := by
    intro t _ y _
    exact (hasDerivAt_mul_mul_besselJ0_mul t y).mul_const (φ t)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun y t => y * t * besselJ0 (y * t) * φ t)
    (F' := fun y t => (t * besselJ0 (y * t) - y * t ^ 2 * besselJ1 (y * t)) * φ t)
    (bound := fun t => ‖t ^ 1 * φ t‖ + 2 * x * ‖t ^ 2 * φ t‖) hs
    (Filter.Eventually.of_forall hmeas) (integrable_d1_integrand hφ h4 hx.le)
    (integrable_d2_integrand hφ h4 hx.le).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound) hbi
    (ae_restrict_of_forall_mem measurableSet_Ioi hdiff)
  exact key.2

/-- `x² AJd2 φ x - x AJd1 φ x = -x² AJ[t² φ](x)`. -/
theorem AJd_comb {φ : ℝ → ℝ} (hφ : PDom φ) {C4 : ℝ}
    (h4 : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |φ t| ≤ C4) {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * AJd2 φ x - x * AJd1 φ x = -x ^ 2 * AJ (fun t : ℝ => t ^ 2 * φ t) x := by
  have hA := (integrable_d2_integrand hφ h4 hx).const_mul (x ^ 2)
  have hB := (integrable_d1_integrand hφ h4 hx).const_mul x
  unfold AJd2 AJd1
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub hA hB, AJ_eq_integral,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  show x ^ 2 * ((t * besselJ0 (x * t) - x * t ^ 2 * besselJ1 (x * t)) * φ t)
      - x * (x * t * besselJ0 (x * t) * φ t)
    = -x ^ 2 * (x * besselJ1 (x * t) * (t ^ 2 * φ t))
  ring

/-- **R2.**  For a chain `φ, φ₁, φ₂` in `PDom` with `t⁴|φ| ≤ C` on `[1, ∞)`:
`AJ φ₂ + 2 AJ φ₁ = -x² AJ[t² φ]` for `x > 0`. -/
theorem AJ_theta2 {φ φ1 φ2 : ℝ → ℝ} (hφ : PDom φ) (hφ1 : PDom φ1) (hφ2 : PDom φ2)
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt φ (φ1 t / t) t)
    (hd1 : ∀ t : ℝ, 0 < t → HasDerivAt φ1 (φ2 t / t) t)
    {C4 : ℝ} (h4 : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |φ t| ≤ C4) {x : ℝ} (hx : 0 < x) :
    AJ φ2 x + 2 * AJ φ1 x = -x ^ 2 * AJ (fun t : ℝ => t ^ 2 * φ t) x := by
  have hD1 : ∀ y : ℝ, 0 < y → AJd1 φ y = -(AJ φ1 y) / y := fun y hy =>
    (hasDerivAt_AJ_d1 hφ h4 hy).unique (hasDerivAt_AJ hφ hφ1 hd hy)
  have hq : HasDerivAt (fun y : ℝ => -(AJ φ1 y) / y)
      ((-(-(AJ φ2 x) / x) * x - -(AJ φ1 x) * 1) / x ^ 2) x :=
    ((hasDerivAt_AJ hφ1 hφ2 hd1 hx).neg).div (hasDerivAt_id x) hx.ne'
  have hD2 : AJd2 φ x = (-(-(AJ φ2 x) / x) * x - -(AJ φ1 x) * 1) / x ^ 2 :=
    eq_of_hasDerivAt_of_eqOn hx hD1 (hasDerivAt_AJd1 hφ h4 hx) hq
  have hcomb := AJd_comb hφ h4 hx.le
  rw [hD2, hD1 x hx] at hcomb
  have hxi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  have hx2 : x ^ 2 * (x ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hx.ne')
  linear_combination hcomb + (-(AJ φ2 x) - AJ φ1 x) * hx2 + (-(AJ φ2 x) * (x ^ 2 * (x ^ 2)⁻¹)) * hxi
    + (-(AJ φ1 x)) * hxi

end Tower.RV6
