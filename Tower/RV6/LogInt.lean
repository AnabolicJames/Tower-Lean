import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselJ
import Tower.RV6.Laplace

/-!
# The logarithm formula with damping

For `a ≥ 0` and `δ > 0`,

`∫₀^∞ (e^{-t} - e^{-δt} J₀(at)) dt/t = log (δ + √(a² + δ²)) - log 2`  (`logInt_eq`).

The left side (`logInt a δ`) has derivative `∫₀^∞ e^{-δt} J₀(at) dt = 1/√(a² + δ²)` in `δ`
(`hasDerivAt_logInt`, `lapl_besselJ0`), and so does `logG a δ = log (δ + √(a² + δ²))`.  For `a = 0`
the difference is fixed at `δ = 1`, where the integrand vanishes.  For `a > 0` the two differences
are compared at large `δ`: `|logInt a δ - logInt 0 δ| ≤ a/δ` and
`0 ≤ logG a δ - logG 0 δ ≤ a/(2δ)`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `Ψ_a(δ) = ∫₀^∞ (e^{-t} - e^{-δt} J₀(at)) dt/t`. -/
noncomputable def logInt (a δ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t)) / t

/-- `G_a(x) = log (x + √(a² + x²))`. -/
noncomputable def logG (a x : ℝ) : ℝ := Real.log (x + Real.sqrt (a * a + x * x))

/-! ## The integrand -/

theorem logInt_integrand_abs_le {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (ht : 0 < t) :
    |(Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t)) / t| ≤ 1 + δ + a := by
  have hat : 0 ≤ a * t := mul_nonneg ha ht.le
  have hδt : 0 ≤ δ * t := mul_nonneg hδ.le ht.le
  have hJ1 := (abs_le.mp (abs_besselJ0_le_one hat)).2
  have h1J := one_sub_besselJ0_le hat
  have he1 : Real.exp (-t) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (by linarith : -t ≤ 0)
    rw [Real.exp_zero] at h
    exact h
  have he2 : -t + 1 ≤ Real.exp (-t) := Real.add_one_le_exp (-t)
  have hd1 : Real.exp (-δ * t) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (by linarith : -δ * t ≤ 0)
    rw [Real.exp_zero] at h
    exact h
  have hd2 : -δ * t + 1 ≤ Real.exp (-δ * t) := Real.add_one_le_exp (-δ * t)
  have hd0 := Real.exp_pos (-δ * t)
  have h1Jn : 0 ≤ 1 - besselJ0 (a * t) := by linarith
  have hp1 : 0 ≤ Real.exp (-δ * t) * (1 - besselJ0 (a * t)) := mul_nonneg hd0.le h1Jn
  have hp2 : Real.exp (-δ * t) * (1 - besselJ0 (a * t)) ≤ 1 * (a * t) :=
    mul_le_mul hd1 h1J h1Jn zero_le_one
  have e : Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t)
      = (Real.exp (-t) - 1) + (1 - Real.exp (-δ * t))
        + Real.exp (-δ * t) * (1 - besselJ0 (a * t)) := by ring
  have e2 : (1 + δ + a) * t = t + δ * t + a * t := by ring
  rw [abs_div, abs_of_pos ht, div_le_iff₀ ht, abs_le, e, e2]
  constructor
  · linarith
  · linarith

theorem logInt_integrand_abs_le_of_one_le {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |(Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t)) / t|
      ≤ Real.exp (-t) + Real.exp (-δ * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hJ := abs_le.mp (abs_besselJ0_le_one (mul_nonneg ha ht0.le))
  have h1 := Real.exp_pos (-t)
  have h2 := Real.exp_pos (-δ * t)
  have hp1 : Real.exp (-δ * t) * besselJ0 (a * t) ≤ Real.exp (-δ * t) * 1 :=
    mul_le_mul_of_nonneg_left hJ.2 h2.le
  have hp2 : Real.exp (-δ * t) * (-1) ≤ Real.exp (-δ * t) * besselJ0 (a * t) :=
    mul_le_mul_of_nonneg_left hJ.1 h2.le
  have hs : 0 ≤ Real.exp (-t) + Real.exp (-δ * t) := by linarith
  have hM : Real.exp (-t) + Real.exp (-δ * t)
      ≤ (Real.exp (-t) + Real.exp (-δ * t)) * t := le_mul_of_one_le_right hs ht
  rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0, abs_le]
  constructor
  · linarith
  · linarith

theorem measurable_logInt_integrand (a δ : ℝ) :
    Measurable fun t : ℝ => (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t)) / t := by
  have h1 : Continuous fun t : ℝ => Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t) :=
    (Real.continuous_exp.comp continuous_neg).sub
      ((continuous_exp_neg_mul δ).mul (continuous_besselJ0_comp a))
  exact h1.measurable.div measurable_id

/-- The integrand of `logInt a δ` is integrable on `(0, ∞)`. -/
theorem integrable_logInt {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t)) / t)
      (Set.Ioi (0 : ℝ)) := by
  have hm := measurable_logInt_integrand a δ
  have h01 : IntegrableOn
      (fun t : ℝ => (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t)) / t)
      (Set.Ioc (0 : ℝ) 1) := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable (1 + δ + a)
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))
    rw [Real.norm_eq_abs]
    exact logInt_integrand_abs_le ha hδ ht.1
  have h1 : IntegrableOn
      (fun t : ℝ => (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t)) / t)
      (Set.Ioi (1 : ℝ)) := by
    have hb1 : Integrable (fun t : ℝ => Real.exp (-t)) (volume.restrict (Set.Ioi (1 : ℝ))) :=
      integrableOn_exp_neg_Ioi 1
    have hb2 : Integrable (fun t : ℝ => Real.exp (-δ * t))
        (volume.restrict (Set.Ioi (1 : ℝ))) := exp_neg_integrableOn_Ioi 1 hδ
    have hb : Integrable (fun t : ℝ => Real.exp (-t) + Real.exp (-δ * t))
        (volume.restrict (Set.Ioi (1 : ℝ))) := hb1.add hb2
    show Integrable
      (fun t : ℝ => (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (a * t)) / t)
      (volume.restrict (Set.Ioi (1 : ℝ)))
    refine Integrable.mono' hb hm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht1 : (1 : ℝ) < t := ht
    rw [Real.norm_eq_abs]
    exact logInt_integrand_abs_le_of_one_le ha δ ht1.le
  have hu := h01.union h1
  rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at hu
  exact hu

/-! ## The derivative in `δ` -/

theorem hasDerivAt_logInt {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    HasDerivAt (logInt a) (lapl (fun t => besselJ0 (a * t)) δ) δ := by
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hs : Set.Ioi (δ / 2) ∈ nhds δ := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable
      (fun t : ℝ => (Real.exp (-t) - Real.exp (-x * t) * besselJ0 (a * t)) / t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := fun x =>
    (measurable_logInt_integrand a x).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => Real.exp (-δ * t) * besselJ0 (a * t))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((continuous_exp_neg_mul δ).mul (continuous_besselJ0_comp a)).aestronglyMeasurable
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ x ∈ Set.Ioi (δ / 2),
      ‖Real.exp (-x * t) * besselJ0 (a * t)‖ ≤ Real.exp (-(δ / 2) * t) := by
    intro t ht x hx
    have ht0 : (0 : ℝ) < t := ht
    have hx' : δ / 2 < x := hx
    have hE := Real.exp_pos (-x * t)
    have hxt := mul_le_mul_of_nonneg_right hx'.le ht0.le
    have hE2 : Real.exp (-x * t) ≤ Real.exp (-(δ / 2) * t) :=
      Real.exp_le_exp.mpr (by linarith)
    have hJ := abs_besselJ0_comp_le ha ht0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE]
    calc Real.exp (-x * t) * |besselJ0 (a * t)| ≤ Real.exp (-x * t) * 1 :=
          mul_le_mul_of_nonneg_left hJ hE.le
      _ = Real.exp (-x * t) := mul_one _
      _ ≤ Real.exp (-(δ / 2) * t) := hE2
  have hdiff : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ x ∈ Set.Ioi (δ / 2),
      HasDerivAt
        (fun y : ℝ => (Real.exp (-t) - Real.exp (-y * t) * besselJ0 (a * t)) / t)
        (Real.exp (-x * t) * besselJ0 (a * t)) x := by
    intro t ht x _
    have ht0 : (0 : ℝ) < t := ht
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y * t))
        (Real.exp (-x * t) * (-1 * t)) x :=
      (((hasDerivAt_id' x).neg).mul_const t).exp
    have h2 := ((h1.mul_const (besselJ0 (a * t))).const_sub (Real.exp (-t))).div_const t
    have h2' : HasDerivAt
        (fun y : ℝ => (Real.exp (-t) - Real.exp (-y * t) * besselJ0 (a * t)) / t)
        (-(Real.exp (-x * t) * (-1 * t) * besselJ0 (a * t)) / t) x := h2
    refine h2'.congr_deriv ?_
    rw [div_eq_iff ht0.ne']
    ring
  have hbi : Integrable (fun t : ℝ => Real.exp (-(δ / 2) * t))
      (volume.restrict (Set.Ioi (0 : ℝ))) := exp_neg_integrableOn_Ioi 0 hδ2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun x t => (Real.exp (-t) - Real.exp (-x * t) * besselJ0 (a * t)) / t)
    (F' := fun x t => Real.exp (-x * t) * besselJ0 (a * t))
    (bound := fun t => Real.exp (-(δ / 2) * t)) hs
    (Filter.Eventually.of_forall hmeas) (integrable_logInt ha hδ) hmeas'
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound) hbi
    (ae_restrict_of_forall_mem measurableSet_Ioi hdiff)
  have h3 : HasDerivAt
      (fun x : ℝ => ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-t) - Real.exp (-x * t) * besselJ0 (a * t)) / t)
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-δ * t) * besselJ0 (a * t)) δ := key.2
  exact h3

theorem hasDerivAt_logG {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    HasDerivAt (logG a) (Real.sqrt (a * a + δ * δ))⁻¹ δ := by
  have hq0 : 0 < a * a + δ * δ := by
    have h1 := mul_nonneg ha ha
    have h2 := mul_pos hδ hδ
    linarith
  have hr : 0 < Real.sqrt (a * a + δ * δ) := Real.sqrt_pos.mpr hq0
  have hq : HasDerivAt (fun x : ℝ => a * a + x * x) (1 * δ + δ * 1) δ :=
    ((hasDerivAt_id' δ).mul (hasDerivAt_id' δ)).const_add (a * a)
  have hsq : HasDerivAt (fun x : ℝ => Real.sqrt (a * a + x * x))
      ((1 * δ + δ * 1) / (2 * Real.sqrt (a * a + δ * δ))) δ := hq.sqrt hq0.ne'
  have hsum : HasDerivAt (fun x : ℝ => x + Real.sqrt (a * a + x * x))
      (1 + (1 * δ + δ * 1) / (2 * Real.sqrt (a * a + δ * δ))) δ :=
    (hasDerivAt_id' δ).add hsq
  have hne : δ + Real.sqrt (a * a + δ * δ) ≠ 0 := (add_pos hδ hr).ne'
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x + Real.sqrt (a * a + x * x)))
      ((1 + (1 * δ + δ * 1) / (2 * Real.sqrt (a * a + δ * δ)))
        / (δ + Real.sqrt (a * a + δ * δ))) δ := hsum.log hne
  have hfun : logG a = fun x : ℝ => Real.log (x + Real.sqrt (a * a + x * x)) := rfl
  have hri : Real.sqrt (a * a + δ * δ) * (Real.sqrt (a * a + δ * δ))⁻¹ = 1 :=
    mul_inv_cancel₀ hr.ne'
  rw [hfun]
  refine hlog.congr_deriv ?_
  rw [div_eq_iff hne]
  linear_combination (-1 : ℝ) * hri

/-- `logInt a - logG a` is constant on `(0, ∞)`. -/
theorem logInt_sub_logG_const {a : ℝ} (ha : 0 ≤ a) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    logInt a y - logG a y = logInt a x - logG a x := by
  have hd : ∀ z : ℝ, 0 < z → HasDerivAt (fun w : ℝ => logInt a w - logG a w) 0 z := by
    intro z hz
    have h := (hasDerivAt_logInt ha hz).sub (hasDerivAt_logG ha hz)
    have h' : HasDerivAt (fun w : ℝ => logInt a w - logG a w)
        (lapl (fun t => besselJ0 (a * t)) z - (Real.sqrt (a * a + z * z))⁻¹) z := h
    refine h'.congr_deriv ?_
    rw [lapl_besselJ0 ha hz, sub_self]
  have hcont : ContinuousOn (fun w : ℝ => logInt a w - logG a w) (Set.Icc x y) := fun z hz =>
    (hd z (lt_of_lt_of_le hx hz.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ z ∈ Set.Ico x y,
      HasDerivWithinAt (fun w : ℝ => logInt a w - logG a w) 0 (Set.Ici z) z := fun z hz =>
    (hd z (lt_of_lt_of_le hx hz.1)).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hcont hderiv y ⟨hxy, le_rfl⟩

/-! ## The case `a = 0` -/

theorem logInt_zero_one : logInt 0 1 = 0 := by
  have h : ∀ t : ℝ, (Real.exp (-t) - Real.exp (-1 * t) * besselJ0 (0 * t)) / t = 0 := by
    intro t
    rw [zero_mul, besselJ0_zero, mul_one, neg_one_mul, sub_self, zero_div]
  have hfun : (fun t : ℝ => (Real.exp (-t) - Real.exp (-1 * t) * besselJ0 (0 * t)) / t)
      = fun _ : ℝ => (0 : ℝ) := funext h
  unfold logInt
  rw [hfun]
  simp

theorem logG_zero_one : logG 0 1 = Real.log 2 := by
  unfold logG
  norm_num

theorem logInt_zero {δ : ℝ} (hδ : 0 < δ) : logInt 0 δ = logG 0 δ - Real.log 2 := by
  have h1 : logInt 0 δ - logG 0 δ = logInt 0 1 - logG 0 1 := by
    rcases le_total 1 δ with h | h
    · exact logInt_sub_logG_const (le_refl (0 : ℝ)) one_pos h
    · exact (logInt_sub_logG_const (le_refl (0 : ℝ)) hδ h).symm
  rw [logInt_zero_one, logG_zero_one] at h1
  linarith

/-! ## Comparison of `a` with `0` at large `δ` -/

theorem abs_logInt_sub_logInt_zero_le {a : ℝ} (ha : 0 ≤ a) {y : ℝ} (hy : 0 < y) :
    |logInt a y - logInt 0 y| ≤ a / y := by
  have i1 := integrable_logInt ha hy
  have i0 := integrable_logInt (le_refl (0 : ℝ)) hy
  have hsub : logInt a y - logInt 0 y
      = ∫ t in Set.Ioi (0 : ℝ),
          ((Real.exp (-t) - Real.exp (-y * t) * besselJ0 (a * t)) / t
            - (Real.exp (-t) - Real.exp (-y * t) * besselJ0 (0 * t)) / t) := by
    unfold logInt
    rw [integral_sub i1 i0]
  have hg : Integrable (fun t : ℝ => a * (Real.exp (-y * t) * 1))
      (volume.restrict (Set.Ioi (0 : ℝ))) := Integrable.const_mul (integrable_one_lapl hy) a
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(Real.exp (-t) - Real.exp (-y * t) * besselJ0 (a * t)) / t
          - (Real.exp (-t) - Real.exp (-y * t) * besselJ0 (0 * t)) / t‖
        ≤ a * (Real.exp (-y * t) * 1) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hat : 0 ≤ a * t := mul_nonneg ha ht0.le
    have hJ1 := (abs_le.mp (abs_besselJ0_le_one hat)).2
    have h1J := one_sub_besselJ0_le hat
    have hE := Real.exp_pos (-y * t)
    have hnn : 0 ≤ Real.exp (-y * t) * (1 - besselJ0 (a * t)) :=
      mul_nonneg hE.le (by linarith)
    have e : (Real.exp (-t) - Real.exp (-y * t) * besselJ0 (a * t)) / t
        - (Real.exp (-t) - Real.exp (-y * t) * besselJ0 (0 * t)) / t
        = Real.exp (-y * t) * (1 - besselJ0 (a * t)) / t := by
      rw [zero_mul, besselJ0_zero]
      ring
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0, abs_of_nonneg hnn]
    calc Real.exp (-y * t) * (1 - besselJ0 (a * t)) ≤ Real.exp (-y * t) * (a * t) :=
          mul_le_mul_of_nonneg_left h1J hE.le
      _ = a * (Real.exp (-y * t) * 1) * t := by ring
  have h := norm_integral_le_of_norm_le hg hae
  rw [integral_const_mul, Real.norm_eq_abs] at h
  have h1 : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-y * t) * 1) = 1 / y := lapl_one hy
  have e2 : a * (1 / y) = a / y := by ring
  rw [h1, e2] at h
  rw [hsub]
  exact h

theorem logG_sub_logG_zero {a : ℝ} (ha : 0 ≤ a) {y : ℝ} (hy : 0 < y) :
    0 ≤ logG a y - logG 0 y ∧ logG a y - logG 0 y ≤ a / (2 * y) := by
  have h1 : Real.sqrt (y * y) ≤ Real.sqrt (a * a + y * y) :=
    Real.sqrt_le_sqrt (by linarith [mul_self_nonneg a])
  rw [Real.sqrt_mul_self hy.le] at h1
  have hay : 0 ≤ a * y := mul_nonneg ha hy.le
  have h2 : Real.sqrt (a * a + y * y) ≤ Real.sqrt ((y + a) * (y + a)) := by
    refine Real.sqrt_le_sqrt ?_
    have e : (y + a) * (y + a) = a * a + y * y + 2 * (a * y) := by ring
    rw [e]
    linarith
  rw [Real.sqrt_mul_self (by linarith : (0 : ℝ) ≤ y + a)] at h2
  have e0 : logG 0 y = Real.log (y + y) := by
    unfold logG
    rw [zero_mul, zero_add, Real.sqrt_mul_self hy.le]
  have eG : logG a y = Real.log (y + Real.sqrt (a * a + y * y)) := rfl
  have h2y : 0 < 2 * y := by linarith
  have hu : 0 ≤ a / (2 * y) := div_nonneg ha h2y.le
  have h1u : 0 < 1 + a / (2 * y) := by linarith
  have hmul : 2 * y * (a / (2 * y)) = a := mul_div_cancel₀ a h2y.ne'
  have e3 : y + (y + a) = (y + y) * (1 + a / (2 * y)) := by
    linear_combination (-1 : ℝ) * hmul
  have hyy : 0 < y + y := by linarith
  have h3 : Real.log (y + (y + a)) = Real.log (y + y) + Real.log (1 + a / (2 * y)) := by
    rw [e3, Real.log_mul hyy.ne' h1u.ne']
  have h4 : Real.log (1 + a / (2 * y)) ≤ a / (2 * y) := by
    have h := Real.log_le_sub_one_of_pos h1u
    linarith
  have hlogmono : Real.log (y + Real.sqrt (a * a + y * y)) ≤ Real.log (y + (y + a)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog0 : Real.log (y + y) ≤ Real.log (y + Real.sqrt (a * a + y * y)) :=
    Real.log_le_log hyy (by linarith)
  rw [eG, e0]
  constructor
  · linarith
  · linarith

/-! ## The formula -/

/-- **The logarithm formula with damping.** For `a ≥ 0` and `δ > 0`,
`∫₀^∞ (e^{-t} - e^{-δt} J₀(at)) dt/t = log (δ + √(a² + δ²)) - log 2`. -/
theorem logInt_eq {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    logInt a δ = Real.log (δ + Real.sqrt (a * a + δ * δ)) - Real.log 2 := by
  have hgoal : logInt a δ - logG a δ = -Real.log 2 := by
    refine eq_of_forall_dist_le (fun ε hε => ?_)
    rw [Real.dist_eq]
    obtain ⟨y, hy1, hδy, hKy⟩ := exists_large hδ (mul_nonneg zero_le_two ha) hε
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    have hc := logInt_sub_logG_const ha hδ hδy
    have h0 := logInt_zero hy0
    have h1 := abs_le.mp (abs_logInt_sub_logInt_zero_le ha hy0)
    have h1a := h1.1
    have h1b := h1.2
    obtain ⟨h2, h3⟩ := logG_sub_logG_zero ha hy0
    have e : logInt a δ - logG a δ - -Real.log 2
        = (logInt a y - logInt 0 y) - (logG a y - logG 0 y) := by linarith
    have e1 : a / y = a * (1 / y) := by ring
    have e2 : a / (2 * y) = a * (1 / y) / 2 := by ring
    have hnn : 0 ≤ a * (1 / y) := mul_nonneg ha (one_div_pos.mpr hy0).le
    have e3 : 2 * a * (1 / y) = 2 * (a * (1 / y)) := by ring
    rw [e1] at h1a h1b
    rw [e2] at h3
    rw [e3] at hKy
    rw [e, abs_le]
    constructor
    · linarith
    · linarith
  have eG : logG a δ = Real.log (δ + Real.sqrt (a * a + δ * δ)) := rfl
  rw [eG] at hgoal
  linarith

end Tower.RV6
