import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselK

/-!
# `K₀` near zero

`expE x = ∫₀^∞ exp(-x e^u) du` is the exponential integral `E₁(x)` for `x > 0`, in a form that
needs no substitution.

* `expE_sub_besselK0_nonneg`, `expE_sub_besselK0_le`: `0 ≤ E(t/2) - K₀(t) ≤ t/2` for `t > 0`.
* `hasDerivAt_expE`: `E'(x) = -e^{-x}/x`.
* `eulerW = E(1) - ∫₀¹ (1 - e^{-w}) dw/w` and `expE_add_log`: `E(x) + log x - eulerW = ∫₀^x (1 - e^{-w}) dw/w`,
  which lies in `[0, x]`.
* **`abs_besselK0_add_log_le`**: `|K₀(t) + log(t/2) - eulerW| ≤ t/2` for `t > 0`.
* `expE_one`: `E(1) = ∫₁^∞ e^{-w} dw/w`.

`eulerW` is minus Euler's constant; that is neither used nor proved.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `E(x) = ∫₀^∞ exp(-x e^u) du`. -/
noncomputable def expE (x : ℝ) : ℝ := ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(x * Real.exp u))

theorem continuous_expE_integrand (x : ℝ) :
    Continuous fun u : ℝ => Real.exp (-(x * Real.exp u)) := by
  have h1 : Continuous fun u : ℝ => x * Real.exp u := continuous_const.mul Real.continuous_exp
  have h2 : Continuous fun u : ℝ => -(x * Real.exp u) := continuous_neg.comp h1
  exact Real.continuous_exp.comp h2

theorem expE_integrand_le {x : ℝ} (hx : 0 < x) {u : ℝ} (hu : 0 < u) :
    Real.exp (-(x * Real.exp u)) ≤ Real.exp (-x) * Real.exp (-x * u) := by
  rw [← Real.exp_add]
  have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
  have h2 : x * (u + 1) ≤ x * Real.exp u := mul_le_mul_of_nonneg_left h1 hx.le
  have h3 : -(x * Real.exp u) ≤ -x + -x * u := by linarith
  exact Real.exp_le_exp.mpr h3

theorem integrable_expE {x : ℝ} (hx : 0 < x) :
    Integrable (fun u : ℝ => Real.exp (-(x * Real.exp u)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hb0 : Integrable (fun u : ℝ => Real.exp (-x * u)) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    exp_neg_integrableOn_Ioi 0 hx
  have hb : Integrable (fun u : ℝ => Real.exp (-x) * Real.exp (-x * u))
      (volume.restrict (Set.Ioi (0 : ℝ))) := Integrable.const_mul hb0 (Real.exp (-x))
  refine Integrable.mono' hb (continuous_expE_integrand x).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_))
  have hu0 : (0 : ℝ) < u := hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact expE_integrand_le hx hu0

/-! ## Comparison with `K₀` -/

theorem exp_neg_mul_cosh (t u : ℝ) :
    Real.exp (-t * Real.cosh u)
      = Real.exp (-(t / 2 * Real.exp u)) * Real.exp (-(t / 2 * Real.exp (-u))) := by
  have e : -t * Real.cosh u = -(t / 2 * Real.exp u) + -(t / 2 * Real.exp (-u)) := by
    rw [Real.cosh_eq]
    ring
  rw [e, Real.exp_add]

theorem expE_sub_integrand_bounds {t : ℝ} (ht : 0 < t) (u : ℝ) :
    0 ≤ Real.exp (-(t / 2 * Real.exp u)) - Real.exp (-t * Real.cosh u) ∧
      Real.exp (-(t / 2 * Real.exp u)) - Real.exp (-t * Real.cosh u)
        ≤ t / 2 * Real.exp (-u) := by
  have hA0 := Real.exp_pos (-(t / 2 * Real.exp u))
  have hy : 0 ≤ t / 2 * Real.exp (-u) := mul_nonneg (half_pos ht).le (Real.exp_pos _).le
  have hy' : 0 ≤ t / 2 * Real.exp u := mul_nonneg (half_pos ht).le (Real.exp_pos _).le
  have hA1 : Real.exp (-(t / 2 * Real.exp u)) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (by linarith : -(t / 2 * Real.exp u) ≤ 0)
    rw [Real.exp_zero] at h
    exact h
  have hB1 : Real.exp (-(t / 2 * Real.exp (-u))) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (by linarith : -(t / 2 * Real.exp (-u)) ≤ 0)
    rw [Real.exp_zero] at h
    exact h
  have hB2 : -(t / 2 * Real.exp (-u)) + 1 ≤ Real.exp (-(t / 2 * Real.exp (-u))) :=
    Real.add_one_le_exp _
  have hs0 : 0 ≤ 1 - Real.exp (-(t / 2 * Real.exp (-u))) := by linarith
  have hs1 : 1 - Real.exp (-(t / 2 * Real.exp (-u))) ≤ t / 2 * Real.exp (-u) := by linarith
  have e : Real.exp (-(t / 2 * Real.exp u)) - Real.exp (-t * Real.cosh u)
      = Real.exp (-(t / 2 * Real.exp u)) * (1 - Real.exp (-(t / 2 * Real.exp (-u)))) := by
    rw [exp_neg_mul_cosh]
    ring
  rw [e]
  constructor
  · exact mul_nonneg hA0.le hs0
  · calc Real.exp (-(t / 2 * Real.exp u)) * (1 - Real.exp (-(t / 2 * Real.exp (-u))))
        ≤ 1 * (t / 2 * Real.exp (-u)) := mul_le_mul hA1 hs1 hs0 zero_le_one
      _ = t / 2 * Real.exp (-u) := one_mul _

theorem integrable_K0_integrand {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ℝ => Real.exp (-t * Real.cosh u))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h02 : (0 : ℕ) ≤ 2 := by norm_num
  have h := integrable_kf ht 0 h02
  have hfun : (fun u : ℝ => kf t 0 u) = fun u : ℝ => Real.exp (-t * Real.cosh u) := by
    funext u
    show Real.exp (-t * Real.cosh u) * Real.cosh u ^ 0 = Real.exp (-t * Real.cosh u)
    rw [pow_zero, mul_one]
  rw [hfun] at h
  exact h

theorem expE_sub_besselK0 {t : ℝ} (ht : 0 < t) :
    expE (t / 2) - besselK0 t
      = ∫ u in Set.Ioi (0 : ℝ),
          (Real.exp (-(t / 2 * Real.exp u)) - Real.exp (-t * Real.cosh u)) := by
  have h1 := integrable_expE (half_pos ht)
  have h2 := integrable_K0_integrand ht
  have h3 : ∫ u in Set.Ioi (0 : ℝ),
        (Real.exp (-(t / 2 * Real.exp u)) - Real.exp (-t * Real.cosh u))
      = (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(t / 2 * Real.exp u)))
        - ∫ u in Set.Ioi (0 : ℝ), Real.exp (-t * Real.cosh u) := integral_sub h1 h2
  rw [h3]
  rfl

/-- `0 ≤ E(t/2) - K₀(t)`. -/
theorem expE_sub_besselK0_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ expE (t / 2) - besselK0 t := by
  rw [expE_sub_besselK0 ht]
  have hnn : (0 : ℝ → ℝ) ≤ fun u : ℝ =>
      Real.exp (-(t / 2 * Real.exp u)) - Real.exp (-t * Real.cosh u) :=
    fun u => (expE_sub_integrand_bounds ht u).1
  exact integral_nonneg hnn

/-- `E(t/2) - K₀(t) ≤ t/2`. -/
theorem expE_sub_besselK0_le {t : ℝ} (ht : 0 < t) : expE (t / 2) - besselK0 t ≤ t / 2 := by
  rw [expE_sub_besselK0 ht]
  have h1 := integrable_expE (half_pos ht)
  have h2 := integrable_K0_integrand ht
  have hi : Integrable
      (fun u : ℝ => Real.exp (-(t / 2 * Real.exp u)) - Real.exp (-t * Real.cosh u))
      (volume.restrict (Set.Ioi (0 : ℝ))) := h1.sub h2
  have hb : Integrable (fun u : ℝ => t / 2 * Real.exp (-u))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) (t / 2)
  have hle : (fun u : ℝ => Real.exp (-(t / 2 * Real.exp u)) - Real.exp (-t * Real.cosh u))
      ≤ fun u : ℝ => t / 2 * Real.exp (-u) := fun u => (expE_sub_integrand_bounds ht u).2
  have hmono : ∫ u in Set.Ioi (0 : ℝ),
        (Real.exp (-(t / 2 * Real.exp u)) - Real.exp (-t * Real.cosh u))
      ≤ ∫ u in Set.Ioi (0 : ℝ), t / 2 * Real.exp (-u) := integral_mono hi hb hle
  have e : ∫ u in Set.Ioi (0 : ℝ), t / 2 * Real.exp (-u) = t / 2 := by
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  linarith

/-! ## The derivative of `E` -/

theorem exp_mul_exp_neg_le {y : ℝ} (hy : 0 < y) (u : ℝ) :
    Real.exp u * Real.exp (-(y * Real.exp u)) ≤ 2 / y ^ 2 * Real.exp (-u) := by
  have hz : 0 < y * Real.exp u := mul_pos hy (Real.exp_pos u)
  have hq := Real.quadratic_le_exp_of_nonneg hz.le
  have hq' : (y * Real.exp u) ^ 2 / 2 ≤ Real.exp (y * Real.exp u) := by linarith
  have hX := Real.exp_pos (-(y * Real.exp u))
  have hI := Real.exp_pos (-u)
  have h1 : Real.exp (y * Real.exp u) * Real.exp (-(y * Real.exp u)) = 1 := by
    rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_pos _).ne']
  have h3 : Real.exp u * Real.exp (-u) = 1 := by
    rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_pos _).ne']
  have h2 : (y * Real.exp u) ^ 2 / 2 * Real.exp (-(y * Real.exp u))
      ≤ Real.exp (y * Real.exp u) * Real.exp (-(y * Real.exp u)) :=
    mul_le_mul_of_nonneg_right hq' hX.le
  rw [h1] at h2
  have h4 : (y * Real.exp u) ^ 2 / 2 * Real.exp (-(y * Real.exp u)) * (2 * Real.exp (-u))
      ≤ 1 * (2 * Real.exp (-u)) :=
    mul_le_mul_of_nonneg_right h2 (mul_nonneg zero_le_two hI.le)
  have e : (y * Real.exp u) ^ 2 / 2 * Real.exp (-(y * Real.exp u)) * (2 * Real.exp (-u))
      = Real.exp u * Real.exp (-(y * Real.exp u)) * y ^ 2
        * (Real.exp u * Real.exp (-u)) := by ring
  rw [e, h3, mul_one, one_mul] at h4
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hy 2)]
  exact h4

theorem integral_exp_mul_exp_neg {x : ℝ} (hx : 0 < x) :
    ∫ u in Set.Ioi (0 : ℝ), Real.exp u * Real.exp (-(x * Real.exp u)) = Real.exp (-x) / x := by
  have hderiv : ∀ u ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun v : ℝ => -(Real.exp (-(x * Real.exp v)) / x))
        (Real.exp u * Real.exp (-(x * Real.exp u))) u := by
    intro u _
    have h1 : HasDerivAt (fun v : ℝ => x * Real.exp v) (x * Real.exp u) u :=
      (Real.hasDerivAt_exp u).const_mul x
    have h2 : HasDerivAt (fun v : ℝ => -(x * Real.exp v)) (-(x * Real.exp u)) u := h1.neg
    have h3 : HasDerivAt (fun v : ℝ => Real.exp (-(x * Real.exp v)))
        (Real.exp (-(x * Real.exp u)) * (-(x * Real.exp u))) u := h2.exp
    have h4 : HasDerivAt (fun v : ℝ => Real.exp (-(x * Real.exp v)) / x)
        (Real.exp (-(x * Real.exp u)) * (-(x * Real.exp u)) / x) u := h3.div_const x
    have h5 : HasDerivAt (fun v : ℝ => -(Real.exp (-(x * Real.exp v)) / x))
        (-(Real.exp (-(x * Real.exp u)) * (-(x * Real.exp u)) / x)) u := h4.neg
    refine h5.congr_deriv ?_
    have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
    rw [div_eq_mul_inv]
    linear_combination (Real.exp u * Real.exp (-(x * Real.exp u))) * hxx
  have hcont : Continuous fun u : ℝ => Real.exp u * Real.exp (-(x * Real.exp u)) :=
    Real.continuous_exp.mul (continuous_expE_integrand x)
  have hint : IntegrableOn (fun u : ℝ => Real.exp u * Real.exp (-(x * Real.exp u)))
      (Set.Ioi (0 : ℝ)) := by
    have hb : Integrable (fun u : ℝ => 2 / x ^ 2 * Real.exp (-u))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      Integrable.const_mul (integrableOn_exp_neg_Ioi 0) (2 / x ^ 2)
    show Integrable (fun u : ℝ => Real.exp u * Real.exp (-(x * Real.exp u)))
      (volume.restrict (Set.Ioi (0 : ℝ)))
    refine Integrable.mono' hb hcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun u => ?_))
    have hnn : 0 ≤ Real.exp u * Real.exp (-(x * Real.exp u)) :=
      mul_nonneg (Real.exp_pos u).le (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact exp_mul_exp_neg_le hx u
  have hlim : Filter.Tendsto (fun v : ℝ => -(Real.exp (-(x * Real.exp v)) / x))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun v : ℝ => Real.exp (-(x * v))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((Filter.tendsto_const_mul_atTop_of_pos hx).mpr Filter.tendsto_id)
    have hg := h0.const_mul (Real.exp (-x) * x⁻¹)
    rw [mul_zero] at hg
    refine squeeze_zero_norm' ((Filter.eventually_gt_atTop (0 : ℝ)).mono (fun v hv => ?_)) hg
    show ‖-(Real.exp (-(x * Real.exp v)) / x)‖ ≤ Real.exp (-x) * x⁻¹ * Real.exp (-(x * v))
    have hb := expE_integrand_le hx hv
    have e : -x * v = -(x * v) := by ring
    rw [e] at hb
    have hnn : 0 ≤ Real.exp (-(x * Real.exp v)) / x := div_nonneg (Real.exp_pos _).le hx.le
    have h1 : Real.exp (-(x * Real.exp v)) * x⁻¹
        ≤ Real.exp (-x) * Real.exp (-(x * v)) * x⁻¹ :=
      mul_le_mul_of_nonneg_right hb (inv_pos.mpr hx).le
    have e2 : Real.exp (-x) * x⁻¹ * Real.exp (-(x * v))
        = Real.exp (-x) * Real.exp (-(x * v)) * x⁻¹ := by ring
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hnn, e2, div_eq_mul_inv]
    exact h1
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  simp only [Real.exp_zero, mul_one] at hftc
  rw [hftc]
  ring

/-- `E'(x) = -e^{-x}/x`. -/
theorem hasDerivAt_expE {x : ℝ} (hx : 0 < x) :
    HasDerivAt expE (-(Real.exp (-x) / x)) x := by
  have hx2 : 0 < x / 2 := half_pos hx
  have hs : Set.Ioi (x / 2) ∈ nhds x := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable (fun u : ℝ => Real.exp (-(y * Real.exp u)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun y => (continuous_expE_integrand y).aestronglyMeasurable
  have hF' : Continuous fun u : ℝ => -(Real.exp u * Real.exp (-(x * Real.exp u))) :=
    continuous_neg.comp (Real.continuous_exp.mul (continuous_expE_integrand x))
  have hbound : ∀ u ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (x / 2),
      ‖-(Real.exp u * Real.exp (-(y * Real.exp u)))‖ ≤ 2 / (x / 2) ^ 2 * Real.exp (-u) := by
    intro u _ y hy
    have hy' : x / 2 < y := hy
    have hE := Real.exp_pos u
    have h1 : x / 2 * Real.exp u ≤ y * Real.exp u := mul_le_mul_of_nonneg_right hy'.le hE.le
    have h1' : -(y * Real.exp u) ≤ -(x / 2 * Real.exp u) := by linarith
    have hmono : Real.exp (-(y * Real.exp u)) ≤ Real.exp (-(x / 2 * Real.exp u)) :=
      Real.exp_le_exp.mpr h1'
    have h2 := exp_mul_exp_neg_le hx2 u
    have hnn : 0 ≤ Real.exp u * Real.exp (-(y * Real.exp u)) :=
      mul_nonneg hE.le (Real.exp_pos _).le
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hnn]
    calc Real.exp u * Real.exp (-(y * Real.exp u))
        ≤ Real.exp u * Real.exp (-(x / 2 * Real.exp u)) :=
          mul_le_mul_of_nonneg_left hmono hE.le
      _ ≤ 2 / (x / 2) ^ 2 * Real.exp (-u) := h2
  have hbi : Integrable (fun u : ℝ => 2 / (x / 2) ^ 2 * Real.exp (-u))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) (2 / (x / 2) ^ 2)
  have hdiff : ∀ u ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (x / 2),
      HasDerivAt (fun z : ℝ => Real.exp (-(z * Real.exp u)))
        (-(Real.exp u * Real.exp (-(y * Real.exp u)))) y := by
    intro u _ y _
    have h1 : HasDerivAt (fun z : ℝ => z * Real.exp u) (1 * Real.exp u) y :=
      (hasDerivAt_id' y).mul_const (Real.exp u)
    have h2 : HasDerivAt (fun z : ℝ => -(z * Real.exp u)) (-(1 * Real.exp u)) y := h1.neg
    have h3 : HasDerivAt (fun z : ℝ => Real.exp (-(z * Real.exp u)))
        (Real.exp (-(y * Real.exp u)) * (-(1 * Real.exp u))) y := h2.exp
    exact h3.congr_deriv (by ring)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun y u => Real.exp (-(y * Real.exp u)))
    (F' := fun y u => -(Real.exp u * Real.exp (-(y * Real.exp u))))
    (bound := fun u => 2 / (x / 2) ^ 2 * Real.exp (-u)) hs
    (Filter.Eventually.of_forall hmeas) (integrable_expE hx) hF'.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound) hbi
    (ae_restrict_of_forall_mem measurableSet_Ioi hdiff)
  have h3 : HasDerivAt (fun y : ℝ => ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(y * Real.exp u)))
      (∫ u in Set.Ioi (0 : ℝ), -(Real.exp u * Real.exp (-(x * Real.exp u)))) x := key.2
  rw [integral_neg, integral_exp_mul_exp_neg hx] at h3
  exact h3

/-! ## The constant and the expansion of `E` at zero -/

/-- `ψ(w) = (1 - e^{-w})/w`. -/
noncomputable def psiE (w : ℝ) : ℝ := (1 - Real.exp (-w)) / w

theorem psiE_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ psiE w := by
  have h := Real.exp_le_exp.mpr (by linarith : -w ≤ 0)
  rw [Real.exp_zero] at h
  have h1 : 0 ≤ 1 - Real.exp (-w) := by linarith
  show 0 ≤ (1 - Real.exp (-w)) / w
  exact div_nonneg h1 hw

theorem psiE_le_one {w : ℝ} (hw : 0 ≤ w) : psiE w ≤ 1 := by
  have h2 : -w + 1 ≤ Real.exp (-w) := Real.add_one_le_exp (-w)
  have h1 : 1 - Real.exp (-w) ≤ w := by linarith
  show (1 - Real.exp (-w)) / w ≤ 1
  exact div_le_one_of_le₀ h1 hw

theorem measurable_psiE : Measurable psiE := by
  have h1 : Continuous fun w : ℝ => 1 - Real.exp (-w) :=
    continuous_const.sub (Real.continuous_exp.comp continuous_neg)
  have h2 : Measurable fun w : ℝ => (1 - Real.exp (-w)) / w := h1.measurable.div measurable_id
  exact h2

theorem integrableOn_psiE {a b : ℝ} (ha : 0 ≤ a) : IntegrableOn psiE (Set.Ioc a b) := by
  refine IntegrableOn.of_bound measure_Ioc_lt_top measurable_psiE.aestronglyMeasurable 1
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun w hw => ?_))
  have hw0 : 0 ≤ w := le_trans ha hw.1.le
  rw [Real.norm_eq_abs, abs_of_nonneg (psiE_nonneg hw0)]
  exact psiE_le_one hw0

theorem intervalIntegrable_psiE {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable psiE volume a b :=
  ⟨integrableOn_psiE ha, integrableOn_psiE hb⟩

/-- `eulerW = E(1) - ∫₀¹ (1 - e^{-w}) dw/w`. -/
noncomputable def eulerW : ℝ := expE 1 - ∫ w in (0 : ℝ)..1, psiE w

theorem hasDerivAt_expE_add_log {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => expE y + Real.log y) (psiE x) x := by
  have h1 := hasDerivAt_expE hx
  have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h3 : HasDerivAt (fun y : ℝ => expE y + Real.log y) (-(Real.exp (-x) / x) + x⁻¹) x :=
    h1.add h2
  refine h3.congr_deriv ?_
  show -(Real.exp (-x) / x) + x⁻¹ = (1 - Real.exp (-x)) / x
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- `E(x) + log x - eulerW = ∫₀^x (1 - e^{-w}) dw/w` for `x > 0`. -/
theorem expE_add_log {x : ℝ} (hx : 0 < x) :
    expE x + Real.log x - eulerW = ∫ w in (0 : ℝ)..x, psiE w := by
  have hderiv : ∀ w ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (fun y : ℝ => expE y + Real.log y) (psiE w) w := by
    intro w hw
    have hw0 : 0 < w := by
      rcases Set.mem_uIcc.mp hw with h | h
      · linarith [h.1]
      · linarith [h.1]
    exact hasDerivAt_expE_add_log hw0
  have hftc : ∫ w in (1 : ℝ)..x, psiE w
      = (expE x + Real.log x) - (expE 1 + Real.log 1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (intervalIntegrable_psiE zero_le_one hx.le)
  have hsplit : (∫ w in (0 : ℝ)..x, psiE w) - ∫ w in (0 : ℝ)..1, psiE w
      = ∫ w in (1 : ℝ)..x, psiE w :=
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_psiE (le_refl (0 : ℝ)) hx.le)
      (intervalIntegrable_psiE (le_refl (0 : ℝ)) zero_le_one)
  rw [Real.log_one, add_zero] at hftc
  unfold eulerW
  linarith

theorem integral_psiE_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ ∫ w in (0 : ℝ)..x, psiE w :=
  intervalIntegral.integral_nonneg hx (fun w hw => psiE_nonneg hw.1)

theorem integral_psiE_le {x : ℝ} (hx : 0 ≤ x) : ∫ w in (0 : ℝ)..x, psiE w ≤ x := by
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 x :=
    continuous_const.intervalIntegrable 0 x
  have h : ∫ w in (0 : ℝ)..x, psiE w ≤ ∫ _w in (0 : ℝ)..x, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hx (intervalIntegrable_psiE (le_refl (0 : ℝ)) hx) hone
      (fun w hw => psiE_le_one hw.1)
  have e : ∫ _w in (0 : ℝ)..x, (1 : ℝ) = x := by
    rw [intervalIntegral.integral_const]
    simp
  linarith

/-! ## `K₀` at zero -/

/-- **`K₀(t) = -log(t/2) + eulerW + O(t)`**: `|K₀(t) + log(t/2) - eulerW| ≤ t/2` for `t > 0`. -/
theorem abs_besselK0_add_log_le {t : ℝ} (ht : 0 < t) :
    |besselK0 t + Real.log (t / 2) - eulerW| ≤ t / 2 := by
  have ht2 : 0 < t / 2 := half_pos ht
  have h1 := expE_sub_besselK0_nonneg ht
  have h2 := expE_sub_besselK0_le ht
  have h3 := expE_add_log ht2
  have h4 := integral_psiE_nonneg ht2.le
  have h5 := integral_psiE_le ht2.le
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-! ## The constant in the other form -/

/-- `E(1) = ∫₁^∞ e^{-w} dw/w`. -/
theorem expE_one : expE 1 = ∫ w in Set.Ioi (1 : ℝ), Real.exp (-w) / w := by
  have h : (∫ u in Set.Ioi (0 : ℝ), Real.exp u • (Real.exp (-Real.exp u) / Real.exp u))
      = ∫ y in Set.Ioi (Real.exp 0), Real.exp (-y) / y :=
    integral_comp_exp_Ioi (fun w : ℝ => Real.exp (-w) / w) 0
  rw [Real.exp_zero] at h
  have hfun : (fun u : ℝ => Real.exp (-(1 * Real.exp u)))
      = fun u : ℝ => Real.exp u • (Real.exp (-Real.exp u) / Real.exp u) := by
    funext u
    rw [one_mul, smul_eq_mul, mul_div_cancel₀ _ (Real.exp_pos u).ne']
  unfold expE
  rw [hfun]
  exact h

end Tower.RV6
