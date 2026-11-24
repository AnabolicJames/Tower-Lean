import Mathlib
import Tower.RV6.CharFun

/-!
# RungBP, step 2: the product formula of `J₀`

`J₀(a) J₀(b) = ∫₀¹ J₀(|a + b e^{2πiθ}|) dθ` for `a, b ≥ 0` (`besselJ0_mul_besselJ0`), from the rotation formula
`besselJ0_mul_norm`, a swap of the two angular integrals, the shift `θ ↦ θ + φ` and `∫₀¹ sin(b cos 2πθ) dθ = 0`.
-/

namespace Tower.RV6

open Real MeasureTheory

theorem add_cexpR_re (a b y : ℝ) : ((a : ℂ) + b * cexpR y).re = a + b * Real.cos y := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, cexpR_re]

theorem add_cexpR_im (a b y : ℝ) : ((a : ℂ) + b * cexpR y).im = b * Real.sin y := by
  rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, cexpR_im, zero_add]

/-- `|a + b e^{iy}|² = a² + b² + 2ab cos y`. -/
theorem norm_add_cexpR_sq (a b y : ℝ) :
    ‖(a : ℂ) + b * cexpR y‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * Real.cos y := by
  rw [Complex.sq_norm, Complex.normSq_apply, add_cexpR_re, add_cexpR_im]
  have h := Real.sin_sq_add_cos_sq y
  linear_combination b ^ 2 * h

/-- `J₀(|a + b e^{2πiθ}|) = ∫₀¹ cos(a cos 2πφ + b cos 2π(φ + θ)) dφ`. -/
theorem besselJ0_norm_add (a b θ : ℝ) :
    besselJ0 ‖(a : ℂ) + b * cexpR (2 * π * θ)‖ = ∫ φ in Set.Ioc (0 : ℝ) 1,
      Real.cos (a * Real.cos (2 * π * φ) + b * Real.cos (2 * π * (φ + θ))) := by
  have h := besselJ0_mul_norm (t := 1) zero_le_one ((a : ℂ) + b * cexpR (2 * π * θ))
  rw [one_mul] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioc (fun φ _ => ?_)
  show Real.cos (1 * (((a : ℂ) + b * cexpR (2 * π * θ)).re * Real.cos (2 * π * φ)
      - ((a : ℂ) + b * cexpR (2 * π * θ)).im * Real.sin (2 * π * φ)))
    = Real.cos (a * Real.cos (2 * π * φ) + b * Real.cos (2 * π * (φ + θ)))
  rw [add_cexpR_re, add_cexpR_im]
  congr 1
  rw [mul_add, Real.cos_add]
  ring

/-- `∫₀¹ cos(A + b cos 2π(θ + φ)) dθ = cos A · J₀(b)`-integral, with `A = a cos 2πφ`. -/
theorem integral_cos_add_shift (a b φ : ℝ) :
    ∫ θ in Set.Ioc (0 : ℝ) 1,
      Real.cos (a * Real.cos (2 * π * φ) + b * Real.cos (2 * π * (φ + θ)))
      = Real.cos (a * Real.cos (2 * π * φ)) * besG b := by
  have e : (fun θ : ℝ => Real.cos (a * Real.cos (2 * π * φ) + b * Real.cos (2 * π * (φ + θ))))
      = fun θ : ℝ => Real.cos (a * Real.cos (2 * π * φ)) * Real.cos (b * Real.cos (2 * π * (θ + φ)))
        - Real.sin (a * Real.cos (2 * π * φ)) * Real.sin (b * Real.cos (2 * π * (θ + φ))) := by
    funext θ
    rw [add_comm φ θ, Real.cos_add]
  have c1 : Continuous fun θ : ℝ => Real.cos (b * Real.cos (2 * π * (θ + φ))) := by fun_prop
  have c2 : Continuous fun θ : ℝ => Real.sin (b * Real.cos (2 * π * (θ + φ))) := by fun_prop
  have i1 : IntegrableOn (fun θ : ℝ => Real.cos (a * Real.cos (2 * π * φ))
      * Real.cos (b * Real.cos (2 * π * (θ + φ)))) (Set.Ioc (0 : ℝ) 1) :=
    (continuous_const.mul c1).integrableOn_Ioc
  have i2 : IntegrableOn (fun θ : ℝ => Real.sin (a * Real.cos (2 * π * φ))
      * Real.sin (b * Real.cos (2 * π * (θ + φ)))) (Set.Ioc (0 : ℝ) 1) :=
    (continuous_const.mul c2).integrableOn_Ioc
  rw [e, integral_sub i1 i2, integral_const_mul, integral_const_mul, integral_cos_shift b φ,
    integral_sin_shift b φ, mul_zero, sub_zero]

/-- **The product formula**: `J₀(a) J₀(b) = ∫₀¹ J₀(|a + b e^{2πiθ}|) dθ` for `a, b ≥ 0`. -/
theorem besselJ0_mul_besselJ0 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    besselJ0 a * besselJ0 b
      = ∫ θ in Set.Ioc (0 : ℝ) 1, besselJ0 ‖(a : ℂ) + b * cexpR (2 * π * θ)‖ := by
  have hfun : (fun θ : ℝ => besselJ0 ‖(a : ℂ) + b * cexpR (2 * π * θ)‖)
      = fun θ : ℝ => ∫ φ in Set.Ioc (0 : ℝ) 1,
          Real.cos (a * Real.cos (2 * π * φ) + b * Real.cos (2 * π * (φ + θ))) :=
    funext (fun θ => besselJ0_norm_add a b θ)
  have hcont : Continuous fun p : ℝ × ℝ =>
      Real.cos (a * Real.cos (2 * π * p.2) + b * Real.cos (2 * π * (p.2 + p.1))) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun (θ : ℝ) (φ : ℝ) =>
      Real.cos (a * Real.cos (2 * π * φ) + b * Real.cos (2 * π * (φ + θ))))
      (((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun p => ?_))
    show ‖Real.cos (a * Real.cos (2 * π * p.2) + b * Real.cos (2 * π * (p.2 + p.1)))‖ ≤ 1
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hsw : ∫ θ in Set.Ioc (0 : ℝ) 1, ∫ φ in Set.Ioc (0 : ℝ) 1,
        Real.cos (a * Real.cos (2 * π * φ) + b * Real.cos (2 * π * (φ + θ)))
      = ∫ φ in Set.Ioc (0 : ℝ) 1, ∫ θ in Set.Ioc (0 : ℝ) 1,
        Real.cos (a * Real.cos (2 * π * φ) + b * Real.cos (2 * π * (φ + θ))) :=
    integral_integral_swap hint
  have hfun2 : (fun φ : ℝ => ∫ θ in Set.Ioc (0 : ℝ) 1,
      Real.cos (a * Real.cos (2 * π * φ) + b * Real.cos (2 * π * (φ + θ))))
      = fun φ : ℝ => Real.cos (a * Real.cos (2 * π * φ)) * besG b :=
    funext (fun φ => integral_cos_add_shift a b φ)
  have hG : ∫ φ in Set.Ioc (0 : ℝ) 1, Real.cos (a * Real.cos (2 * π * φ)) = besG a := rfl
  rw [hfun, hsw, hfun2, integral_mul_const, hG, besselJ0_eq_besG ha, besselJ0_eq_besG hb]

end Tower.RV6
