import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselJ
import Tower.RV6.BesselInt

/-!
# The characteristic function of the six-step walk on the cube

With `X(τ) = 1 + e(τ₁) + ⋯ + e(τ₅)`, `e(u) = exp(2πiu)`:

* `integral_cos_shift`, `integral_sin_shift`: `∫₀¹ cos(x cos 2π(u + θ)) du = ∫₀¹ cos(x cos 2πu) du`
  and `∫₀¹ sin(x cos 2π(u + θ)) du = 0`.
* `besselJ0_mul_norm`: `J₀(t|z|) = ∫₀¹ cos(t (Re z cos 2πθ - Im z sin 2πθ)) dθ` for `t ≥ 0`.
* `cubeX_rot`: `Re X cos 2πθ - Im X sin 2πθ = cos 2πθ + ∑ cos 2π(τ_j + θ)`.
* `cube_restrict`, `integral_cube_prod`: Lebesgue measure on the cube `[0,1]⁵` is the product of
  the measures on `[0,1]`; the integral of a product of functions of the coordinates.
* `integral_cube_cos`: `∫_{[0,1]⁵} cos(t (cos 2πθ + ∑ cos 2π(τ_j + θ))) dτ = cos(t cos 2πθ) J₀(t)⁵`.
* **`integral_cube_besselJ0`**: `∫_{[0,1]⁵} J₀(t |X(τ)|) dτ = J₀(t)⁶` for `t ≥ 0`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## Shifts over a period -/

/-- The integral of a `1`-periodic function over `(0, 1]` is invariant under shifts. -/
theorem integral_Ioc_shift {g : ℝ → ℝ} (hg : Function.Periodic g 1) (θ : ℝ) :
    ∫ u in Set.Ioc (0 : ℝ) 1, g (u + θ) = ∫ u in Set.Ioc (0 : ℝ) 1, g u := by
  have h1 : ∫ u in (0 : ℝ)..1, g (u + θ) = ∫ x in (0 + θ)..(1 + θ), g x :=
    intervalIntegral.integral_comp_add_right g θ
  have h2 : ∫ x in θ..(θ + 1), g x = ∫ x in (0 : ℝ)..(0 + 1), g x :=
    hg.intervalIntegral_add_eq θ 0
  have e1 : (0 : ℝ) + θ = θ := zero_add θ
  have e2 : (1 : ℝ) + θ = θ + 1 := add_comm 1 θ
  have e3 : (0 : ℝ) + 1 = 1 := zero_add 1
  rw [e1, e2] at h1
  rw [e3] at h2
  rw [← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1), h1, h2]

theorem periodic_cos_comp (x : ℝ) :
    Function.Periodic (fun u : ℝ => Real.cos (x * Real.cos (2 * π * u))) 1 := by
  intro u
  show Real.cos (x * Real.cos (2 * π * (u + 1))) = Real.cos (x * Real.cos (2 * π * u))
  rw [mul_add, mul_one, Real.cos_add_two_pi]

theorem periodic_sin_comp (x : ℝ) :
    Function.Periodic (fun u : ℝ => Real.sin (x * Real.cos (2 * π * u))) 1 := by
  intro u
  show Real.sin (x * Real.cos (2 * π * (u + 1))) = Real.sin (x * Real.cos (2 * π * u))
  rw [mul_add, mul_one, Real.cos_add_two_pi]

/-- `∫₀¹ cos(x cos 2π(u + θ)) du = ∫₀¹ cos(x cos 2πu) du`. -/
theorem integral_cos_shift (x θ : ℝ) :
    ∫ u in Set.Ioc (0 : ℝ) 1, Real.cos (x * Real.cos (2 * π * (u + θ))) = besG x := by
  have h : ∫ u in Set.Ioc (0 : ℝ) 1, Real.cos (x * Real.cos (2 * π * (u + θ)))
      = ∫ u in Set.Ioc (0 : ℝ) 1, Real.cos (x * Real.cos (2 * π * u)) :=
    integral_Ioc_shift (periodic_cos_comp x) θ
  exact h

/-- `∫₀¹ sin(x cos 2πu) du = 0`: the integrand changes sign under `u ↦ u + 1/2`. -/
theorem integral_sin_cos_zero (x : ℝ) :
    ∫ u in Set.Ioc (0 : ℝ) 1, Real.sin (x * Real.cos (2 * π * u)) = 0 := by
  have h : ∫ u in Set.Ioc (0 : ℝ) 1, Real.sin (x * Real.cos (2 * π * (u + 1 / 2)))
      = ∫ u in Set.Ioc (0 : ℝ) 1, Real.sin (x * Real.cos (2 * π * u)) :=
    integral_Ioc_shift (periodic_sin_comp x) (1 / 2)
  have hneg : (fun u : ℝ => Real.sin (x * Real.cos (2 * π * (u + 1 / 2))))
      = fun u : ℝ => -Real.sin (x * Real.cos (2 * π * u)) := by
    funext u
    have e : 2 * π * (u + 1 / 2) = 2 * π * u + π := by ring
    rw [e, Real.cos_add_pi, mul_neg, Real.sin_neg]
  rw [hneg, integral_neg] at h
  linarith

/-- `∫₀¹ sin(x cos 2π(u + θ)) du = 0`. -/
theorem integral_sin_shift (x θ : ℝ) :
    ∫ u in Set.Ioc (0 : ℝ) 1, Real.sin (x * Real.cos (2 * π * (u + θ))) = 0 := by
  have h : ∫ u in Set.Ioc (0 : ℝ) 1, Real.sin (x * Real.cos (2 * π * (u + θ)))
      = ∫ u in Set.Ioc (0 : ℝ) 1, Real.sin (x * Real.cos (2 * π * u)) :=
    integral_Ioc_shift (periodic_sin_comp x) θ
  rw [h]
  exact integral_sin_cos_zero x

/-! ## The rotation formula -/

/-- `J₀(t|z|) = ∫₀¹ cos(t (Re z cos 2πθ - Im z sin 2πθ)) dθ` for `t ≥ 0`. -/
theorem besselJ0_mul_norm {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    besselJ0 (t * ‖z‖) = ∫ θ in Set.Ioc (0 : ℝ) 1,
      Real.cos (t * (z.re * Real.cos (2 * π * θ) - z.im * Real.sin (2 * π * θ))) := by
  have hre : ‖z‖ * Real.cos (Complex.arg z) = z.re := Complex.norm_mul_cos_arg z
  have him : ‖z‖ * Real.sin (Complex.arg z) = z.im := Complex.norm_mul_sin_arg z
  have hpi : (2 * π) * (2 * π)⁻¹ = 1 := mul_inv_cancel₀ (mul_pos two_pos Real.pi_pos).ne'
  have hfun : (fun θ : ℝ =>
      Real.cos (t * (z.re * Real.cos (2 * π * θ) - z.im * Real.sin (2 * π * θ))))
      = fun θ : ℝ =>
        Real.cos (t * ‖z‖ * Real.cos (2 * π * (θ + Complex.arg z * (2 * π)⁻¹))) := by
    funext θ
    have e : 2 * π * (θ + Complex.arg z * (2 * π)⁻¹) = 2 * π * θ + Complex.arg z := by
      linear_combination Complex.arg z * hpi
    have key : t * (z.re * Real.cos (2 * π * θ) - z.im * Real.sin (2 * π * θ))
        = t * ‖z‖ * Real.cos (2 * π * (θ + Complex.arg z * (2 * π)⁻¹)) := by
      rw [e, Real.cos_add]
      linear_combination (-(t * Real.cos (2 * π * θ))) * hre + (t * Real.sin (2 * π * θ)) * him
    rw [key]
  rw [hfun, integral_cos_shift (t * ‖z‖) (Complex.arg z * (2 * π)⁻¹)]
  exact besselJ0_eq_besG (mul_nonneg ht (norm_nonneg z))

/-! ## The sum of unit vectors -/

/-- `X(τ) = 1 + e(τ₁) + ⋯ + e(τ₅)`, the argument of the norm in `mu6`. -/
noncomputable def cubeX (τ : Fin 5 → ℝ) : ℂ :=
  (1 : ℂ) + ∑ j, Complex.exp (2 * π * Complex.I * (τ j))

theorem mu6_eq_cubeX : mu6 = ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, Real.log ‖cubeX τ‖ := rfl

theorem cexp_two_pi_I (x : ℝ) :
    Complex.exp (2 * π * Complex.I * (x : ℂ)) = Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I) := by
  have e : 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e]

theorem cubeX_re (τ : Fin 5 → ℝ) : (cubeX τ).re = 1 + ∑ j, Real.cos (2 * π * τ j) := by
  have h : ∀ j : Fin 5, (Complex.exp (2 * π * Complex.I * (τ j))).re = Real.cos (2 * π * τ j) := by
    intro j
    rw [cexp_two_pi_I, Complex.exp_ofReal_mul_I_re]
  unfold cubeX
  rw [Complex.add_re, Complex.one_re, Complex.re_sum]
  simp only [h]

theorem cubeX_im (τ : Fin 5 → ℝ) : (cubeX τ).im = ∑ j, Real.sin (2 * π * τ j) := by
  have h : ∀ j : Fin 5, (Complex.exp (2 * π * Complex.I * (τ j))).im = Real.sin (2 * π * τ j) := by
    intro j
    rw [cexp_two_pi_I, Complex.exp_ofReal_mul_I_im]
  unfold cubeX
  rw [Complex.add_im, Complex.one_im, Complex.im_sum, zero_add]
  simp only [h]

/-- `Re X cos 2πθ - Im X sin 2πθ = cos 2πθ + ∑ cos 2π(τ_j + θ)`. -/
theorem cubeX_rot (τ : Fin 5 → ℝ) (θ : ℝ) :
    (cubeX τ).re * Real.cos (2 * π * θ) - (cubeX τ).im * Real.sin (2 * π * θ)
      = Real.cos (2 * π * θ) + ∑ j, Real.cos (2 * π * (τ j + θ)) := by
  have h : ∀ j : Fin 5, Real.cos (2 * π * (τ j + θ))
      = Real.cos (2 * π * τ j) * Real.cos (2 * π * θ)
        - Real.sin (2 * π * τ j) * Real.sin (2 * π * θ) := by
    intro j
    rw [mul_add, Real.cos_add]
  have hsum : ∑ j, Real.cos (2 * π * (τ j + θ))
      = (∑ j, Real.cos (2 * π * τ j)) * Real.cos (2 * π * θ)
        - (∑ j, Real.sin (2 * π * τ j)) * Real.sin (2 * π * θ) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => h j)
  rw [cubeX_re, cubeX_im, hsum]
  ring

/-! ## Unit complex exponentials -/

/-- `e^{iy}`. -/
noncomputable def cexpR (y : ℝ) : ℂ := Complex.exp ((y : ℂ) * Complex.I)

theorem cexpR_re (y : ℝ) : (cexpR y).re = Real.cos y := Complex.exp_ofReal_mul_I_re y

theorem cexpR_im (y : ℝ) : (cexpR y).im = Real.sin y := Complex.exp_ofReal_mul_I_im y

theorem cexpR_add (x y : ℝ) : cexpR (x + y) = cexpR x * cexpR y := by
  unfold cexpR
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

theorem cexpR_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    cexpR (∑ j ∈ s, x j) = ∏ j ∈ s, cexpR (x j) := by
  unfold cexpR
  rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

theorem continuous_cexpR : Continuous cexpR := by
  have h : Continuous fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  exact h

theorem continuous_cexpR_shift (t θ : ℝ) :
    Continuous fun u : ℝ => cexpR (t * Real.cos (2 * π * (u + θ))) := by
  have h1 : Continuous fun u : ℝ => u + θ := continuous_id'.add continuous_const
  have h2 : Continuous fun u : ℝ => 2 * π * (u + θ) := continuous_const.mul h1
  have h3 : Continuous fun u : ℝ => Real.cos (2 * π * (u + θ)) := Real.continuous_cos.comp h2
  have h4 : Continuous fun u : ℝ => t * Real.cos (2 * π * (u + θ)) := continuous_const.mul h3
  exact continuous_cexpR.comp h4

/-- `∫₀¹ exp(i t cos 2π(u + θ)) du = J₀(t)` for `t ≥ 0`. -/
theorem integral_cexpR_shift {t : ℝ} (ht : 0 ≤ t) (θ : ℝ) :
    ∫ u in Set.Icc (0 : ℝ) 1, cexpR (t * Real.cos (2 * π * (u + θ)))
      = ((besselJ0 t : ℝ) : ℂ) := by
  have hg1 : Integrable (fun u : ℝ => cexpR (t * Real.cos (2 * π * (u + θ))))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := (continuous_cexpR_shift t θ).integrableOn_Icc
  have hre : (∫ u in Set.Icc (0 : ℝ) 1, cexpR (t * Real.cos (2 * π * (u + θ)))).re
      = ∫ u in Set.Icc (0 : ℝ) 1, (cexpR (t * Real.cos (2 * π * (u + θ)))).re :=
    (Complex.reCLM.integral_comp_comm hg1).symm
  have him : (∫ u in Set.Icc (0 : ℝ) 1, cexpR (t * Real.cos (2 * π * (u + θ)))).im
      = ∫ u in Set.Icc (0 : ℝ) 1, (cexpR (t * Real.cos (2 * π * (u + θ)))).im :=
    (Complex.imCLM.integral_comp_comm hg1).symm
  have hre2 : (fun u : ℝ => (cexpR (t * Real.cos (2 * π * (u + θ)))).re)
      = fun u : ℝ => Real.cos (t * Real.cos (2 * π * (u + θ))) := by
    funext u
    exact cexpR_re _
  have him2 : (fun u : ℝ => (cexpR (t * Real.cos (2 * π * (u + θ)))).im)
      = fun u : ℝ => Real.sin (t * Real.cos (2 * π * (u + θ))) := by
    funext u
    exact cexpR_im _
  apply Complex.ext
  · rw [hre, hre2, integral_Icc_eq_integral_Ioc, integral_cos_shift t θ, Complex.ofReal_re]
    exact (besselJ0_eq_besG ht).symm
  · rw [him, him2, integral_Icc_eq_integral_Ioc, integral_sin_shift t θ, Complex.ofReal_im]

/-! ## Lebesgue measure on the cube -/

/-- The restriction of Lebesgue measure to the cube `[0,1]⁵` is the product of the restrictions
to `[0,1]`. -/
theorem cube_restrict :
    (volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)
      = Measure.pi (fun _ : Fin 5 => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := by
  have hset : Set.Icc (0 : Fin 5 → ℝ) 1 = Set.univ.pi (fun _ : Fin 5 => Set.Icc (0 : ℝ) 1) :=
    (Set.pi_univ_Icc (0 : Fin 5 → ℝ) 1).symm
  show (Measure.pi (fun _ : Fin 5 => (volume : Measure ℝ))).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)
      = Measure.pi (fun _ : Fin 5 => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))
  rw [hset]
  exact Measure.restrict_pi_pi (fun _ : Fin 5 => (volume : Measure ℝ))
    (fun _ : Fin 5 => Set.Icc (0 : ℝ) 1)

instance cube_isFiniteMeasure :
    IsFiniteMeasure ((volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := by
  rw [cube_restrict]
  infer_instance

/-- The integral over the cube of a product of one function of each coordinate. -/
theorem integral_cube_prod (f : ℝ → ℂ) :
    ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, ∏ j : Fin 5, f (τ j)
      = (∫ u in Set.Icc (0 : ℝ) 1, f u) ^ 5 := by
  rw [cube_restrict]
  have h := integral_fintype_prod_eq_pow (ι := Fin 5) (𝕜 := ℂ) f
    (μ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))
  rw [Fintype.card_fin] at h
  exact h

/-! ## The integral over the cube at a fixed angle -/

/-- `∫_{[0,1]⁵} cos(t (cos 2πθ + ∑ cos 2π(τ_j + θ))) dτ = cos(t cos 2πθ) J₀(t)⁵`. -/
theorem integral_cube_cos {t : ℝ} (ht : 0 ≤ t) (θ : ℝ) :
    ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1,
        Real.cos (t * (Real.cos (2 * π * θ) + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ))))
      = Real.cos (t * Real.cos (2 * π * θ)) * besselJ0 t ^ 5 := by
  have hg1 : Integrable (fun u : ℝ => cexpR (t * Real.cos (2 * π * (u + θ))))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := (continuous_cexpR_shift t θ).integrableOn_Icc
  have hprod : Integrable
      (fun τ : Fin 5 → ℝ => ∏ j : Fin 5, cexpR (t * Real.cos (2 * π * (τ j + θ))))
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := by
    rw [cube_restrict]
    exact Integrable.fintype_prod
      (f := fun _ : Fin 5 => fun u : ℝ => cexpR (t * Real.cos (2 * π * (u + θ))))
      (fun _ => hg1)
  have hF : Integrable (fun τ : Fin 5 → ℝ => cexpR (t * Real.cos (2 * π * θ))
      * ∏ j : Fin 5, cexpR (t * Real.cos (2 * π * (τ j + θ))))
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := hprod.const_mul _
  have hpt : ∀ τ : Fin 5 → ℝ,
      Real.cos (t * (Real.cos (2 * π * θ) + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ))))
        = (cexpR (t * Real.cos (2 * π * θ))
            * ∏ j : Fin 5, cexpR (t * Real.cos (2 * π * (τ j + θ)))).re := by
    intro τ
    rw [← cexpR_sum, ← cexpR_add, cexpR_re, mul_add, Finset.mul_sum]
  have hfun : (fun τ : Fin 5 → ℝ =>
      Real.cos (t * (Real.cos (2 * π * θ) + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ)))))
      = fun τ : Fin 5 → ℝ => (cexpR (t * Real.cos (2 * π * θ))
          * ∏ j : Fin 5, cexpR (t * Real.cos (2 * π * (τ j + θ)))).re := funext hpt
  have hre : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, (cexpR (t * Real.cos (2 * π * θ))
        * ∏ j : Fin 5, cexpR (t * Real.cos (2 * π * (τ j + θ)))).re
      = (∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cexpR (t * Real.cos (2 * π * θ))
        * ∏ j : Fin 5, cexpR (t * Real.cos (2 * π * (τ j + θ)))).re :=
    Complex.reCLM.integral_comp_comm hF
  have hpr : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1,
        ∏ j : Fin 5, cexpR (t * Real.cos (2 * π * (τ j + θ)))
      = (∫ u in Set.Icc (0 : ℝ) 1, cexpR (t * Real.cos (2 * π * (u + θ)))) ^ 5 :=
    integral_cube_prod (fun u : ℝ => cexpR (t * Real.cos (2 * π * (u + θ))))
  rw [hfun, hre, integral_const_mul, hpr, integral_cexpR_shift ht θ, ← Complex.ofReal_pow,
    Complex.re_mul_ofReal, cexpR_re]

/-! ## The characteristic function -/

theorem continuous_cube_cos (t : ℝ) :
    Continuous fun p : (Fin 5 → ℝ) × ℝ =>
      Real.cos (t * (Real.cos (2 * π * p.2)
        + ∑ j : Fin 5, Real.cos (2 * π * (p.1 j + p.2)))) := by
  have h2 : Continuous fun p : (Fin 5 → ℝ) × ℝ => Real.cos (2 * π * p.2) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_snd)
  have h3 : ∀ j : Fin 5,
      Continuous fun p : (Fin 5 → ℝ) × ℝ => Real.cos (2 * π * (p.1 j + p.2)) := by
    intro j
    have ha : Continuous fun p : (Fin 5 → ℝ) × ℝ => p.1 j :=
      (continuous_apply j).comp continuous_fst
    have hb : Continuous fun p : (Fin 5 → ℝ) × ℝ => p.1 j + p.2 := ha.add continuous_snd
    have hc : Continuous fun p : (Fin 5 → ℝ) × ℝ => 2 * π * (p.1 j + p.2) :=
      continuous_const.mul hb
    exact Real.continuous_cos.comp hc
  have h4 : Continuous fun p : (Fin 5 → ℝ) × ℝ =>
      ∑ j : Fin 5, Real.cos (2 * π * (p.1 j + p.2)) :=
    continuous_finsetSum _ (fun j _ => h3 j)
  have h5 : Continuous fun p : (Fin 5 → ℝ) × ℝ =>
      Real.cos (2 * π * p.2) + ∑ j : Fin 5, Real.cos (2 * π * (p.1 j + p.2)) := h2.add h4
  have h6 : Continuous fun p : (Fin 5 → ℝ) × ℝ =>
      t * (Real.cos (2 * π * p.2) + ∑ j : Fin 5, Real.cos (2 * π * (p.1 j + p.2))) :=
    continuous_const.mul h5
  exact Real.continuous_cos.comp h6

/-- **The characteristic function of the walk.** `∫_{[0,1]⁵} J₀(t |X(τ)|) dτ = J₀(t)⁶`. -/
theorem integral_cube_besselJ0 {t : ℝ} (ht : 0 ≤ t) :
    ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, besselJ0 (t * ‖cubeX τ‖) = besselJ0 t ^ 6 := by
  have h1 : ∀ τ : Fin 5 → ℝ, besselJ0 (t * ‖cubeX τ‖)
      = ∫ θ in Set.Ioc (0 : ℝ) 1,
          Real.cos (t * (Real.cos (2 * π * θ)
            + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ)))) := by
    intro τ
    rw [besselJ0_mul_norm ht (cubeX τ)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
    show Real.cos (t * ((cubeX τ).re * Real.cos (2 * π * θ)
        - (cubeX τ).im * Real.sin (2 * π * θ)))
      = Real.cos (t * (Real.cos (2 * π * θ) + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ))))
    rw [cubeX_rot]
  have hfun : (fun τ : Fin 5 → ℝ => besselJ0 (t * ‖cubeX τ‖))
      = fun τ : Fin 5 → ℝ => ∫ θ in Set.Ioc (0 : ℝ) 1,
          Real.cos (t * (Real.cos (2 * π * θ)
            + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ)))) := funext h1
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (τ : Fin 5 → ℝ) (θ : ℝ) =>
      Real.cos (t * (Real.cos (2 * π * θ) + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ)))))
      (((volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) :=
    (continuous_cube_cos t).aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun (τ : Fin 5 → ℝ) (θ : ℝ) =>
      Real.cos (t * (Real.cos (2 * π * θ) + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ)))))
      (((volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine Integrable.of_bound hmeas 1 (Filter.Eventually.of_forall (fun p => ?_))
    show ‖Real.cos (t * (Real.cos (2 * π * p.2)
      + ∑ j : Fin 5, Real.cos (2 * π * (p.1 j + p.2))))‖ ≤ 1
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hsw : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, ∫ θ in Set.Ioc (0 : ℝ) 1,
        Real.cos (t * (Real.cos (2 * π * θ) + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ))))
      = ∫ θ in Set.Ioc (0 : ℝ) 1, ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1,
        Real.cos (t * (Real.cos (2 * π * θ) + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ)))) :=
    integral_integral_swap hint
  have hfun2 : (fun θ : ℝ => ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1,
        Real.cos (t * (Real.cos (2 * π * θ) + ∑ j : Fin 5, Real.cos (2 * π * (τ j + θ)))))
      = fun θ : ℝ => Real.cos (t * Real.cos (2 * π * θ)) * besselJ0 t ^ 5 :=
    funext (fun θ => integral_cube_cos ht θ)
  have hG : ∫ θ in Set.Ioc (0 : ℝ) 1, Real.cos (t * Real.cos (2 * π * θ)) = besselJ0 t :=
    (besselJ0_eq_besG ht).symm
  rw [hfun, hsw, hfun2, integral_mul_const, hG]
  ring

/-- The same with the factors of the argument in the other order. -/
theorem integral_cube_besselJ0' {t : ℝ} (ht : 0 ≤ t) :
    ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, besselJ0 (‖cubeX τ‖ * t) = besselJ0 t ^ 6 := by
  have hfun : (fun τ : Fin 5 → ℝ => besselJ0 (‖cubeX τ‖ * t))
      = fun τ : Fin 5 → ℝ => besselJ0 (t * ‖cubeX τ‖) := by
    funext τ
    rw [mul_comm ‖cubeX τ‖ t]
  rw [hfun]
  exact integral_cube_besselJ0 ht

end Tower.RV6
