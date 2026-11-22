import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselJ
import Tower.RV6.Laplace
import Tower.RV6.LogInt
import Tower.RV6.CharFun

/-!
# The exchange over the cube

For `δ > 0`, with `X(τ) = 1 + e(τ₁) + ⋯ + e(τ₅)`:

`∫_{[0,1]⁵} log (δ + √(|X(τ)|² + δ²)) dτ = log 2 + ∫₀^∞ (e^{-t} - e^{-δt} J₀(t)⁶) dt/t`
(`integral_cube_logG`).

The damped logarithm formula `logInt_eq` at `a = |X(τ)|` is integrated over the cube; the two
integrals are exchanged (`integrable_cubeLog`: the integrand on `cube × (0, ∞)` is bounded by
`(7 + δ) e^{1-t} + e^{-t} + e^{-δt}`), and the characteristic function of the walk
(`integral_cube_besselJ0'`) evaluates the inner integral.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## The sum of unit vectors: continuity and size -/

theorem continuous_cubeX : Continuous cubeX := by
  have h : ∀ j : Fin 5,
      Continuous fun τ : Fin 5 → ℝ => Complex.exp (2 * π * Complex.I * (τ j)) := by
    intro j
    have h1 : Continuous fun τ : Fin 5 → ℝ => ((τ j : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_apply j)
    have h2 : Continuous fun τ : Fin 5 → ℝ => 2 * (π : ℂ) * Complex.I * ((τ j : ℝ) : ℂ) :=
      continuous_const.mul h1
    exact Complex.continuous_exp.comp h2
  have hs : Continuous fun τ : Fin 5 → ℝ =>
      ∑ j : Fin 5, Complex.exp (2 * π * Complex.I * (τ j)) :=
    continuous_finsetSum _ (fun j _ => h j)
  have h1 : Continuous fun τ : Fin 5 → ℝ =>
      (1 : ℂ) + ∑ j : Fin 5, Complex.exp (2 * π * Complex.I * (τ j)) := continuous_const.add hs
  exact h1

theorem continuous_norm_cubeX : Continuous fun τ : Fin 5 → ℝ => ‖cubeX τ‖ :=
  continuous_norm.comp continuous_cubeX

/-- `|X(τ)| ≤ 6`. -/
theorem norm_cubeX_le (τ : Fin 5 → ℝ) : ‖cubeX τ‖ ≤ 6 := by
  have h : ∀ j : Fin 5, ‖Complex.exp (2 * π * Complex.I * (τ j))‖ = 1 := by
    intro j
    rw [cexp_two_pi_I, Complex.norm_exp_ofReal_mul_I]
  have hs : ‖∑ j : Fin 5, Complex.exp (2 * π * Complex.I * (τ j))‖
      ≤ ∑ j : Fin 5, ‖Complex.exp (2 * π * Complex.I * (τ j))‖ := norm_sum_le _ _
  have hs2 : ∑ j : Fin 5, ‖Complex.exp (2 * π * Complex.I * (τ j))‖ = 5 := by
    rw [Fin.sum_univ_five, h, h, h, h, h]
    norm_num
  have h1 : ‖(1 : ℂ) + ∑ j : Fin 5, Complex.exp (2 * π * Complex.I * (τ j))‖
      ≤ ‖(1 : ℂ)‖ + ‖∑ j : Fin 5, Complex.exp (2 * π * Complex.I * (τ j))‖ := norm_add_le _ _
  have h2 : ‖(1 : ℂ)‖ = 1 := norm_one
  have h3 : ‖cubeX τ‖ = ‖(1 : ℂ) + ∑ j : Fin 5, Complex.exp (2 * π * Complex.I * (τ j))‖ := rfl
  linarith

/-! ## Constants over the cube -/

/-- The cube has volume `1`. -/
theorem integral_cube_one : ∫ _τ in Set.Icc (0 : Fin 5 → ℝ) 1, (1 : ℝ) = 1 := by
  have h := integral_cube_besselJ0 (le_refl (0 : ℝ))
  simp only [zero_mul, besselJ0_zero, one_pow] at h
  exact h

/-! ## The integrand on the product -/

theorem continuous_cubeLog_num (δ : ℝ) :
    Continuous fun p : (Fin 5 → ℝ) × ℝ =>
      Real.exp (-p.2) - Real.exp (-δ * p.2) * besselJ0 (‖cubeX p.1‖ * p.2) := by
  have h1 : Continuous fun p : (Fin 5 → ℝ) × ℝ => Real.exp (-p.2) :=
    Real.continuous_exp.comp (continuous_neg.comp continuous_snd)
  have h2 : Continuous fun p : (Fin 5 → ℝ) × ℝ => Real.exp (-δ * p.2) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_snd)
  have h3 : Continuous fun p : (Fin 5 → ℝ) × ℝ => ‖cubeX p.1‖ :=
    continuous_norm_cubeX.comp continuous_fst
  have h4 : Continuous fun p : (Fin 5 → ℝ) × ℝ => ‖cubeX p.1‖ * p.2 := h3.mul continuous_snd
  have h5 : Continuous fun p : (Fin 5 → ℝ) × ℝ => besselJ0 (‖cubeX p.1‖ * p.2) :=
    continuous_besselJ0.comp h4
  exact h1.sub (h2.mul h5)

theorem measurable_cubeLog (δ : ℝ) :
    Measurable fun p : (Fin 5 → ℝ) × ℝ =>
      (Real.exp (-p.2) - Real.exp (-δ * p.2) * besselJ0 (‖cubeX p.1‖ * p.2)) / p.2 := by
  exact (continuous_cubeLog_num δ).measurable.div measurable_snd

/-- A bound for the integrand, uniform in `τ`. -/
theorem cubeLog_integrand_abs_le {δ : ℝ} (hδ : 0 < δ) (τ : Fin 5 → ℝ) {t : ℝ} (ht : 0 < t) :
    |(Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (‖cubeX τ‖ * t)) / t|
      ≤ (7 + δ) * (Real.exp 1 * Real.exp (-t)) + (Real.exp (-t) + Real.exp (-δ * t)) := by
  have ha : 0 ≤ ‖cubeX τ‖ := norm_nonneg _
  have ha6 := norm_cubeX_le τ
  have h1 := Real.exp_pos (-t)
  have h2 := Real.exp_pos (-δ * t)
  rcases le_total t 1 with h | h
  · have hb := logInt_integrand_abs_le ha hδ ht
    have he : 1 ≤ Real.exp 1 * Real.exp (-t) := by
      rw [← Real.exp_add]
      have h0 : Real.exp 0 ≤ Real.exp (1 + -t) := Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_zero] at h0
      exact h0
    have hp : (7 + δ) * 1 ≤ (7 + δ) * (Real.exp 1 * Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left he (by linarith)
    linarith
  · have hb := logInt_integrand_abs_le_of_one_le ha δ h
    have hp : 0 ≤ (7 + δ) * (Real.exp 1 * Real.exp (-t)) :=
      mul_nonneg (by linarith) (mul_nonneg (Real.exp_pos 1).le h1.le)
    linarith

theorem integrable_cubeLog_bound {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ =>
      (7 + δ) * (Real.exp 1 * Real.exp (-t)) + (Real.exp (-t) + Real.exp (-δ * t)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hb1 : Integrable (fun t : ℝ => Real.exp (-t)) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_exp_neg_Ioi 0
  have hb2 : Integrable (fun t : ℝ => Real.exp (-δ * t))
      (volume.restrict (Set.Ioi (0 : ℝ))) := exp_neg_integrableOn_Ioi 0 hδ
  have hb3 : Integrable (fun t : ℝ => Real.exp 1 * Real.exp (-t))
      (volume.restrict (Set.Ioi (0 : ℝ))) := Integrable.const_mul hb1 (Real.exp 1)
  have hb4 : Integrable (fun t : ℝ => (7 + δ) * (Real.exp 1 * Real.exp (-t)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := Integrable.const_mul hb3 (7 + δ)
  have hb5 : Integrable (fun t : ℝ => Real.exp (-t) + Real.exp (-δ * t))
      (volume.restrict (Set.Ioi (0 : ℝ))) := hb1.add hb2
  exact hb4.add hb5

/-- The integrand of the exchange is integrable on `cube × (0, ∞)`. -/
theorem integrable_cubeLog {δ : ℝ} (hδ : 0 < δ) :
    Integrable (Function.uncurry fun (τ : Fin 5 → ℝ) (t : ℝ) =>
      (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (‖cubeX τ‖ * t)) / t)
      (((volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun (τ : Fin 5 → ℝ) (t : ℝ) =>
      (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (‖cubeX τ‖ * t)) / t)
      (((volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :=
    (measurable_cubeLog δ).aestronglyMeasurable
  have hB : Integrable (fun p : (Fin 5 → ℝ) × ℝ =>
      (7 + δ) * (Real.exp 1 * Real.exp (-p.2)) + (Real.exp (-p.2) + Real.exp (-δ * p.2)))
      (((volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :=
    (integrable_cubeLog_bound hδ).comp_snd _
  refine Integrable.mono' hB hm ?_
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Ioi) (fun p hp => ?_)
  have ht : (0 : ℝ) < p.2 := hp.2
  show ‖(Real.exp (-p.2) - Real.exp (-δ * p.2) * besselJ0 (‖cubeX p.1‖ * p.2)) / p.2‖
    ≤ (7 + δ) * (Real.exp 1 * Real.exp (-p.2)) + (Real.exp (-p.2) + Real.exp (-δ * p.2))
  rw [Real.norm_eq_abs]
  exact cubeLog_integrand_abs_le hδ p.1 ht

/-! ## The exchange -/

/-- `∫_{[0,1]⁵} logInt |X(τ)| δ dτ = ∫₀^∞ (e^{-t} - e^{-δt} J₀(t)⁶) dt/t`. -/
theorem integral_cube_logInt {δ : ℝ} (hδ : 0 < δ) :
    ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, logInt ‖cubeX τ‖ δ
      = ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 t ^ 6) / t := by
  have hsw : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (‖cubeX τ‖ * t)) / t
      = ∫ t in Set.Ioi (0 : ℝ), ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1,
        (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (‖cubeX τ‖ * t)) / t :=
    integral_integral_swap (integrable_cubeLog hδ)
  have hL : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, logInt ‖cubeX τ‖ δ
      = ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (‖cubeX τ‖ * t)) / t := rfl
  rw [hL, hsw]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  show ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1,
        (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (‖cubeX τ‖ * t)) / t
      = (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 t ^ 6) / t
  have hJc : Continuous fun τ : Fin 5 → ℝ => besselJ0 (‖cubeX τ‖ * t) :=
    continuous_besselJ0.comp (continuous_norm_cubeX.mul continuous_const)
  have hJi : Integrable (fun τ : Fin 5 → ℝ => besselJ0 (‖cubeX τ‖ * t))
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := hJc.integrableOn_Icc
  have hfun : (fun τ : Fin 5 → ℝ =>
      (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 (‖cubeX τ‖ * t)) / t)
      = fun τ : Fin 5 → ℝ => Real.exp (-t) / t * 1
          - Real.exp (-δ * t) / t * besselJ0 (‖cubeX τ‖ * t) := by
    funext τ
    ring
  have hi1 : Integrable (fun _ : Fin 5 → ℝ => Real.exp (-t) / t * 1)
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := integrable_const _
  have hi2 : Integrable
      (fun τ : Fin 5 → ℝ => Real.exp (-δ * t) / t * besselJ0 (‖cubeX τ‖ * t))
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := Integrable.const_mul hJi _
  rw [hfun, integral_sub hi1 hi2, integral_const_mul, integral_const_mul, integral_cube_one,
    integral_cube_besselJ0' ht0.le]
  ring

/-- **The exchange.**
`∫_{[0,1]⁵} log (δ + √(|X|² + δ²)) dτ = log 2 + ∫₀^∞ (e^{-t} - e^{-δt} J₀(t)⁶) dt/t`. -/
theorem integral_cube_logG {δ : ℝ} (hδ : 0 < δ) :
    ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1,
        Real.log (δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ))
      = Real.log 2 + ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 t ^ 6) / t := by
  have hfun : (fun τ : Fin 5 → ℝ =>
      Real.log (δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ)))
      = fun τ : Fin 5 → ℝ => logInt ‖cubeX τ‖ δ + Real.log 2 * 1 := by
    funext τ
    rw [logInt_eq (norm_nonneg (cubeX τ)) hδ]
    ring
  have hi1 : Integrable (fun τ : Fin 5 → ℝ => logInt ‖cubeX τ‖ δ)
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) :=
    (integrable_cubeLog hδ).integral_prod_left
  have hi2 : Integrable (fun _ : Fin 5 → ℝ => Real.log 2 * 1)
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := integrable_const _
  rw [hfun, integral_add hi1 hi2, integral_const_mul, integral_cube_one,
    integral_cube_logInt hδ]
  ring

end Tower.RV6
