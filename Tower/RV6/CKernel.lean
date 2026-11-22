import Mathlib
import Tower.RV6.Defs

/-!
# Complex kernels for the rotation of the contour, I: `J₀` on `ℂ`

Sub-rung A2R needs `J₀` and `H₀⁽¹⁾ = J₀ + iY₀` at complex arguments.  This file has the first
kernel and a wrapper for differentiation under the integral sign.

* `hasDerivAt_integral_cexp_mul`: for `g` real and continuous, `w ↦ ∫ exp(w g(a)) dμ(a)` has
  derivative `∫ g(a) exp(w₀ g(a)) dμ(a)` at `w₀`, given an integrable bound for
  `‖g(a) exp(w g(a))‖` on a neighbourhood of `w₀`.
* `kerA z = ∫₀^{π/2} exp(i z sin t) dt`: entire (`differentiable_kerA`), `‖kerA z‖ ≤ e^{|Im z|} π/2`.
* `cJ0 z = (kerA z + kerA (-z))/π = (2/π) ∫₀^{π/2} cos(z sin t) dt` (`cJ0_eq_integral`): entire
  (`differentiable_cJ0`), **`‖cJ0 z‖ ≤ e^{|Im z|}`** (`norm_cJ0_le`).

That `cJ0` is `J₀` on the real axis and `I₀` on the imaginary axis is in `CJSeries.lean`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## Differentiation under the integral sign for `exp(w g)` -/

/-- For `g` real and continuous: `w ↦ ∫ exp(w g(a)) dμ(a)` has derivative
`∫ g(a) exp(w₀ g(a)) dμ(a)` at `w₀`, if `‖g(a) exp(w g(a))‖ ≤ bound a` for `w` near `w₀`, with
`bound` integrable. -/
theorem hasDerivAt_integral_cexp_mul {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    {w₀ : ℂ} {s : Set ℂ} (hs : s ∈ nhds w₀) {bound : ℝ → ℝ}
    (hint : Integrable (fun a : ℝ => Complex.exp (w₀ * (g a : ℂ))) μ)
    (hbound : ∀ a : ℝ, ∀ w ∈ s, ‖(g a : ℂ) * Complex.exp (w * (g a : ℂ))‖ ≤ bound a)
    (hbi : Integrable bound μ) :
    HasDerivAt (fun w : ℂ => ∫ a, Complex.exp (w * (g a : ℂ)) ∂μ)
      (∫ a, (g a : ℂ) * Complex.exp (w₀ * (g a : ℂ)) ∂μ) w₀ := by
  have hgc : Continuous (fun a : ℝ => (g a : ℂ)) := Complex.continuous_ofReal.comp hg
  have hcont : ∀ w : ℂ, Continuous (fun a : ℝ => Complex.exp (w * (g a : ℂ))) := by
    intro w
    have h1 : Continuous (fun a : ℝ => w * (g a : ℂ)) := continuous_const.mul hgc
    exact Complex.continuous_exp.comp h1
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (fun a : ℝ => Complex.exp (w * (g a : ℂ))) μ :=
    fun w => (hcont w).aestronglyMeasurable
  have hc' : Continuous (fun a : ℝ => (g a : ℂ) * Complex.exp (w₀ * (g a : ℂ))) :=
    hgc.mul (hcont w₀)
  have hdiff : ∀ a : ℝ, ∀ w ∈ s,
      HasDerivAt (fun w : ℂ => Complex.exp (w * (g a : ℂ)))
        ((g a : ℂ) * Complex.exp (w * (g a : ℂ))) w := by
    intro a w _
    have h1 : HasDerivAt (fun w : ℂ => w * (g a : ℂ)) (1 * (g a : ℂ)) w :=
      (hasDerivAt_id' w).mul_const (g a : ℂ)
    have h2 : HasDerivAt (fun w : ℂ => Complex.exp (w * (g a : ℂ)))
        (Complex.exp (w * (g a : ℂ)) * (1 * (g a : ℂ))) w := h1.cexp
    exact h2.congr_deriv (by ring)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun (w : ℂ) (a : ℝ) => Complex.exp (w * (g a : ℂ)))
    (F' := fun (w : ℂ) (a : ℝ) => (g a : ℂ) * Complex.exp (w * (g a : ℂ)))
    (bound := bound) hs
    (Filter.Eventually.of_forall hmeas) hint hc'.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound) hbi
    (Filter.Eventually.of_forall hdiff)
  exact key.2

/-! ## The kernel `kerA` -/

/-- `∫₀^{π/2} exp(i z sin t) dt`. -/
noncomputable def kerA (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..(π / 2), Complex.exp (Complex.I * z * (Real.sin t : ℂ))

theorem continuous_cexp_mul_sin (w : ℂ) :
    Continuous (fun t : ℝ => Complex.exp (w * (Real.sin t : ℂ))) := by
  have h0 : Continuous (fun t : ℝ => (Real.sin t : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_sin
  have h1 : Continuous (fun t : ℝ => w * (Real.sin t : ℂ)) := continuous_const.mul h0
  exact Complex.continuous_exp.comp h1

/-- `kerA` is entire. -/
theorem differentiable_kerA : Differentiable ℂ kerA := by
  intro z
  have hint : Integrable (fun a : ℝ => Complex.exp (Complex.I * z * (Real.sin a : ℂ)))
      (volume.restrict (Set.Ioc (0 : ℝ) (π / 2))) :=
    (continuous_cexp_mul_sin (Complex.I * z)).integrableOn_Ioc
  have hbi : Integrable (fun _ : ℝ => Real.exp (‖Complex.I * z‖ + 1))
      (volume.restrict (Set.Ioc (0 : ℝ) (π / 2))) :=
    (continuous_const : Continuous fun _ : ℝ => Real.exp (‖Complex.I * z‖ + 1)).integrableOn_Ioc
  have hbound : ∀ a : ℝ, ∀ w ∈ Metric.ball (Complex.I * z) 1,
      ‖(Real.sin a : ℂ) * Complex.exp (w * (Real.sin a : ℂ))‖
        ≤ Real.exp (‖Complex.I * z‖ + 1) := by
    intro a w hw
    have hw1 : ‖w - Complex.I * z‖ < 1 := by
      have h := Metric.mem_ball.mp hw
      rw [dist_eq_norm] at h
      exact h
    have hw2 : ‖w‖ ≤ ‖Complex.I * z‖ + 1 := by
      have h := norm_sub_norm_le w (Complex.I * z)
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, Complex.re_mul_ofReal]
    have h1 : |Real.sin a| ≤ 1 := Real.abs_sin_le_one a
    have h3 : w.re * Real.sin a ≤ |w.re * Real.sin a| := le_abs_self _
    have h4 : |w.re * Real.sin a| = |w.re| * |Real.sin a| := abs_mul _ _
    have h5 : |w.re| * |Real.sin a| ≤ |w.re| * 1 :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h6 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h7 : Real.exp (w.re * Real.sin a) ≤ Real.exp (‖Complex.I * z‖ + 1) :=
      Real.exp_le_exp.mpr (by linarith)
    have h8 : |Real.sin a| * Real.exp (w.re * Real.sin a)
        ≤ 1 * Real.exp (‖Complex.I * z‖ + 1) :=
      mul_le_mul h1 h7 (Real.exp_pos _).le zero_le_one
    rw [one_mul (Real.exp (‖Complex.I * z‖ + 1))] at h8
    exact h8
  have hL : HasDerivAt
      (fun w : ℂ => ∫ a in Set.Ioc (0 : ℝ) (π / 2), Complex.exp (w * (Real.sin a : ℂ)))
      (∫ a in Set.Ioc (0 : ℝ) (π / 2),
        (Real.sin a : ℂ) * Complex.exp (Complex.I * z * (Real.sin a : ℂ)))
      (Complex.I * z) :=
    hasDerivAt_integral_cexp_mul (μ := volume.restrict (Set.Ioc (0 : ℝ) (π / 2)))
      (g := Real.sin) (bound := fun _ : ℝ => Real.exp (‖Complex.I * z‖ + 1))
      Real.continuous_sin (Metric.ball_mem_nhds (Complex.I * z) one_pos) hint hbound hbi
  have hin : HasDerivAt (fun y : ℂ => Complex.I * y) (Complex.I * 1) z :=
    (hasDerivAt_id' z).const_mul Complex.I
  have hd : DifferentiableAt ℂ
      ((fun w : ℂ => ∫ a in Set.Ioc (0 : ℝ) (π / 2), Complex.exp (w * (Real.sin a : ℂ)))
        ∘ (fun y : ℂ => Complex.I * y)) z :=
    (HasDerivAt.comp z hL hin).differentiableAt
  have hfun : kerA
      = (fun w : ℂ => ∫ a in Set.Ioc (0 : ℝ) (π / 2), Complex.exp (w * (Real.sin a : ℂ)))
        ∘ (fun y : ℂ => Complex.I * y) := by
    funext y
    show (∫ t in (0 : ℝ)..(π / 2), Complex.exp (Complex.I * y * (Real.sin t : ℂ)))
      = ∫ a in Set.Ioc (0 : ℝ) (π / 2), Complex.exp (Complex.I * y * (Real.sin a : ℂ))
    exact intervalIntegral.integral_of_le Real.pi_div_two_pos.le
  rw [hfun]
  exact hd

/-- `‖kerA z‖ ≤ e^{|Im z|} π/2`. -/
theorem norm_kerA_le (z : ℂ) : ‖kerA z‖ ≤ Real.exp |z.im| * (π / 2) := by
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) (π / 2),
      ‖Complex.exp (Complex.I * z * (Real.sin t : ℂ))‖ ≤ Real.exp |z.im| := by
    intro t _
    rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.I_mul_re]
    have h1 : -z.im * Real.sin t ≤ |-z.im * Real.sin t| := le_abs_self _
    have h2 : |-z.im * Real.sin t| = |z.im| * |Real.sin t| := by rw [abs_mul, abs_neg]
    have h3 : |z.im| * |Real.sin t| ≤ |z.im| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t) (abs_nonneg _)
    exact Real.exp_le_exp.mpr (by linarith)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have h' : ‖∫ t in (0 : ℝ)..(π / 2), Complex.exp (Complex.I * z * (Real.sin t : ℂ))‖
      ≤ Real.exp |z.im| * |π / 2 - 0| := h
  rw [sub_zero, abs_of_pos Real.pi_div_two_pos] at h'
  exact h'

/-! ## `J₀` on `ℂ` -/

/-- `J₀(z) = (2/π) ∫₀^{π/2} cos(z sin t) dt`, written with `kerA`. -/
noncomputable def cJ0 (z : ℂ) : ℂ := (kerA z + kerA (-z)) / (π : ℂ)

/-- `cJ0` is entire. -/
theorem differentiable_cJ0 : Differentiable ℂ cJ0 := by
  intro z
  have h1 : HasDerivAt kerA (deriv kerA z) z := (differentiable_kerA z).hasDerivAt
  have h2 : HasDerivAt kerA (deriv kerA (-z)) (-z) := (differentiable_kerA (-z)).hasDerivAt
  have hneg : HasDerivAt (fun y : ℂ => -y) (-1) z := (hasDerivAt_id' z).neg
  have h3 : HasDerivAt (fun y : ℂ => kerA (-y)) (deriv kerA (-z) * -1) z :=
    HasDerivAt.comp z h2 hneg
  have h4 : HasDerivAt (fun y : ℂ => kerA y + kerA (-y))
      (deriv kerA z + deriv kerA (-z) * -1) z := h1.add h3
  have h5 : HasDerivAt (fun y : ℂ => (kerA y + kerA (-y)) / (π : ℂ))
      ((deriv kerA z + deriv kerA (-z) * -1) / (π : ℂ)) z := h4.div_const (π : ℂ)
  show DifferentiableAt ℂ (fun y : ℂ => (kerA y + kerA (-y)) / (π : ℂ)) z
  exact h5.differentiableAt

/-- **`‖J₀(z)‖ ≤ e^{|Im z|}`.** -/
theorem norm_cJ0_le (z : ℂ) : ‖cJ0 z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖kerA z‖ ≤ Real.exp |z.im| * (π / 2) := norm_kerA_le z
  have h2 : ‖kerA (-z)‖ ≤ Real.exp |(-z).im| * (π / 2) := norm_kerA_le (-z)
  rw [Complex.neg_im, abs_neg] at h2
  have h3 : ‖kerA z + kerA (-z)‖ ≤ ‖kerA z‖ + ‖kerA (-z)‖ := norm_add_le _ _
  have hpi : ‖(π : ℂ)‖ = π := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  show ‖(kerA z + kerA (-z)) / (π : ℂ)‖ ≤ Real.exp |z.im|
  rw [norm_div, hpi, div_le_iff₀ Real.pi_pos]
  linarith

/-- `J₀(z) = (2/π) ∫₀^{π/2} cos(z sin t) dt`. -/
theorem cJ0_eq_integral (z : ℂ) :
    cJ0 z = 2 / (π : ℂ) * ∫ t in (0 : ℝ)..(π / 2), Complex.cos (z * (Real.sin t : ℂ)) := by
  have hc1 : Continuous (fun t : ℝ => Complex.exp (Complex.I * z * (Real.sin t : ℂ))) :=
    continuous_cexp_mul_sin (Complex.I * z)
  have hc2 : Continuous (fun t : ℝ => Complex.exp (Complex.I * -z * (Real.sin t : ℂ))) :=
    continuous_cexp_mul_sin (Complex.I * -z)
  have hadd : (∫ t in (0 : ℝ)..(π / 2),
        (Complex.exp (Complex.I * z * (Real.sin t : ℂ))
          + Complex.exp (Complex.I * -z * (Real.sin t : ℂ))))
      = (∫ t in (0 : ℝ)..(π / 2), Complex.exp (Complex.I * z * (Real.sin t : ℂ)))
        + ∫ t in (0 : ℝ)..(π / 2), Complex.exp (Complex.I * -z * (Real.sin t : ℂ)) :=
    intervalIntegral.integral_add (hc1.intervalIntegrable 0 (π / 2))
      (hc2.intervalIntegrable 0 (π / 2))
  have hfun : (fun t : ℝ => Complex.exp (Complex.I * z * (Real.sin t : ℂ))
        + Complex.exp (Complex.I * -z * (Real.sin t : ℂ)))
      = fun t : ℝ => 2 * Complex.cos (z * (Real.sin t : ℂ)) := by
    funext t
    show Complex.exp (Complex.I * z * (Real.sin t : ℂ))
        + Complex.exp (Complex.I * -z * (Real.sin t : ℂ))
      = 2 * Complex.cos (z * (Real.sin t : ℂ))
    have e1 : Complex.I * z * (Real.sin t : ℂ) = z * (Real.sin t : ℂ) * Complex.I := by ring
    have e2 : Complex.I * -z * (Real.sin t : ℂ) = -(z * (Real.sin t : ℂ)) * Complex.I := by
      ring
    rw [Complex.two_cos, e1, e2]
  have hmul : (∫ t in (0 : ℝ)..(π / 2), 2 * Complex.cos (z * (Real.sin t : ℂ)))
      = 2 * ∫ t in (0 : ℝ)..(π / 2), Complex.cos (z * (Real.sin t : ℂ)) :=
    intervalIntegral.integral_const_mul 2 (fun t : ℝ => Complex.cos (z * (Real.sin t : ℂ)))
  rw [hfun, hmul] at hadd
  have e3 : kerA z + kerA (-z)
      = 2 * ∫ t in (0 : ℝ)..(π / 2), Complex.cos (z * (Real.sin t : ℂ)) := hadd.symm
  show (kerA z + kerA (-z)) / (π : ℂ)
    = 2 / (π : ℂ) * ∫ t in (0 : ℝ)..(π / 2), Complex.cos (z * (Real.sin t : ℂ))
  rw [e3]
  ring

end Tower.RV6
