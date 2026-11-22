import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselK
import Tower.RV6.RungA2P
import Tower.RV6.CKernel
import Tower.RV6.CJSeries

/-!
# Complex kernels for the rotation of the contour, III: `K₀` on the right half-plane, and the two forms of `H₀⁽¹⁾`

* `cK0 w = ∫₀^∞ exp(-w cosh u) du`: differentiable at `w` for `Re w > 0` (`differentiableAt_cK0`),
  `‖cK0 w‖ ≤ K₀(Re w)` (`norm_cK0_le`), `cK0 t = K₀(t)` for real `t` (`cK0_ofReal`).
* `kerB z = ∫_{x ≤ 0} exp(z sinh x) dx` (`= ∫₀^∞ exp(-z sinh u) du`): differentiable at `z` for
  `Re z > 0` (`differentiableAt_kerB`), real on the real axis (`kerB_ofReal`).
* `hE z = (2/π) kerA z - (2i/π) kerB z`, differentiable for `Re z > 0`;  **`hE_ofReal_re`**:
  `Re hE(x) = J₀(x)` for real `x`.
* `hK z = -(2i/π) cK0(-iz)`, differentiable for `Im z > 0`;  **`norm_hK_le`**:
  `‖hK z‖ ≤ (2/π) K₀(Im z)`;  **`hK_I_mul`**: `hK (i y) = -(2i/π) K₀(y)`.

Both `hE` and `hK` are `H₀⁽¹⁾ = J₀ + iY₀`; that they agree on the open first quadrant is
`HAgree.lean`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## Differentiation under the integral sign, with an almost-everywhere bound -/

/-- `hasDerivAt_integral_cexp_mul` with the bound required only almost everywhere. -/
theorem hasDerivAt_integral_cexp_mul_ae {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    {w₀ : ℂ} {s : Set ℂ} (hs : s ∈ nhds w₀) {bound : ℝ → ℝ}
    (hint : Integrable (fun a : ℝ => Complex.exp (w₀ * (g a : ℂ))) μ)
    (hbound : ∀ᵐ a ∂μ, ∀ w ∈ s, ‖(g a : ℂ) * Complex.exp (w * (g a : ℂ))‖ ≤ bound a)
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
    hbound hbi
    (Filter.Eventually.of_forall hdiff)
  exact key.2

theorem norm_cexp_mul_ofReal (ζ : ℂ) (r : ℝ) :
    ‖Complex.exp (ζ * (r : ℂ))‖ = Real.exp (ζ.re * r) := by
  rw [Complex.norm_exp, Complex.re_mul_ofReal]

theorem continuous_cexp_mul_cosh (ζ : ℂ) :
    Continuous (fun u : ℝ => Complex.exp (ζ * (Real.cosh u : ℂ))) := by
  have h0 : Continuous (fun u : ℝ => (Real.cosh u : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_cosh
  have h1 : Continuous (fun u : ℝ => ζ * (Real.cosh u : ℂ)) := continuous_const.mul h0
  exact Complex.continuous_exp.comp h1

theorem continuous_cexp_mul_sinh (ζ : ℂ) :
    Continuous (fun u : ℝ => Complex.exp (ζ * (Real.sinh u : ℂ))) := by
  have h0 : Continuous (fun u : ℝ => (Real.sinh u : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_sinh
  have h1 : Continuous (fun u : ℝ => ζ * (Real.sinh u : ℂ)) := continuous_const.mul h0
  exact Complex.continuous_exp.comp h1

/-! ## `K₀` on the right half-plane -/

/-- `K₀(w) = ∫₀^∞ exp(-w cosh u) du`, used for `Re w > 0`. -/
noncomputable def cK0 (w : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-w * (Real.cosh u : ℂ))

/-- For `Re ζ < 0`, `u ↦ exp(ζ cosh u)` is integrable on `(0, ∞)`. -/
theorem integrable_cexp_mul_cosh {ζ : ℂ} (hζ : ζ.re < 0) :
    Integrable (fun u : ℝ => Complex.exp (ζ * (Real.cosh u : ℂ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hb : Integrable (fun u : ℝ => kf (-ζ.re) 0 u) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_kf (neg_pos.mpr hζ) 0 (by norm_num)
  refine hb.mono' (continuous_cexp_mul_cosh ζ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => ?_))
  show ‖Complex.exp (ζ * (Real.cosh u : ℂ))‖ ≤ kf (-ζ.re) 0 u
  rw [norm_cexp_mul_ofReal]
  have e : Real.exp (ζ.re * Real.cosh u) = kf (-ζ.re) 0 u := by
    show Real.exp (ζ.re * Real.cosh u) = Real.exp (-(-ζ.re) * Real.cosh u) * Real.cosh u ^ 0
    rw [pow_zero, mul_one (Real.exp (-(-ζ.re) * Real.cosh u)), neg_neg]
  exact le_of_eq e

/-- `cK0` is differentiable on the right half-plane. -/
theorem differentiableAt_cK0 {w₀ : ℂ} (hw : 0 < w₀.re) : DifferentiableAt ℂ cK0 w₀ := by
  have hc2 : 0 < w₀.re / 2 := half_pos hw
  have hneg0 : (-w₀).re < 0 := by
    rw [Complex.neg_re]
    linarith
  have hint : Integrable (fun a : ℝ => Complex.exp (-w₀ * (Real.cosh a : ℂ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := integrable_cexp_mul_cosh hneg0
  have hbi : Integrable (fun a : ℝ => kf (w₀.re / 2) 1 a)
      (volume.restrict (Set.Ioi (0 : ℝ))) := integrable_kf hc2 1 (by norm_num)
  have hbound : ∀ a : ℝ, ∀ ζ ∈ Metric.ball (-w₀) (w₀.re / 2),
      ‖(Real.cosh a : ℂ) * Complex.exp (ζ * (Real.cosh a : ℂ))‖ ≤ kf (w₀.re / 2) 1 a := by
    intro a ζ hζ
    have h1 : ‖ζ - -w₀‖ < w₀.re / 2 := by
      have h := Metric.mem_ball.mp hζ
      rw [dist_eq_norm] at h
      exact h
    have h2 : |(ζ - -w₀).re| ≤ ‖ζ - -w₀‖ := Complex.abs_re_le_norm _
    have h3 : (ζ - -w₀).re = ζ.re + w₀.re := by
      rw [Complex.sub_re, Complex.neg_re]
      ring
    have h4 : (ζ - -w₀).re ≤ |(ζ - -w₀).re| := le_abs_self _
    have hre : ζ.re ≤ -(w₀.re / 2) := by linarith
    have hch : 0 < Real.cosh a := Real.cosh_pos a
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hch, norm_cexp_mul_ofReal]
    have h5 : ζ.re * Real.cosh a ≤ -(w₀.re / 2) * Real.cosh a :=
      mul_le_mul_of_nonneg_right hre hch.le
    have h6 : Real.exp (ζ.re * Real.cosh a) ≤ Real.exp (-(w₀.re / 2) * Real.cosh a) :=
      Real.exp_le_exp.mpr h5
    have h7 : Real.cosh a * Real.exp (ζ.re * Real.cosh a)
        ≤ Real.cosh a * Real.exp (-(w₀.re / 2) * Real.cosh a) :=
      mul_le_mul_of_nonneg_left h6 hch.le
    have e : kf (w₀.re / 2) 1 a
        = Real.cosh a * Real.exp (-(w₀.re / 2) * Real.cosh a) := by
      show Real.exp (-(w₀.re / 2) * Real.cosh a) * Real.cosh a ^ 1
        = Real.cosh a * Real.exp (-(w₀.re / 2) * Real.cosh a)
      rw [pow_one, mul_comm (Real.exp (-(w₀.re / 2) * Real.cosh a)) (Real.cosh a)]
    rw [e]
    exact h7
  have hL : HasDerivAt
      (fun ζ : ℂ => ∫ a in Set.Ioi (0 : ℝ), Complex.exp (ζ * (Real.cosh a : ℂ)))
      (∫ a in Set.Ioi (0 : ℝ), (Real.cosh a : ℂ) * Complex.exp (-w₀ * (Real.cosh a : ℂ)))
      (-w₀) :=
    hasDerivAt_integral_cexp_mul (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (g := Real.cosh) (bound := fun a : ℝ => kf (w₀.re / 2) 1 a)
      Real.continuous_cosh (Metric.ball_mem_nhds (-w₀) hc2) hint hbound hbi
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) w₀ := (hasDerivAt_id' w₀).neg
  have hd : DifferentiableAt ℂ
      ((fun ζ : ℂ => ∫ a in Set.Ioi (0 : ℝ), Complex.exp (ζ * (Real.cosh a : ℂ)))
        ∘ (fun w : ℂ => -w)) w₀ :=
    (HasDerivAt.comp w₀ hL hneg).differentiableAt
  have hfun : cK0
      = (fun ζ : ℂ => ∫ a in Set.Ioi (0 : ℝ), Complex.exp (ζ * (Real.cosh a : ℂ)))
        ∘ (fun w : ℂ => -w) := by
    funext w
    rfl
  rw [hfun]
  exact hd

/-- `‖K₀(w)‖ ≤ K₀(Re w)`. -/
theorem norm_cK0_le (w : ℂ) : ‖cK0 w‖ ≤ besselK0 w.re := by
  have h := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (fun u : ℝ => Complex.exp (-w * (Real.cosh u : ℂ)))
  have hfun : (fun u : ℝ => ‖Complex.exp (-w * (Real.cosh u : ℂ))‖)
      = fun u : ℝ => Real.exp (-w.re * Real.cosh u) := by
    funext u
    show ‖Complex.exp (-w * (Real.cosh u : ℂ))‖ = Real.exp (-w.re * Real.cosh u)
    rw [norm_cexp_mul_ofReal, Complex.neg_re]
  rw [hfun] at h
  exact h

/-- On the positive real axis `cK0` is `K₀`. -/
theorem cK0_ofReal (t : ℝ) : cK0 (t : ℂ) = (besselK0 t : ℂ) := by
  have hfun : (fun u : ℝ => Complex.exp (-(t : ℂ) * (Real.cosh u : ℂ)))
      = fun u : ℝ => ((Real.exp (-t * Real.cosh u) : ℝ) : ℂ) := by
    funext u
    show Complex.exp (-(t : ℂ) * (Real.cosh u : ℂ)) = ((Real.exp (-t * Real.cosh u) : ℝ) : ℂ)
    rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  show (∫ u in Set.Ioi (0 : ℝ), Complex.exp (-(t : ℂ) * (Real.cosh u : ℂ)))
    = (((∫ u in Set.Ioi (0 : ℝ), Real.exp (-t * Real.cosh u)) : ℝ) : ℂ)
  rw [hfun]
  exact integral_complex_ofReal

/-! ## The kernel `kerB` -/

/-- `∫_{x ≤ 0} exp(z sinh x) dx = ∫₀^∞ exp(-z sinh u) du`, used for `Re z > 0`. -/
noncomputable def kerB (z : ℂ) : ℂ :=
  ∫ x in Set.Iic (0 : ℝ), Complex.exp (z * (Real.sinh x : ℂ))

/-- For `Re z > 0`, `x ↦ exp(z sinh x)` is integrable on `x ≤ 0`. -/
theorem integrable_cexp_mul_sinh {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun x : ℝ => Complex.exp (z * (Real.sinh x : ℂ)))
      (volume.restrict (Set.Iic (0 : ℝ))) := by
  have hb : Integrable (fun x : ℝ => Real.exp (z.re * x)) (volume.restrict (Set.Iic (0 : ℝ))) :=
    integrableOn_exp_mul_Iic hz 0
  refine hb.mono' (continuous_cexp_mul_sinh z).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Iic (fun x hx => ?_))
  have hx0 : x ≤ 0 := hx
  show ‖Complex.exp (z * (Real.sinh x : ℂ))‖ ≤ Real.exp (z.re * x)
  rw [norm_cexp_mul_ofReal]
  have h1 : Real.sinh x ≤ x := Real.sinh_le_self_iff.mpr hx0
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1 hz.le)

/-- For `a ≤ 0`, `c > 0`, `r ≥ c/2`: `|sinh a| e^{r sinh a} ≤ (4/c) e^{ca/4}`. -/
theorem abs_sinh_mul_exp_le {c r a : ℝ} (hc : 0 < c) (hr : c / 2 ≤ r) (ha : a ≤ 0) :
    |Real.sinh a| * Real.exp (r * Real.sinh a) ≤ 4 / c * Real.exp (c / 4 * a) := by
  have hs0 : Real.sinh a ≤ 0 := Real.sinh_nonpos_iff.mpr ha
  have hsa : Real.sinh a ≤ a := Real.sinh_le_self_iff.mpr ha
  have habs : |Real.sinh a| = -Real.sinh a := abs_of_nonpos hs0
  have hc4 : (0 : ℝ) ≤ c / 4 := by linarith
  have h4c : (0 : ℝ) ≤ 4 / c := (div_pos (by norm_num) hc).le
  have hA0 : 0 < Real.exp (c / 4 * Real.sinh a) := Real.exp_pos _
  have hAA : Real.exp (c / 4 * Real.sinh a) * Real.exp (c / 4 * Real.sinh a)
      = Real.exp (c / 2 * Real.sinh a) := exp_mul_exp_of_add_eq (by ring)
  have hAB : Real.exp (c / 4 * Real.sinh a) ≤ Real.exp (c / 4 * a) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsa hc4)
  have h1 : r * Real.sinh a ≤ c / 2 * Real.sinh a := by
    have h := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr) hs0
    linarith
  have h2 : Real.exp (r * Real.sinh a) ≤ Real.exp (c / 2 * Real.sinh a) :=
    Real.exp_le_exp.mpr h1
  have hE : -(c / 4 * Real.sinh a) + 1 ≤ Real.exp (-(c / 4 * Real.sinh a)) :=
    Real.add_one_le_exp _
  have hAinv : Real.exp (c / 4 * Real.sinh a) * Real.exp (-(c / 4 * Real.sinh a))
      = Real.exp 0 := exp_mul_exp_of_add_eq (by ring)
  rw [Real.exp_zero] at hAinv
  have h3 : Real.exp (c / 4 * Real.sinh a) * (-(c / 4 * Real.sinh a) + 1)
      ≤ Real.exp (c / 4 * Real.sinh a) * Real.exp (-(c / 4 * Real.sinh a)) :=
    mul_le_mul_of_nonneg_left hE hA0.le
  have h4 : -Real.sinh a * Real.exp (c / 4 * Real.sinh a) ≤ 4 / c := by
    rw [le_div_iff₀ hc]
    linarith
  have h5 : -Real.sinh a * Real.exp (r * Real.sinh a)
      ≤ -Real.sinh a * Real.exp (c / 2 * Real.sinh a) :=
    mul_le_mul_of_nonneg_left h2 (neg_nonneg.mpr hs0)
  have h6 : -Real.sinh a * Real.exp (c / 4 * Real.sinh a) * Real.exp (c / 4 * Real.sinh a)
      ≤ 4 / c * Real.exp (c / 4 * Real.sinh a) :=
    mul_le_mul_of_nonneg_right h4 hA0.le
  have h7 : 4 / c * Real.exp (c / 4 * Real.sinh a) ≤ 4 / c * Real.exp (c / 4 * a) :=
    mul_le_mul_of_nonneg_left hAB h4c
  have h8 : -Real.sinh a * Real.exp (c / 2 * Real.sinh a)
      = -Real.sinh a * Real.exp (c / 4 * Real.sinh a) * Real.exp (c / 4 * Real.sinh a) := by
    rw [← hAA]
    ring
  rw [habs]
  linarith

/-- `kerB` is differentiable on the right half-plane. -/
theorem differentiableAt_kerB {z₀ : ℂ} (hz : 0 < z₀.re) : DifferentiableAt ℂ kerB z₀ := by
  have hc2 : 0 < z₀.re / 2 := half_pos hz
  have hc4 : 0 < z₀.re / 4 := by linarith
  have hint : Integrable (fun a : ℝ => Complex.exp (z₀ * (Real.sinh a : ℂ)))
      (volume.restrict (Set.Iic (0 : ℝ))) := integrable_cexp_mul_sinh hz
  have hb0 : Integrable (fun a : ℝ => Real.exp (z₀.re / 4 * a))
      (volume.restrict (Set.Iic (0 : ℝ))) := integrableOn_exp_mul_Iic hc4 0
  have hbi : Integrable (fun a : ℝ => 4 / z₀.re * Real.exp (z₀.re / 4 * a))
      (volume.restrict (Set.Iic (0 : ℝ))) := Integrable.const_mul hb0 (4 / z₀.re)
  have hbound : ∀ᵐ a ∂(volume.restrict (Set.Iic (0 : ℝ))), ∀ z ∈ Metric.ball z₀ (z₀.re / 2),
      ‖(Real.sinh a : ℂ) * Complex.exp (z * (Real.sinh a : ℂ))‖
        ≤ 4 / z₀.re * Real.exp (z₀.re / 4 * a) := by
    refine ae_restrict_of_forall_mem measurableSet_Iic (fun a ha z hzb => ?_)
    have ha0 : a ≤ 0 := ha
    have h1 : ‖z - z₀‖ < z₀.re / 2 := by
      have h := Metric.mem_ball.mp hzb
      rw [dist_eq_norm] at h
      exact h
    have h2 : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
    have h3 : (z - z₀).re = z.re - z₀.re := Complex.sub_re z z₀
    have h4 : -(z - z₀).re ≤ |(z - z₀).re| := neg_le_abs _
    have hre : z₀.re / 2 ≤ z.re := by linarith
    show ‖(Real.sinh a : ℂ) * Complex.exp (z * (Real.sinh a : ℂ))‖
      ≤ 4 / z₀.re * Real.exp (z₀.re / 4 * a)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_mul_ofReal]
    exact abs_sinh_mul_exp_le hz hre ha0
  have hL : HasDerivAt
      (fun z : ℂ => ∫ a in Set.Iic (0 : ℝ), Complex.exp (z * (Real.sinh a : ℂ)))
      (∫ a in Set.Iic (0 : ℝ), (Real.sinh a : ℂ) * Complex.exp (z₀ * (Real.sinh a : ℂ)))
      z₀ :=
    hasDerivAt_integral_cexp_mul_ae (μ := volume.restrict (Set.Iic (0 : ℝ)))
      (g := Real.sinh) (bound := fun a : ℝ => 4 / z₀.re * Real.exp (z₀.re / 4 * a))
      Real.continuous_sinh (Metric.ball_mem_nhds z₀ hc2) hint hbound hbi
  show DifferentiableAt ℂ
    (fun z : ℂ => ∫ a in Set.Iic (0 : ℝ), Complex.exp (z * (Real.sinh a : ℂ))) z₀
  exact hL.differentiableAt

/-- On the real axis `kerB` is real. -/
theorem kerB_ofReal (x : ℝ) :
    kerB (x : ℂ) = (((∫ u in Set.Iic (0 : ℝ), Real.exp (x * Real.sinh u)) : ℝ) : ℂ) := by
  have hfun : (fun u : ℝ => Complex.exp ((x : ℂ) * (Real.sinh u : ℂ)))
      = fun u : ℝ => ((Real.exp (x * Real.sinh u) : ℝ) : ℂ) := by
    funext u
    show Complex.exp ((x : ℂ) * (Real.sinh u : ℂ)) = ((Real.exp (x * Real.sinh u) : ℝ) : ℂ)
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
  show (∫ u in Set.Iic (0 : ℝ), Complex.exp ((x : ℂ) * (Real.sinh u : ℂ)))
    = (((∫ u in Set.Iic (0 : ℝ), Real.exp (x * Real.sinh u)) : ℝ) : ℂ)
  rw [hfun]
  exact integral_complex_ofReal

/-! ## `kerA` on the real axis -/

/-- `kerA x = ∫₀^{π/2} cos(x sin t) dt + i ∫₀^{π/2} sin(x sin t) dt` for real `x`. -/
theorem kerA_ofReal (x : ℝ) :
    kerA (x : ℂ)
      = (((∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t)) : ℝ) : ℂ)
        + (((∫ t in (0 : ℝ)..(π / 2), Real.sin (x * Real.sin t)) : ℝ) : ℂ) * Complex.I := by
  have hfun : (fun t : ℝ => Complex.exp (Complex.I * (x : ℂ) * (Real.sin t : ℂ)))
      = fun t : ℝ => ((Real.cos (x * Real.sin t) : ℝ) : ℂ)
        + ((Real.sin (x * Real.sin t) : ℝ) : ℂ) * Complex.I := by
    funext t
    show Complex.exp (Complex.I * (x : ℂ) * (Real.sin t : ℂ))
      = ((Real.cos (x * Real.sin t) : ℝ) : ℂ) + ((Real.sin (x * Real.sin t) : ℝ) : ℂ) * Complex.I
    have e : Complex.I * (x : ℂ) * (Real.sin t : ℂ) = ((x * Real.sin t : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_mul]
      ring
    rw [e, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hcr : Continuous (fun t : ℝ => x * Real.sin t) := continuous_const.mul Real.continuous_sin
  have hc : Continuous (fun t : ℝ => ((Real.cos (x * Real.sin t) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp hcr)
  have hs0 : Continuous (fun t : ℝ => ((Real.sin (x * Real.sin t) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp hcr)
  have hs : Continuous (fun t : ℝ => ((Real.sin (x * Real.sin t) : ℝ) : ℂ) * Complex.I) :=
    hs0.mul continuous_const
  have hadd : (∫ t in (0 : ℝ)..(π / 2), (((Real.cos (x * Real.sin t) : ℝ) : ℂ)
        + ((Real.sin (x * Real.sin t) : ℝ) : ℂ) * Complex.I))
      = (∫ t in (0 : ℝ)..(π / 2), ((Real.cos (x * Real.sin t) : ℝ) : ℂ))
        + ∫ t in (0 : ℝ)..(π / 2), ((Real.sin (x * Real.sin t) : ℝ) : ℂ) * Complex.I :=
    intervalIntegral.integral_add (hc.intervalIntegrable 0 (π / 2))
      (hs.intervalIntegrable 0 (π / 2))
  have h1 : (∫ t in (0 : ℝ)..(π / 2), ((Real.cos (x * Real.sin t) : ℝ) : ℂ))
      = (((∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t)) : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  have h2 : (∫ t in (0 : ℝ)..(π / 2), ((Real.sin (x * Real.sin t) : ℝ) : ℂ) * Complex.I)
      = (∫ t in (0 : ℝ)..(π / 2), ((Real.sin (x * Real.sin t) : ℝ) : ℂ)) * Complex.I :=
    intervalIntegral.integral_mul_const Complex.I
      (fun t : ℝ => ((Real.sin (x * Real.sin t) : ℝ) : ℂ))
  have h3 : (∫ t in (0 : ℝ)..(π / 2), ((Real.sin (x * Real.sin t) : ℝ) : ℂ))
      = (((∫ t in (0 : ℝ)..(π / 2), Real.sin (x * Real.sin t)) : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  show (∫ t in (0 : ℝ)..(π / 2), Complex.exp (Complex.I * (x : ℂ) * (Real.sin t : ℂ)))
    = (((∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t)) : ℝ) : ℂ)
      + (((∫ t in (0 : ℝ)..(π / 2), Real.sin (x * Real.sin t)) : ℝ) : ℂ) * Complex.I
  rw [hfun, hadd, h1, h2, h3]

theorem kerA_ofReal_re (x : ℝ) :
    (kerA (x : ℂ)).re = ∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t) := by
  rw [kerA_ofReal, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero]

/-- `∫₀^{π/2} cos(x sin t) dt = (π/2) J₀(x)` for real `x`. -/
theorem integral_cos_mul_sin_eq (x : ℝ) :
    (∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t)) = π / 2 * besselJ0 x := by
  have hfun : (fun t : ℝ => Complex.cos ((x : ℂ) * (Real.sin t : ℂ)))
      = fun t : ℝ => ((Real.cos (x * Real.sin t) : ℝ) : ℂ) := by
    funext t
    show Complex.cos ((x : ℂ) * (Real.sin t : ℂ)) = ((Real.cos (x * Real.sin t) : ℝ) : ℂ)
    rw [Complex.ofReal_cos, Complex.ofReal_mul]
  have h1 : cJ0 (x : ℂ)
      = 2 / (π : ℂ) * ∫ t in (0 : ℝ)..(π / 2), Complex.cos ((x : ℂ) * (Real.sin t : ℂ)) :=
    cJ0_eq_integral (x : ℂ)
  have h2 : (∫ t in (0 : ℝ)..(π / 2), ((Real.cos (x * Real.sin t) : ℝ) : ℂ))
      = (((∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t)) : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  rw [hfun, h2, cJ0_ofReal] at h1
  have h3 : ((2 / π * ∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t) : ℝ) : ℂ)
      = 2 / (π : ℂ) * (((∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  have h4 : besselJ0 x = 2 / π * ∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t) :=
    Complex.ofReal_injective (h1.trans h3.symm)
  have hpi : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  linear_combination (-(π / 2)) * h4
    - (∫ t in (0 : ℝ)..(π / 2), Real.cos (x * Real.sin t)) * hpi

/-! ## The two forms of `H₀⁽¹⁾` -/

/-- `H₀⁽¹⁾(z) = (2/π) ∫₀^{π/2} e^{iz sin t} dt - (2i/π) ∫₀^∞ e^{-z sinh u} du`, for `Re z > 0`. -/
noncomputable def hE (z : ℂ) : ℂ :=
  2 / (π : ℂ) * kerA z - 2 * Complex.I / (π : ℂ) * kerB z

/-- `H₀⁽¹⁾(z) = -(2i/π) K₀(-iz)`, for `Im z > 0`. -/
noncomputable def hK (z : ℂ) : ℂ :=
  -(2 * Complex.I / (π : ℂ)) * cK0 (-Complex.I * z)

theorem differentiableAt_hE {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ hE z := by
  have h1 : HasDerivAt kerA (deriv kerA z) z := (differentiable_kerA z).hasDerivAt
  have h2 : HasDerivAt kerB (deriv kerB z) z := (differentiableAt_kerB hz).hasDerivAt
  have h3 : HasDerivAt (fun y : ℂ => 2 / (π : ℂ) * kerA y) (2 / (π : ℂ) * deriv kerA z) z :=
    h1.const_mul (2 / (π : ℂ))
  have h4 : HasDerivAt (fun y : ℂ => 2 * Complex.I / (π : ℂ) * kerB y)
      (2 * Complex.I / (π : ℂ) * deriv kerB z) z := h2.const_mul (2 * Complex.I / (π : ℂ))
  have h5 : HasDerivAt (fun y : ℂ => 2 / (π : ℂ) * kerA y - 2 * Complex.I / (π : ℂ) * kerB y)
      (2 / (π : ℂ) * deriv kerA z - 2 * Complex.I / (π : ℂ) * deriv kerB z) z := h3.sub h4
  show DifferentiableAt ℂ
    (fun y : ℂ => 2 / (π : ℂ) * kerA y - 2 * Complex.I / (π : ℂ) * kerB y) z
  exact h5.differentiableAt

/-- **`Re hE(x) = J₀(x)` on the real axis.** -/
theorem hE_ofReal_re (x : ℝ) : (hE (x : ℂ)).re = besselJ0 x := by
  have hA : (kerA (x : ℂ)).re = π / 2 * besselJ0 x := by
    rw [kerA_ofReal_re, integral_cos_mul_sin_eq]
  have hB : (kerB (x : ℂ)).im = 0 := by
    rw [kerB_ofReal, Complex.ofReal_im]
  have e1 : 2 / (π : ℂ) = ((2 / π : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
  have e2 : 2 * Complex.I / (π : ℂ) * kerB (x : ℂ)
      = ((2 / π : ℝ) : ℂ) * kerB (x : ℂ) * Complex.I := by
    rw [← e1]
    ring
  have hpi : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  show (2 / (π : ℂ) * kerA (x : ℂ) - 2 * Complex.I / (π : ℂ) * kerB (x : ℂ)).re = besselJ0 x
  rw [e2, e1, Complex.sub_re, Complex.mul_I_re, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    hA, hB]
  linear_combination (besselJ0 x) * hpi

theorem neg_I_mul_re (z : ℂ) : (-Complex.I * z).re = z.im := by
  rw [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]

theorem differentiableAt_hK {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ hK z := by
  have hre : 0 < (-Complex.I * z).re := by
    rw [neg_I_mul_re]
    exact hz
  have h1 : HasDerivAt cK0 (deriv cK0 (-Complex.I * z)) (-Complex.I * z) :=
    (differentiableAt_cK0 hre).hasDerivAt
  have hin : HasDerivAt (fun y : ℂ => -Complex.I * y) (-Complex.I * 1) z :=
    (hasDerivAt_id' z).const_mul (-Complex.I)
  have h2 : HasDerivAt (fun y : ℂ => cK0 (-Complex.I * y))
      (deriv cK0 (-Complex.I * z) * (-Complex.I * 1)) z := HasDerivAt.comp z h1 hin
  have h3 : HasDerivAt (fun y : ℂ => -(2 * Complex.I / (π : ℂ)) * cK0 (-Complex.I * y))
      (-(2 * Complex.I / (π : ℂ)) * (deriv cK0 (-Complex.I * z) * (-Complex.I * 1))) z :=
    h2.const_mul (-(2 * Complex.I / (π : ℂ)))
  show DifferentiableAt ℂ
    (fun y : ℂ => -(2 * Complex.I / (π : ℂ)) * cK0 (-Complex.I * y)) z
  exact h3.differentiableAt

/-- **`‖hK z‖ ≤ (2/π) K₀(Im z)`.** -/
theorem norm_hK_le (z : ℂ) : ‖hK z‖ ≤ 2 / π * besselK0 z.im := by
  have h1 : ‖cK0 (-Complex.I * z)‖ ≤ besselK0 (-Complex.I * z).re :=
    norm_cK0_le (-Complex.I * z)
  rw [neg_I_mul_re] at h1
  have hc : -(2 * Complex.I / (π : ℂ)) = ((-(2 / π) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have h2pi : (0 : ℝ) < 2 / π := div_pos two_pos Real.pi_pos
  have hn : ‖-(2 * Complex.I / (π : ℂ))‖ = 2 / π := by
    rw [hc, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_neg,
      abs_of_pos h2pi]
  show ‖-(2 * Complex.I / (π : ℂ)) * cK0 (-Complex.I * z)‖ ≤ 2 / π * besselK0 z.im
  rw [norm_mul, hn]
  exact mul_le_mul_of_nonneg_left h1 h2pi.le

/-- **On the imaginary axis `hK (i y) = -(2i/π) K₀(y)`.** -/
theorem hK_I_mul (y : ℝ) :
    hK (Complex.I * (y : ℂ)) = -(2 * Complex.I / (π : ℂ)) * (besselK0 y : ℂ) := by
  have e : -Complex.I * (Complex.I * (y : ℂ)) = (y : ℂ) := by
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  show -(2 * Complex.I / (π : ℂ)) * cK0 (-Complex.I * (Complex.I * (y : ℂ)))
    = -(2 * Complex.I / (π : ℂ)) * (besselK0 y : ℂ)
  rw [e, cK0_ofReal]

end Tower.RV6
