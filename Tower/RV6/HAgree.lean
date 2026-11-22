import Mathlib
import Tower.RV6.Defs
import Tower.RV6.CKernel
import Tower.RV6.CKZero

/-!
# Complex kernels for the rotation of the contour, IV: the two forms of `H₀⁽¹⁾` agree

**`hE_eq_hK`**: `hE z = hK z` for `Re z > 0` and `Im z > 0`.

The entire function `w ↦ exp(z sinh w)` is integrated over the boundary of the rectangle
`[-R, 0] × [0, π/2]` (Mathlib's Cauchy–Goursat theorem for rectangles):

`∫_{-R}^0 e^{z sinh x} dx - ∫_{-R}^0 e^{iz cosh x} dx + i ∫₀^{π/2} e^{iz sin t} dt - i ∫₀^{π/2} e^{z sinh(-R + it)} dt = 0`

(`sinh(x + iπ/2) = i cosh x`, `sinh(it) = i sin t`).  On the side `Re w = -R`,
`Re(z sinh(-R + it)) = -Re z · sinh R cos t - Im z · cosh R sin t ≤ -min(Re z, Im z) R`
(`cos t + sin t ≥ cos² t + sin² t = 1` on `[0, π/2]`, `sinh R ≥ R`), so the last term tends to `0`.
The first tends to `kerB z`, the second to `∫₀^∞ e^{iz cosh u} du = cK0(-iz)` (reflection).
Hence `cK0(-iz) = kerB z + i kerA z` (`cK0_neg_I_mul_eq`), which is `hK z = hE z`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## `sinh` on the sides of the rectangle -/

theorem sinh_add_mul_I (a b : ℝ) :
    Complex.sinh ((a : ℂ) + (b : ℂ) * Complex.I)
      = ((Real.sinh a * Real.cos b : ℝ) : ℂ)
        + ((Real.cosh a * Real.sin b : ℝ) : ℂ) * Complex.I := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.ofReal_mul,
    Complex.ofReal_mul, Complex.ofReal_sinh, Complex.ofReal_cos, Complex.ofReal_cosh,
    Complex.ofReal_sin]
  ring

theorem cexp_mul_sinh_bottom (z : ℂ) (x : ℝ) :
    Complex.exp (z * Complex.sinh ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I))
      = Complex.exp (z * (Real.sinh x : ℂ)) := by
  rw [sinh_add_mul_I, Real.cos_zero, Real.sin_zero, mul_one (Real.sinh x),
    mul_zero (Real.cosh x), Complex.ofReal_zero, zero_mul, add_zero]

theorem cexp_mul_sinh_top (z : ℂ) (x : ℝ) :
    Complex.exp (z * Complex.sinh ((x : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I))
      = Complex.exp (Complex.I * z * (Real.cosh x : ℂ)) := by
  have e : z * ((Real.cosh x : ℂ) * Complex.I) = Complex.I * z * (Real.cosh x : ℂ) := by ring
  rw [sinh_add_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero (Real.sinh x),
    mul_one (Real.cosh x), Complex.ofReal_zero, zero_add, e]

theorem cexp_mul_sinh_left (z : ℂ) (y : ℝ) :
    Complex.exp (z * Complex.sinh (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = Complex.exp (Complex.I * z * (Real.sin y : ℂ)) := by
  have e : z * ((Real.sin y : ℂ) * Complex.I) = Complex.I * z * (Real.sin y : ℂ) := by ring
  rw [sinh_add_mul_I, Real.sinh_zero, Real.cosh_zero, zero_mul (Real.cos y),
    one_mul (Real.sin y), Complex.ofReal_zero, zero_add, e]

theorem re_mul_sinh_add_mul_I (z : ℂ) (a b : ℝ) :
    (z * Complex.sinh ((a : ℂ) + (b : ℂ) * Complex.I)).re
      = z.re * (Real.sinh a * Real.cos b) - z.im * (Real.cosh a * Real.sin b) := by
  rw [sinh_add_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im]
  ring

/-- On the side `Re w = -R`: `Re(z sinh(-R + iy)) ≤ -(m R)` for `0 ≤ y ≤ π/2`, when
`0 < m ≤ Re z` and `m ≤ Im z`. -/
theorem re_mul_sinh_side_le {z : ℂ} {m R y : ℝ} (hm : 0 < m) (hmx : m ≤ z.re) (hmy : m ≤ z.im)
    (hR : 0 ≤ R) (hy0 : 0 ≤ y) (hy1 : y ≤ π / 2) :
    (z * Complex.sinh (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re ≤ -(m * R) := by
  rw [re_mul_sinh_add_mul_I, Real.sinh_neg, Real.cosh_neg]
  have hpi : 0 < π := Real.pi_pos
  have hc : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hy1⟩
  have hs : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith)
  have hc1 : Real.cos y ≤ 1 := Real.cos_le_one y
  have hs1 : Real.sin y ≤ 1 := Real.sin_le_one y
  have hpy : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  have h1 : 0 ≤ Real.cos y * (1 - Real.cos y) := mul_nonneg hc (sub_nonneg.mpr hc1)
  have h2 : 0 ≤ Real.sin y * (1 - Real.sin y) := mul_nonneg hs (sub_nonneg.mpr hs1)
  have hcs : 1 ≤ Real.cos y + Real.sin y := by linarith
  have hsh : R ≤ Real.sinh R := Real.self_le_sinh_iff.mpr hR
  have hsh0 : 0 ≤ Real.sinh R := le_trans hR hsh
  have hch : Real.sinh R ≤ Real.cosh R := (Real.sinh_lt_cosh R).le
  have hy' : 0 ≤ z.im := le_trans hm.le hmy
  have p1 : m * (Real.sinh R * Real.cos y) ≤ z.re * (Real.sinh R * Real.cos y) :=
    mul_le_mul_of_nonneg_right hmx (mul_nonneg hsh0 hc)
  have p2 : m * (Real.sinh R * Real.sin y) ≤ z.im * (Real.cosh R * Real.sin y) :=
    mul_le_mul hmy (mul_le_mul_of_nonneg_right hch hs) (mul_nonneg hsh0 hs) hy'
  have p3 : m * Real.sinh R * 1 ≤ m * Real.sinh R * (Real.cos y + Real.sin y) :=
    mul_le_mul_of_nonneg_left hcs (mul_nonneg hm.le hsh0)
  have p4 : m * R ≤ m * Real.sinh R := mul_le_mul_of_nonneg_left hsh hm.le
  linarith

/-! ## The three limits -/

/-- The side `Re w = -R` tends to `0`. -/
theorem tendsto_side_integral {z : ℂ} (hx : 0 < z.re) (hy : 0 < z.im) :
    Filter.Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..(π / 2),
        Complex.exp (z * Complex.sinh (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)))
      Filter.atTop (nhds 0) := by
  have hm : 0 < min z.re z.im := lt_min hx hy
  have hbound : ∀ᶠ R in Filter.atTop, ‖∫ y in (0 : ℝ)..(π / 2),
        Complex.exp (z * Complex.sinh (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖
      ≤ Real.exp (-(min z.re z.im * R)) * (π / 2) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    have hpt : ∀ y ∈ Set.uIoc (0 : ℝ) (π / 2),
        ‖Complex.exp (z * Complex.sinh (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖
          ≤ Real.exp (-(min z.re z.im * R)) := by
      intro y hyI
      rw [Set.uIoc_of_le Real.pi_div_two_pos.le] at hyI
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr
        (re_mul_sinh_side_le hm (min_le_left _ _) (min_le_right _ _) hR hyI.1.le hyI.2)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have h' : ‖∫ y in (0 : ℝ)..(π / 2),
          Complex.exp (z * Complex.sinh (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖
        ≤ Real.exp (-(min z.re z.im * R)) * |π / 2 - 0| := h
    rw [sub_zero, abs_of_pos Real.pi_div_two_pos] at h'
    exact h'
  have hlim0 : Filter.Tendsto (fun R : ℝ => min z.re z.im * R) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hm Filter.tendsto_id
  have hlim1 : Filter.Tendsto (fun R : ℝ => Real.exp (-(min z.re z.im * R)))
      Filter.atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlim0
  have hlim2 : Filter.Tendsto (fun R : ℝ => Real.exp (-(min z.re z.im * R)) * (π / 2))
      Filter.atTop (nhds (0 * (π / 2))) := hlim1.mul_const (π / 2)
  rw [zero_mul] at hlim2
  exact squeeze_zero_norm' hbound hlim2

/-- The bottom side tends to `kerB z`. -/
theorem tendsto_bottom_integral {z : ℂ} (hx : 0 < z.re) :
    Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..0, Complex.exp (z * (Real.sinh x : ℂ)))
      Filter.atTop (nhds (kerB z)) := by
  have hint : IntegrableOn (fun x : ℝ => Complex.exp (z * (Real.sinh x : ℂ)))
      (Set.Iic (0 : ℝ)) := integrable_cexp_mul_sinh hx
  have h : Filter.Tendsto
      (fun R : ℝ => ∫ x in (-R)..0, Complex.exp (z * (Real.sinh x : ℂ))) Filter.atTop
      (nhds (∫ x in Set.Iic (0 : ℝ), Complex.exp (z * (Real.sinh x : ℂ)))) :=
    intervalIntegral_tendsto_integral_Iic 0 hint Filter.tendsto_neg_atTop_atBot
  exact h

/-- Reflection: `∫_{-R}^0 g(cosh x) dx = ∫₀^R g(cosh u) du`. -/
theorem integral_cosh_reflect (g : ℝ → ℂ) (R : ℝ) :
    (∫ x in (-R)..0, g (Real.cosh x)) = ∫ u in (0 : ℝ)..R, g (Real.cosh u) := by
  have h : (∫ x in (0 : ℝ)..R, g (Real.cosh (-x))) = ∫ x in (-R)..(-0), g (Real.cosh x) :=
    intervalIntegral.integral_comp_neg (fun x : ℝ => g (Real.cosh x))
  have hfun : (fun x : ℝ => g (Real.cosh (-x))) = fun x : ℝ => g (Real.cosh x) := by
    funext x
    show g (Real.cosh (-x)) = g (Real.cosh x)
    rw [Real.cosh_neg]
  rw [hfun, neg_zero] at h
  exact h.symm

theorem cK0_neg_I_mul (z : ℂ) :
    cK0 (-Complex.I * z)
      = ∫ u in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * z * (Real.cosh u : ℂ)) := by
  have e : -(-Complex.I * z) = Complex.I * z := by rw [neg_mul, neg_neg]
  show (∫ u in Set.Ioi (0 : ℝ), Complex.exp (-(-Complex.I * z) * (Real.cosh u : ℂ)))
    = ∫ u in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * z * (Real.cosh u : ℂ))
  rw [e]

/-- The top side tends to `cK0(-iz)`. -/
theorem tendsto_top_integral {z : ℂ} (hy : 0 < z.im) :
    Filter.Tendsto
      (fun R : ℝ => ∫ x in (-R)..0, Complex.exp (Complex.I * z * (Real.cosh x : ℂ)))
      Filter.atTop (nhds (cK0 (-Complex.I * z))) := by
  have hre : (Complex.I * z).re < 0 := by
    rw [Complex.I_mul_re]
    linarith
  have hint : IntegrableOn (fun u : ℝ => Complex.exp (Complex.I * z * (Real.cosh u : ℂ)))
      (Set.Ioi (0 : ℝ)) := integrable_cexp_mul_cosh hre
  have h1 : Filter.Tendsto
      (fun R : ℝ => ∫ u in (0 : ℝ)..R, Complex.exp (Complex.I * z * (Real.cosh u : ℂ)))
      Filter.atTop
      (nhds (∫ u in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * z * (Real.cosh u : ℂ)))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint Filter.tendsto_id
  have hfun : (fun R : ℝ => ∫ x in (-R)..0, Complex.exp (Complex.I * z * (Real.cosh x : ℂ)))
      = fun R : ℝ => ∫ u in (0 : ℝ)..R, Complex.exp (Complex.I * z * (Real.cosh u : ℂ)) := by
    funext R
    show (∫ x in (-R)..0, Complex.exp (Complex.I * z * (Real.cosh x : ℂ)))
      = ∫ u in (0 : ℝ)..R, Complex.exp (Complex.I * z * (Real.cosh u : ℂ))
    exact integral_cosh_reflect (fun c : ℝ => Complex.exp (Complex.I * z * (c : ℂ))) R
  rw [hfun, cK0_neg_I_mul]
  exact h1

/-! ## The agreement -/

/-- The rectangle identity for `w ↦ exp(z sinh w)` on `[-R, 0] × [0, π/2]`. -/
theorem rect_cexp_mul_sinh (z : ℂ) (R : ℝ) :
    (∫ x in (-R)..0, Complex.exp (z * (Real.sinh x : ℂ)))
      - (∫ x in (-R)..0, Complex.exp (Complex.I * z * (Real.cosh x : ℂ)))
      + Complex.I * kerA z
      - Complex.I * (∫ y in (0 : ℝ)..(π / 2),
          Complex.exp (z * Complex.sinh (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))) = 0 := by
  have hφ : Differentiable ℂ (fun w : ℂ => Complex.exp (z * Complex.sinh w)) := by
    intro w
    have h1 : HasDerivAt (fun w : ℂ => z * Complex.sinh w) (z * Complex.cosh w) w :=
      (Complex.hasDerivAt_sinh w).const_mul z
    have h2 : HasDerivAt (fun w : ℂ => Complex.exp (z * Complex.sinh w))
        (Complex.exp (z * Complex.sinh w) * (z * Complex.cosh w)) w := h1.cexp
    exact h2.differentiableAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun w : ℂ => Complex.exp (z * Complex.sinh w)) (⟨-R, 0⟩ : ℂ) (⟨0, π / 2⟩ : ℂ)
    hφ.differentiableOn
  have h' : (∫ x in (-R)..(0 : ℝ),
        Complex.exp (z * Complex.sinh ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)))
      - (∫ x in (-R)..(0 : ℝ),
        Complex.exp (z * Complex.sinh ((x : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I)))
      + Complex.I • (∫ y in (0 : ℝ)..(π / 2),
        Complex.exp (z * Complex.sinh (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)))
      - Complex.I • (∫ y in (0 : ℝ)..(π / 2),
        Complex.exp (z * Complex.sinh (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))) = 0 := h
  have e1 : (fun x : ℝ => Complex.exp (z * Complex.sinh ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)))
      = fun x : ℝ => Complex.exp (z * (Real.sinh x : ℂ)) := by
    funext x
    exact cexp_mul_sinh_bottom z x
  have e2 : (fun x : ℝ =>
        Complex.exp (z * Complex.sinh ((x : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I)))
      = fun x : ℝ => Complex.exp (Complex.I * z * (Real.cosh x : ℂ)) := by
    funext x
    exact cexp_mul_sinh_top z x
  have e3 : (fun y : ℝ => Complex.exp (z * Complex.sinh (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)))
      = fun y : ℝ => Complex.exp (Complex.I * z * (Real.sin y : ℂ)) := by
    funext y
    exact cexp_mul_sinh_left z y
  rw [e1, e2, e3, smul_eq_mul, smul_eq_mul] at h'
  exact h'

/-- `K₀(-iz) = kerB z + i kerA z` on the open first quadrant. -/
theorem cK0_neg_I_mul_eq {z : ℂ} (hx : 0 < z.re) (hy : 0 < z.im) :
    cK0 (-Complex.I * z) = kerB z + Complex.I * kerA z := by
  have hT1 := tendsto_bottom_integral hx
  have hT2 := tendsto_top_integral hy
  have hT4 := tendsto_side_integral hx hy
  have hlim : Filter.Tendsto (fun R : ℝ =>
      (∫ x in (-R)..0, Complex.exp (z * (Real.sinh x : ℂ)))
        - (∫ x in (-R)..0, Complex.exp (Complex.I * z * (Real.cosh x : ℂ)))
        + Complex.I * kerA z
        - Complex.I * (∫ y in (0 : ℝ)..(π / 2),
            Complex.exp (z * Complex.sinh (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))))
      Filter.atTop
      (nhds (kerB z - cK0 (-Complex.I * z) + Complex.I * kerA z - Complex.I * 0)) :=
    ((hT1.sub hT2).add tendsto_const_nhds).sub (hT4.const_mul Complex.I)
  have hconst : (fun R : ℝ =>
      (∫ x in (-R)..0, Complex.exp (z * (Real.sinh x : ℂ)))
        - (∫ x in (-R)..0, Complex.exp (Complex.I * z * (Real.cosh x : ℂ)))
        + Complex.I * kerA z
        - Complex.I * (∫ y in (0 : ℝ)..(π / 2),
            Complex.exp (z * Complex.sinh (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))))
      = fun _ : ℝ => (0 : ℂ) := funext (fun R => rect_cexp_mul_sinh z R)
  rw [hconst] at hlim
  have h0 : kerB z - cK0 (-Complex.I * z) + Complex.I * kerA z - Complex.I * 0 = 0 :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  linear_combination (-1 : ℂ) * h0

/-- **The two forms of `H₀⁽¹⁾` agree on the open first quadrant.** -/
theorem hE_eq_hK {z : ℂ} (hx : 0 < z.re) (hy : 0 < z.im) : hE z = hK z := by
  have h := cK0_neg_I_mul_eq hx hy
  show 2 / (π : ℂ) * kerA z - 2 * Complex.I / (π : ℂ) * kerB z
    = -(2 * Complex.I / (π : ℂ)) * cK0 (-Complex.I * z)
  rw [h]
  linear_combination (2 / (π : ℂ) * kerA z) * Complex.I_mul_I

end Tower.RV6
