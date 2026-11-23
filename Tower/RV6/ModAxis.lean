import Mathlib
import Tower.RV6.AxisEv

/-!
# The four functions of the modular side of Rung B on the imaginary axis

With `e_d = E₂(i d y)` (`E2im (d * y)` of `EisAxis.lean`):

* `Zax = (e₁ - 4e₂ - 3e₃ + 12e₆)/6`, the weight-two form `η(τ)⁴η(3τ)⁴/(η(2τ)²η(6τ)²)` of the
  paper (here it is *defined* as this Eisenstein combination; no eta product is used);
* `Uax = (-e₁ + e₂ + 3e₃ - 3e₆)/24`, the form `x² Z/64`;
* `Pax = -e₁ + 2e₂ - 3e₃ + 6e₆`, the paper's `P`;
* `Eax = (e₁ - e₂ + 3e₃ - 3e₆)/6`, the logarithmic derivative `q d/dq log Z`.

Proved here, from the relations `axis_Rf1 … axis_Rf9` and Ramanujan's identity on the axis:

* `Pax_sq : P² = 16 Z² + 320 Z U + 1024 U²` (so `P = (Z/2) √((x²+4)(x²+16))` with
  `x² = 64U/Z`);
* `hasDerivAt_Zax : Z' = -2π Z E`,  `hasDerivAt_Uax : U' = -2π U (E + P/4)`,
  `hasDerivAt_Eax : E' = -2π (E²/2 - 4ZU - 32U²)`;
* `g4_eq_UP : g₄(iy) = 8 U P` for the `g₄` of `Defs.lean`.

This file is written by `tools/gen_modaxis.py`; the constants of every `linear_combination` are
computed and checked there in exact arithmetic.
-/

namespace Tower.RV6

open Real

/-! ## The derivative of `E₂(i d y)` -/

/-- Ramanujan's identity as a derivative on the axis: `d/dy E₂(iy) = -(π/6)(E₂² - E₄)`. -/
theorem hasDerivAt_E2im {y : ℝ} (hy : 0 < y) :
    HasDerivAt E2im (-(π / 6) * (E2im y ^ 2 - E4im y)) y := by
  have h := hasDerivAt_const_add_qa (polyBdd_sig 1) (g := E2im) (a := 1) (b := -24)
    (fun t ht => by rw [E2im_eq_qa ht]; ring) hy
  have r := ram2_axis hy
  have e : -(2 * π) * (-24 * qa (fun n => (n : ℝ) * sig 1 n) y)
      = -(π / 6) * (E2im y ^ 2 - E4im y) := by
    linear_combination (-(2 * π)) * r
  exact h.congr_deriv e

/-- The derivative of `E₂(iy)` in `y`. -/
noncomputable def dE1 (y : ℝ) : ℝ := -(π / 6) * (E2im y ^ 2 - E4im y)

/-- The derivative of `E₂(i d y)` in `y`. -/
noncomputable def dE2 (d y : ℝ) : ℝ := -(π * d / 6) * (E2im (d * y) ^ 2 - E4im (d * y))

theorem hasDerivAt_E2im_mul (d : ℝ) (hd : 0 < d) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => E2im (d * t)) (dE2 d y) y := by
  have h0 := hasDerivAt_E2im (mul_pos hd hy)
  have hlin : HasDerivAt (fun t : ℝ => d * t) (d * 1) y := (hasDerivAt_id' y).const_mul d
  have hc := HasDerivAt.comp y h0 hlin
  have e : -(π / 6) * (E2im (d * y) ^ 2 - E4im (d * y)) * (d * 1)
      = -(π * d / 6) * (E2im (d * y) ^ 2 - E4im (d * y)) := by ring
  have hc2 := hc.congr_deriv e
  exact hc2

/-! ## The four functions -/

/-- `Z(iy) = (E₂(iy) - 4E₂(2iy) - 3E₂(3iy) + 12E₂(6iy))/6`. -/
noncomputable def Zax (y : ℝ) : ℝ :=
  (E2im y - 4 * E2im (2 * y) - 3 * E2im (3 * y) + 12 * E2im (6 * y)) / 6

/-- `U(iy) = (-E₂(iy) + E₂(2iy) + 3E₂(3iy) - 3E₂(6iy))/24`. -/
noncomputable def Uax (y : ℝ) : ℝ :=
  (-E2im y + E2im (2 * y) + 3 * E2im (3 * y) - 3 * E2im (6 * y)) / 24

/-- `P(iy) = -E₂(iy) + 2E₂(2iy) - 3E₂(3iy) + 6E₂(6iy)`. -/
noncomputable def Pax (y : ℝ) : ℝ :=
  -E2im y + 2 * E2im (2 * y) - 3 * E2im (3 * y) + 6 * E2im (6 * y)

/-- `E(iy) = (E₂(iy) - E₂(2iy) + 3E₂(3iy) - 3E₂(6iy))/6`. -/
noncomputable def Eax (y : ℝ) : ℝ :=
  (E2im y - E2im (2 * y) + 3 * E2im (3 * y) - 3 * E2im (6 * y)) / 6

/-- The quadratic relation of level six: `P² = 16 Z² + 320 Z U + 1024 U²`. -/
theorem Pax_sq {y : ℝ} (hy : 0 < y) :
    Pax y ^ 2 = 16 * Zax y ^ 2 + 320 * Zax y * Uax y + 1024 * Uax y ^ 2 := by
  unfold Pax Zax Uax
  linear_combination axis_Rf9 hy

/-- `Z' = -2π Z E`. -/
theorem hasDerivAt_Zax {y : ℝ} (hy : 0 < y) :
    HasDerivAt Zax (-(2 * π) * (Zax y * Eax y)) y := by
  have h1 : HasDerivAt E2im (dE1 y) y := hasDerivAt_E2im hy
  have h2 := hasDerivAt_E2im_mul 2 (by norm_num) hy
  have h3 := hasDerivAt_E2im_mul 3 (by norm_num) hy
  have h6 := hasDerivAt_E2im_mul 6 (by norm_num) hy
  have k1 : HasDerivAt
      (fun t : ℝ => E2im t)
      (dE1 y) y := h1
  have k2 : HasDerivAt
      (fun t : ℝ => E2im t - 4 * E2im (2 * t))
      (dE1 y - 4 * dE2 2 y) y := k1.sub (h2.const_mul 4)
  have k3 : HasDerivAt
      (fun t : ℝ => E2im t - 4 * E2im (2 * t) - 3 * E2im (3 * t))
      (dE1 y - 4 * dE2 2 y - 3 * dE2 3 y) y := k2.sub (h3.const_mul 3)
  have k4 : HasDerivAt
      (fun t : ℝ => E2im t - 4 * E2im (2 * t) - 3 * E2im (3 * t) + 12 * E2im (6 * t))
      (dE1 y - 4 * dE2 2 y - 3 * dE2 3 y + 12 * dE2 6 y) y := k3.add (h6.const_mul 12)
  have k5 : HasDerivAt
      (fun t : ℝ => (E2im t - 4 * E2im (2 * t) - 3 * E2im (3 * t) + 12 * E2im (6 * t)) / 6)
      ((dE1 y - 4 * dE2 2 y - 3 * dE2 3 y + 12 * dE2 6 y) / 6) y := k4.div_const 6
  have kf : HasDerivAt Zax
      ((dE1 y - 4 * dE2 2 y - 3 * dE2 3 y + 12 * dE2 6 y) / 6) y := k5
  have e : (dE1 y - 4 * dE2 2 y - 3 * dE2 3 y + 12 * dE2 6 y) / 6
      = -(2 * π) * (Zax y * Eax y) := by
    unfold dE1 dE2 Zax Eax
    linear_combination (-(2 * π)) * ((-1 / 72 : ℝ) * axis_Rf1 hy + (1 / 36 : ℝ) * axis_Rf2 hy
      + (1 / 24 : ℝ) * axis_Rf3 hy + (-1 / 12 : ℝ) * axis_Rf4 hy
      + (-1 / 72 : ℝ) * axis_Rf9 hy)
  exact kf.congr_deriv e

/-- `U' = -2π U (E + P/4)`. -/
theorem hasDerivAt_Uax {y : ℝ} (hy : 0 < y) :
    HasDerivAt Uax (-(2 * π) * (Uax y * (Eax y + Pax y / 4))) y := by
  have h1 : HasDerivAt E2im (dE1 y) y := hasDerivAt_E2im hy
  have h2 := hasDerivAt_E2im_mul 2 (by norm_num) hy
  have h3 := hasDerivAt_E2im_mul 3 (by norm_num) hy
  have h6 := hasDerivAt_E2im_mul 6 (by norm_num) hy
  have k1 : HasDerivAt
      (fun t : ℝ => -E2im t)
      (-dE1 y) y := h1.neg
  have k2 : HasDerivAt
      (fun t : ℝ => -E2im t + E2im (2 * t))
      (-dE1 y + dE2 2 y) y := k1.add h2
  have k3 : HasDerivAt
      (fun t : ℝ => -E2im t + E2im (2 * t) + 3 * E2im (3 * t))
      (-dE1 y + dE2 2 y + 3 * dE2 3 y) y := k2.add (h3.const_mul 3)
  have k4 : HasDerivAt
      (fun t : ℝ => -E2im t + E2im (2 * t) + 3 * E2im (3 * t) - 3 * E2im (6 * t))
      (-dE1 y + dE2 2 y + 3 * dE2 3 y - 3 * dE2 6 y) y := k3.sub (h6.const_mul 3)
  have k5 : HasDerivAt
      (fun t : ℝ => (-E2im t + E2im (2 * t) + 3 * E2im (3 * t) - 3 * E2im (6 * t)) / 24)
      ((-dE1 y + dE2 2 y + 3 * dE2 3 y - 3 * dE2 6 y) / 24) y := k4.div_const 24
  have kf : HasDerivAt Uax
      ((-dE1 y + dE2 2 y + 3 * dE2 3 y - 3 * dE2 6 y) / 24) y := k5
  have e : (-dE1 y + dE2 2 y + 3 * dE2 3 y - 3 * dE2 6 y) / 24
      = -(2 * π) * (Uax y * (Eax y + Pax y / 4)) := by
    unfold dE1 dE2 Uax Eax Pax
    linear_combination (-(2 * π)) * ((1 / 288 : ℝ) * axis_Rf1 hy + (-1 / 576 : ℝ) * axis_Rf2 hy
      + (-1 / 96 : ℝ) * axis_Rf3 hy + (1 / 192 : ℝ) * axis_Rf4 hy
      + (-1 / 144 : ℝ) * axis_Rf9 hy)
  exact kf.congr_deriv e

/-- `E' = -2π (E²/2 - 4ZU - 32U²)`. -/
theorem hasDerivAt_Eax {y : ℝ} (hy : 0 < y) :
    HasDerivAt Eax (-(2 * π) * (Eax y ^ 2 / 2 - 4 * Zax y * Uax y - 32 * Uax y ^ 2)) y := by
  have h1 : HasDerivAt E2im (dE1 y) y := hasDerivAt_E2im hy
  have h2 := hasDerivAt_E2im_mul 2 (by norm_num) hy
  have h3 := hasDerivAt_E2im_mul 3 (by norm_num) hy
  have h6 := hasDerivAt_E2im_mul 6 (by norm_num) hy
  have k1 : HasDerivAt
      (fun t : ℝ => E2im t)
      (dE1 y) y := h1
  have k2 : HasDerivAt
      (fun t : ℝ => E2im t - E2im (2 * t))
      (dE1 y - dE2 2 y) y := k1.sub h2
  have k3 : HasDerivAt
      (fun t : ℝ => E2im t - E2im (2 * t) + 3 * E2im (3 * t))
      (dE1 y - dE2 2 y + 3 * dE2 3 y) y := k2.add (h3.const_mul 3)
  have k4 : HasDerivAt
      (fun t : ℝ => E2im t - E2im (2 * t) + 3 * E2im (3 * t) - 3 * E2im (6 * t))
      (dE1 y - dE2 2 y + 3 * dE2 3 y - 3 * dE2 6 y) y := k3.sub (h6.const_mul 3)
  have k5 : HasDerivAt
      (fun t : ℝ => (E2im t - E2im (2 * t) + 3 * E2im (3 * t) - 3 * E2im (6 * t)) / 6)
      ((dE1 y - dE2 2 y + 3 * dE2 3 y - 3 * dE2 6 y) / 6) y := k4.div_const 6
  have kf : HasDerivAt Eax
      ((dE1 y - dE2 2 y + 3 * dE2 3 y - 3 * dE2 6 y) / 6) y := k5
  have e : (dE1 y - dE2 2 y + 3 * dE2 3 y - 3 * dE2 6 y) / 6
      = -(2 * π) * (Eax y ^ 2 / 2 - 4 * Zax y * Uax y - 32 * Uax y ^ 2) := by
    unfold dE1 dE2 Eax Zax Uax
    linear_combination (-(2 * π)) * ((-1 / 72 : ℝ) * axis_Rf1 hy + (1 / 144 : ℝ) * axis_Rf2 hy
      + (-1 / 24 : ℝ) * axis_Rf3 hy + (1 / 48 : ℝ) * axis_Rf4 hy
      + (1 / 36 : ℝ) * axis_Rf9 hy)
  exact kf.congr_deriv e

/-- `g₄(iy) = 8 U(iy) P(iy)` for the `g₄` of `Defs.lean`. -/
theorem g4_eq_UP {y : ℝ} (hy : 0 < y) : g4 y = 8 * Uax y * Pax y := by
  rw [g4_eq_g4E hy]
  unfold g4E Uax Pax
  linear_combination (2 / 15 : ℝ) * axis_Rf1 hy + (-1 / 30 : ℝ) * axis_Rf2 hy
      + (-2 / 5 : ℝ) * axis_Rf3 hy + (1 / 10 : ℝ) * axis_Rf4 hy
      + (-1 / 3 : ℝ) * axis_Rf9 hy

end Tower.RV6
