import Mathlib

/-!
# The elementary identity behind the Lambert-series interchange

`Φ(m, n; s) = ∫₀^∞ exp(-πm/(3y) - 2πny) y^{s-1} dy`.  The substitution `y = r v` gives
`Φ(r m, n; s) = r^s Φ(m, r n; s)`; with `r = d/a` this is the identity
`Φ(cd, ab; s) = (d/a)^s Φ(ac, bd; s)` that regroups the product of two Lambert series in the
evaluation of the double Eisenstein integral.  No integrability hypothesis is needed.
-/

namespace Tower.RV6

open Real MeasureTheory Set

/-- `Φ(m, n; s) = ∫₀^∞ exp(-πm/(3y) - 2πny) y^{s-1} dy`. -/
noncomputable def Phi (m n s : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), Real.exp (-(π * m) / (3 * y) - 2 * π * n * y) * y ^ (s - 1)

theorem Phi_scale {r : ℝ} (hr : 0 < r) (m n s : ℝ) :
    Phi (r * m) n s = r ^ s * Phi m (r * n) s := by
  unfold Phi
  have key : r * ∫ x in Ioi (0 : ℝ),
        Real.exp (-(π * (r * m)) / (3 * (r * x)) - 2 * π * n * (r * x)) * (r * x) ^ (s - 1)
      = ∫ y in Ioi (0 : ℝ), Real.exp (-(π * (r * m)) / (3 * y) - 2 * π * n * y) * y ^ (s - 1) := by
    have h := integral_comp_mul_left_Ioi'
      (fun y : ℝ => Real.exp (-(π * (r * m)) / (3 * y) - 2 * π * n * y) * y ^ (s - 1)) (0 : ℝ) hr
    rw [mul_zero, smul_eq_mul] at h
    exact h
  have hcongr : ∫ x in Ioi (0 : ℝ),
        Real.exp (-(π * (r * m)) / (3 * (r * x)) - 2 * π * n * (r * x)) * (r * x) ^ (s - 1)
      = ∫ x in Ioi (0 : ℝ),
        r ^ (s - 1) * (Real.exp (-(π * m) / (3 * x) - 2 * π * (r * n) * x) * x ^ (s - 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have e1 : -(π * (r * m)) / (3 * (r * x)) = -(π * m) / (3 * x) := by
      have e : -(π * (r * m)) / (3 * (r * x)) = r * (-(π * m)) / (r * (3 * x)) := by ring
      rw [e, mul_div_mul_left _ _ hr.ne']
    have e2 : 2 * π * n * (r * x) = 2 * π * (r * n) * x := by ring
    show Real.exp (-(π * (r * m)) / (3 * (r * x)) - 2 * π * n * (r * x)) * (r * x) ^ (s - 1)
      = r ^ (s - 1) * (Real.exp (-(π * m) / (3 * x) - 2 * π * (r * n) * x) * x ^ (s - 1))
    rw [e1, e2, Real.mul_rpow hr.le hx0.le]
    ring
  have hpow : r * r ^ (s - 1) = r ^ s := by
    have h := Real.rpow_add_one hr.ne' (s - 1)
    rw [sub_add_cancel] at h
    rw [h]
    ring
  rw [← key, hcongr, integral_const_mul, ← mul_assoc, hpow]

/-- The identity in the form used for the interchange. -/
theorem Phi_swap {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (b c s : ℝ) :
    Phi (c * d) (a * b) s = (d / a) ^ s * Phi (a * c) (b * d) s := by
  have h := Phi_scale (div_pos hd ha) (a * c) (a * b) s
  have e1 : d / a * (a * c) = c * d := by
    rw [← mul_assoc, div_mul_cancel₀ d ha.ne', mul_comm]
  have e2 : d / a * (a * b) = b * d := by
    rw [← mul_assoc, div_mul_cancel₀ d ha.ne', mul_comm]
  rw [e1, e2] at h
  exact h

end Tower.RV6
