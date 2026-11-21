import Mathlib

/-!
# Certificates for the group law on a Weierstrass curve

Mathlib's addition of points divides by `x₁ - x₂` or `y₁ - negY`.  The lemmas here replace the
division by a slope certificate `ℓ` with `ℓ * (x₁ - x₂) = y₁ - y₂`, so that every side condition
of an explicit computation in `E(𝔽_p)` is an equation or inequation between ring expressions and
can be checked by `decide`.  The conclusions are statements about Mathlib's own group
`WeierstrassCurve.Affine.Point`.
-/

namespace Tower.EC

open WeierstrassCurve.Affine

section

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-- Nonsingularity from the explicit Weierstrass equation and partial derivatives. -/
theorem nonsingular_of {x y : F}
    (he : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (hs : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 ∨ 2 * y + W.a₁ * x + W.a₃ ≠ 0) :
    W.Nonsingular x y :=
  (nonsingular_iff' x y).mpr ⟨(equation_iff x y).mpr he, hs⟩

/-- Chord addition with a slope certificate. -/
theorem add_cert {x₁ y₁ x₂ y₂ x₃ y₃ ℓ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂) (h₃ : W.Nonsingular x₃ y₃)
    (hx : x₁ ≠ x₂) (hℓ : ℓ * (x₁ - x₂) = y₁ - y₂)
    (hx₃ : W.addX x₁ x₂ ℓ = x₃) (hy₃ : W.addY x₁ x₂ y₁ ℓ = y₃) :
    Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ := by
  have hs : W.slope x₁ x₂ y₁ y₂ = ℓ := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
    exact hℓ.symm
  subst hs
  subst hx₃
  subst hy₃
  exact Point.add_of_X_ne hx

/-- Doubling with a slope certificate. -/
theorem dbl_cert {x₁ y₁ x₃ y₃ ℓ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₃ : W.Nonsingular x₃ y₃)
    (hy : y₁ ≠ W.negY x₁ y₁)
    (hℓ : ℓ * (y₁ - W.negY x₁ y₁) = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁)
    (hx₃ : W.addX x₁ x₁ ℓ = x₃) (hy₃ : W.addY x₁ x₁ y₁ ℓ = y₃) :
    Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ = Point.some x₃ y₃ h₃ := by
  have hs : W.slope x₁ x₁ y₁ y₁ = ℓ := by
    rw [slope_of_Y_ne rfl hy, div_eq_iff (sub_ne_zero.mpr hy)]
    exact hℓ.symm
  subst hs
  subst hx₃
  subst hy₃
  exact Point.add_self_of_Y_ne hy

/-- The sum of a point and its negative. -/
theorem add_zero_cert {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) :
    Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = 0 :=
  Point.add_of_Y_eq hx hy

end

/-- One step of an addition chain for multiples. -/
theorem nsmul_step {A : Type*} [AddMonoid A] {P Pm Pn Pk : A} {m n k : ℕ}
    (hm : m • P = Pm) (hn : n • P = Pn) (hadd : Pm + Pn = Pk) (hk : m + n = k) :
    k • P = Pk := by
  subst hk
  rw [add_nsmul, hm, hn, hadd]

end Tower.EC
