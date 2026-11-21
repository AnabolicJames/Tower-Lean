import Mathlib

/-!
# Tangent lines through a node: elimination and factorisation

Let `E` be the curve `G(x, y) = x y² + (x² + x + 1) y + x = 0`, i.e. `1 + x + 1/x + y + 1/y = 0`
on the torus, and let `B` be its image under `(x, y) ↦ (x⁻², y⁻²)`.  For a primitive cube root
of unity `w`, the point `(-1, w)` is a node of `B`.  On `E`, the tangent line to `B` at the
image of `(x, y)` passes through that node exactly when

`F(x, y) = y (x² - 1)(-x² - 1) + x (y² - 1)(w y² - 1) = 0`.

This file proves, over any commutative ring:

* `pseudo_div`, `res_identity`, `elimination`: `x² · Res(x)` lies in the ideal `(G, F)`,
  where `Res = x² U² - b U V + V²` is the resultant of `G` and `F` in `y`;
* `res_factor`: if `w² + w + 1 = 0` then
  `Res(x) = (1 + w) x³ (x² + 1)² (x + 1) Q₄(x)` with
  `Q₄(t) = t⁴ + (2 + 3w) t³ - t² + (2 + w) t + (1 + w)`;

and over a field (`tangent_through_node`): a common zero of `G` and `F` with `x ≠ 0` has
`x² + 1 = 0`, `x + 1 = 0` or `Q₄(x) = 0`.

The geometric reading of `F` (tangency through the node) is not formalised here; `F` is taken
as the definition of the condition.
-/

namespace Tower.TangentLine

section CommRing

variable {R : Type*} [CommRing R]

/-- `b(x) = x² + x + 1`, the coefficient of `y` in `G`. -/
def bq (x : R) : R := x ^ 2 + x + 1

/-- The curve `E`: `x y² + (x² + x + 1) y + x`. -/
def G (x y : R) : R := x * y ^ 2 + bq x * y + x

/-- The tangency condition through the node `(-1, w)`. -/
def F (x y w : R) : R :=
  y * (x ^ 2 - 1) * (-(x ^ 2) - 1) + x * (y ^ 2 - 1) * (w * y ^ 2 - 1)

/-- Constant coefficient of the remainder of `F` modulo `G` (cleared of denominators). -/
def U (x w : R) : R := x ^ 2 * (2 + 2 * w) - w * (bq x) ^ 2

/-- Linear coefficient of the remainder of `F` modulo `G` (cleared of denominators). -/
def V (x w : R) : R :=
  x ^ 2 * bq x * (1 + 3 * w) - w * (bq x) ^ 3 + x ^ 2 * (x ^ 2 - 1) * (-(x ^ 2) - 1)

/-- The linear form `x U + V y`: the remainder of `x² F` modulo `G`. -/
def L (x y w : R) : R := x * U x w + V x w * y

/-- The resultant of `G` and `F` with respect to `y`. -/
def Res (x w : R) : R := x ^ 2 * (U x w) ^ 2 - bq x * U x w * V x w + (V x w) ^ 2

/-- The quartic whose roots are the non-trivial tangency points. -/
def Q4 (x w : R) : R := x ^ 4 + (2 + 3 * w) * x ^ 3 - x ^ 2 + (2 + w) * x + (1 + w)

/-- The quotient in the pseudo-division of `x³ F` by `G` with respect to `y`. -/
def Quo (x y w : R) : R :=
  w * x ^ 3 * y ^ 2 - w * x ^ 4 * y - w * x ^ 3 * y - w * x ^ 2 * y + w * x ^ 5
    + 2 * w * x ^ 4 + w * x ^ 3 + 2 * w * x ^ 2 + w * x - x ^ 3

/-- Pseudo-division: `x³ F = Quo · G + x · L`. -/
theorem pseudo_div (x y w : R) :
    x ^ 3 * F x y w = Quo x y w * G x y + x * L x y w := by
  simp only [F, Quo, G, L, U, V, bq]
  ring

/-- `x · Res` in terms of `G` and the linear remainder `L`. -/
theorem res_identity (x y w : R) :
    x * Res x w =
      (V x w) ^ 2 * G x y
        - L x y w * (x * L x y w - 2 * x ^ 2 * U x w + bq x * V x w) := by
  simp only [Res, G, L]
  ring

/-- Elimination of `y`: on the common zeros of `G` and `F`, `x² · Res(x) = 0`. -/
theorem elimination (x y w : R) (hG : G x y = 0) (hF : F x y w = 0) :
    x ^ 2 * Res x w = 0 := by
  have h1 := pseudo_div x y w
  have h2 := res_identity x y w
  linear_combination x * h2
    + (x * L x y w - 2 * x ^ 2 * U x w + bq x * V x w) * h1
    + (x * (V x w) ^ 2
        + (x * L x y w - 2 * x ^ 2 * U x w + bq x * V x w) * Quo x y w) * hG
    - ((x * L x y w - 2 * x ^ 2 * U x w + bq x * V x w) * x ^ 3) * hF

/-- Factorisation of the resultant when `w` is a primitive cube root of unity. -/
theorem res_factor (x w : R) (hw : w ^ 2 + w + 1 = 0) :
    Res x w = (1 + w) * x ^ 3 * ((x ^ 2 + 1) * (x ^ 2 + 1)) * (x + 1) * Q4 x w := by
  simp only [Res, U, V, bq, Q4]
  linear_combination
    (-3 * x ^ 11 - 3 * x ^ 10 - 7 * x ^ 9 - 9 * x ^ 8 - 8 * x ^ 7 - 6 * x ^ 6 - 5 * x ^ 5
      - 3 * x ^ 4 - x ^ 3) * hw

end CommRing

section Field

variable {K : Type*} [Field K]

/-- `1 + w` is non-zero when `w² + w + 1 = 0` (indeed `(1 + w)(-w) = 1`). -/
theorem one_add_ne_zero (w : K) (hw : w ^ 2 + w + 1 = 0) : (1 + w) ≠ 0 := by
  intro h0
  have h1 : (1 : K) = 0 := by linear_combination hw - w * h0
  exact one_ne_zero h1

/-- A point of `E` on the torus whose tangent line passes through the node `(-1, w)` lies over
the node (`x² + 1 = 0`), is the axis-parallel tangency (`x + 1 = 0`), or is a root of `Q₄`. -/
theorem tangent_through_node (x y w : K) (hw : w ^ 2 + w + 1 = 0) (hx : x ≠ 0)
    (hG : G x y = 0) (hF : F x y w = 0) :
    x ^ 2 + 1 = 0 ∨ x + 1 = 0 ∨ Q4 x w = 0 := by
  have h := elimination x y w hG hF
  have hf := res_factor x w hw
  have hu : (1 + w) ≠ 0 := one_add_ne_zero w hw
  have key :
      (x ^ 2 * ((1 + w) * x ^ 3)) * ((x ^ 2 + 1) * ((x ^ 2 + 1) * ((x + 1) * Q4 x w))) = 0 := by
    linear_combination h - x ^ 2 * hf
  have hc : x ^ 2 * ((1 + w) * x ^ 3) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx) (mul_ne_zero hu (pow_ne_zero 3 hx))
  rcases mul_eq_zero.mp key with h1 | h1
  · exact absurd h1 hc
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact Or.inl h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr h4)

end Field

end Tower.TangentLine
