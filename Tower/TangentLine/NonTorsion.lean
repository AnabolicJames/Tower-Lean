import Mathlib
import Tower.TangentLine.Red103
import Tower.TangentLine.Red373
import Tower.TangentLine.Red499

/-!
# The points over the roots of `Q₄` have infinite order (conditional on reduction maps)

This file is generated.  Setting: `K` a field, `A` a commutative ring with `ι : A → K`, `W` a
Weierstrass curve over `K`; `w, t, y, X, Y ∈ A` with `Q₄(t, w) = 0`, `G(t, y) = 0`,
`F(t, y, w) = 0`, `X t y = -1`, `2 Y = (y - t) X (X - 1)`, so that `(ι X, ι Y)` is the point
of `W` over the root `t` (see `equation_of_link` for the curve).

**Assumed, not proved:** reduction maps at two primes, as `Tower.EC.Reduction` packages
(homomorphism; reduces integral coordinates; torsion in the kernel is `p`-primary).
**Proved:** under these, the point has infinite order, and so does the difference of the
points over two distinct roots.  The orders of the reductions are computed in
`Orders*.lean`; they differ at the two primes, which no torsion point allows.
-/

namespace Tower.TangentLine

open WeierstrassCurve.Affine Tower.EC

variable {K A : Type*} [Field K] [DecidableEq K] [CommRing A] {ι : A →+* K}
  {W : WeierstrassCurve.Affine K}

/-- **Infinite order.**  Given reduction packages at `103` (with `w ↦ 56`) and `373`
(with `w ↦ 284`), the point over a root of `Q₄` is not a torsion point: its reductions have
orders in `{6, 24, 40, 120}` and `{80, 400}`. -/
theorem addOrderOf_eq_zero_of_reductions
    (R₁ : Reduction ι W 103 P103.E) (R₂ : Reduction ι W 373 P373.E) {w t y X Y : A}
    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)
    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))
    (hw₁ : R₁.res w = 56) (hw₂ : R₂.res w = 284) (h : W.Nonsingular (ι X) (ι Y)) :
    addOrderOf (Point.some (ι X) (ι Y) h) = 0 := by
  have h₁ := P103.red_order R₁ hQ hG hF hX hY hw₁ h
  have h₂ := P373.red_order R₂ hQ hG hF hX hY hw₂ h
  rcases h₁ with e₁ | e₁ | e₁ | e₁ <;> rcases h₂ with e₂ | e₂ <;>
    exact addOrderOf_eq_zero_of_two_reductions R₁.red R₂.red (p₁ := 103) (p₂ := 373)
      (by norm_num) (by norm_num) (by norm_num) R₁.ker_torsion R₂.ker_torsion _ e₁ e₂
      (by norm_num) (by norm_num) (by norm_num)

/-- **Non-torsion differences.**  Given reduction packages at `103` (with `w ↦ 56`) and
`499` (with `w ↦ 359`), the difference of the points over two distinct roots of `Q₄` is not a
torsion point: its reductions have orders in `{8, 20, 30, 40, 60, 120}` and
`{62, 124, 248}`. -/
theorem sub_addOrderOf_eq_zero_of_reductions [IsDomain A]
    (R₁ : Reduction ι W 103 P103.E) (R₂ : Reduction ι W 499 P499.E)
    {w t y X Y t' y' X' Y' : A}
    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)
    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))
    (hQ' : Q4 t' w = 0) (hG' : G t' y' = 0) (hF' : F t' y' w = 0)
    (hX' : X' * (t' * y') = -1) (hY' : 2 * Y' = (y' - t') * X' * (X' - 1))
    (hne : t ≠ t') (hw₁ : R₁.res w = 56) (hw₂ : R₂.res w = 359)
    (h : W.Nonsingular (ι X) (ι Y)) (h' : W.Nonsingular (ι X') (ι Y')) :
    addOrderOf (Point.some (ι X) (ι Y) h - Point.some (ι X') (ι Y') h') = 0 := by
  have h₁ := P103.red_sub_order R₁ hQ hG hF hX hY hQ' hG' hF' hX' hY' hne hw₁ h h'
  have h₂ := P499.red_sub_order R₂ hQ hG hF hX hY hQ' hG' hF' hX' hY' hne hw₂ h h'
  rcases h₁ with e₁ | e₁ | e₁ | e₁ | e₁ | e₁ <;> rcases h₂ with e₂ | e₂ | e₂ <;>
    exact addOrderOf_eq_zero_of_two_reductions R₁.red R₂.red (p₁ := 103) (p₂ := 499)
      (by norm_num) (by norm_num) (by norm_num) R₁.ker_torsion R₂.ker_torsion _ e₁ e₂
      (by norm_num) (by norm_num) (by norm_num)

end Tower.TangentLine
