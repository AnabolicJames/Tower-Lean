import Mathlib
import Tower.EC.Reduction
import Tower.TangentLine.Orders373

/-!
# Reduction modulo a prime above `373` of the points over the roots of `Q₄`

This file is generated.  Everything here is conditional on a `Tower.EC.Reduction` package
`R` at `373` (an assumption, see `Tower/EC/Reduction.lean`) with `R.res w = 284`.
-/

namespace Tower.TangentLine

namespace P373

open WeierstrassCurve.Affine Tower.EC

variable {K A : Type*} [Field K] [DecidableEq K] [CommRing A] {ι : A →+* K}
  {W : WeierstrassCurve.Affine K}

/-- The reduction of the point over a root of `Q₄` is one of the four listed points. -/
theorem red_eq (R : Reduction ι W 373 E) {w t y X Y : A}
    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)
    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))
    (hw : R.res w = 284) (h : W.Nonsingular (ι X) (ι Y)) :
    (R.res t = 108 ∧ R.red (Point.some (ι X) (ι Y) h) = P1) ∨
    (R.res t = 200 ∧ R.red (Point.some (ι X) (ι Y) h) = P2) ∨
    (R.res t = 336 ∧ R.red (Point.some (ι X) (ι Y) h) = P3) ∨
    (R.res t = 367 ∧ R.red (Point.some (ι X) (ι Y) h) = P4) := by
  have rQ : Q4 (R.res t) (R.res w) = 0 := by rw [Q4_map, hQ, map_zero]
  have rG : G (R.res t) (R.res y) = 0 := by rw [G_map, hG, map_zero]
  have rF : F (R.res t) (R.res y) (R.res w) = 0 := by rw [F_map, hF, map_zero]
  have rX : R.res X * (R.res t * R.res y) = -1 := by
    have e := congrArg R.res hX
    simp only [map_mul, map_neg, map_one] at e
    exact e
  have rY : 2 * R.res Y = (R.res y - R.res t) * R.res X * (R.res X - 1) := by
    have e := congrArg R.res hY
    simp only [map_mul, map_sub, map_one, map_ofNat] at e
    exact e
  rw [hw] at rQ rF
  rcases (Q4_roots _).mp rQ with ht | ht | ht | ht
  · rw [ht] at rG rF rX rY
    obtain ⟨hx, hy⟩ := coords1 _ _ _ rG rF rX rY
    exact Or.inl ⟨ht, R.red_some X Y h _ _ ns_35_369 hx hy⟩
  · rw [ht] at rG rF rX rY
    obtain ⟨hx, hy⟩ := coords2 _ _ _ rG rF rX rY
    exact Or.inr (Or.inl ⟨ht, R.red_some X Y h _ _ ns_155_291 hx hy⟩)
  · rw [ht] at rG rF rX rY
    obtain ⟨hx, hy⟩ := coords3 _ _ _ rG rF rX rY
    exact Or.inr (Or.inr (Or.inl ⟨ht, R.red_some X Y h _ _ ns_269_29 hx hy⟩))
  · rw [ht] at rG rF rX rY
    obtain ⟨hx, hy⟩ := coords4 _ _ _ rG rF rX rY
    exact Or.inr (Or.inr (Or.inr (⟨ht, R.red_some X Y h _ _ ns_5_309 hx hy⟩)))

/-- The order of the reduction of the point over a root of `Q₄` is one of `80, 400`. -/
theorem red_order (R : Reduction ι W 373 E) {w t y X Y : A}
    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)
    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))
    (hw : R.res w = 284) (h : W.Nonsingular (ι X) (ι Y)) :
    addOrderOf (R.red (Point.some (ι X) (ι Y) h)) = 80 ∨
    addOrderOf (R.red (Point.some (ι X) (ι Y) h)) = 400 := by
  rcases red_eq R hQ hG hF hX hY hw h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩
  · rw [e]
    exact Or.inr (P1_addOrderOf)
  · rw [e]
    exact Or.inr (P2_addOrderOf)
  · rw [e]
    exact Or.inr (P3_addOrderOf)
  · rw [e]
    exact Or.inl P4_addOrderOf

end P373

end Tower.TangentLine
