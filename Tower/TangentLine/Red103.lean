import Mathlib
import Tower.EC.Reduction
import Tower.TangentLine.Orders103

/-!
# Reduction modulo a prime above `103` of the points over the roots of `Q₄`

This file is generated.  Everything here is conditional on a `Tower.EC.Reduction` package
`R` at `103` (an assumption, see `Tower/EC/Reduction.lean`) with `R.res w = 56`.
-/

namespace Tower.TangentLine

namespace P103

open WeierstrassCurve.Affine Tower.EC

variable {K A : Type*} [Field K] [DecidableEq K] [CommRing A] {ι : A →+* K}
  {W : WeierstrassCurve.Affine K}

/-- The reduction of the point over a root of `Q₄` is one of the four listed points. -/
theorem red_eq (R : Reduction ι W 103 E) {w t y X Y : A}
    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)
    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))
    (hw : R.res w = 56) (h : W.Nonsingular (ι X) (ι Y)) :
    (R.res t = 2 ∧ R.red (Point.some (ι X) (ι Y) h) = P1) ∨
    (R.res t = 41 ∧ R.red (Point.some (ι X) (ι Y) h) = P2) ∨
    (R.res t = 99 ∧ R.red (Point.some (ι X) (ι Y) h) = P3) ∨
    (R.res t = 100 ∧ R.red (Point.some (ι X) (ι Y) h) = P4) := by
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
    exact Or.inl ⟨ht, R.red_some X Y h _ _ ns_6_46 hx hy⟩
  · rw [ht] at rG rF rX rY
    obtain ⟨hx, hy⟩ := coords2 _ _ _ rG rF rX rY
    exact Or.inr (Or.inl ⟨ht, R.red_some X Y h _ _ ns_89_35 hx hy⟩)
  · rw [ht] at rG rF rX rY
    obtain ⟨hx, hy⟩ := coords3 _ _ _ rG rF rX rY
    exact Or.inr (Or.inr (Or.inl ⟨ht, R.red_some X Y h _ _ ns_99_78 hx hy⟩))
  · rw [ht] at rG rF rX rY
    obtain ⟨hx, hy⟩ := coords4 _ _ _ rG rF rX rY
    exact Or.inr (Or.inr (Or.inr (⟨ht, R.red_some X Y h _ _ ns_61_41 hx hy⟩)))

/-- The order of the reduction of the point over a root of `Q₄` is one of `6, 24, 40, 120`. -/
theorem red_order (R : Reduction ι W 103 E) {w t y X Y : A}
    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)
    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))
    (hw : R.res w = 56) (h : W.Nonsingular (ι X) (ι Y)) :
    addOrderOf (R.red (Point.some (ι X) (ι Y) h)) = 6 ∨
    addOrderOf (R.red (Point.some (ι X) (ι Y) h)) = 24 ∨
    addOrderOf (R.red (Point.some (ι X) (ι Y) h)) = 40 ∨
    addOrderOf (R.red (Point.some (ι X) (ι Y) h)) = 120 := by
  rcases red_eq R hQ hG hF hX hY hw h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩
  · rw [e]
    exact Or.inr (Or.inr (Or.inr (P1_addOrderOf)))
  · rw [e]
    exact Or.inr (Or.inr (Or.inl P2_addOrderOf))
  · rw [e]
    exact Or.inr (Or.inl P3_addOrderOf)
  · rw [e]
    exact Or.inl P4_addOrderOf

/-- For two distinct roots, the order of the reduction of the difference of the two points is
one of `8, 20, 30, 40, 60, 120`. -/
theorem red_sub_order [IsDomain A] (R : Reduction ι W 103 E) {w t y X Y t' y' X' Y' : A}
    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)
    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))
    (hQ' : Q4 t' w = 0) (hG' : G t' y' = 0) (hF' : F t' y' w = 0)
    (hX' : X' * (t' * y') = -1) (hY' : 2 * Y' = (y' - t') * X' * (X' - 1))
    (hne : t ≠ t') (hw : R.res w = 56)
    (h : W.Nonsingular (ι X) (ι Y)) (h' : W.Nonsingular (ι X') (ι Y')) :
    addOrderOf (R.red (Point.some (ι X) (ι Y) h - Point.some (ι X') (ι Y') h')) = 8 ∨
    addOrderOf (R.red (Point.some (ι X) (ι Y) h - Point.some (ι X') (ι Y') h')) = 20 ∨
    addOrderOf (R.red (Point.some (ι X) (ι Y) h - Point.some (ι X') (ι Y') h')) = 30 ∨
    addOrderOf (R.red (Point.some (ι X) (ι Y) h - Point.some (ι X') (ι Y') h')) = 40 ∨
    addOrderOf (R.red (Point.some (ι X) (ι Y) h - Point.some (ι X') (ι Y') h')) = 60 ∨
    addOrderOf (R.red (Point.some (ι X) (ι Y) h - Point.some (ι X') (ι Y') h')) = 120 := by
  have hd : dQ4 (R.res t) (R.res t') 56 = 0 := by
    rw [← hw, dQ4_map, dQ4_eq_zero hQ hQ' hne, map_zero]
  have hs : R.red (Point.some (ι X) (ι Y) h - Point.some (ι X') (ι Y') h') =
      R.red (Point.some (ι X) (ι Y) h) - R.red (Point.some (ι X') (ι Y') h') := map_sub R.red _ _
  rw [hs]
  rcases red_eq R hQ hG hF hX hY hw h with ⟨a, e⟩ | ⟨a, e⟩ | ⟨a, e⟩ | ⟨a, e⟩
  · rcases red_eq R hQ' hG' hF' hX' hY' hw h' with ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩
    · rw [a, a'] at hd
      exact absurd hd diag1
    · rw [e, e']
      exact Or.inr (Or.inr (Or.inl P1_sub_P2_addOrderOf))
    · rw [e, e']
      exact Or.inr (Or.inl P1_sub_P3_addOrderOf)
    · rw [e, e']
      exact Or.inr (Or.inr (Or.inr (Or.inl P1_sub_P4_addOrderOf)))
  · rcases red_eq R hQ' hG' hF' hX' hY' hw h' with ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩
    · rw [e, e']
      exact Or.inr (Or.inr (Or.inl P2_sub_P1_addOrderOf))
    · rw [a, a'] at hd
      exact absurd hd diag2
    · rw [e, e']
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl P2_sub_P3_addOrderOf))))
    · rw [e, e']
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (P2_sub_P4_addOrderOf)))))
  · rcases red_eq R hQ' hG' hF' hX' hY' hw h' with ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩
    · rw [e, e']
      exact Or.inr (Or.inl P3_sub_P1_addOrderOf)
    · rw [e, e']
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl P3_sub_P2_addOrderOf))))
    · rw [a, a'] at hd
      exact absurd hd diag3
    · rw [e, e']
      exact Or.inl P3_sub_P4_addOrderOf
  · rcases red_eq R hQ' hG' hF' hX' hY' hw h' with ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩
    · rw [e, e']
      exact Or.inr (Or.inr (Or.inr (Or.inl P4_sub_P1_addOrderOf)))
    · rw [e, e']
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (P4_sub_P2_addOrderOf)))))
    · rw [e, e']
      exact Or.inl P4_sub_P3_addOrderOf
    · rw [a, a'] at hd
      exact absurd hd diag4

end P103

end Tower.TangentLine
