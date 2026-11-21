import Mathlib
import Tower.TangentLine.Resultant

/-!
# Ring homomorphisms, simple roots, and the Weierstrass model

* `Q4_map`, `G_map`, `F_map`, `dQ4_map`: the polynomials commute with ring homomorphisms.
* `dQ4`: the divided difference of `Q₄`; two distinct roots of `Q₄` in a domain are a zero of
  `dQ4`, and `dQ4 r r w` is the derivative at `r`.  This is how distinct roots are shown to
  stay distinct modulo a prime at which `Q₄` has simple roots.
* `four_mul_sq_of_link`, `equation_of_link`: a point `(t, y)` of `G = 0` goes to a point of
  `Y² = X³ - (7/4) X² + X` under `X = -1/(t y)`, `Y = (y - t) X (X - 1)/2`.
-/

namespace Tower.TangentLine

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

theorem Q4_map (f : R →+* S) (x w : R) : Q4 (f x) (f w) = f (Q4 x w) := by
  simp only [Q4, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

theorem G_map (f : R →+* S) (x y : R) : G (f x) (f y) = f (G x y) := by
  simp only [G, bq, map_add, map_mul, map_pow, map_one]

theorem F_map (f : R →+* S) (x y w : R) : F (f x) (f y) (f w) = f (F x y w) := by
  simp only [F, map_add, map_sub, map_mul, map_pow, map_one, map_neg]

/-- Divided difference of `Q₄`: `Q₄(x) - Q₄(x') = (x - x') · dQ4 x x'`. -/
def dQ4 (x x' w : R) : R :=
  (x ^ 3 + x ^ 2 * x' + x * x' ^ 2 + x' ^ 3) + (2 + 3 * w) * (x ^ 2 + x * x' + x' ^ 2)
    - (x + x') + (2 + w)

theorem Q4_sub (x x' w : R) : Q4 x w - Q4 x' w = (x - x') * dQ4 x x' w := by
  simp only [Q4, dQ4]
  ring

theorem dQ4_map (f : R →+* S) (x x' w : R) : dQ4 (f x) (f x') (f w) = f (dQ4 x x' w) := by
  simp only [dQ4, map_add, map_sub, map_mul, map_pow, map_ofNat]

/-- Two distinct roots of `Q₄` in a domain are a zero of the divided difference. -/
theorem dQ4_eq_zero [IsDomain R] {x x' w : R} (h : Q4 x w = 0) (h' : Q4 x' w = 0)
    (hne : x ≠ x') : dQ4 x x' w = 0 := by
  have e := Q4_sub x x' w
  rw [h, h', sub_zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_left (sub_ne_zero.mpr hne)

/-- The Weierstrass equation, cleared of denominators, from the equation of `G`. -/
theorem four_mul_sq_of_link {t y X Y : R} (hG : G t y = 0)
    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1)) :
    4 * Y ^ 2 = 4 * X ^ 3 - 7 * X ^ 2 + 4 * X := by
  simp only [G, bq] at hG
  linear_combination (2 * Y + (y - t) * X * (X - 1)) * hY
    + X ^ 3 * ((t + y) * (X - 1) + 1) * hG
    - (X ^ 2 * ((t + y) * (X - 1) + 1) * (t + y + 1) + 4 * X * (X - 1) ^ 2) * hX

end CommRing

section Field

variable {K : Type*} [Field K]

/-- Over a field with `2 ≠ 0`, the image of a point of `G = 0` satisfies Mathlib's equation of
the curve `Y² = X³ + a₂ X² + X` with `4 a₂ = -7`. -/
theorem equation_of_link (h2 : (2 : K) ≠ 0) {a₂ : K} (ha : 4 * a₂ = -7) {t y X Y : K}
    (hG : G t y = 0) (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1)) :
    (⟨0, a₂, 0, 1, 0⟩ : WeierstrassCurve.Affine K).Equation X Y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  show Y ^ 2 + 0 * X * Y + 0 * Y = X ^ 3 + a₂ * X ^ 2 + 1 * X + 0
  have h4 : (4 : K) ≠ 0 := by
    have e : (4 : K) = 2 * 2 := by norm_num
    rw [e]
    exact mul_ne_zero h2 h2
  have key := four_mul_sq_of_link hG hX hY
  apply mul_left_cancel₀ h4
  linear_combination key - X ^ 2 * ha

end Field

end Tower.TangentLine
