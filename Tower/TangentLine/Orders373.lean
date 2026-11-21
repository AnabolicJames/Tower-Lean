import Mathlib
import Tower.EC.Cert
import Tower.TangentLine.Resultant

/-!
# The points over the roots of `Q₄` in `E(𝔽_373)`

This file is generated (the generator computes the slopes; Lean checks every step).
`E : Y² = X³ - (7/4) X² + X` over `𝔽_373`, where `-7/4 = 278`; cube root of unity `z = 284`.
For each root `t` of `Q₄`: the point `(t, y)` of the curve `G = 0` with `F = 0`, its image
`(X, Y)` under `X = -1/(t y)`, `Y = (y - t) X (X - 1)/2`, and the exact multiples that
determine its order in Mathlib's group `E(𝔽_p)`.
-/

namespace Tower.TangentLine

namespace P373

open WeierstrassCurve.Affine Tower.EC

instance : Fact (Nat.Prime 373) := ⟨by norm_num⟩

/-- The curve `Y² = X³ + 278 X² + X` over `𝔽_373`. -/
def E : WeierstrassCurve.Affine (ZMod 373) := ⟨0, 278, 0, 1, 0⟩


/-! ## Root `t = 108`: `y = 276`, `(X, Y) = (35, 369)`, order `400` -/

/-- `(t, y) = (108, 276)` lies on `G = 0` and `F = 0`, and `(X, Y) = (35, 369)` is its image. -/
theorem link1 : G (108 : ZMod 373) 276 = 0 ∧ F (108 : ZMod 373) 276 284 = 0 ∧
    (35 : ZMod 373) * (108 * 276) = -1 ∧ 2 * (369 : ZMod 373) = (276 - 108) * 35 * (35 - 1) := by
  decide

theorem ns_35_369 : E.Nonsingular (35 : ZMod 373) 369 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_373)` over the root `t = 108`. -/
abbrev P1 : E.Point := Point.some (35 : ZMod 373) 369 ns_35_369

theorem P1_m1 : (1 : ℕ) • P1 = Point.some (35 : ZMod 373) 369 ns_35_369 := one_nsmul _
theorem ns_283_314 : E.Nonsingular (283 : ZMod 373) 314 := nonsingular_of (by decide) (by decide)
theorem step1 : Point.some (35 : ZMod 373) 369 ns_35_369 + Point.some (35 : ZMod 373) 369 ns_35_369 = Point.some (283 : ZMod 373) 314 ns_283_314 :=
  dbl_cert (ℓ := (92 : ZMod 373)) ns_35_369 ns_283_314 (by decide) (by decide) (by decide) (by decide)
theorem P1_m2 : (2 : ℕ) • P1 = Point.some (283 : ZMod 373) 314 ns_283_314 :=
  nsmul_step P1_m1 P1_m1 step1 (by norm_num)
theorem ns_272_350 : E.Nonsingular (272 : ZMod 373) 350 := nonsingular_of (by decide) (by decide)
theorem step2 : Point.some (283 : ZMod 373) 314 ns_283_314 + Point.some (283 : ZMod 373) 314 ns_283_314 = Point.some (272 : ZMod 373) 350 ns_272_350 :=
  dbl_cert (ℓ := (196 : ZMod 373)) ns_283_314 ns_272_350 (by decide) (by decide) (by decide) (by decide)
theorem P1_m4 : (4 : ℕ) • P1 = Point.some (272 : ZMod 373) 350 ns_272_350 :=
  nsmul_step P1_m2 P1_m2 step2 (by norm_num)
theorem ns_258_64 : E.Nonsingular (258 : ZMod 373) 64 := nonsingular_of (by decide) (by decide)
theorem step3 : Point.some (272 : ZMod 373) 350 ns_272_350 + Point.some (272 : ZMod 373) 350 ns_272_350 = Point.some (258 : ZMod 373) 64 ns_258_64 :=
  dbl_cert (ℓ := (296 : ZMod 373)) ns_272_350 ns_258_64 (by decide) (by decide) (by decide) (by decide)
theorem P1_m8 : (8 : ℕ) • P1 = Point.some (258 : ZMod 373) 64 ns_258_64 :=
  nsmul_step P1_m4 P1_m4 step3 (by norm_num)
theorem ns_59_329 : E.Nonsingular (59 : ZMod 373) 329 := nonsingular_of (by decide) (by decide)
theorem step4 : Point.some (258 : ZMod 373) 64 ns_258_64 + Point.some (258 : ZMod 373) 64 ns_258_64 = Point.some (59 : ZMod 373) 329 ns_59_329 :=
  dbl_cert (ℓ := (300 : ZMod 373)) ns_258_64 ns_59_329 (by decide) (by decide) (by decide) (by decide)
theorem P1_m16 : (16 : ℕ) • P1 = Point.some (59 : ZMod 373) 329 ns_59_329 :=
  nsmul_step P1_m8 P1_m8 step4 (by norm_num)
theorem ns_115_133 : E.Nonsingular (115 : ZMod 373) 133 := nonsingular_of (by decide) (by decide)
theorem step5 : Point.some (59 : ZMod 373) 329 ns_59_329 + Point.some (59 : ZMod 373) 329 ns_59_329 = Point.some (115 : ZMod 373) 133 ns_115_133 :=
  dbl_cert (ℓ := (85 : ZMod 373)) ns_59_329 ns_115_133 (by decide) (by decide) (by decide) (by decide)
theorem P1_m32 : (32 : ℕ) • P1 = Point.some (115 : ZMod 373) 133 ns_115_133 :=
  nsmul_step P1_m16 P1_m16 step5 (by norm_num)
theorem ns_165_92 : E.Nonsingular (165 : ZMod 373) 92 := nonsingular_of (by decide) (by decide)
theorem step6 : Point.some (115 : ZMod 373) 133 ns_115_133 + Point.some (115 : ZMod 373) 133 ns_115_133 = Point.some (165 : ZMod 373) 92 ns_165_92 :=
  dbl_cert (ℓ := (182 : ZMod 373)) ns_115_133 ns_165_92 (by decide) (by decide) (by decide) (by decide)
theorem P1_m64 : (64 : ℕ) • P1 = Point.some (165 : ZMod 373) 92 ns_165_92 :=
  nsmul_step P1_m32 P1_m32 step6 (by norm_num)
theorem ns_4_209 : E.Nonsingular (4 : ZMod 373) 209 := nonsingular_of (by decide) (by decide)
theorem step7 : Point.some (165 : ZMod 373) 92 ns_165_92 + Point.some (165 : ZMod 373) 92 ns_165_92 = Point.some (4 : ZMod 373) 209 ns_4_209 :=
  dbl_cert (ℓ := (310 : ZMod 373)) ns_165_92 ns_4_209 (by decide) (by decide) (by decide) (by decide)
theorem P1_m128 : (128 : ℕ) • P1 = Point.some (4 : ZMod 373) 209 ns_4_209 :=
  nsmul_step P1_m64 P1_m64 step7 (by norm_num)
theorem ns_83_144 : E.Nonsingular (83 : ZMod 373) 144 := nonsingular_of (by decide) (by decide)
theorem step8 : Point.some (4 : ZMod 373) 209 ns_4_209 + Point.some (4 : ZMod 373) 209 ns_4_209 = Point.some (83 : ZMod 373) 144 ns_83_144 :=
  dbl_cert (ℓ := (208 : ZMod 373)) ns_4_209 ns_83_144 (by decide) (by decide) (by decide) (by decide)
theorem P1_m256 : (256 : ℕ) • P1 = Point.some (83 : ZMod 373) 144 ns_83_144 :=
  nsmul_step P1_m128 P1_m128 step8 (by norm_num)
theorem ns_59_44 : E.Nonsingular (59 : ZMod 373) 44 := nonsingular_of (by decide) (by decide)
theorem step9 : Point.some (83 : ZMod 373) 144 ns_83_144 + Point.some (4 : ZMod 373) 209 ns_4_209 = Point.some (59 : ZMod 373) 44 ns_59_44 :=
  add_cert (ℓ := (70 : ZMod 373)) ns_83_144 ns_4_209 ns_59_44 (by decide) (by decide) (by decide) (by decide)
theorem P1_m384 : (384 : ℕ) • P1 = Point.some (59 : ZMod 373) 44 ns_59_44 :=
  nsmul_step P1_m256 P1_m128 step9 (by norm_num)
theorem step10 : Point.some (59 : ZMod 373) 44 ns_59_44 + Point.some (59 : ZMod 373) 329 ns_59_329 = (0 : E.Point) :=
  add_zero_cert ns_59_44 ns_59_329 (by decide) (by decide)
theorem P1_m400 : (400 : ℕ) • P1 = (0 : E.Point) :=
  nsmul_step P1_m384 P1_m16 step10 (by norm_num)

/-- `400 • P1 = 0`. -/
theorem P1_nsmul_order : (400 : ℕ) • P1 = 0 := P1_m400
theorem ns_120_290 : E.Nonsingular (120 : ZMod 373) 290 := nonsingular_of (by decide) (by decide)
theorem step11 : Point.some (4 : ZMod 373) 209 ns_4_209 + Point.some (165 : ZMod 373) 92 ns_165_92 = Point.some (120 : ZMod 373) 290 ns_120_290 :=
  add_cert (ℓ := (224 : ZMod 373)) ns_4_209 ns_165_92 ns_120_290 (by decide) (by decide) (by decide) (by decide)
theorem P1_m192 : (192 : ℕ) • P1 = Point.some (120 : ZMod 373) 290 ns_120_290 :=
  nsmul_step P1_m128 P1_m64 step11 (by norm_num)
theorem ns_0_0 : E.Nonsingular (0 : ZMod 373) 0 := nonsingular_of (by decide) (by decide)
theorem step12 : Point.some (120 : ZMod 373) 290 ns_120_290 + Point.some (258 : ZMod 373) 64 ns_258_64 = Point.some (0 : ZMod 373) 0 ns_0_0 :=
  add_cert (ℓ := (220 : ZMod 373)) ns_120_290 ns_258_64 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P1_m200 : (200 : ℕ) • P1 = Point.some (0 : ZMod 373) 0 ns_0_0 :=
  nsmul_step P1_m192 P1_m8 step12 (by norm_num)

/-- `(400/2) • P1 ≠ 0`. -/
theorem P1_nsmul_200_ne : (200 : ℕ) • P1 ≠ 0 := by
  rw [P1_m200]
  exact Point.some_ne_zero _
theorem ns_192_366 : E.Nonsingular (192 : ZMod 373) 366 := nonsingular_of (by decide) (by decide)
theorem step13 : Point.some (165 : ZMod 373) 92 ns_165_92 + Point.some (59 : ZMod 373) 329 ns_59_329 = Point.some (192 : ZMod 373) 366 ns_192_366 :=
  add_cert (ℓ := (135 : ZMod 373)) ns_165_92 ns_59_329 ns_192_366 (by decide) (by decide) (by decide) (by decide)
theorem P1_m80 : (80 : ℕ) • P1 = Point.some (192 : ZMod 373) 366 ns_192_366 :=
  nsmul_step P1_m64 P1_m16 step13 (by norm_num)

/-- `(400/5) • P1 ≠ 0`. -/
theorem P1_nsmul_80_ne : (80 : ℕ) • P1 ≠ 0 := by
  rw [P1_m80]
  exact Point.some_ne_zero _

/-! ## Root `t = 200`: `y = 282`, `(X, Y) = (155, 291)`, order `400` -/

/-- `(t, y) = (200, 282)` lies on `G = 0` and `F = 0`, and `(X, Y) = (155, 291)` is its image. -/
theorem link2 : G (200 : ZMod 373) 282 = 0 ∧ F (200 : ZMod 373) 282 284 = 0 ∧
    (155 : ZMod 373) * (200 * 282) = -1 ∧ 2 * (291 : ZMod 373) = (282 - 200) * 155 * (155 - 1) := by
  decide

theorem ns_155_291 : E.Nonsingular (155 : ZMod 373) 291 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_373)` over the root `t = 200`. -/
abbrev P2 : E.Point := Point.some (155 : ZMod 373) 291 ns_155_291

theorem P2_m1 : (1 : ℕ) • P2 = Point.some (155 : ZMod 373) 291 ns_155_291 := one_nsmul _
theorem ns_130_239 : E.Nonsingular (130 : ZMod 373) 239 := nonsingular_of (by decide) (by decide)
theorem step14 : Point.some (155 : ZMod 373) 291 ns_155_291 + Point.some (155 : ZMod 373) 291 ns_155_291 = Point.some (130 : ZMod 373) 239 ns_130_239 :=
  dbl_cert (ℓ := (245 : ZMod 373)) ns_155_291 ns_130_239 (by decide) (by decide) (by decide) (by decide)
theorem P2_m2 : (2 : ℕ) • P2 = Point.some (130 : ZMod 373) 239 ns_130_239 :=
  nsmul_step P2_m1 P2_m1 step14 (by norm_num)
theorem ns_84_239 : E.Nonsingular (84 : ZMod 373) 239 := nonsingular_of (by decide) (by decide)
theorem step15 : Point.some (130 : ZMod 373) 239 ns_130_239 + Point.some (130 : ZMod 373) 239 ns_130_239 = Point.some (84 : ZMod 373) 239 ns_84_239 :=
  dbl_cert (ℓ := (205 : ZMod 373)) ns_130_239 ns_84_239 (by decide) (by decide) (by decide) (by decide)
theorem P2_m4 : (4 : ℕ) • P2 = Point.some (84 : ZMod 373) 239 ns_84_239 :=
  nsmul_step P2_m2 P2_m2 step15 (by norm_num)
theorem ns_91_110 : E.Nonsingular (91 : ZMod 373) 110 := nonsingular_of (by decide) (by decide)
theorem step16 : Point.some (84 : ZMod 373) 239 ns_84_239 + Point.some (84 : ZMod 373) 239 ns_84_239 = Point.some (91 : ZMod 373) 110 ns_91_110 :=
  dbl_cert (ℓ := (110 : ZMod 373)) ns_84_239 ns_91_110 (by decide) (by decide) (by decide) (by decide)
theorem P2_m8 : (8 : ℕ) • P2 = Point.some (91 : ZMod 373) 110 ns_91_110 :=
  nsmul_step P2_m4 P2_m4 step16 (by norm_num)
theorem ns_279_359 : E.Nonsingular (279 : ZMod 373) 359 := nonsingular_of (by decide) (by decide)
theorem step17 : Point.some (91 : ZMod 373) 110 ns_91_110 + Point.some (91 : ZMod 373) 110 ns_91_110 = Point.some (279 : ZMod 373) 359 ns_279_359 :=
  dbl_cert (ℓ := (309 : ZMod 373)) ns_91_110 ns_279_359 (by decide) (by decide) (by decide) (by decide)
theorem P2_m16 : (16 : ℕ) • P2 = Point.some (279 : ZMod 373) 359 ns_279_359 :=
  nsmul_step P2_m8 P2_m8 step17 (by norm_num)
theorem ns_213_163 : E.Nonsingular (213 : ZMod 373) 163 := nonsingular_of (by decide) (by decide)
theorem step18 : Point.some (279 : ZMod 373) 359 ns_279_359 + Point.some (279 : ZMod 373) 359 ns_279_359 = Point.some (213 : ZMod 373) 163 ns_213_163 :=
  dbl_cert (ℓ := (347 : ZMod 373)) ns_279_359 ns_213_163 (by decide) (by decide) (by decide) (by decide)
theorem P2_m32 : (32 : ℕ) • P2 = Point.some (213 : ZMod 373) 163 ns_213_163 :=
  nsmul_step P2_m16 P2_m16 step18 (by norm_num)
theorem ns_25_356 : E.Nonsingular (25 : ZMod 373) 356 := nonsingular_of (by decide) (by decide)
theorem step19 : Point.some (213 : ZMod 373) 163 ns_213_163 + Point.some (213 : ZMod 373) 163 ns_213_163 = Point.some (25 : ZMod 373) 356 ns_25_356 :=
  dbl_cert (ℓ := (346 : ZMod 373)) ns_213_163 ns_25_356 (by decide) (by decide) (by decide) (by decide)
theorem P2_m64 : (64 : ℕ) • P2 = Point.some (25 : ZMod 373) 356 ns_25_356 :=
  nsmul_step P2_m32 P2_m32 step19 (by norm_num)
theorem ns_120_83 : E.Nonsingular (120 : ZMod 373) 83 := nonsingular_of (by decide) (by decide)
theorem step20 : Point.some (25 : ZMod 373) 356 ns_25_356 + Point.some (25 : ZMod 373) 356 ns_25_356 = Point.some (120 : ZMod 373) 83 ns_120_83 :=
  dbl_cert (ℓ := (282 : ZMod 373)) ns_25_356 ns_120_83 (by decide) (by decide) (by decide) (by decide)
theorem P2_m128 : (128 : ℕ) • P2 = Point.some (120 : ZMod 373) 83 ns_120_83 :=
  nsmul_step P2_m64 P2_m64 step20 (by norm_num)
theorem step21 : Point.some (120 : ZMod 373) 83 ns_120_83 + Point.some (120 : ZMod 373) 83 ns_120_83 = Point.some (59 : ZMod 373) 329 ns_59_329 :=
  dbl_cert (ℓ := (233 : ZMod 373)) ns_120_83 ns_59_329 (by decide) (by decide) (by decide) (by decide)
theorem P2_m256 : (256 : ℕ) • P2 = Point.some (59 : ZMod 373) 329 ns_59_329 :=
  nsmul_step P2_m128 P2_m128 step21 (by norm_num)
theorem ns_279_14 : E.Nonsingular (279 : ZMod 373) 14 := nonsingular_of (by decide) (by decide)
theorem step22 : Point.some (59 : ZMod 373) 329 ns_59_329 + Point.some (120 : ZMod 373) 83 ns_120_83 = Point.some (279 : ZMod 373) 14 ns_279_14 :=
  add_cert (ℓ := (51 : ZMod 373)) ns_59_329 ns_120_83 ns_279_14 (by decide) (by decide) (by decide) (by decide)
theorem P2_m384 : (384 : ℕ) • P2 = Point.some (279 : ZMod 373) 14 ns_279_14 :=
  nsmul_step P2_m256 P2_m128 step22 (by norm_num)
theorem step23 : Point.some (279 : ZMod 373) 14 ns_279_14 + Point.some (279 : ZMod 373) 359 ns_279_359 = (0 : E.Point) :=
  add_zero_cert ns_279_14 ns_279_359 (by decide) (by decide)
theorem P2_m400 : (400 : ℕ) • P2 = (0 : E.Point) :=
  nsmul_step P2_m384 P2_m16 step23 (by norm_num)

/-- `400 • P2 = 0`. -/
theorem P2_nsmul_order : (400 : ℕ) • P2 = 0 := P2_m400
theorem ns_41_275 : E.Nonsingular (41 : ZMod 373) 275 := nonsingular_of (by decide) (by decide)
theorem step24 : Point.some (120 : ZMod 373) 83 ns_120_83 + Point.some (25 : ZMod 373) 356 ns_25_356 = Point.some (41 : ZMod 373) 275 ns_41_275 :=
  add_cert (ℓ := (217 : ZMod 373)) ns_120_83 ns_25_356 ns_41_275 (by decide) (by decide) (by decide) (by decide)
theorem P2_m192 : (192 : ℕ) • P2 = Point.some (41 : ZMod 373) 275 ns_41_275 :=
  nsmul_step P2_m128 P2_m64 step24 (by norm_num)
theorem step25 : Point.some (41 : ZMod 373) 275 ns_41_275 + Point.some (91 : ZMod 373) 110 ns_91_110 = Point.some (0 : ZMod 373) 0 ns_0_0 :=
  add_cert (ℓ := (34 : ZMod 373)) ns_41_275 ns_91_110 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P2_m200 : (200 : ℕ) • P2 = Point.some (0 : ZMod 373) 0 ns_0_0 :=
  nsmul_step P2_m192 P2_m8 step25 (by norm_num)

/-- `(400/2) • P2 ≠ 0`. -/
theorem P2_nsmul_200_ne : (200 : ℕ) • P2 ≠ 0 := by
  rw [P2_m200]
  exact Point.some_ne_zero _
theorem step26 : Point.some (25 : ZMod 373) 356 ns_25_356 + Point.some (279 : ZMod 373) 359 ns_279_359 = Point.some (192 : ZMod 373) 366 ns_192_366 :=
  add_cert (ℓ := (257 : ZMod 373)) ns_25_356 ns_279_359 ns_192_366 (by decide) (by decide) (by decide) (by decide)
theorem P2_m80 : (80 : ℕ) • P2 = Point.some (192 : ZMod 373) 366 ns_192_366 :=
  nsmul_step P2_m64 P2_m16 step26 (by norm_num)

/-- `(400/5) • P2 ≠ 0`. -/
theorem P2_nsmul_80_ne : (80 : ℕ) • P2 ≠ 0 := by
  rw [P2_m80]
  exact Point.some_ne_zero _

/-! ## Root `t = 336`: `y = 275`, `(X, Y) = (269, 29)`, order `400` -/

/-- `(t, y) = (336, 275)` lies on `G = 0` and `F = 0`, and `(X, Y) = (269, 29)` is its image. -/
theorem link3 : G (336 : ZMod 373) 275 = 0 ∧ F (336 : ZMod 373) 275 284 = 0 ∧
    (269 : ZMod 373) * (336 * 275) = -1 ∧ 2 * (29 : ZMod 373) = (275 - 336) * 269 * (269 - 1) := by
  decide

theorem ns_269_29 : E.Nonsingular (269 : ZMod 373) 29 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_373)` over the root `t = 336`. -/
abbrev P3 : E.Point := Point.some (269 : ZMod 373) 29 ns_269_29

theorem P3_m1 : (1 : ℕ) • P3 = Point.some (269 : ZMod 373) 29 ns_269_29 := one_nsmul _
theorem ns_267_215 : E.Nonsingular (267 : ZMod 373) 215 := nonsingular_of (by decide) (by decide)
theorem step27 : Point.some (269 : ZMod 373) 29 ns_269_29 + Point.some (269 : ZMod 373) 29 ns_269_29 = Point.some (267 : ZMod 373) 215 ns_267_215 :=
  dbl_cert (ℓ := (122 : ZMod 373)) ns_269_29 ns_267_215 (by decide) (by decide) (by decide) (by decide)
theorem P3_m2 : (2 : ℕ) • P3 = Point.some (267 : ZMod 373) 215 ns_267_215 :=
  nsmul_step P3_m1 P3_m1 step27 (by norm_num)
theorem ns_261_35 : E.Nonsingular (261 : ZMod 373) 35 := nonsingular_of (by decide) (by decide)
theorem step28 : Point.some (267 : ZMod 373) 215 ns_267_215 + Point.some (267 : ZMod 373) 215 ns_267_215 = Point.some (261 : ZMod 373) 35 ns_261_35 :=
  dbl_cert (ℓ := (166 : ZMod 373)) ns_267_215 ns_261_35 (by decide) (by decide) (by decide) (by decide)
theorem P3_m4 : (4 : ℕ) • P3 = Point.some (261 : ZMod 373) 35 ns_261_35 :=
  nsmul_step P3_m2 P3_m2 step28 (by norm_num)
theorem ns_196_132 : E.Nonsingular (196 : ZMod 373) 132 := nonsingular_of (by decide) (by decide)
theorem step29 : Point.some (261 : ZMod 373) 35 ns_261_35 + Point.some (261 : ZMod 373) 35 ns_261_35 = Point.some (196 : ZMod 373) 132 ns_196_132 :=
  dbl_cert (ℓ := (37 : ZMod 373)) ns_261_35 ns_196_132 (by decide) (by decide) (by decide) (by decide)
theorem P3_m8 : (8 : ℕ) • P3 = Point.some (196 : ZMod 373) 132 ns_196_132 :=
  nsmul_step P3_m4 P3_m4 step29 (by norm_num)
theorem ns_115_240 : E.Nonsingular (115 : ZMod 373) 240 := nonsingular_of (by decide) (by decide)
theorem step30 : Point.some (196 : ZMod 373) 132 ns_196_132 + Point.some (196 : ZMod 373) 132 ns_196_132 = Point.some (115 : ZMod 373) 240 ns_115_240 :=
  dbl_cert (ℓ := (198 : ZMod 373)) ns_196_132 ns_115_240 (by decide) (by decide) (by decide) (by decide)
theorem P3_m16 : (16 : ℕ) • P3 = Point.some (115 : ZMod 373) 240 ns_115_240 :=
  nsmul_step P3_m8 P3_m8 step30 (by norm_num)
theorem ns_165_281 : E.Nonsingular (165 : ZMod 373) 281 := nonsingular_of (by decide) (by decide)
theorem step31 : Point.some (115 : ZMod 373) 240 ns_115_240 + Point.some (115 : ZMod 373) 240 ns_115_240 = Point.some (165 : ZMod 373) 281 ns_165_281 :=
  dbl_cert (ℓ := (191 : ZMod 373)) ns_115_240 ns_165_281 (by decide) (by decide) (by decide) (by decide)
theorem P3_m32 : (32 : ℕ) • P3 = Point.some (165 : ZMod 373) 281 ns_165_281 :=
  nsmul_step P3_m16 P3_m16 step31 (by norm_num)
theorem ns_4_164 : E.Nonsingular (4 : ZMod 373) 164 := nonsingular_of (by decide) (by decide)
theorem step32 : Point.some (165 : ZMod 373) 281 ns_165_281 + Point.some (165 : ZMod 373) 281 ns_165_281 = Point.some (4 : ZMod 373) 164 ns_4_164 :=
  dbl_cert (ℓ := (63 : ZMod 373)) ns_165_281 ns_4_164 (by decide) (by decide) (by decide) (by decide)
theorem P3_m64 : (64 : ℕ) • P3 = Point.some (4 : ZMod 373) 164 ns_4_164 :=
  nsmul_step P3_m32 P3_m32 step32 (by norm_num)
theorem ns_83_229 : E.Nonsingular (83 : ZMod 373) 229 := nonsingular_of (by decide) (by decide)
theorem step33 : Point.some (4 : ZMod 373) 164 ns_4_164 + Point.some (4 : ZMod 373) 164 ns_4_164 = Point.some (83 : ZMod 373) 229 ns_83_229 :=
  dbl_cert (ℓ := (165 : ZMod 373)) ns_4_164 ns_83_229 (by decide) (by decide) (by decide) (by decide)
theorem P3_m128 : (128 : ℕ) • P3 = Point.some (83 : ZMod 373) 229 ns_83_229 :=
  nsmul_step P3_m64 P3_m64 step33 (by norm_num)
theorem ns_41_98 : E.Nonsingular (41 : ZMod 373) 98 := nonsingular_of (by decide) (by decide)
theorem step34 : Point.some (83 : ZMod 373) 229 ns_83_229 + Point.some (83 : ZMod 373) 229 ns_83_229 = Point.some (41 : ZMod 373) 98 ns_41_98 :=
  dbl_cert (ℓ := (141 : ZMod 373)) ns_83_229 ns_41_98 (by decide) (by decide) (by decide) (by decide)
theorem P3_m256 : (256 : ℕ) • P3 = Point.some (41 : ZMod 373) 98 ns_41_98 :=
  nsmul_step P3_m128 P3_m128 step34 (by norm_num)
theorem step35 : Point.some (41 : ZMod 373) 98 ns_41_98 + Point.some (83 : ZMod 373) 229 ns_83_229 = Point.some (115 : ZMod 373) 133 ns_115_133 :=
  add_cert (ℓ := (12 : ZMod 373)) ns_41_98 ns_83_229 ns_115_133 (by decide) (by decide) (by decide) (by decide)
theorem P3_m384 : (384 : ℕ) • P3 = Point.some (115 : ZMod 373) 133 ns_115_133 :=
  nsmul_step P3_m256 P3_m128 step35 (by norm_num)
theorem step36 : Point.some (115 : ZMod 373) 133 ns_115_133 + Point.some (115 : ZMod 373) 240 ns_115_240 = (0 : E.Point) :=
  add_zero_cert ns_115_133 ns_115_240 (by decide) (by decide)
theorem P3_m400 : (400 : ℕ) • P3 = (0 : E.Point) :=
  nsmul_step P3_m384 P3_m16 step36 (by norm_num)

/-- `400 • P3 = 0`. -/
theorem P3_nsmul_order : (400 : ℕ) • P3 = 0 := P3_m400
theorem step37 : Point.some (83 : ZMod 373) 229 ns_83_229 + Point.some (4 : ZMod 373) 164 ns_4_164 = Point.some (59 : ZMod 373) 329 ns_59_329 :=
  add_cert (ℓ := (303 : ZMod 373)) ns_83_229 ns_4_164 ns_59_329 (by decide) (by decide) (by decide) (by decide)
theorem P3_m192 : (192 : ℕ) • P3 = Point.some (59 : ZMod 373) 329 ns_59_329 :=
  nsmul_step P3_m128 P3_m64 step37 (by norm_num)
theorem step38 : Point.some (59 : ZMod 373) 329 ns_59_329 + Point.some (196 : ZMod 373) 132 ns_196_132 = Point.some (0 : ZMod 373) 0 ns_0_0 :=
  add_cert (ℓ := (328 : ZMod 373)) ns_59_329 ns_196_132 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P3_m200 : (200 : ℕ) • P3 = Point.some (0 : ZMod 373) 0 ns_0_0 :=
  nsmul_step P3_m192 P3_m8 step38 (by norm_num)

/-- `(400/2) • P3 ≠ 0`. -/
theorem P3_nsmul_200_ne : (200 : ℕ) • P3 ≠ 0 := by
  rw [P3_m200]
  exact Point.some_ne_zero _
theorem ns_333_182 : E.Nonsingular (333 : ZMod 373) 182 := nonsingular_of (by decide) (by decide)
theorem step39 : Point.some (4 : ZMod 373) 164 ns_4_164 + Point.some (115 : ZMod 373) 240 ns_115_240 = Point.some (333 : ZMod 373) 182 ns_333_182 :=
  add_cert (ℓ := (330 : ZMod 373)) ns_4_164 ns_115_240 ns_333_182 (by decide) (by decide) (by decide) (by decide)
theorem P3_m80 : (80 : ℕ) • P3 = Point.some (333 : ZMod 373) 182 ns_333_182 :=
  nsmul_step P3_m64 P3_m16 step39 (by norm_num)

/-- `(400/5) • P3 ≠ 0`. -/
theorem P3_nsmul_80_ne : (80 : ℕ) • P3 ≠ 0 := by
  rw [P3_m80]
  exact Point.some_ne_zero _

/-! ## Root `t = 367`: `y = 286`, `(X, Y) = (5, 309)`, order `80` -/

/-- `(t, y) = (367, 286)` lies on `G = 0` and `F = 0`, and `(X, Y) = (5, 309)` is its image. -/
theorem link4 : G (367 : ZMod 373) 286 = 0 ∧ F (367 : ZMod 373) 286 284 = 0 ∧
    (5 : ZMod 373) * (367 * 286) = -1 ∧ 2 * (309 : ZMod 373) = (286 - 367) * 5 * (5 - 1) := by
  decide

theorem ns_5_309 : E.Nonsingular (5 : ZMod 373) 309 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_373)` over the root `t = 367`. -/
abbrev P4 : E.Point := Point.some (5 : ZMod 373) 309 ns_5_309

theorem P4_m1 : (1 : ℕ) • P4 = Point.some (5 : ZMod 373) 309 ns_5_309 := one_nsmul _
theorem ns_86_356 : E.Nonsingular (86 : ZMod 373) 356 := nonsingular_of (by decide) (by decide)
theorem step40 : Point.some (5 : ZMod 373) 309 ns_5_309 + Point.some (5 : ZMod 373) 309 ns_5_309 = Point.some (86 : ZMod 373) 356 ns_86_356 :=
  dbl_cert (ℓ := (1 : ZMod 373)) ns_5_309 ns_86_356 (by decide) (by decide) (by decide) (by decide)
theorem P4_m2 : (2 : ℕ) • P4 = Point.some (86 : ZMod 373) 356 ns_86_356 :=
  nsmul_step P4_m1 P4_m1 step40 (by norm_num)
theorem ns_215_125 : E.Nonsingular (215 : ZMod 373) 125 := nonsingular_of (by decide) (by decide)
theorem step41 : Point.some (86 : ZMod 373) 356 ns_86_356 + Point.some (86 : ZMod 373) 356 ns_86_356 = Point.some (215 : ZMod 373) 125 ns_215_125 :=
  dbl_cert (ℓ := (190 : ZMod 373)) ns_86_356 ns_215_125 (by decide) (by decide) (by decide) (by decide)
theorem P4_m4 : (4 : ℕ) • P4 = Point.some (215 : ZMod 373) 125 ns_215_125 :=
  nsmul_step P4_m2 P4_m2 step41 (by norm_num)
theorem ns_68_83 : E.Nonsingular (68 : ZMod 373) 83 := nonsingular_of (by decide) (by decide)
theorem step42 : Point.some (215 : ZMod 373) 125 ns_215_125 + Point.some (215 : ZMod 373) 125 ns_215_125 = Point.some (68 : ZMod 373) 83 ns_68_83 :=
  dbl_cert (ℓ := (75 : ZMod 373)) ns_215_125 ns_68_83 (by decide) (by decide) (by decide) (by decide)
theorem P4_m8 : (8 : ℕ) • P4 = Point.some (68 : ZMod 373) 83 ns_68_83 :=
  nsmul_step P4_m4 P4_m4 step42 (by norm_num)
theorem step43 : Point.some (68 : ZMod 373) 83 ns_68_83 + Point.some (68 : ZMod 373) 83 ns_68_83 = Point.some (333 : ZMod 373) 182 ns_333_182 :=
  dbl_cert (ℓ := (372 : ZMod 373)) ns_68_83 ns_333_182 (by decide) (by decide) (by decide) (by decide)
theorem P4_m16 : (16 : ℕ) • P4 = Point.some (333 : ZMod 373) 182 ns_333_182 :=
  nsmul_step P4_m8 P4_m8 step43 (by norm_num)
theorem step44 : Point.some (333 : ZMod 373) 182 ns_333_182 + Point.some (333 : ZMod 373) 182 ns_333_182 = Point.some (192 : ZMod 373) 366 ns_192_366 :=
  dbl_cert (ℓ := (197 : ZMod 373)) ns_333_182 ns_192_366 (by decide) (by decide) (by decide) (by decide)
theorem P4_m32 : (32 : ℕ) • P4 = Point.some (192 : ZMod 373) 366 ns_192_366 :=
  nsmul_step P4_m16 P4_m16 step44 (by norm_num)
theorem ns_333_191 : E.Nonsingular (333 : ZMod 373) 191 := nonsingular_of (by decide) (by decide)
theorem step45 : Point.some (192 : ZMod 373) 366 ns_192_366 + Point.some (192 : ZMod 373) 366 ns_192_366 = Point.some (333 : ZMod 373) 191 ns_333_191 :=
  dbl_cert (ℓ := (168 : ZMod 373)) ns_192_366 ns_333_191 (by decide) (by decide) (by decide) (by decide)
theorem P4_m64 : (64 : ℕ) • P4 = Point.some (333 : ZMod 373) 191 ns_333_191 :=
  nsmul_step P4_m32 P4_m32 step45 (by norm_num)
theorem step46 : Point.some (333 : ZMod 373) 191 ns_333_191 + Point.some (333 : ZMod 373) 182 ns_333_182 = (0 : E.Point) :=
  add_zero_cert ns_333_191 ns_333_182 (by decide) (by decide)
theorem P4_m80 : (80 : ℕ) • P4 = (0 : E.Point) :=
  nsmul_step P4_m64 P4_m16 step46 (by norm_num)

/-- `80 • P4 = 0`. -/
theorem P4_nsmul_order : (80 : ℕ) • P4 = 0 := P4_m80
theorem step47 : Point.some (192 : ZMod 373) 366 ns_192_366 + Point.some (68 : ZMod 373) 83 ns_68_83 = Point.some (0 : ZMod 373) 0 ns_0_0 :=
  add_cert (ℓ := (270 : ZMod 373)) ns_192_366 ns_68_83 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P4_m40 : (40 : ℕ) • P4 = Point.some (0 : ZMod 373) 0 ns_0_0 :=
  nsmul_step P4_m32 P4_m8 step47 (by norm_num)

/-- `(80/2) • P4 ≠ 0`. -/
theorem P4_nsmul_40_ne : (40 : ℕ) • P4 ≠ 0 := by
  rw [P4_m40]
  exact Point.some_ne_zero _

/-- `(80/5) • P4 ≠ 0`. -/
theorem P4_nsmul_16_ne : (16 : ℕ) • P4 ≠ 0 := by
  rw [P4_m16]
  exact Point.some_ne_zero _

end P373

end Tower.TangentLine
