import Mathlib
import Tower.EC.Cert
import Tower.TangentLine.Maps

/-!
# The points over the roots of `Q₄` in `E(𝔽_499)`

This file is generated (the generator computes the slopes; Lean checks every step).
`E : Y² = X³ - (7/4) X² + X` over `𝔽_499`, where `-7/4 = 123`; cube root of unity `z = 359`.
For each root `t` of `Q₄`: the point `(t, y)` of the curve `G = 0` with `F = 0`, its image
`(X, Y)` under `X = -1/(t y)`, `Y = (y - t) X (X - 1)/2`, the exact multiples that
determine its order in Mathlib's group `E(𝔽_p)`, and the fact that `(X, Y)` is determined by
`t`.  The last section does the same for the six differences of the four points.
-/

namespace Tower.TangentLine

namespace P499

open WeierstrassCurve.Affine Tower.EC

instance : Fact (Nat.Prime 499) := ⟨by norm_num⟩

/-- The curve `Y² = X³ + 123 X² + X` over `𝔽_499`. -/
def E : WeierstrassCurve.Affine (ZMod 499) := ⟨0, 123, 0, 1, 0⟩

/-- `359` is a primitive cube root of unity in `𝔽_499`. -/
theorem cubeRoot : (359 : ZMod 499) ^ 2 + 359 + 1 = 0 := by decide

/-- Over `𝔽_499` with `w = 359`, the quartic `Q₄` has exactly the four roots `16, 88, 316, 497`. -/
theorem Q4_roots : ∀ t : ZMod 499, Q4 t 359 = 0 ↔ (t = 16 ∨ t = 88 ∨ t = 316 ∨ t = 497) := by
  decide +kernel


/-! ## Root `t = 16`: `y = 152`, `(X, Y) = (301, 205)`, order `248` -/

/-- `(t, y) = (16, 152)` lies on `G = 0` and `F = 0`, and `(X, Y) = (301, 205)` is its image. -/
theorem link1 : G (16 : ZMod 499) 152 = 0 ∧ F (16 : ZMod 499) 152 359 = 0 ∧
    (301 : ZMod 499) * (16 * 152) = -1 ∧ 2 * (205 : ZMod 499) = (152 - 16) * 301 * (301 - 1) := by
  decide

theorem uniq_y1 : ∀ y : ZMod 499, G 16 y = 0 → F 16 y 359 = 0 → y = 152 := by
  decide +kernel
theorem uniq_X1 : ∀ X : ZMod 499, X * (16 * 152) = -1 → X = 301 := by
  decide +kernel
theorem uniq_Y1 : ∀ Y : ZMod 499, 2 * Y = (152 - 16) * 301 * (301 - 1) → Y = 205 := by
  decide +kernel

/-- Over the root `t = 16` the point `(X, Y)` is determined. -/
theorem coords1 (y X Y : ZMod 499) (hG : G 16 y = 0) (hF : F 16 y 359 = 0)
    (hX : X * (16 * y) = -1) (hY : 2 * Y = (y - 16) * X * (X - 1)) : X = 301 ∧ Y = 205 := by
  have hy : y = 152 := uniq_y1 y hG hF
  subst hy
  have hX' : X = 301 := uniq_X1 X hX
  subst hX'
  exact ⟨rfl, uniq_Y1 Y hY⟩

/-- `t = 16` is a simple root of `Q₄`. -/
theorem diag1 : dQ4 (16 : ZMod 499) 16 359 ≠ 0 := by decide

theorem ns_301_205 : E.Nonsingular (301 : ZMod 499) 205 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_499)` over the root `t = 16`. -/
abbrev P1 : E.Point := Point.some (301 : ZMod 499) 205 ns_301_205

theorem P1_m1 : (1 : ℕ) • P1 = Point.some (301 : ZMod 499) 205 ns_301_205 := one_nsmul _
theorem ns_109_5 : E.Nonsingular (109 : ZMod 499) 5 := nonsingular_of (by decide) (by decide)
theorem step1 : Point.some (301 : ZMod 499) 205 ns_301_205 + Point.some (301 : ZMod 499) 205 ns_301_205 = Point.some (109 : ZMod 499) 5 ns_109_5 :=
  dbl_cert (ℓ := (235 : ZMod 499)) ns_301_205 ns_109_5 (by decide) (by decide) (by decide) (by decide)
theorem P1_m2 : (2 : ℕ) • P1 = Point.some (109 : ZMod 499) 5 ns_109_5 :=
  nsmul_step P1_m1 P1_m1 step1 (by norm_num)
theorem ns_172_21 : E.Nonsingular (172 : ZMod 499) 21 := nonsingular_of (by decide) (by decide)
theorem step2 : Point.some (109 : ZMod 499) 5 ns_109_5 + Point.some (109 : ZMod 499) 5 ns_109_5 = Point.some (172 : ZMod 499) 21 ns_172_21 :=
  dbl_cert (ℓ := (158 : ZMod 499)) ns_109_5 ns_172_21 (by decide) (by decide) (by decide) (by decide)
theorem P1_m4 : (4 : ℕ) • P1 = Point.some (172 : ZMod 499) 21 ns_172_21 :=
  nsmul_step P1_m2 P1_m2 step2 (by norm_num)
theorem ns_197_319 : E.Nonsingular (197 : ZMod 499) 319 := nonsingular_of (by decide) (by decide)
theorem step3 : Point.some (172 : ZMod 499) 21 ns_172_21 + Point.some (172 : ZMod 499) 21 ns_172_21 = Point.some (197 : ZMod 499) 319 ns_197_319 :=
  dbl_cert (ℓ := (186 : ZMod 499)) ns_172_21 ns_197_319 (by decide) (by decide) (by decide) (by decide)
theorem P1_m8 : (8 : ℕ) • P1 = Point.some (197 : ZMod 499) 319 ns_197_319 :=
  nsmul_step P1_m4 P1_m4 step3 (by norm_num)
theorem ns_64_71 : E.Nonsingular (64 : ZMod 499) 71 := nonsingular_of (by decide) (by decide)
theorem step4 : Point.some (197 : ZMod 499) 319 ns_197_319 + Point.some (197 : ZMod 499) 319 ns_197_319 = Point.some (64 : ZMod 499) 71 ns_64_71 :=
  dbl_cert (ℓ := (138 : ZMod 499)) ns_197_319 ns_64_71 (by decide) (by decide) (by decide) (by decide)
theorem P1_m16 : (16 : ℕ) • P1 = Point.some (64 : ZMod 499) 71 ns_64_71 :=
  nsmul_step P1_m8 P1_m8 step4 (by norm_num)
theorem ns_211_494 : E.Nonsingular (211 : ZMod 499) 494 := nonsingular_of (by decide) (by decide)
theorem step5 : Point.some (64 : ZMod 499) 71 ns_64_71 + Point.some (64 : ZMod 499) 71 ns_64_71 = Point.some (211 : ZMod 499) 494 ns_211_494 :=
  dbl_cert (ℓ := (468 : ZMod 499)) ns_64_71 ns_211_494 (by decide) (by decide) (by decide) (by decide)
theorem P1_m32 : (32 : ℕ) • P1 = Point.some (211 : ZMod 499) 494 ns_211_494 :=
  nsmul_step P1_m16 P1_m16 step5 (by norm_num)
theorem ns_24_265 : E.Nonsingular (24 : ZMod 499) 265 := nonsingular_of (by decide) (by decide)
theorem step6 : Point.some (211 : ZMod 499) 494 ns_211_494 + Point.some (211 : ZMod 499) 494 ns_211_494 = Point.some (24 : ZMod 499) 265 ns_24_265 :=
  dbl_cert (ℓ := (415 : ZMod 499)) ns_211_494 ns_24_265 (by decide) (by decide) (by decide) (by decide)
theorem P1_m64 : (64 : ℕ) • P1 = Point.some (24 : ZMod 499) 265 ns_24_265 :=
  nsmul_step P1_m32 P1_m32 step6 (by norm_num)
theorem ns_235_450 : E.Nonsingular (235 : ZMod 499) 450 := nonsingular_of (by decide) (by decide)
theorem step7 : Point.some (24 : ZMod 499) 265 ns_24_265 + Point.some (24 : ZMod 499) 265 ns_24_265 = Point.some (235 : ZMod 499) 450 ns_235_450 :=
  dbl_cert (ℓ := (375 : ZMod 499)) ns_24_265 ns_235_450 (by decide) (by decide) (by decide) (by decide)
theorem P1_m128 : (128 : ℕ) • P1 = Point.some (235 : ZMod 499) 450 ns_235_450 :=
  nsmul_step P1_m64 P1_m64 step7 (by norm_num)
theorem ns_224_210 : E.Nonsingular (224 : ZMod 499) 210 := nonsingular_of (by decide) (by decide)
theorem step8 : Point.some (235 : ZMod 499) 450 ns_235_450 + Point.some (24 : ZMod 499) 265 ns_24_265 = Point.some (224 : ZMod 499) 210 ns_224_210 :=
  add_cert (ℓ := (60 : ZMod 499)) ns_235_450 ns_24_265 ns_224_210 (by decide) (by decide) (by decide) (by decide)
theorem P1_m192 : (192 : ℕ) • P1 = Point.some (224 : ZMod 499) 210 ns_224_210 :=
  nsmul_step P1_m128 P1_m64 step8 (by norm_num)
theorem ns_247_446 : E.Nonsingular (247 : ZMod 499) 446 := nonsingular_of (by decide) (by decide)
theorem step9 : Point.some (224 : ZMod 499) 210 ns_224_210 + Point.some (211 : ZMod 499) 494 ns_211_494 = Point.some (247 : ZMod 499) 446 ns_247_446 :=
  add_cert (ℓ := (362 : ZMod 499)) ns_224_210 ns_211_494 ns_247_446 (by decide) (by decide) (by decide) (by decide)
theorem P1_m224 : (224 : ℕ) • P1 = Point.some (247 : ZMod 499) 446 ns_247_446 :=
  nsmul_step P1_m192 P1_m32 step9 (by norm_num)
theorem ns_197_180 : E.Nonsingular (197 : ZMod 499) 180 := nonsingular_of (by decide) (by decide)
theorem step10 : Point.some (247 : ZMod 499) 446 ns_247_446 + Point.some (64 : ZMod 499) 71 ns_64_71 = Point.some (197 : ZMod 499) 180 ns_197_180 :=
  add_cert (ℓ := (272 : ZMod 499)) ns_247_446 ns_64_71 ns_197_180 (by decide) (by decide) (by decide) (by decide)
theorem P1_m240 : (240 : ℕ) • P1 = Point.some (197 : ZMod 499) 180 ns_197_180 :=
  nsmul_step P1_m224 P1_m16 step10 (by norm_num)
theorem step11 : Point.some (197 : ZMod 499) 180 ns_197_180 + Point.some (197 : ZMod 499) 319 ns_197_319 = (0 : E.Point) :=
  add_zero_cert ns_197_180 ns_197_319 (by decide) (by decide)
theorem P1_m248 : (248 : ℕ) • P1 = (0 : E.Point) :=
  nsmul_step P1_m240 P1_m8 step11 (by norm_num)

/-- `248 • P1 = 0`. -/
theorem P1_nsmul_order : (248 : ℕ) • P1 = 0 := P1_m248
theorem ns_91_224 : E.Nonsingular (91 : ZMod 499) 224 := nonsingular_of (by decide) (by decide)
theorem step12 : Point.some (24 : ZMod 499) 265 ns_24_265 + Point.some (211 : ZMod 499) 494 ns_211_494 = Point.some (91 : ZMod 499) 224 ns_91_224 :=
  add_cert (ℓ := (164 : ZMod 499)) ns_24_265 ns_211_494 ns_91_224 (by decide) (by decide) (by decide) (by decide)
theorem P1_m96 : (96 : ℕ) • P1 = Point.some (91 : ZMod 499) 224 ns_91_224 :=
  nsmul_step P1_m64 P1_m32 step12 (by norm_num)
theorem ns_364_225 : E.Nonsingular (364 : ZMod 499) 225 := nonsingular_of (by decide) (by decide)
theorem step13 : Point.some (91 : ZMod 499) 224 ns_91_224 + Point.some (64 : ZMod 499) 71 ns_64_71 = Point.some (364 : ZMod 499) 225 ns_364_225 :=
  add_cert (ℓ := (172 : ZMod 499)) ns_91_224 ns_64_71 ns_364_225 (by decide) (by decide) (by decide) (by decide)
theorem P1_m112 : (112 : ℕ) • P1 = Point.some (364 : ZMod 499) 225 ns_364_225 :=
  nsmul_step P1_m96 P1_m16 step13 (by norm_num)
theorem ns_235_49 : E.Nonsingular (235 : ZMod 499) 49 := nonsingular_of (by decide) (by decide)
theorem step14 : Point.some (364 : ZMod 499) 225 ns_364_225 + Point.some (197 : ZMod 499) 319 ns_197_319 = Point.some (235 : ZMod 499) 49 ns_235_49 :=
  add_cert (ℓ := (358 : ZMod 499)) ns_364_225 ns_197_319 ns_235_49 (by decide) (by decide) (by decide) (by decide)
theorem P1_m120 : (120 : ℕ) • P1 = Point.some (235 : ZMod 499) 49 ns_235_49 :=
  nsmul_step P1_m112 P1_m8 step14 (by norm_num)
theorem ns_0_0 : E.Nonsingular (0 : ZMod 499) 0 := nonsingular_of (by decide) (by decide)
theorem step15 : Point.some (235 : ZMod 499) 49 ns_235_49 + Point.some (172 : ZMod 499) 21 ns_172_21 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  add_cert (ℓ := (444 : ZMod 499)) ns_235_49 ns_172_21 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P1_m124 : (124 : ℕ) • P1 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  nsmul_step P1_m120 P1_m4 step15 (by norm_num)

/-- `(248/2) • P1 ≠ 0`. -/
theorem P1_nsmul_124_ne : (124 : ℕ) • P1 ≠ 0 := by
  rw [P1_m124]
  exact Point.some_ne_zero _

/-- `(248/31) • P1 ≠ 0`. -/
theorem P1_nsmul_8_ne : (8 : ℕ) • P1 ≠ 0 := by
  rw [P1_m8]
  exact Point.some_ne_zero _

/-- `P1` has exact order `248` in `E(𝔽_499)`. -/
theorem P1_addOrderOf : addOrderOf P1 = 248 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul P1_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 * 31 ^ 1 : ℕ) = 248 := by norm_num
  have h : q ∣ 2 ^ 3 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact P1_nsmul_124_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact P1_nsmul_8_ne

/-! ## Root `t = 88`: `y = 55`, `(X, Y) = (336, 38)`, order `124` -/

/-- `(t, y) = (88, 55)` lies on `G = 0` and `F = 0`, and `(X, Y) = (336, 38)` is its image. -/
theorem link2 : G (88 : ZMod 499) 55 = 0 ∧ F (88 : ZMod 499) 55 359 = 0 ∧
    (336 : ZMod 499) * (88 * 55) = -1 ∧ 2 * (38 : ZMod 499) = (55 - 88) * 336 * (336 - 1) := by
  decide

theorem uniq_y2 : ∀ y : ZMod 499, G 88 y = 0 → F 88 y 359 = 0 → y = 55 := by
  decide +kernel
theorem uniq_X2 : ∀ X : ZMod 499, X * (88 * 55) = -1 → X = 336 := by
  decide +kernel
theorem uniq_Y2 : ∀ Y : ZMod 499, 2 * Y = (55 - 88) * 336 * (336 - 1) → Y = 38 := by
  decide +kernel

/-- Over the root `t = 88` the point `(X, Y)` is determined. -/
theorem coords2 (y X Y : ZMod 499) (hG : G 88 y = 0) (hF : F 88 y 359 = 0)
    (hX : X * (88 * y) = -1) (hY : 2 * Y = (y - 88) * X * (X - 1)) : X = 336 ∧ Y = 38 := by
  have hy : y = 55 := uniq_y2 y hG hF
  subst hy
  have hX' : X = 336 := uniq_X2 X hX
  subst hX'
  exact ⟨rfl, uniq_Y2 Y hY⟩

/-- `t = 88` is a simple root of `Q₄`. -/
theorem diag2 : dQ4 (88 : ZMod 499) 88 359 ≠ 0 := by decide

theorem ns_336_38 : E.Nonsingular (336 : ZMod 499) 38 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_499)` over the root `t = 88`. -/
abbrev P2 : E.Point := Point.some (336 : ZMod 499) 38 ns_336_38

theorem P2_m1 : (1 : ℕ) • P2 = Point.some (336 : ZMod 499) 38 ns_336_38 := one_nsmul _
theorem ns_437_177 : E.Nonsingular (437 : ZMod 499) 177 := nonsingular_of (by decide) (by decide)
theorem step16 : Point.some (336 : ZMod 499) 38 ns_336_38 + Point.some (336 : ZMod 499) 38 ns_336_38 = Point.some (437 : ZMod 499) 177 ns_437_177 :=
  dbl_cert (ℓ := (403 : ZMod 499)) ns_336_38 ns_437_177 (by decide) (by decide) (by decide) (by decide)
theorem P2_m2 : (2 : ℕ) • P2 = Point.some (437 : ZMod 499) 177 ns_437_177 :=
  nsmul_step P2_m1 P2_m1 step16 (by norm_num)
theorem ns_26_381 : E.Nonsingular (26 : ZMod 499) 381 := nonsingular_of (by decide) (by decide)
theorem step17 : Point.some (437 : ZMod 499) 177 ns_437_177 + Point.some (437 : ZMod 499) 177 ns_437_177 = Point.some (26 : ZMod 499) 381 ns_26_381 :=
  dbl_cert (ℓ := (5 : ZMod 499)) ns_437_177 ns_26_381 (by decide) (by decide) (by decide) (by decide)
theorem P2_m4 : (4 : ℕ) • P2 = Point.some (26 : ZMod 499) 381 ns_26_381 :=
  nsmul_step P2_m2 P2_m2 step17 (by norm_num)
theorem ns_5_305 : E.Nonsingular (5 : ZMod 499) 305 := nonsingular_of (by decide) (by decide)
theorem step18 : Point.some (26 : ZMod 499) 381 ns_26_381 + Point.some (26 : ZMod 499) 381 ns_26_381 = Point.some (5 : ZMod 499) 305 ns_5_305 :=
  dbl_cert (ℓ := (199 : ZMod 499)) ns_26_381 ns_5_305 (by decide) (by decide) (by decide) (by decide)
theorem P2_m8 : (8 : ℕ) • P2 = Point.some (5 : ZMod 499) 305 ns_5_305 :=
  nsmul_step P2_m4 P2_m4 step18 (by norm_num)
theorem ns_249_470 : E.Nonsingular (249 : ZMod 499) 470 := nonsingular_of (by decide) (by decide)
theorem step19 : Point.some (5 : ZMod 499) 305 ns_5_305 + Point.some (5 : ZMod 499) 305 ns_5_305 = Point.some (249 : ZMod 499) 470 ns_249_470 :=
  dbl_cert (ℓ := (277 : ZMod 499)) ns_5_305 ns_249_470 (by decide) (by decide) (by decide) (by decide)
theorem P2_m16 : (16 : ℕ) • P2 = Point.some (249 : ZMod 499) 470 ns_249_470 :=
  nsmul_step P2_m8 P2_m8 step19 (by norm_num)
theorem ns_198_469 : E.Nonsingular (198 : ZMod 499) 469 := nonsingular_of (by decide) (by decide)
theorem step20 : Point.some (249 : ZMod 499) 470 ns_249_470 + Point.some (249 : ZMod 499) 470 ns_249_470 = Point.some (198 : ZMod 499) 469 ns_198_469 :=
  dbl_cert (ℓ := (400 : ZMod 499)) ns_249_470 ns_198_469 (by decide) (by decide) (by decide) (by decide)
theorem P2_m32 : (32 : ℕ) • P2 = Point.some (198 : ZMod 499) 469 ns_198_469 :=
  nsmul_step P2_m16 P2_m16 step20 (by norm_num)
theorem ns_169_72 : E.Nonsingular (169 : ZMod 499) 72 := nonsingular_of (by decide) (by decide)
theorem step21 : Point.some (198 : ZMod 499) 469 ns_198_469 + Point.some (198 : ZMod 499) 469 ns_198_469 = Point.some (169 : ZMod 499) 72 ns_169_72 :=
  dbl_cert (ℓ := (380 : ZMod 499)) ns_198_469 ns_169_72 (by decide) (by decide) (by decide) (by decide)
theorem P2_m64 : (64 : ℕ) • P2 = Point.some (169 : ZMod 499) 72 ns_169_72 :=
  nsmul_step P2_m32 P2_m32 step21 (by norm_num)
theorem step22 : Point.some (169 : ZMod 499) 72 ns_169_72 + Point.some (198 : ZMod 499) 469 ns_198_469 = Point.some (197 : ZMod 499) 319 ns_197_319 :=
  add_cert (ℓ := (289 : ZMod 499)) ns_169_72 ns_198_469 ns_197_319 (by decide) (by decide) (by decide) (by decide)
theorem P2_m96 : (96 : ℕ) • P2 = Point.some (197 : ZMod 499) 319 ns_197_319 :=
  nsmul_step P2_m64 P2_m32 step22 (by norm_num)
theorem ns_211_5 : E.Nonsingular (211 : ZMod 499) 5 := nonsingular_of (by decide) (by decide)
theorem step23 : Point.some (197 : ZMod 499) 319 ns_197_319 + Point.some (249 : ZMod 499) 470 ns_249_470 = Point.some (211 : ZMod 499) 5 ns_211_5 :=
  add_cert (ℓ := (262 : ZMod 499)) ns_197_319 ns_249_470 ns_211_5 (by decide) (by decide) (by decide) (by decide)
theorem P2_m112 : (112 : ℕ) • P2 = Point.some (211 : ZMod 499) 5 ns_211_5 :=
  nsmul_step P2_m96 P2_m16 step23 (by norm_num)
theorem ns_26_118 : E.Nonsingular (26 : ZMod 499) 118 := nonsingular_of (by decide) (by decide)
theorem step24 : Point.some (211 : ZMod 499) 5 ns_211_5 + Point.some (5 : ZMod 499) 305 ns_5_305 = Point.some (26 : ZMod 499) 118 ns_26_118 :=
  add_cert (ℓ := (265 : ZMod 499)) ns_211_5 ns_5_305 ns_26_118 (by decide) (by decide) (by decide) (by decide)
theorem P2_m120 : (120 : ℕ) • P2 = Point.some (26 : ZMod 499) 118 ns_26_118 :=
  nsmul_step P2_m112 P2_m8 step24 (by norm_num)
theorem step25 : Point.some (26 : ZMod 499) 118 ns_26_118 + Point.some (26 : ZMod 499) 381 ns_26_381 = (0 : E.Point) :=
  add_zero_cert ns_26_118 ns_26_381 (by decide) (by decide)
theorem P2_m124 : (124 : ℕ) • P2 = (0 : E.Point) :=
  nsmul_step P2_m120 P2_m4 step25 (by norm_num)

/-- `124 • P2 = 0`. -/
theorem P2_nsmul_order : (124 : ℕ) • P2 = 0 := P2_m124
theorem step26 : Point.some (198 : ZMod 499) 469 ns_198_469 + Point.some (249 : ZMod 499) 470 ns_249_470 = Point.some (235 : ZMod 499) 450 ns_235_450 :=
  add_cert (ℓ := (137 : ZMod 499)) ns_198_469 ns_249_470 ns_235_450 (by decide) (by decide) (by decide) (by decide)
theorem P2_m48 : (48 : ℕ) • P2 = Point.some (235 : ZMod 499) 450 ns_235_450 :=
  nsmul_step P2_m32 P2_m16 step26 (by norm_num)
theorem ns_64_428 : E.Nonsingular (64 : ZMod 499) 428 := nonsingular_of (by decide) (by decide)
theorem step27 : Point.some (235 : ZMod 499) 450 ns_235_450 + Point.some (5 : ZMod 499) 305 ns_5_305 = Point.some (64 : ZMod 499) 428 ns_64_428 :=
  add_cert (ℓ := (402 : ZMod 499)) ns_235_450 ns_5_305 ns_64_428 (by decide) (by decide) (by decide) (by decide)
theorem P2_m56 : (56 : ℕ) • P2 = Point.some (64 : ZMod 499) 428 ns_64_428 :=
  nsmul_step P2_m48 P2_m8 step27 (by norm_num)
theorem ns_169_427 : E.Nonsingular (169 : ZMod 499) 427 := nonsingular_of (by decide) (by decide)
theorem step28 : Point.some (64 : ZMod 499) 428 ns_64_428 + Point.some (26 : ZMod 499) 381 ns_26_381 = Point.some (169 : ZMod 499) 427 ns_169_427 :=
  add_cert (ℓ := (277 : ZMod 499)) ns_64_428 ns_26_381 ns_169_427 (by decide) (by decide) (by decide) (by decide)
theorem P2_m60 : (60 : ℕ) • P2 = Point.some (169 : ZMod 499) 427 ns_169_427 :=
  nsmul_step P2_m56 P2_m4 step28 (by norm_num)
theorem step29 : Point.some (169 : ZMod 499) 427 ns_169_427 + Point.some (437 : ZMod 499) 177 ns_437_177 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  add_cert (ℓ := (472 : ZMod 499)) ns_169_427 ns_437_177 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P2_m62 : (62 : ℕ) • P2 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  nsmul_step P2_m60 P2_m2 step29 (by norm_num)

/-- `(124/2) • P2 ≠ 0`. -/
theorem P2_nsmul_62_ne : (62 : ℕ) • P2 ≠ 0 := by
  rw [P2_m62]
  exact Point.some_ne_zero _

/-- `(124/31) • P2 ≠ 0`. -/
theorem P2_nsmul_4_ne : (4 : ℕ) • P2 ≠ 0 := by
  rw [P2_m4]
  exact Point.some_ne_zero _

/-- `P2` has exact order `124` in `E(𝔽_499)`. -/
theorem P2_addOrderOf : addOrderOf P2 = 124 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul P2_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 2 * 31 ^ 1 : ℕ) = 124 := by norm_num
  have h : q ∣ 2 ^ 2 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact P2_nsmul_62_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact P2_nsmul_4_ne

/-! ## Root `t = 316`: `y = 367`, `(X, Y) = (340, 20)`, order `62` -/

/-- `(t, y) = (316, 367)` lies on `G = 0` and `F = 0`, and `(X, Y) = (340, 20)` is its image. -/
theorem link3 : G (316 : ZMod 499) 367 = 0 ∧ F (316 : ZMod 499) 367 359 = 0 ∧
    (340 : ZMod 499) * (316 * 367) = -1 ∧ 2 * (20 : ZMod 499) = (367 - 316) * 340 * (340 - 1) := by
  decide

theorem uniq_y3 : ∀ y : ZMod 499, G 316 y = 0 → F 316 y 359 = 0 → y = 367 := by
  decide +kernel
theorem uniq_X3 : ∀ X : ZMod 499, X * (316 * 367) = -1 → X = 340 := by
  decide +kernel
theorem uniq_Y3 : ∀ Y : ZMod 499, 2 * Y = (367 - 316) * 340 * (340 - 1) → Y = 20 := by
  decide +kernel

/-- Over the root `t = 316` the point `(X, Y)` is determined. -/
theorem coords3 (y X Y : ZMod 499) (hG : G 316 y = 0) (hF : F 316 y 359 = 0)
    (hX : X * (316 * y) = -1) (hY : 2 * Y = (y - 316) * X * (X - 1)) : X = 340 ∧ Y = 20 := by
  have hy : y = 367 := uniq_y3 y hG hF
  subst hy
  have hX' : X = 340 := uniq_X3 X hX
  subst hX'
  exact ⟨rfl, uniq_Y3 Y hY⟩

/-- `t = 316` is a simple root of `Q₄`. -/
theorem diag3 : dQ4 (316 : ZMod 499) 316 359 ≠ 0 := by decide

theorem ns_340_20 : E.Nonsingular (340 : ZMod 499) 20 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_499)` over the root `t = 316`. -/
abbrev P3 : E.Point := Point.some (340 : ZMod 499) 20 ns_340_20

theorem P3_m1 : (1 : ℕ) • P3 = Point.some (340 : ZMod 499) 20 ns_340_20 := one_nsmul _
theorem step30 : Point.some (340 : ZMod 499) 20 ns_340_20 + Point.some (340 : ZMod 499) 20 ns_340_20 = Point.some (224 : ZMod 499) 210 ns_224_210 :=
  dbl_cert (ℓ := (45 : ZMod 499)) ns_340_20 ns_224_210 (by decide) (by decide) (by decide) (by decide)
theorem P3_m2 : (2 : ℕ) • P3 = Point.some (224 : ZMod 499) 210 ns_224_210 :=
  nsmul_step P3_m1 P3_m1 step30 (by norm_num)
theorem ns_364_274 : E.Nonsingular (364 : ZMod 499) 274 := nonsingular_of (by decide) (by decide)
theorem step31 : Point.some (224 : ZMod 499) 210 ns_224_210 + Point.some (224 : ZMod 499) 210 ns_224_210 = Point.some (364 : ZMod 499) 274 ns_364_274 :=
  dbl_cert (ℓ := (410 : ZMod 499)) ns_224_210 ns_364_274 (by decide) (by decide) (by decide) (by decide)
theorem P3_m4 : (4 : ℕ) • P3 = Point.some (364 : ZMod 499) 274 ns_364_274 :=
  nsmul_step P3_m2 P3_m2 step31 (by norm_num)
theorem ns_247_53 : E.Nonsingular (247 : ZMod 499) 53 := nonsingular_of (by decide) (by decide)
theorem step32 : Point.some (364 : ZMod 499) 274 ns_364_274 + Point.some (364 : ZMod 499) 274 ns_364_274 = Point.some (247 : ZMod 499) 53 ns_247_53 :=
  dbl_cert (ℓ := (489 : ZMod 499)) ns_364_274 ns_247_53 (by decide) (by decide) (by decide) (by decide)
theorem P3_m8 : (8 : ℕ) • P3 = Point.some (247 : ZMod 499) 53 ns_247_53 :=
  nsmul_step P3_m4 P3_m4 step32 (by norm_num)
theorem ns_139_202 : E.Nonsingular (139 : ZMod 499) 202 := nonsingular_of (by decide) (by decide)
theorem step33 : Point.some (247 : ZMod 499) 53 ns_247_53 + Point.some (247 : ZMod 499) 53 ns_247_53 = Point.some (139 : ZMod 499) 202 ns_139_202 :=
  dbl_cert (ℓ := (238 : ZMod 499)) ns_247_53 ns_139_202 (by decide) (by decide) (by decide) (by decide)
theorem P3_m16 : (16 : ℕ) • P3 = Point.some (139 : ZMod 499) 202 ns_139_202 :=
  nsmul_step P3_m8 P3_m8 step33 (by norm_num)
theorem step34 : Point.some (139 : ZMod 499) 202 ns_139_202 + Point.some (139 : ZMod 499) 202 ns_139_202 = Point.some (91 : ZMod 499) 224 ns_91_224 :=
  dbl_cert (ℓ := (196 : ZMod 499)) ns_139_202 ns_91_224 (by decide) (by decide) (by decide) (by decide)
theorem P3_m32 : (32 : ℕ) • P3 = Point.some (91 : ZMod 499) 224 ns_91_224 :=
  nsmul_step P3_m16 P3_m16 step34 (by norm_num)
theorem ns_5_194 : E.Nonsingular (5 : ZMod 499) 194 := nonsingular_of (by decide) (by decide)
theorem step35 : Point.some (91 : ZMod 499) 224 ns_91_224 + Point.some (139 : ZMod 499) 202 ns_139_202 = Point.some (5 : ZMod 499) 194 ns_5_194 :=
  add_cert (ℓ := (353 : ZMod 499)) ns_91_224 ns_139_202 ns_5_194 (by decide) (by decide) (by decide) (by decide)
theorem P3_m48 : (48 : ℕ) • P3 = Point.some (5 : ZMod 499) 194 ns_5_194 :=
  nsmul_step P3_m32 P3_m16 step35 (by norm_num)
theorem step36 : Point.some (5 : ZMod 499) 194 ns_5_194 + Point.some (247 : ZMod 499) 53 ns_247_53 = Point.some (198 : ZMod 499) 469 ns_198_469 :=
  add_cert (ℓ := (418 : ZMod 499)) ns_5_194 ns_247_53 ns_198_469 (by decide) (by decide) (by decide) (by decide)
theorem P3_m56 : (56 : ℕ) • P3 = Point.some (198 : ZMod 499) 469 ns_198_469 :=
  nsmul_step P3_m48 P3_m8 step36 (by norm_num)
theorem ns_224_289 : E.Nonsingular (224 : ZMod 499) 289 := nonsingular_of (by decide) (by decide)
theorem step37 : Point.some (198 : ZMod 499) 469 ns_198_469 + Point.some (364 : ZMod 499) 274 ns_364_274 = Point.some (224 : ZMod 499) 289 ns_224_289 :=
  add_cert (ℓ := (86 : ZMod 499)) ns_198_469 ns_364_274 ns_224_289 (by decide) (by decide) (by decide) (by decide)
theorem P3_m60 : (60 : ℕ) • P3 = Point.some (224 : ZMod 499) 289 ns_224_289 :=
  nsmul_step P3_m56 P3_m4 step37 (by norm_num)
theorem step38 : Point.some (224 : ZMod 499) 289 ns_224_289 + Point.some (224 : ZMod 499) 210 ns_224_210 = (0 : E.Point) :=
  add_zero_cert ns_224_289 ns_224_210 (by decide) (by decide)
theorem P3_m62 : (62 : ℕ) • P3 = (0 : E.Point) :=
  nsmul_step P3_m60 P3_m2 step38 (by norm_num)

/-- `62 • P3 = 0`. -/
theorem P3_nsmul_order : (62 : ℕ) • P3 = 0 := P3_m62
theorem step39 : Point.some (139 : ZMod 499) 202 ns_139_202 + Point.some (247 : ZMod 499) 53 ns_247_53 = Point.some (26 : ZMod 499) 118 ns_26_118 :=
  add_cert (ℓ := (493 : ZMod 499)) ns_139_202 ns_247_53 ns_26_118 (by decide) (by decide) (by decide) (by decide)
theorem P3_m24 : (24 : ℕ) • P3 = Point.some (26 : ZMod 499) 118 ns_26_118 :=
  nsmul_step P3_m16 P3_m8 step39 (by norm_num)
theorem step40 : Point.some (26 : ZMod 499) 118 ns_26_118 + Point.some (364 : ZMod 499) 274 ns_364_274 = Point.some (249 : ZMod 499) 470 ns_249_470 :=
  add_cert (ℓ := (154 : ZMod 499)) ns_26_118 ns_364_274 ns_249_470 (by decide) (by decide) (by decide) (by decide)
theorem P3_m28 : (28 : ℕ) • P3 = Point.some (249 : ZMod 499) 470 ns_249_470 :=
  nsmul_step P3_m24 P3_m4 step40 (by norm_num)
theorem ns_91_275 : E.Nonsingular (91 : ZMod 499) 275 := nonsingular_of (by decide) (by decide)
theorem step41 : Point.some (249 : ZMod 499) 470 ns_249_470 + Point.some (224 : ZMod 499) 210 ns_224_210 = Point.some (91 : ZMod 499) 275 ns_91_275 :=
  add_cert (ℓ := (210 : ZMod 499)) ns_249_470 ns_224_210 ns_91_275 (by decide) (by decide) (by decide) (by decide)
theorem P3_m30 : (30 : ℕ) • P3 = Point.some (91 : ZMod 499) 275 ns_91_275 :=
  nsmul_step P3_m28 P3_m2 step41 (by norm_num)
theorem ns_66_0 : E.Nonsingular (66 : ZMod 499) 0 := nonsingular_of (by decide) (by decide)
theorem step42 : Point.some (91 : ZMod 499) 275 ns_91_275 + Point.some (340 : ZMod 499) 20 ns_340_20 = Point.some (66 : ZMod 499) 0 ns_66_0 :=
  add_cert (ℓ := (11 : ZMod 499)) ns_91_275 ns_340_20 ns_66_0 (by decide) (by decide) (by decide) (by decide)
theorem P3_m31 : (31 : ℕ) • P3 = Point.some (66 : ZMod 499) 0 ns_66_0 :=
  nsmul_step P3_m30 P3_m1 step42 (by norm_num)

/-- `(62/2) • P3 ≠ 0`. -/
theorem P3_nsmul_31_ne : (31 : ℕ) • P3 ≠ 0 := by
  rw [P3_m31]
  exact Point.some_ne_zero _

/-- `(62/31) • P3 ≠ 0`. -/
theorem P3_nsmul_2_ne : (2 : ℕ) • P3 ≠ 0 := by
  rw [P3_m2]
  exact Point.some_ne_zero _

/-- `P3` has exact order `62` in `E(𝔽_499)`. -/
theorem P3_addOrderOf : addOrderOf P3 = 62 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul P3_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 1 * 31 ^ 1 : ℕ) = 62 := by norm_num
  have h : q ∣ 2 ^ 1 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact P3_nsmul_31_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact P3_nsmul_2_ne

/-! ## Root `t = 497`: `y = 424`, `(X, Y) = (163, 249)`, order `124` -/

/-- `(t, y) = (497, 424)` lies on `G = 0` and `F = 0`, and `(X, Y) = (163, 249)` is its image. -/
theorem link4 : G (497 : ZMod 499) 424 = 0 ∧ F (497 : ZMod 499) 424 359 = 0 ∧
    (163 : ZMod 499) * (497 * 424) = -1 ∧ 2 * (249 : ZMod 499) = (424 - 497) * 163 * (163 - 1) := by
  decide

theorem uniq_y4 : ∀ y : ZMod 499, G 497 y = 0 → F 497 y 359 = 0 → y = 424 := by
  decide +kernel
theorem uniq_X4 : ∀ X : ZMod 499, X * (497 * 424) = -1 → X = 163 := by
  decide +kernel
theorem uniq_Y4 : ∀ Y : ZMod 499, 2 * Y = (424 - 497) * 163 * (163 - 1) → Y = 249 := by
  decide +kernel

/-- Over the root `t = 497` the point `(X, Y)` is determined. -/
theorem coords4 (y X Y : ZMod 499) (hG : G 497 y = 0) (hF : F 497 y 359 = 0)
    (hX : X * (497 * y) = -1) (hY : 2 * Y = (y - 497) * X * (X - 1)) : X = 163 ∧ Y = 249 := by
  have hy : y = 424 := uniq_y4 y hG hF
  subst hy
  have hX' : X = 163 := uniq_X4 X hX
  subst hX'
  exact ⟨rfl, uniq_Y4 Y hY⟩

/-- `t = 497` is a simple root of `Q₄`. -/
theorem diag4 : dQ4 (497 : ZMod 499) 497 359 ≠ 0 := by decide

theorem ns_163_249 : E.Nonsingular (163 : ZMod 499) 249 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_499)` over the root `t = 497`. -/
abbrev P4 : E.Point := Point.some (163 : ZMod 499) 249 ns_163_249

theorem P4_m1 : (1 : ℕ) • P4 = Point.some (163 : ZMod 499) 249 ns_163_249 := one_nsmul _
theorem ns_170_73 : E.Nonsingular (170 : ZMod 499) 73 := nonsingular_of (by decide) (by decide)
theorem step43 : Point.some (163 : ZMod 499) 249 ns_163_249 + Point.some (163 : ZMod 499) 249 ns_163_249 = Point.some (170 : ZMod 499) 73 ns_170_73 :=
  dbl_cert (ℓ := (453 : ZMod 499)) ns_163_249 ns_170_73 (by decide) (by decide) (by decide) (by decide)
theorem P4_m2 : (2 : ℕ) • P4 = Point.some (170 : ZMod 499) 73 ns_170_73 :=
  nsmul_step P4_m1 P4_m1 step43 (by norm_num)
theorem step44 : Point.some (170 : ZMod 499) 73 ns_170_73 + Point.some (170 : ZMod 499) 73 ns_170_73 = Point.some (224 : ZMod 499) 289 ns_224_289 :=
  dbl_cert (ℓ := (289 : ZMod 499)) ns_170_73 ns_224_289 (by decide) (by decide) (by decide) (by decide)
theorem P4_m4 : (4 : ℕ) • P4 = Point.some (224 : ZMod 499) 289 ns_224_289 :=
  nsmul_step P4_m2 P4_m2 step44 (by norm_num)
theorem step45 : Point.some (224 : ZMod 499) 289 ns_224_289 + Point.some (224 : ZMod 499) 289 ns_224_289 = Point.some (364 : ZMod 499) 225 ns_364_225 :=
  dbl_cert (ℓ := (89 : ZMod 499)) ns_224_289 ns_364_225 (by decide) (by decide) (by decide) (by decide)
theorem P4_m8 : (8 : ℕ) • P4 = Point.some (364 : ZMod 499) 225 ns_364_225 :=
  nsmul_step P4_m4 P4_m4 step45 (by norm_num)
theorem step46 : Point.some (364 : ZMod 499) 225 ns_364_225 + Point.some (364 : ZMod 499) 225 ns_364_225 = Point.some (247 : ZMod 499) 446 ns_247_446 :=
  dbl_cert (ℓ := (10 : ZMod 499)) ns_364_225 ns_247_446 (by decide) (by decide) (by decide) (by decide)
theorem P4_m16 : (16 : ℕ) • P4 = Point.some (247 : ZMod 499) 446 ns_247_446 :=
  nsmul_step P4_m8 P4_m8 step46 (by norm_num)
theorem ns_139_297 : E.Nonsingular (139 : ZMod 499) 297 := nonsingular_of (by decide) (by decide)
theorem step47 : Point.some (247 : ZMod 499) 446 ns_247_446 + Point.some (247 : ZMod 499) 446 ns_247_446 = Point.some (139 : ZMod 499) 297 ns_139_297 :=
  dbl_cert (ℓ := (261 : ZMod 499)) ns_247_446 ns_139_297 (by decide) (by decide) (by decide) (by decide)
theorem P4_m32 : (32 : ℕ) • P4 = Point.some (139 : ZMod 499) 297 ns_139_297 :=
  nsmul_step P4_m16 P4_m16 step47 (by norm_num)
theorem step48 : Point.some (139 : ZMod 499) 297 ns_139_297 + Point.some (139 : ZMod 499) 297 ns_139_297 = Point.some (91 : ZMod 499) 275 ns_91_275 :=
  dbl_cert (ℓ := (303 : ZMod 499)) ns_139_297 ns_91_275 (by decide) (by decide) (by decide) (by decide)
theorem P4_m64 : (64 : ℕ) • P4 = Point.some (91 : ZMod 499) 275 ns_91_275 :=
  nsmul_step P4_m32 P4_m32 step48 (by norm_num)
theorem step49 : Point.some (91 : ZMod 499) 275 ns_91_275 + Point.some (139 : ZMod 499) 297 ns_139_297 = Point.some (5 : ZMod 499) 305 ns_5_305 :=
  add_cert (ℓ := (146 : ZMod 499)) ns_91_275 ns_139_297 ns_5_305 (by decide) (by decide) (by decide) (by decide)
theorem P4_m96 : (96 : ℕ) • P4 = Point.some (5 : ZMod 499) 305 ns_5_305 :=
  nsmul_step P4_m64 P4_m32 step49 (by norm_num)
theorem ns_198_30 : E.Nonsingular (198 : ZMod 499) 30 := nonsingular_of (by decide) (by decide)
theorem step50 : Point.some (5 : ZMod 499) 305 ns_5_305 + Point.some (247 : ZMod 499) 446 ns_247_446 = Point.some (198 : ZMod 499) 30 ns_198_30 :=
  add_cert (ℓ := (81 : ZMod 499)) ns_5_305 ns_247_446 ns_198_30 (by decide) (by decide) (by decide) (by decide)
theorem P4_m112 : (112 : ℕ) • P4 = Point.some (198 : ZMod 499) 30 ns_198_30 :=
  nsmul_step P4_m96 P4_m16 step50 (by norm_num)
theorem step51 : Point.some (198 : ZMod 499) 30 ns_198_30 + Point.some (364 : ZMod 499) 225 ns_364_225 = Point.some (224 : ZMod 499) 210 ns_224_210 :=
  add_cert (ℓ := (413 : ZMod 499)) ns_198_30 ns_364_225 ns_224_210 (by decide) (by decide) (by decide) (by decide)
theorem P4_m120 : (120 : ℕ) • P4 = Point.some (224 : ZMod 499) 210 ns_224_210 :=
  nsmul_step P4_m112 P4_m8 step51 (by norm_num)
theorem step52 : Point.some (224 : ZMod 499) 210 ns_224_210 + Point.some (224 : ZMod 499) 289 ns_224_289 = (0 : E.Point) :=
  add_zero_cert ns_224_210 ns_224_289 (by decide) (by decide)
theorem P4_m124 : (124 : ℕ) • P4 = (0 : E.Point) :=
  nsmul_step P4_m120 P4_m4 step52 (by norm_num)

/-- `124 • P4 = 0`. -/
theorem P4_nsmul_order : (124 : ℕ) • P4 = 0 := P4_m124
theorem step53 : Point.some (139 : ZMod 499) 297 ns_139_297 + Point.some (247 : ZMod 499) 446 ns_247_446 = Point.some (26 : ZMod 499) 381 ns_26_381 :=
  add_cert (ℓ := (6 : ZMod 499)) ns_139_297 ns_247_446 ns_26_381 (by decide) (by decide) (by decide) (by decide)
theorem P4_m48 : (48 : ℕ) • P4 = Point.some (26 : ZMod 499) 381 ns_26_381 :=
  nsmul_step P4_m32 P4_m16 step53 (by norm_num)
theorem ns_249_29 : E.Nonsingular (249 : ZMod 499) 29 := nonsingular_of (by decide) (by decide)
theorem step54 : Point.some (26 : ZMod 499) 381 ns_26_381 + Point.some (364 : ZMod 499) 225 ns_364_225 = Point.some (249 : ZMod 499) 29 ns_249_29 :=
  add_cert (ℓ := (345 : ZMod 499)) ns_26_381 ns_364_225 ns_249_29 (by decide) (by decide) (by decide) (by decide)
theorem P4_m56 : (56 : ℕ) • P4 = Point.some (249 : ZMod 499) 29 ns_249_29 :=
  nsmul_step P4_m48 P4_m8 step54 (by norm_num)
theorem step55 : Point.some (249 : ZMod 499) 29 ns_249_29 + Point.some (224 : ZMod 499) 289 ns_224_289 = Point.some (91 : ZMod 499) 224 ns_91_224 :=
  add_cert (ℓ := (289 : ZMod 499)) ns_249_29 ns_224_289 ns_91_224 (by decide) (by decide) (by decide) (by decide)
theorem P4_m60 : (60 : ℕ) • P4 = Point.some (91 : ZMod 499) 224 ns_91_224 :=
  nsmul_step P4_m56 P4_m4 step55 (by norm_num)
theorem step56 : Point.some (91 : ZMod 499) 224 ns_91_224 + Point.some (170 : ZMod 499) 73 ns_170_73 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  add_cert (ℓ := (156 : ZMod 499)) ns_91_224 ns_170_73 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P4_m62 : (62 : ℕ) • P4 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  nsmul_step P4_m60 P4_m2 step56 (by norm_num)

/-- `(124/2) • P4 ≠ 0`. -/
theorem P4_nsmul_62_ne : (62 : ℕ) • P4 ≠ 0 := by
  rw [P4_m62]
  exact Point.some_ne_zero _

/-- `(124/31) • P4 ≠ 0`. -/
theorem P4_nsmul_4_ne : (4 : ℕ) • P4 ≠ 0 := by
  rw [P4_m4]
  exact Point.some_ne_zero _

/-- `P4` has exact order `124` in `E(𝔽_499)`. -/
theorem P4_addOrderOf : addOrderOf P4 = 124 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul P4_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 2 * 31 ^ 1 : ℕ) = 124 := by norm_num
  have h : q ∣ 2 ^ 2 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact P4_nsmul_62_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact P4_nsmul_4_ne

/-! ## Differences of the four points -/

/-! ### `P1 - P2` -/

theorem ns_336_461 : E.Nonsingular (336 : ZMod 499) 461 := nonsingular_of (by decide) (by decide)
theorem ns_408_267 : E.Nonsingular (408 : ZMod 499) 267 := nonsingular_of (by decide) (by decide)
theorem step57 : Point.some (301 : ZMod 499) 205 ns_301_205 + Point.some (336 : ZMod 499) 461 ns_336_461 = Point.some (408 : ZMod 499) 267 ns_408_267 :=
  add_cert (ℓ := (378 : ZMod 499)) ns_301_205 ns_336_461 ns_408_267 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P1 - P2` as an explicit point. -/
theorem D12_eq : P1 - P2 = Point.some (408 : ZMod 499) 267 ns_408_267 :=
  sub_cert ns_301_205 ns_336_38 ns_336_461 ns_408_267 (by decide) step57

abbrev D12 : E.Point := Point.some (408 : ZMod 499) 267 ns_408_267

theorem D12_m1 : (1 : ℕ) • D12 = Point.some (408 : ZMod 499) 267 ns_408_267 := one_nsmul _
theorem ns_353_459 : E.Nonsingular (353 : ZMod 499) 459 := nonsingular_of (by decide) (by decide)
theorem step58 : Point.some (408 : ZMod 499) 267 ns_408_267 + Point.some (408 : ZMod 499) 267 ns_408_267 = Point.some (353 : ZMod 499) 459 ns_353_459 :=
  dbl_cert (ℓ := (113 : ZMod 499)) ns_408_267 ns_353_459 (by decide) (by decide) (by decide) (by decide)
theorem D12_m2 : (2 : ℕ) • D12 = Point.some (353 : ZMod 499) 459 ns_353_459 :=
  nsmul_step D12_m1 D12_m1 step58 (by norm_num)
theorem ns_359_134 : E.Nonsingular (359 : ZMod 499) 134 := nonsingular_of (by decide) (by decide)
theorem step59 : Point.some (353 : ZMod 499) 459 ns_353_459 + Point.some (353 : ZMod 499) 459 ns_353_459 = Point.some (359 : ZMod 499) 134 ns_359_134 :=
  dbl_cert (ℓ := (317 : ZMod 499)) ns_353_459 ns_359_134 (by decide) (by decide) (by decide) (by decide)
theorem D12_m4 : (4 : ℕ) • D12 = Point.some (359 : ZMod 499) 134 ns_359_134 :=
  nsmul_step D12_m2 D12_m2 step59 (by norm_num)
theorem step60 : Point.some (359 : ZMod 499) 134 ns_359_134 + Point.some (359 : ZMod 499) 134 ns_359_134 = Point.some (91 : ZMod 499) 275 ns_91_275 :=
  dbl_cert (ℓ := (130 : ZMod 499)) ns_359_134 ns_91_275 (by decide) (by decide) (by decide) (by decide)
theorem D12_m8 : (8 : ℕ) • D12 = Point.some (91 : ZMod 499) 275 ns_91_275 :=
  nsmul_step D12_m4 D12_m4 step60 (by norm_num)
theorem step61 : Point.some (91 : ZMod 499) 275 ns_91_275 + Point.some (91 : ZMod 499) 275 ns_91_275 = Point.some (224 : ZMod 499) 289 ns_224_289 :=
  dbl_cert (ℓ := (476 : ZMod 499)) ns_91_275 ns_224_289 (by decide) (by decide) (by decide) (by decide)
theorem D12_m16 : (16 : ℕ) • D12 = Point.some (224 : ZMod 499) 289 ns_224_289 :=
  nsmul_step D12_m8 D12_m8 step61 (by norm_num)
theorem D12_m32 : (32 : ℕ) • D12 = Point.some (364 : ZMod 499) 225 ns_364_225 :=
  nsmul_step D12_m16 D12_m16 step45 (by norm_num)
theorem D12_m64 : (64 : ℕ) • D12 = Point.some (247 : ZMod 499) 446 ns_247_446 :=
  nsmul_step D12_m32 D12_m32 step46 (by norm_num)
theorem D12_m128 : (128 : ℕ) • D12 = Point.some (139 : ZMod 499) 297 ns_139_297 :=
  nsmul_step D12_m64 D12_m64 step47 (by norm_num)
theorem D12_m192 : (192 : ℕ) • D12 = Point.some (26 : ZMod 499) 381 ns_26_381 :=
  nsmul_step D12_m128 D12_m64 step53 (by norm_num)
theorem D12_m224 : (224 : ℕ) • D12 = Point.some (249 : ZMod 499) 29 ns_249_29 :=
  nsmul_step D12_m192 D12_m32 step54 (by norm_num)
theorem D12_m240 : (240 : ℕ) • D12 = Point.some (91 : ZMod 499) 224 ns_91_224 :=
  nsmul_step D12_m224 D12_m16 step55 (by norm_num)
theorem step62 : Point.some (91 : ZMod 499) 224 ns_91_224 + Point.some (91 : ZMod 499) 275 ns_91_275 = (0 : E.Point) :=
  add_zero_cert ns_91_224 ns_91_275 (by decide) (by decide)
theorem D12_m248 : (248 : ℕ) • D12 = (0 : E.Point) :=
  nsmul_step D12_m240 D12_m8 step62 (by norm_num)

/-- `248 • D12 = 0`. -/
theorem D12_nsmul_order : (248 : ℕ) • D12 = 0 := D12_m248
theorem step63 : Point.some (247 : ZMod 499) 446 ns_247_446 + Point.some (364 : ZMod 499) 225 ns_364_225 = Point.some (169 : ZMod 499) 72 ns_169_72 :=
  add_cert (ℓ := (109 : ZMod 499)) ns_247_446 ns_364_225 ns_169_72 (by decide) (by decide) (by decide) (by decide)
theorem D12_m96 : (96 : ℕ) • D12 = Point.some (169 : ZMod 499) 72 ns_169_72 :=
  nsmul_step D12_m64 D12_m32 step63 (by norm_num)
theorem step64 : Point.some (169 : ZMod 499) 72 ns_169_72 + Point.some (224 : ZMod 499) 289 ns_224_289 = Point.some (5 : ZMod 499) 194 ns_5_194 :=
  add_cert (ℓ := (385 : ZMod 499)) ns_169_72 ns_224_289 ns_5_194 (by decide) (by decide) (by decide) (by decide)
theorem D12_m112 : (112 : ℕ) • D12 = Point.some (5 : ZMod 499) 194 ns_5_194 :=
  nsmul_step D12_m96 D12_m16 step64 (by norm_num)
theorem step65 : Point.some (5 : ZMod 499) 194 ns_5_194 + Point.some (91 : ZMod 499) 275 ns_91_275 = Point.some (139 : ZMod 499) 202 ns_139_202 :=
  add_cert (ℓ := (146 : ZMod 499)) ns_5_194 ns_91_275 ns_139_202 (by decide) (by decide) (by decide) (by decide)
theorem D12_m120 : (120 : ℕ) • D12 = Point.some (139 : ZMod 499) 202 ns_139_202 :=
  nsmul_step D12_m112 D12_m8 step65 (by norm_num)
theorem step66 : Point.some (139 : ZMod 499) 202 ns_139_202 + Point.some (359 : ZMod 499) 134 ns_359_134 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  add_cert (ℓ := (163 : ZMod 499)) ns_139_202 ns_359_134 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D12_m124 : (124 : ℕ) • D12 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  nsmul_step D12_m120 D12_m4 step66 (by norm_num)

/-- `(248/2) • D12 ≠ 0`. -/
theorem D12_nsmul_124_ne : (124 : ℕ) • D12 ≠ 0 := by
  rw [D12_m124]
  exact Point.some_ne_zero _

/-- `(248/31) • D12 ≠ 0`. -/
theorem D12_nsmul_8_ne : (8 : ℕ) • D12 ≠ 0 := by
  rw [D12_m8]
  exact Point.some_ne_zero _

/-- `D12` has exact order `248` in `E(𝔽_499)`. -/
theorem D12_addOrderOf : addOrderOf D12 = 248 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D12_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 * 31 ^ 1 : ℕ) = 248 := by norm_num
  have h : q ∣ 2 ^ 3 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact D12_nsmul_124_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact D12_nsmul_8_ne

theorem P1_sub_P2_addOrderOf : addOrderOf (P1 - P2) = 248 := by
  rw [D12_eq]
  exact D12_addOrderOf

theorem P2_sub_P1_addOrderOf : addOrderOf (P2 - P1) = 248 := by
  rw [← neg_sub P1 P2, addOrderOf_neg]
  exact P1_sub_P2_addOrderOf

/-! ### `P1 - P3` -/

theorem ns_340_479 : E.Nonsingular (340 : ZMod 499) 479 := nonsingular_of (by decide) (by decide)
theorem ns_285_432 : E.Nonsingular (285 : ZMod 499) 432 := nonsingular_of (by decide) (by decide)
theorem step67 : Point.some (301 : ZMod 499) 205 ns_301_205 + Point.some (340 : ZMod 499) 479 ns_340_479 = Point.some (285 : ZMod 499) 432 ns_285_432 :=
  add_cert (ℓ := (71 : ZMod 499)) ns_301_205 ns_340_479 ns_285_432 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P1 - P3` as an explicit point. -/
theorem D13_eq : P1 - P3 = Point.some (285 : ZMod 499) 432 ns_285_432 :=
  sub_cert ns_301_205 ns_340_20 ns_340_479 ns_285_432 (by decide) step67

abbrev D13 : E.Point := Point.some (285 : ZMod 499) 432 ns_285_432

theorem D13_m1 : (1 : ℕ) • D13 = Point.some (285 : ZMod 499) 432 ns_285_432 := one_nsmul _
theorem ns_88_151 : E.Nonsingular (88 : ZMod 499) 151 := nonsingular_of (by decide) (by decide)
theorem step68 : Point.some (285 : ZMod 499) 432 ns_285_432 + Point.some (285 : ZMod 499) 432 ns_285_432 = Point.some (88 : ZMod 499) 151 ns_88_151 :=
  dbl_cert (ℓ := (198 : ZMod 499)) ns_285_432 ns_88_151 (by decide) (by decide) (by decide) (by decide)
theorem D13_m2 : (2 : ℕ) • D13 = Point.some (88 : ZMod 499) 151 ns_88_151 :=
  nsmul_step D13_m1 D13_m1 step68 (by norm_num)
theorem ns_38_59 : E.Nonsingular (38 : ZMod 499) 59 := nonsingular_of (by decide) (by decide)
theorem step69 : Point.some (88 : ZMod 499) 151 ns_88_151 + Point.some (88 : ZMod 499) 151 ns_88_151 = Point.some (38 : ZMod 499) 59 ns_38_59 :=
  dbl_cert (ℓ := (104 : ZMod 499)) ns_88_151 ns_38_59 (by decide) (by decide) (by decide) (by decide)
theorem D13_m4 : (4 : ℕ) • D13 = Point.some (38 : ZMod 499) 59 ns_38_59 :=
  nsmul_step D13_m2 D13_m2 step69 (by norm_num)
theorem step70 : Point.some (38 : ZMod 499) 59 ns_38_59 + Point.some (38 : ZMod 499) 59 ns_38_59 = Point.some (64 : ZMod 499) 428 ns_64_428 :=
  dbl_cert (ℓ := (154 : ZMod 499)) ns_38_59 ns_64_428 (by decide) (by decide) (by decide) (by decide)
theorem D13_m8 : (8 : ℕ) • D13 = Point.some (64 : ZMod 499) 428 ns_64_428 :=
  nsmul_step D13_m4 D13_m4 step70 (by norm_num)
theorem step71 : Point.some (64 : ZMod 499) 428 ns_64_428 + Point.some (64 : ZMod 499) 428 ns_64_428 = Point.some (211 : ZMod 499) 5 ns_211_5 :=
  dbl_cert (ℓ := (31 : ZMod 499)) ns_64_428 ns_211_5 (by decide) (by decide) (by decide) (by decide)
theorem D13_m16 : (16 : ℕ) • D13 = Point.some (211 : ZMod 499) 5 ns_211_5 :=
  nsmul_step D13_m8 D13_m8 step71 (by norm_num)
theorem ns_24_234 : E.Nonsingular (24 : ZMod 499) 234 := nonsingular_of (by decide) (by decide)
theorem step72 : Point.some (211 : ZMod 499) 5 ns_211_5 + Point.some (211 : ZMod 499) 5 ns_211_5 = Point.some (24 : ZMod 499) 234 ns_24_234 :=
  dbl_cert (ℓ := (84 : ZMod 499)) ns_211_5 ns_24_234 (by decide) (by decide) (by decide) (by decide)
theorem D13_m32 : (32 : ℕ) • D13 = Point.some (24 : ZMod 499) 234 ns_24_234 :=
  nsmul_step D13_m16 D13_m16 step72 (by norm_num)
theorem step73 : Point.some (24 : ZMod 499) 234 ns_24_234 + Point.some (24 : ZMod 499) 234 ns_24_234 = Point.some (235 : ZMod 499) 49 ns_235_49 :=
  dbl_cert (ℓ := (124 : ZMod 499)) ns_24_234 ns_235_49 (by decide) (by decide) (by decide) (by decide)
theorem D13_m64 : (64 : ℕ) • D13 = Point.some (235 : ZMod 499) 49 ns_235_49 :=
  nsmul_step D13_m32 D13_m32 step73 (by norm_num)
theorem step74 : Point.some (235 : ZMod 499) 49 ns_235_49 + Point.some (235 : ZMod 499) 49 ns_235_49 = Point.some (197 : ZMod 499) 180 ns_197_180 :=
  dbl_cert (ℓ := (203 : ZMod 499)) ns_235_49 ns_197_180 (by decide) (by decide) (by decide) (by decide)
theorem D13_m128 : (128 : ℕ) • D13 = Point.some (197 : ZMod 499) 180 ns_197_180 :=
  nsmul_step D13_m64 D13_m64 step74 (by norm_num)
theorem step75 : Point.some (197 : ZMod 499) 180 ns_197_180 + Point.some (235 : ZMod 499) 49 ns_235_49 = Point.some (364 : ZMod 499) 225 ns_364_225 :=
  add_cert (ℓ := (141 : ZMod 499)) ns_197_180 ns_235_49 ns_364_225 (by decide) (by decide) (by decide) (by decide)
theorem D13_m192 : (192 : ℕ) • D13 = Point.some (364 : ZMod 499) 225 ns_364_225 :=
  nsmul_step D13_m128 D13_m64 step75 (by norm_num)
theorem step76 : Point.some (364 : ZMod 499) 225 ns_364_225 + Point.some (24 : ZMod 499) 234 ns_24_234 = Point.some (139 : ZMod 499) 202 ns_139_202 :=
  add_cert (ℓ := (339 : ZMod 499)) ns_364_225 ns_24_234 ns_139_202 (by decide) (by decide) (by decide) (by decide)
theorem D13_m224 : (224 : ℕ) • D13 = Point.some (139 : ZMod 499) 202 ns_139_202 :=
  nsmul_step D13_m192 D13_m32 step76 (by norm_num)
theorem step77 : Point.some (139 : ZMod 499) 202 ns_139_202 + Point.some (211 : ZMod 499) 5 ns_211_5 = Point.some (64 : ZMod 499) 71 ns_64_71 :=
  add_cert (ℓ := (323 : ZMod 499)) ns_139_202 ns_211_5 ns_64_71 (by decide) (by decide) (by decide) (by decide)
theorem D13_m240 : (240 : ℕ) • D13 = Point.some (64 : ZMod 499) 71 ns_64_71 :=
  nsmul_step D13_m224 D13_m16 step77 (by norm_num)
theorem step78 : Point.some (64 : ZMod 499) 71 ns_64_71 + Point.some (64 : ZMod 499) 428 ns_64_428 = (0 : E.Point) :=
  add_zero_cert ns_64_71 ns_64_428 (by decide) (by decide)
theorem D13_m248 : (248 : ℕ) • D13 = (0 : E.Point) :=
  nsmul_step D13_m240 D13_m8 step78 (by norm_num)

/-- `248 • D13 = 0`. -/
theorem D13_nsmul_order : (248 : ℕ) • D13 = 0 := D13_m248
theorem step79 : Point.some (235 : ZMod 499) 49 ns_235_49 + Point.some (24 : ZMod 499) 234 ns_24_234 = Point.some (224 : ZMod 499) 289 ns_224_289 :=
  add_cert (ℓ := (439 : ZMod 499)) ns_235_49 ns_24_234 ns_224_289 (by decide) (by decide) (by decide) (by decide)
theorem D13_m96 : (96 : ℕ) • D13 = Point.some (224 : ZMod 499) 289 ns_224_289 :=
  nsmul_step D13_m64 D13_m32 step79 (by norm_num)
theorem step80 : Point.some (224 : ZMod 499) 289 ns_224_289 + Point.some (211 : ZMod 499) 5 ns_211_5 = Point.some (247 : ZMod 499) 53 ns_247_53 :=
  add_cert (ℓ := (137 : ZMod 499)) ns_224_289 ns_211_5 ns_247_53 (by decide) (by decide) (by decide) (by decide)
theorem D13_m112 : (112 : ℕ) • D13 = Point.some (247 : ZMod 499) 53 ns_247_53 :=
  nsmul_step D13_m96 D13_m16 step80 (by norm_num)
theorem step81 : Point.some (247 : ZMod 499) 53 ns_247_53 + Point.some (64 : ZMod 499) 428 ns_64_428 = Point.some (197 : ZMod 499) 319 ns_197_319 :=
  add_cert (ℓ := (227 : ZMod 499)) ns_247_53 ns_64_428 ns_197_319 (by decide) (by decide) (by decide) (by decide)
theorem D13_m120 : (120 : ℕ) • D13 = Point.some (197 : ZMod 499) 319 ns_197_319 :=
  nsmul_step D13_m112 D13_m8 step81 (by norm_num)
theorem step82 : Point.some (197 : ZMod 499) 319 ns_197_319 + Point.some (38 : ZMod 499) 59 ns_38_59 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  add_cert (ℓ := (146 : ZMod 499)) ns_197_319 ns_38_59 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D13_m124 : (124 : ℕ) • D13 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  nsmul_step D13_m120 D13_m4 step82 (by norm_num)

/-- `(248/2) • D13 ≠ 0`. -/
theorem D13_nsmul_124_ne : (124 : ℕ) • D13 ≠ 0 := by
  rw [D13_m124]
  exact Point.some_ne_zero _

/-- `(248/31) • D13 ≠ 0`. -/
theorem D13_nsmul_8_ne : (8 : ℕ) • D13 ≠ 0 := by
  rw [D13_m8]
  exact Point.some_ne_zero _

/-- `D13` has exact order `248` in `E(𝔽_499)`. -/
theorem D13_addOrderOf : addOrderOf D13 = 248 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D13_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 * 31 ^ 1 : ℕ) = 248 := by norm_num
  have h : q ∣ 2 ^ 3 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact D13_nsmul_124_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact D13_nsmul_8_ne

theorem P1_sub_P3_addOrderOf : addOrderOf (P1 - P3) = 248 := by
  rw [D13_eq]
  exact D13_addOrderOf

theorem P3_sub_P1_addOrderOf : addOrderOf (P3 - P1) = 248 := by
  rw [← neg_sub P1 P3, addOrderOf_neg]
  exact P1_sub_P3_addOrderOf

/-! ### `P1 - P4` -/

theorem ns_163_250 : E.Nonsingular (163 : ZMod 499) 250 := nonsingular_of (by decide) (by decide)
theorem ns_101_142 : E.Nonsingular (101 : ZMod 499) 142 := nonsingular_of (by decide) (by decide)
theorem step83 : Point.some (301 : ZMod 499) 205 ns_301_205 + Point.some (163 : ZMod 499) 250 ns_163_250 = Point.some (101 : ZMod 499) 142 ns_101_142 :=
  add_cert (ℓ := (119 : ZMod 499)) ns_301_205 ns_163_250 ns_101_142 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P1 - P4` as an explicit point. -/
theorem D14_eq : P1 - P4 = Point.some (101 : ZMod 499) 142 ns_101_142 :=
  sub_cert ns_301_205 ns_163_249 ns_163_250 ns_101_142 (by decide) step83

abbrev D14 : E.Point := Point.some (101 : ZMod 499) 142 ns_101_142

theorem D14_m1 : (1 : ℕ) • D14 = Point.some (101 : ZMod 499) 142 ns_101_142 := one_nsmul _
theorem ns_255_468 : E.Nonsingular (255 : ZMod 499) 468 := nonsingular_of (by decide) (by decide)
theorem step84 : Point.some (101 : ZMod 499) 142 ns_101_142 + Point.some (101 : ZMod 499) 142 ns_101_142 = Point.some (255 : ZMod 499) 468 ns_255_468 :=
  dbl_cert (ℓ := (9 : ZMod 499)) ns_101_142 ns_255_468 (by decide) (by decide) (by decide) (by decide)
theorem D14_m2 : (2 : ℕ) • D14 = Point.some (255 : ZMod 499) 468 ns_255_468 :=
  nsmul_step D14_m1 D14_m1 step84 (by norm_num)
theorem ns_96_332 : E.Nonsingular (96 : ZMod 499) 332 := nonsingular_of (by decide) (by decide)
theorem step85 : Point.some (255 : ZMod 499) 468 ns_255_468 + Point.some (255 : ZMod 499) 468 ns_255_468 = Point.some (96 : ZMod 499) 332 ns_96_332 :=
  dbl_cert (ℓ := (27 : ZMod 499)) ns_255_468 ns_96_332 (by decide) (by decide) (by decide) (by decide)
theorem D14_m4 : (4 : ℕ) • D14 = Point.some (96 : ZMod 499) 332 ns_96_332 :=
  nsmul_step D14_m2 D14_m2 step85 (by norm_num)
theorem step86 : Point.some (96 : ZMod 499) 332 ns_96_332 + Point.some (96 : ZMod 499) 332 ns_96_332 = Point.some (5 : ZMod 499) 194 ns_5_194 :=
  dbl_cert (ℓ := (99 : ZMod 499)) ns_96_332 ns_5_194 (by decide) (by decide) (by decide) (by decide)
theorem D14_m8 : (8 : ℕ) • D14 = Point.some (5 : ZMod 499) 194 ns_5_194 :=
  nsmul_step D14_m4 D14_m4 step86 (by norm_num)
theorem step87 : Point.some (5 : ZMod 499) 194 ns_5_194 + Point.some (5 : ZMod 499) 194 ns_5_194 = Point.some (249 : ZMod 499) 29 ns_249_29 :=
  dbl_cert (ℓ := (222 : ZMod 499)) ns_5_194 ns_249_29 (by decide) (by decide) (by decide) (by decide)
theorem D14_m16 : (16 : ℕ) • D14 = Point.some (249 : ZMod 499) 29 ns_249_29 :=
  nsmul_step D14_m8 D14_m8 step87 (by norm_num)
theorem step88 : Point.some (249 : ZMod 499) 29 ns_249_29 + Point.some (249 : ZMod 499) 29 ns_249_29 = Point.some (198 : ZMod 499) 30 ns_198_30 :=
  dbl_cert (ℓ := (99 : ZMod 499)) ns_249_29 ns_198_30 (by decide) (by decide) (by decide) (by decide)
theorem D14_m32 : (32 : ℕ) • D14 = Point.some (198 : ZMod 499) 30 ns_198_30 :=
  nsmul_step D14_m16 D14_m16 step88 (by norm_num)
theorem step89 : Point.some (198 : ZMod 499) 30 ns_198_30 + Point.some (198 : ZMod 499) 30 ns_198_30 = Point.some (169 : ZMod 499) 427 ns_169_427 :=
  dbl_cert (ℓ := (119 : ZMod 499)) ns_198_30 ns_169_427 (by decide) (by decide) (by decide) (by decide)
theorem D14_m64 : (64 : ℕ) • D14 = Point.some (169 : ZMod 499) 427 ns_169_427 :=
  nsmul_step D14_m32 D14_m32 step89 (by norm_num)
theorem step90 : Point.some (169 : ZMod 499) 427 ns_169_427 + Point.some (169 : ZMod 499) 427 ns_169_427 = Point.some (26 : ZMod 499) 118 ns_26_118 :=
  dbl_cert (ℓ := (440 : ZMod 499)) ns_169_427 ns_26_118 (by decide) (by decide) (by decide) (by decide)
theorem D14_m128 : (128 : ℕ) • D14 = Point.some (26 : ZMod 499) 118 ns_26_118 :=
  nsmul_step D14_m64 D14_m64 step90 (by norm_num)
theorem step91 : Point.some (26 : ZMod 499) 118 ns_26_118 + Point.some (169 : ZMod 499) 427 ns_169_427 = Point.some (64 : ZMod 499) 428 ns_64_428 :=
  add_cert (ℓ := (222 : ZMod 499)) ns_26_118 ns_169_427 ns_64_428 (by decide) (by decide) (by decide) (by decide)
theorem D14_m192 : (192 : ℕ) • D14 = Point.some (64 : ZMod 499) 428 ns_64_428 :=
  nsmul_step D14_m128 D14_m64 step91 (by norm_num)
theorem step92 : Point.some (64 : ZMod 499) 428 ns_64_428 + Point.some (198 : ZMod 499) 30 ns_198_30 = Point.some (24 : ZMod 499) 265 ns_24_265 :=
  add_cert (ℓ := (429 : ZMod 499)) ns_64_428 ns_198_30 ns_24_265 (by decide) (by decide) (by decide) (by decide)
theorem D14_m224 : (224 : ℕ) • D14 = Point.some (24 : ZMod 499) 265 ns_24_265 :=
  nsmul_step D14_m192 D14_m32 step92 (by norm_num)
theorem step93 : Point.some (24 : ZMod 499) 265 ns_24_265 + Point.some (249 : ZMod 499) 29 ns_249_29 = Point.some (5 : ZMod 499) 305 ns_5_305 :=
  add_cert (ℓ := (30 : ZMod 499)) ns_24_265 ns_249_29 ns_5_305 (by decide) (by decide) (by decide) (by decide)
theorem D14_m240 : (240 : ℕ) • D14 = Point.some (5 : ZMod 499) 305 ns_5_305 :=
  nsmul_step D14_m224 D14_m16 step93 (by norm_num)
theorem step94 : Point.some (5 : ZMod 499) 305 ns_5_305 + Point.some (5 : ZMod 499) 194 ns_5_194 = (0 : E.Point) :=
  add_zero_cert ns_5_305 ns_5_194 (by decide) (by decide)
theorem D14_m248 : (248 : ℕ) • D14 = (0 : E.Point) :=
  nsmul_step D14_m240 D14_m8 step94 (by norm_num)

/-- `248 • D14 = 0`. -/
theorem D14_nsmul_order : (248 : ℕ) • D14 = 0 := D14_m248
theorem step95 : Point.some (169 : ZMod 499) 427 ns_169_427 + Point.some (198 : ZMod 499) 30 ns_198_30 = Point.some (197 : ZMod 499) 180 ns_197_180 :=
  add_cert (ℓ := (210 : ZMod 499)) ns_169_427 ns_198_30 ns_197_180 (by decide) (by decide) (by decide) (by decide)
theorem D14_m96 : (96 : ℕ) • D14 = Point.some (197 : ZMod 499) 180 ns_197_180 :=
  nsmul_step D14_m64 D14_m32 step95 (by norm_num)
theorem step96 : Point.some (197 : ZMod 499) 180 ns_197_180 + Point.some (249 : ZMod 499) 29 ns_249_29 = Point.some (211 : ZMod 499) 494 ns_211_494 :=
  add_cert (ℓ := (237 : ZMod 499)) ns_197_180 ns_249_29 ns_211_494 (by decide) (by decide) (by decide) (by decide)
theorem D14_m112 : (112 : ℕ) • D14 = Point.some (211 : ZMod 499) 494 ns_211_494 :=
  nsmul_step D14_m96 D14_m16 step96 (by norm_num)
theorem step97 : Point.some (211 : ZMod 499) 494 ns_211_494 + Point.some (5 : ZMod 499) 194 ns_5_194 = Point.some (26 : ZMod 499) 381 ns_26_381 :=
  add_cert (ℓ := (234 : ZMod 499)) ns_211_494 ns_5_194 ns_26_381 (by decide) (by decide) (by decide) (by decide)
theorem D14_m120 : (120 : ℕ) • D14 = Point.some (26 : ZMod 499) 381 ns_26_381 :=
  nsmul_step D14_m112 D14_m8 step97 (by norm_num)
theorem step98 : Point.some (26 : ZMod 499) 381 ns_26_381 + Point.some (96 : ZMod 499) 332 ns_96_332 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  add_cert (ℓ := (149 : ZMod 499)) ns_26_381 ns_96_332 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D14_m124 : (124 : ℕ) • D14 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  nsmul_step D14_m120 D14_m4 step98 (by norm_num)

/-- `(248/2) • D14 ≠ 0`. -/
theorem D14_nsmul_124_ne : (124 : ℕ) • D14 ≠ 0 := by
  rw [D14_m124]
  exact Point.some_ne_zero _

/-- `(248/31) • D14 ≠ 0`. -/
theorem D14_nsmul_8_ne : (8 : ℕ) • D14 ≠ 0 := by
  rw [D14_m8]
  exact Point.some_ne_zero _

/-- `D14` has exact order `248` in `E(𝔽_499)`. -/
theorem D14_addOrderOf : addOrderOf D14 = 248 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D14_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 * 31 ^ 1 : ℕ) = 248 := by norm_num
  have h : q ∣ 2 ^ 3 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact D14_nsmul_124_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact D14_nsmul_8_ne

theorem P1_sub_P4_addOrderOf : addOrderOf (P1 - P4) = 248 := by
  rw [D14_eq]
  exact D14_addOrderOf

theorem P4_sub_P1_addOrderOf : addOrderOf (P4 - P1) = 248 := by
  rw [← neg_sub P1 P4, addOrderOf_neg]
  exact P1_sub_P4_addOrderOf

/-! ### `P2 - P3` -/

theorem ns_35_338 : E.Nonsingular (35 : ZMod 499) 338 := nonsingular_of (by decide) (by decide)
theorem step99 : Point.some (336 : ZMod 499) 38 ns_336_38 + Point.some (340 : ZMod 499) 479 ns_340_479 = Point.some (35 : ZMod 499) 338 ns_35_338 :=
  add_cert (ℓ := (235 : ZMod 499)) ns_336_38 ns_340_479 ns_35_338 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P2 - P3` as an explicit point. -/
theorem D23_eq : P2 - P3 = Point.some (35 : ZMod 499) 338 ns_35_338 :=
  sub_cert ns_336_38 ns_340_20 ns_340_479 ns_35_338 (by decide) step99

abbrev D23 : E.Point := Point.some (35 : ZMod 499) 338 ns_35_338

theorem D23_m1 : (1 : ℕ) • D23 = Point.some (35 : ZMod 499) 338 ns_35_338 := one_nsmul _
theorem ns_100_112 : E.Nonsingular (100 : ZMod 499) 112 := nonsingular_of (by decide) (by decide)
theorem step100 : Point.some (35 : ZMod 499) 338 ns_35_338 + Point.some (35 : ZMod 499) 338 ns_35_338 = Point.some (100 : ZMod 499) 112 ns_100_112 :=
  dbl_cert (ℓ := (185 : ZMod 499)) ns_35_338 ns_100_112 (by decide) (by decide) (by decide) (by decide)
theorem D23_m2 : (2 : ℕ) • D23 = Point.some (100 : ZMod 499) 112 ns_100_112 :=
  nsmul_step D23_m1 D23_m1 step100 (by norm_num)
theorem step101 : Point.some (100 : ZMod 499) 112 ns_100_112 + Point.some (100 : ZMod 499) 112 ns_100_112 = Point.some (249 : ZMod 499) 29 ns_249_29 :=
  dbl_cert (ℓ := (344 : ZMod 499)) ns_100_112 ns_249_29 (by decide) (by decide) (by decide) (by decide)
theorem D23_m4 : (4 : ℕ) • D23 = Point.some (249 : ZMod 499) 29 ns_249_29 :=
  nsmul_step D23_m2 D23_m2 step101 (by norm_num)
theorem D23_m8 : (8 : ℕ) • D23 = Point.some (198 : ZMod 499) 30 ns_198_30 :=
  nsmul_step D23_m4 D23_m4 step88 (by norm_num)
theorem D23_m16 : (16 : ℕ) • D23 = Point.some (169 : ZMod 499) 427 ns_169_427 :=
  nsmul_step D23_m8 D23_m8 step89 (by norm_num)
theorem D23_m32 : (32 : ℕ) • D23 = Point.some (26 : ZMod 499) 118 ns_26_118 :=
  nsmul_step D23_m16 D23_m16 step90 (by norm_num)
theorem step102 : Point.some (26 : ZMod 499) 118 ns_26_118 + Point.some (26 : ZMod 499) 118 ns_26_118 = Point.some (5 : ZMod 499) 194 ns_5_194 :=
  dbl_cert (ℓ := (300 : ZMod 499)) ns_26_118 ns_5_194 (by decide) (by decide) (by decide) (by decide)
theorem D23_m64 : (64 : ℕ) • D23 = Point.some (5 : ZMod 499) 194 ns_5_194 :=
  nsmul_step D23_m32 D23_m32 step102 (by norm_num)
theorem step103 : Point.some (5 : ZMod 499) 194 ns_5_194 + Point.some (26 : ZMod 499) 118 ns_26_118 = Point.some (211 : ZMod 499) 5 ns_211_5 :=
  add_cert (ℓ := (234 : ZMod 499)) ns_5_194 ns_26_118 ns_211_5 (by decide) (by decide) (by decide) (by decide)
theorem D23_m96 : (96 : ℕ) • D23 = Point.some (211 : ZMod 499) 5 ns_211_5 :=
  nsmul_step D23_m64 D23_m32 step103 (by norm_num)
theorem step104 : Point.some (211 : ZMod 499) 5 ns_211_5 + Point.some (169 : ZMod 499) 427 ns_169_427 = Point.some (235 : ZMod 499) 450 ns_235_450 :=
  add_cert (ℓ := (85 : ZMod 499)) ns_211_5 ns_169_427 ns_235_450 (by decide) (by decide) (by decide) (by decide)
theorem D23_m112 : (112 : ℕ) • D23 = Point.some (235 : ZMod 499) 450 ns_235_450 :=
  nsmul_step D23_m96 D23_m16 step104 (by norm_num)
theorem step105 : Point.some (235 : ZMod 499) 450 ns_235_450 + Point.some (198 : ZMod 499) 30 ns_198_30 = Point.some (249 : ZMod 499) 470 ns_249_470 :=
  add_cert (ℓ := (362 : ZMod 499)) ns_235_450 ns_198_30 ns_249_470 (by decide) (by decide) (by decide) (by decide)
theorem D23_m120 : (120 : ℕ) • D23 = Point.some (249 : ZMod 499) 470 ns_249_470 :=
  nsmul_step D23_m112 D23_m8 step105 (by norm_num)
theorem step106 : Point.some (249 : ZMod 499) 470 ns_249_470 + Point.some (249 : ZMod 499) 29 ns_249_29 = (0 : E.Point) :=
  add_zero_cert ns_249_470 ns_249_29 (by decide) (by decide)
theorem D23_m124 : (124 : ℕ) • D23 = (0 : E.Point) :=
  nsmul_step D23_m120 D23_m4 step106 (by norm_num)

/-- `124 • D23 = 0`. -/
theorem D23_nsmul_order : (124 : ℕ) • D23 = 0 := D23_m124
theorem D23_m48 : (48 : ℕ) • D23 = Point.some (64 : ZMod 499) 428 ns_64_428 :=
  nsmul_step D23_m32 D23_m16 step91 (by norm_num)
theorem D23_m56 : (56 : ℕ) • D23 = Point.some (24 : ZMod 499) 265 ns_24_265 :=
  nsmul_step D23_m48 D23_m8 step92 (by norm_num)
theorem D23_m60 : (60 : ℕ) • D23 = Point.some (5 : ZMod 499) 305 ns_5_305 :=
  nsmul_step D23_m56 D23_m4 step93 (by norm_num)
theorem step107 : Point.some (5 : ZMod 499) 305 ns_5_305 + Point.some (100 : ZMod 499) 112 ns_100_112 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  add_cert (ℓ := (61 : ZMod 499)) ns_5_305 ns_100_112 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D23_m62 : (62 : ℕ) • D23 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  nsmul_step D23_m60 D23_m2 step107 (by norm_num)

/-- `(124/2) • D23 ≠ 0`. -/
theorem D23_nsmul_62_ne : (62 : ℕ) • D23 ≠ 0 := by
  rw [D23_m62]
  exact Point.some_ne_zero _

/-- `(124/31) • D23 ≠ 0`. -/
theorem D23_nsmul_4_ne : (4 : ℕ) • D23 ≠ 0 := by
  rw [D23_m4]
  exact Point.some_ne_zero _

/-- `D23` has exact order `124` in `E(𝔽_499)`. -/
theorem D23_addOrderOf : addOrderOf D23 = 124 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D23_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 2 * 31 ^ 1 : ℕ) = 124 := by norm_num
  have h : q ∣ 2 ^ 2 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact D23_nsmul_62_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact D23_nsmul_4_ne

theorem P2_sub_P3_addOrderOf : addOrderOf (P2 - P3) = 124 := by
  rw [D23_eq]
  exact D23_addOrderOf

theorem P3_sub_P2_addOrderOf : addOrderOf (P3 - P2) = 124 := by
  rw [← neg_sub P2 P3, addOrderOf_neg]
  exact P2_sub_P3_addOrderOf

/-! ### `P2 - P4` -/

theorem ns_10_174 : E.Nonsingular (10 : ZMod 499) 174 := nonsingular_of (by decide) (by decide)
theorem step108 : Point.some (336 : ZMod 499) 38 ns_336_38 + Point.some (163 : ZMod 499) 250 ns_163_250 = Point.some (10 : ZMod 499) 174 ns_10_174 :=
  add_cert (ℓ := (68 : ZMod 499)) ns_336_38 ns_163_250 ns_10_174 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P2 - P4` as an explicit point. -/
theorem D24_eq : P2 - P4 = Point.some (10 : ZMod 499) 174 ns_10_174 :=
  sub_cert ns_336_38 ns_163_249 ns_163_250 ns_10_174 (by decide) step108

abbrev D24 : E.Point := Point.some (10 : ZMod 499) 174 ns_10_174

theorem D24_m1 : (1 : ℕ) • D24 = Point.some (10 : ZMod 499) 174 ns_10_174 := one_nsmul _
theorem step109 : Point.some (10 : ZMod 499) 174 ns_10_174 + Point.some (10 : ZMod 499) 174 ns_10_174 = Point.some (24 : ZMod 499) 234 ns_24_234 :=
  dbl_cert (ℓ := (256 : ZMod 499)) ns_10_174 ns_24_234 (by decide) (by decide) (by decide) (by decide)
theorem D24_m2 : (2 : ℕ) • D24 = Point.some (24 : ZMod 499) 234 ns_24_234 :=
  nsmul_step D24_m1 D24_m1 step109 (by norm_num)
theorem D24_m4 : (4 : ℕ) • D24 = Point.some (235 : ZMod 499) 49 ns_235_49 :=
  nsmul_step D24_m2 D24_m2 step73 (by norm_num)
theorem D24_m8 : (8 : ℕ) • D24 = Point.some (197 : ZMod 499) 180 ns_197_180 :=
  nsmul_step D24_m4 D24_m4 step74 (by norm_num)
theorem step110 : Point.some (197 : ZMod 499) 180 ns_197_180 + Point.some (197 : ZMod 499) 180 ns_197_180 = Point.some (64 : ZMod 499) 428 ns_64_428 :=
  dbl_cert (ℓ := (361 : ZMod 499)) ns_197_180 ns_64_428 (by decide) (by decide) (by decide) (by decide)
theorem D24_m16 : (16 : ℕ) • D24 = Point.some (64 : ZMod 499) 428 ns_64_428 :=
  nsmul_step D24_m8 D24_m8 step110 (by norm_num)
theorem D24_m32 : (32 : ℕ) • D24 = Point.some (211 : ZMod 499) 5 ns_211_5 :=
  nsmul_step D24_m16 D24_m16 step71 (by norm_num)
theorem step111 : Point.some (211 : ZMod 499) 5 ns_211_5 + Point.some (64 : ZMod 499) 428 ns_64_428 = Point.some (139 : ZMod 499) 297 ns_139_297 :=
  add_cert (ℓ := (323 : ZMod 499)) ns_211_5 ns_64_428 ns_139_297 (by decide) (by decide) (by decide) (by decide)
theorem D24_m48 : (48 : ℕ) • D24 = Point.some (139 : ZMod 499) 297 ns_139_297 :=
  nsmul_step D24_m32 D24_m16 step111 (by norm_num)
theorem step112 : Point.some (139 : ZMod 499) 297 ns_139_297 + Point.some (197 : ZMod 499) 180 ns_197_180 = Point.some (224 : ZMod 499) 210 ns_224_210 :=
  add_cert (ℓ := (41 : ZMod 499)) ns_139_297 ns_197_180 ns_224_210 (by decide) (by decide) (by decide) (by decide)
theorem D24_m56 : (56 : ℕ) • D24 = Point.some (224 : ZMod 499) 210 ns_224_210 :=
  nsmul_step D24_m48 D24_m8 step112 (by norm_num)
theorem step113 : Point.some (224 : ZMod 499) 210 ns_224_210 + Point.some (235 : ZMod 499) 49 ns_235_49 = Point.some (24 : ZMod 499) 265 ns_24_265 :=
  add_cert (ℓ := (439 : ZMod 499)) ns_224_210 ns_235_49 ns_24_265 (by decide) (by decide) (by decide) (by decide)
theorem D24_m60 : (60 : ℕ) • D24 = Point.some (24 : ZMod 499) 265 ns_24_265 :=
  nsmul_step D24_m56 D24_m4 step113 (by norm_num)
theorem step114 : Point.some (24 : ZMod 499) 265 ns_24_265 + Point.some (24 : ZMod 499) 234 ns_24_234 = (0 : E.Point) :=
  add_zero_cert ns_24_265 ns_24_234 (by decide) (by decide)
theorem D24_m62 : (62 : ℕ) • D24 = (0 : E.Point) :=
  nsmul_step D24_m60 D24_m2 step114 (by norm_num)

/-- `62 • D24 = 0`. -/
theorem D24_nsmul_order : (62 : ℕ) • D24 = 0 := D24_m62
theorem step115 : Point.some (64 : ZMod 499) 428 ns_64_428 + Point.some (197 : ZMod 499) 180 ns_197_180 = Point.some (247 : ZMod 499) 446 ns_247_446 :=
  add_cert (ℓ := (227 : ZMod 499)) ns_64_428 ns_197_180 ns_247_446 (by decide) (by decide) (by decide) (by decide)
theorem D24_m24 : (24 : ℕ) • D24 = Point.some (247 : ZMod 499) 446 ns_247_446 :=
  nsmul_step D24_m16 D24_m8 step115 (by norm_num)
theorem step116 : Point.some (247 : ZMod 499) 446 ns_247_446 + Point.some (235 : ZMod 499) 49 ns_235_49 = Point.some (91 : ZMod 499) 224 ns_91_224 :=
  add_cert (ℓ := (241 : ZMod 499)) ns_247_446 ns_235_49 ns_91_224 (by decide) (by decide) (by decide) (by decide)
theorem D24_m28 : (28 : ℕ) • D24 = Point.some (91 : ZMod 499) 224 ns_91_224 :=
  nsmul_step D24_m24 D24_m4 step116 (by norm_num)
theorem step117 : Point.some (91 : ZMod 499) 224 ns_91_224 + Point.some (24 : ZMod 499) 234 ns_24_234 = Point.some (211 : ZMod 499) 494 ns_211_494 :=
  add_cert (ℓ := (335 : ZMod 499)) ns_91_224 ns_24_234 ns_211_494 (by decide) (by decide) (by decide) (by decide)
theorem D24_m30 : (30 : ℕ) • D24 = Point.some (211 : ZMod 499) 494 ns_211_494 :=
  nsmul_step D24_m28 D24_m2 step117 (by norm_num)
theorem step118 : Point.some (211 : ZMod 499) 494 ns_211_494 + Point.some (10 : ZMod 499) 174 ns_10_174 = Point.some (66 : ZMod 499) 0 ns_66_0 :=
  add_cert (ℓ := (86 : ZMod 499)) ns_211_494 ns_10_174 ns_66_0 (by decide) (by decide) (by decide) (by decide)
theorem D24_m31 : (31 : ℕ) • D24 = Point.some (66 : ZMod 499) 0 ns_66_0 :=
  nsmul_step D24_m30 D24_m1 step118 (by norm_num)

/-- `(62/2) • D24 ≠ 0`. -/
theorem D24_nsmul_31_ne : (31 : ℕ) • D24 ≠ 0 := by
  rw [D24_m31]
  exact Point.some_ne_zero _

/-- `(62/31) • D24 ≠ 0`. -/
theorem D24_nsmul_2_ne : (2 : ℕ) • D24 ≠ 0 := by
  rw [D24_m2]
  exact Point.some_ne_zero _

/-- `D24` has exact order `62` in `E(𝔽_499)`. -/
theorem D24_addOrderOf : addOrderOf D24 = 62 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D24_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 1 * 31 ^ 1 : ℕ) = 62 := by norm_num
  have h : q ∣ 2 ^ 1 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact D24_nsmul_31_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact D24_nsmul_2_ne

theorem P2_sub_P4_addOrderOf : addOrderOf (P2 - P4) = 62 := by
  rw [D24_eq]
  exact D24_addOrderOf

theorem P4_sub_P2_addOrderOf : addOrderOf (P4 - P2) = 62 := by
  rw [← neg_sub P2 P4, addOrderOf_neg]
  exact P2_sub_P4_addOrderOf

/-! ### `P3 - P4` -/

theorem ns_67_175 : E.Nonsingular (67 : ZMod 499) 175 := nonsingular_of (by decide) (by decide)
theorem step119 : Point.some (340 : ZMod 499) 20 ns_340_20 + Point.some (163 : ZMod 499) 250 ns_163_250 = Point.some (67 : ZMod 499) 175 ns_67_175 :=
  add_cert (ℓ := (72 : ZMod 499)) ns_340_20 ns_163_250 ns_67_175 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P3 - P4` as an explicit point. -/
theorem D34_eq : P3 - P4 = Point.some (67 : ZMod 499) 175 ns_67_175 :=
  sub_cert ns_340_20 ns_163_249 ns_163_250 ns_67_175 (by decide) step119

abbrev D34 : E.Point := Point.some (67 : ZMod 499) 175 ns_67_175

theorem D34_m1 : (1 : ℕ) • D34 = Point.some (67 : ZMod 499) 175 ns_67_175 := one_nsmul _
theorem ns_497_383 : E.Nonsingular (497 : ZMod 499) 383 := nonsingular_of (by decide) (by decide)
theorem step120 : Point.some (67 : ZMod 499) 175 ns_67_175 + Point.some (67 : ZMod 499) 175 ns_67_175 = Point.some (497 : ZMod 499) 383 ns_497_383 :=
  dbl_cert (ℓ := (442 : ZMod 499)) ns_67_175 ns_497_383 (by decide) (by decide) (by decide) (by decide)
theorem D34_m2 : (2 : ℕ) • D34 = Point.some (497 : ZMod 499) 383 ns_497_383 :=
  nsmul_step D34_m1 D34_m1 step120 (by norm_num)
theorem step121 : Point.some (497 : ZMod 499) 383 ns_497_383 + Point.some (497 : ZMod 499) 383 ns_497_383 = Point.some (198 : ZMod 499) 30 ns_198_30 :=
  dbl_cert (ℓ := (215 : ZMod 499)) ns_497_383 ns_198_30 (by decide) (by decide) (by decide) (by decide)
theorem D34_m4 : (4 : ℕ) • D34 = Point.some (198 : ZMod 499) 30 ns_198_30 :=
  nsmul_step D34_m2 D34_m2 step121 (by norm_num)
theorem D34_m8 : (8 : ℕ) • D34 = Point.some (169 : ZMod 499) 427 ns_169_427 :=
  nsmul_step D34_m4 D34_m4 step89 (by norm_num)
theorem D34_m16 : (16 : ℕ) • D34 = Point.some (26 : ZMod 499) 118 ns_26_118 :=
  nsmul_step D34_m8 D34_m8 step90 (by norm_num)
theorem D34_m32 : (32 : ℕ) • D34 = Point.some (5 : ZMod 499) 194 ns_5_194 :=
  nsmul_step D34_m16 D34_m16 step102 (by norm_num)
theorem D34_m64 : (64 : ℕ) • D34 = Point.some (249 : ZMod 499) 29 ns_249_29 :=
  nsmul_step D34_m32 D34_m32 step87 (by norm_num)
theorem step122 : Point.some (249 : ZMod 499) 29 ns_249_29 + Point.some (5 : ZMod 499) 194 ns_5_194 = Point.some (24 : ZMod 499) 234 ns_24_234 :=
  add_cert (ℓ := (30 : ZMod 499)) ns_249_29 ns_5_194 ns_24_234 (by decide) (by decide) (by decide) (by decide)
theorem D34_m96 : (96 : ℕ) • D34 = Point.some (24 : ZMod 499) 234 ns_24_234 :=
  nsmul_step D34_m64 D34_m32 step122 (by norm_num)
theorem step123 : Point.some (24 : ZMod 499) 234 ns_24_234 + Point.some (26 : ZMod 499) 118 ns_26_118 = Point.some (197 : ZMod 499) 319 ns_197_319 :=
  add_cert (ℓ := (441 : ZMod 499)) ns_24_234 ns_26_118 ns_197_319 (by decide) (by decide) (by decide) (by decide)
theorem D34_m112 : (112 : ℕ) • D34 = Point.some (197 : ZMod 499) 319 ns_197_319 :=
  nsmul_step D34_m96 D34_m16 step123 (by norm_num)
theorem step124 : Point.some (197 : ZMod 499) 319 ns_197_319 + Point.some (169 : ZMod 499) 427 ns_169_427 = Point.some (198 : ZMod 499) 469 ns_198_469 :=
  add_cert (ℓ := (210 : ZMod 499)) ns_197_319 ns_169_427 ns_198_469 (by decide) (by decide) (by decide) (by decide)
theorem D34_m120 : (120 : ℕ) • D34 = Point.some (198 : ZMod 499) 469 ns_198_469 :=
  nsmul_step D34_m112 D34_m8 step124 (by norm_num)
theorem step125 : Point.some (198 : ZMod 499) 469 ns_198_469 + Point.some (198 : ZMod 499) 30 ns_198_30 = (0 : E.Point) :=
  add_zero_cert ns_198_469 ns_198_30 (by decide) (by decide)
theorem D34_m124 : (124 : ℕ) • D34 = (0 : E.Point) :=
  nsmul_step D34_m120 D34_m4 step125 (by norm_num)

/-- `124 • D34 = 0`. -/
theorem D34_nsmul_order : (124 : ℕ) • D34 = 0 := D34_m124
theorem D34_m48 : (48 : ℕ) • D34 = Point.some (211 : ZMod 499) 5 ns_211_5 :=
  nsmul_step D34_m32 D34_m16 step103 (by norm_num)
theorem D34_m56 : (56 : ℕ) • D34 = Point.some (235 : ZMod 499) 450 ns_235_450 :=
  nsmul_step D34_m48 D34_m8 step104 (by norm_num)
theorem D34_m60 : (60 : ℕ) • D34 = Point.some (249 : ZMod 499) 470 ns_249_470 :=
  nsmul_step D34_m56 D34_m4 step105 (by norm_num)
theorem step126 : Point.some (249 : ZMod 499) 470 ns_249_470 + Point.some (497 : ZMod 499) 383 ns_497_383 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  add_cert (ℓ := (58 : ZMod 499)) ns_249_470 ns_497_383 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D34_m62 : (62 : ℕ) • D34 = Point.some (0 : ZMod 499) 0 ns_0_0 :=
  nsmul_step D34_m60 D34_m2 step126 (by norm_num)

/-- `(124/2) • D34 ≠ 0`. -/
theorem D34_nsmul_62_ne : (62 : ℕ) • D34 ≠ 0 := by
  rw [D34_m62]
  exact Point.some_ne_zero _

/-- `(124/31) • D34 ≠ 0`. -/
theorem D34_nsmul_4_ne : (4 : ℕ) • D34 ≠ 0 := by
  rw [D34_m4]
  exact Point.some_ne_zero _

/-- `D34` has exact order `124` in `E(𝔽_499)`. -/
theorem D34_addOrderOf : addOrderOf D34 = 124 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D34_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 2 * 31 ^ 1 : ℕ) = 124 := by norm_num
  have h : q ∣ 2 ^ 2 * 31 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact D34_nsmul_62_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact D34_nsmul_4_ne

theorem P3_sub_P4_addOrderOf : addOrderOf (P3 - P4) = 124 := by
  rw [D34_eq]
  exact D34_addOrderOf

theorem P4_sub_P3_addOrderOf : addOrderOf (P4 - P3) = 124 := by
  rw [← neg_sub P3 P4, addOrderOf_neg]
  exact P3_sub_P4_addOrderOf

end P499

end Tower.TangentLine
