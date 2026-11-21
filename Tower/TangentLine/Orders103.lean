import Mathlib
import Tower.EC.Cert
import Tower.TangentLine.Resultant

/-!
# The points over the roots of `Q₄` in `E(𝔽_103)`

This file is generated (the generator computes the slopes; Lean checks every step).
`E : Y² = X³ - (7/4) X² + X` over `𝔽_103`, where `-7/4 = 24`; cube root of unity `z = 56`.
For each root `t` of `Q₄`: the point `(t, y)` of the curve `G = 0` with `F = 0`, its image
`(X, Y)` under `X = -1/(t y)`, `Y = (y - t) X (X - 1)/2`, and the exact multiples that
determine its order in Mathlib's group `E(𝔽_p)`.
-/

namespace Tower.TangentLine

namespace P103

open WeierstrassCurve.Affine Tower.EC

instance : Fact (Nat.Prime 103) := ⟨by norm_num⟩

/-- The curve `Y² = X³ + 24 X² + X` over `𝔽_103`. -/
def E : WeierstrassCurve.Affine (ZMod 103) := ⟨0, 24, 0, 1, 0⟩


/-! ## Root `t = 2`: `y = 60`, `(X, Y) = (6, 46)`, order `120` -/

/-- `(t, y) = (2, 60)` lies on `G = 0` and `F = 0`, and `(X, Y) = (6, 46)` is its image. -/
theorem link1 : G (2 : ZMod 103) 60 = 0 ∧ F (2 : ZMod 103) 60 56 = 0 ∧
    (6 : ZMod 103) * (2 * 60) = -1 ∧ 2 * (46 : ZMod 103) = (60 - 2) * 6 * (6 - 1) := by
  decide

theorem ns_6_46 : E.Nonsingular (6 : ZMod 103) 46 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_103)` over the root `t = 2`. -/
abbrev P1 : E.Point := Point.some (6 : ZMod 103) 46 ns_6_46

theorem P1_m1 : (1 : ℕ) • P1 = Point.some (6 : ZMod 103) 46 ns_6_46 := one_nsmul _
theorem ns_28_27 : E.Nonsingular (28 : ZMod 103) 27 := nonsingular_of (by decide) (by decide)
theorem step1 : Point.some (6 : ZMod 103) 46 ns_6_46 + Point.some (6 : ZMod 103) 46 ns_6_46 = Point.some (28 : ZMod 103) 27 ns_28_27 :=
  dbl_cert (ℓ := (95 : ZMod 103)) ns_6_46 ns_28_27 (by decide) (by decide) (by decide) (by decide)
theorem P1_m2 : (2 : ℕ) • P1 = Point.some (28 : ZMod 103) 27 ns_28_27 :=
  nsmul_step P1_m1 P1_m1 step1 (by norm_num)
theorem ns_30_23 : E.Nonsingular (30 : ZMod 103) 23 := nonsingular_of (by decide) (by decide)
theorem step2 : Point.some (28 : ZMod 103) 27 ns_28_27 + Point.some (28 : ZMod 103) 27 ns_28_27 = Point.some (30 : ZMod 103) 23 ns_30_23 :=
  dbl_cert (ℓ := (78 : ZMod 103)) ns_28_27 ns_30_23 (by decide) (by decide) (by decide) (by decide)
theorem P1_m4 : (4 : ℕ) • P1 = Point.some (30 : ZMod 103) 23 ns_30_23 :=
  nsmul_step P1_m2 P1_m2 step2 (by norm_num)
theorem ns_14_47 : E.Nonsingular (14 : ZMod 103) 47 := nonsingular_of (by decide) (by decide)
theorem step3 : Point.some (30 : ZMod 103) 23 ns_30_23 + Point.some (30 : ZMod 103) 23 ns_30_23 = Point.some (14 : ZMod 103) 47 ns_14_47 :=
  dbl_cert (ℓ := (43 : ZMod 103)) ns_30_23 ns_14_47 (by decide) (by decide) (by decide) (by decide)
theorem P1_m8 : (8 : ℕ) • P1 = Point.some (14 : ZMod 103) 47 ns_14_47 :=
  nsmul_step P1_m4 P1_m4 step3 (by norm_num)
theorem ns_46_19 : E.Nonsingular (46 : ZMod 103) 19 := nonsingular_of (by decide) (by decide)
theorem step4 : Point.some (14 : ZMod 103) 47 ns_14_47 + Point.some (14 : ZMod 103) 47 ns_14_47 = Point.some (46 : ZMod 103) 19 ns_46_19 :=
  dbl_cert (ℓ := (43 : ZMod 103)) ns_14_47 ns_46_19 (by decide) (by decide) (by decide) (by decide)
theorem P1_m16 : (16 : ℕ) • P1 = Point.some (46 : ZMod 103) 19 ns_46_19 :=
  nsmul_step P1_m8 P1_m8 step4 (by norm_num)
theorem ns_19_68 : E.Nonsingular (19 : ZMod 103) 68 := nonsingular_of (by decide) (by decide)
theorem step5 : Point.some (46 : ZMod 103) 19 ns_46_19 + Point.some (46 : ZMod 103) 19 ns_46_19 = Point.some (19 : ZMod 103) 68 ns_19_68 :=
  dbl_cert (ℓ := (49 : ZMod 103)) ns_46_19 ns_19_68 (by decide) (by decide) (by decide) (by decide)
theorem P1_m32 : (32 : ℕ) • P1 = Point.some (19 : ZMod 103) 68 ns_19_68 :=
  nsmul_step P1_m16 P1_m16 step5 (by norm_num)
theorem ns_79_39 : E.Nonsingular (79 : ZMod 103) 39 := nonsingular_of (by decide) (by decide)
theorem step6 : Point.some (19 : ZMod 103) 68 ns_19_68 + Point.some (19 : ZMod 103) 68 ns_19_68 = Point.some (79 : ZMod 103) 39 ns_79_39 :=
  dbl_cert (ℓ := (48 : ZMod 103)) ns_19_68 ns_79_39 (by decide) (by decide) (by decide) (by decide)
theorem P1_m64 : (64 : ℕ) • P1 = Point.some (79 : ZMod 103) 39 ns_79_39 :=
  nsmul_step P1_m32 P1_m32 step6 (by norm_num)
theorem ns_60_84 : E.Nonsingular (60 : ZMod 103) 84 := nonsingular_of (by decide) (by decide)
theorem step7 : Point.some (79 : ZMod 103) 39 ns_79_39 + Point.some (19 : ZMod 103) 68 ns_19_68 = Point.some (60 : ZMod 103) 84 ns_60_84 :=
  add_cert (ℓ := (39 : ZMod 103)) ns_79_39 ns_19_68 ns_60_84 (by decide) (by decide) (by decide) (by decide)
theorem P1_m96 : (96 : ℕ) • P1 = Point.some (60 : ZMod 103) 84 ns_60_84 :=
  nsmul_step P1_m64 P1_m32 step7 (by norm_num)
theorem ns_14_56 : E.Nonsingular (14 : ZMod 103) 56 := nonsingular_of (by decide) (by decide)
theorem step8 : Point.some (60 : ZMod 103) 84 ns_60_84 + Point.some (46 : ZMod 103) 19 ns_46_19 = Point.some (14 : ZMod 103) 56 ns_14_56 :=
  add_cert (ℓ := (12 : ZMod 103)) ns_60_84 ns_46_19 ns_14_56 (by decide) (by decide) (by decide) (by decide)
theorem P1_m112 : (112 : ℕ) • P1 = Point.some (14 : ZMod 103) 56 ns_14_56 :=
  nsmul_step P1_m96 P1_m16 step8 (by norm_num)
theorem step9 : Point.some (14 : ZMod 103) 56 ns_14_56 + Point.some (14 : ZMod 103) 47 ns_14_47 = (0 : E.Point) :=
  add_zero_cert ns_14_56 ns_14_47 (by decide) (by decide)
theorem P1_m120 : (120 : ℕ) • P1 = (0 : E.Point) :=
  nsmul_step P1_m112 P1_m8 step9 (by norm_num)

/-- `120 • P1 = 0`. -/
theorem P1_nsmul_order : (120 : ℕ) • P1 = 0 := P1_m120
theorem ns_18_37 : E.Nonsingular (18 : ZMod 103) 37 := nonsingular_of (by decide) (by decide)
theorem step10 : Point.some (19 : ZMod 103) 68 ns_19_68 + Point.some (46 : ZMod 103) 19 ns_46_19 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  add_cert (ℓ := (2 : ZMod 103)) ns_19_68 ns_46_19 ns_18_37 (by decide) (by decide) (by decide) (by decide)
theorem P1_m48 : (48 : ℕ) • P1 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  nsmul_step P1_m32 P1_m16 step10 (by norm_num)
theorem ns_79_64 : E.Nonsingular (79 : ZMod 103) 64 := nonsingular_of (by decide) (by decide)
theorem step11 : Point.some (18 : ZMod 103) 37 ns_18_37 + Point.some (14 : ZMod 103) 47 ns_14_47 = Point.some (79 : ZMod 103) 64 ns_79_64 :=
  add_cert (ℓ := (49 : ZMod 103)) ns_18_37 ns_14_47 ns_79_64 (by decide) (by decide) (by decide) (by decide)
theorem P1_m56 : (56 : ℕ) • P1 = Point.some (79 : ZMod 103) 64 ns_79_64 :=
  nsmul_step P1_m48 P1_m8 step11 (by norm_num)
theorem ns_0_0 : E.Nonsingular (0 : ZMod 103) 0 := nonsingular_of (by decide) (by decide)
theorem step12 : Point.some (79 : ZMod 103) 64 ns_79_64 + Point.some (30 : ZMod 103) 23 ns_30_23 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  add_cert (ℓ := (66 : ZMod 103)) ns_79_64 ns_30_23 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P1_m60 : (60 : ℕ) • P1 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step P1_m56 P1_m4 step12 (by norm_num)

/-- `(120/2) • P1 ≠ 0`. -/
theorem P1_nsmul_60_ne : (60 : ℕ) • P1 ≠ 0 := by
  rw [P1_m60]
  exact Point.some_ne_zero _
theorem ns_76_84 : E.Nonsingular (76 : ZMod 103) 84 := nonsingular_of (by decide) (by decide)
theorem step13 : Point.some (19 : ZMod 103) 68 ns_19_68 + Point.some (14 : ZMod 103) 47 ns_14_47 = Point.some (76 : ZMod 103) 84 ns_76_84 :=
  add_cert (ℓ := (66 : ZMod 103)) ns_19_68 ns_14_47 ns_76_84 (by decide) (by decide) (by decide) (by decide)
theorem P1_m40 : (40 : ℕ) • P1 = Point.some (76 : ZMod 103) 84 ns_76_84 :=
  nsmul_step P1_m32 P1_m8 step13 (by norm_num)

/-- `(120/3) • P1 ≠ 0`. -/
theorem P1_nsmul_40_ne : (40 : ℕ) • P1 ≠ 0 := by
  rw [P1_m40]
  exact Point.some_ne_zero _
theorem ns_60_19 : E.Nonsingular (60 : ZMod 103) 19 := nonsingular_of (by decide) (by decide)
theorem step14 : Point.some (46 : ZMod 103) 19 ns_46_19 + Point.some (14 : ZMod 103) 47 ns_14_47 = Point.some (60 : ZMod 103) 19 ns_60_19 :=
  add_cert (ℓ := (12 : ZMod 103)) ns_46_19 ns_14_47 ns_60_19 (by decide) (by decide) (by decide) (by decide)
theorem P1_m24 : (24 : ℕ) • P1 = Point.some (60 : ZMod 103) 19 ns_60_19 :=
  nsmul_step P1_m16 P1_m8 step14 (by norm_num)

/-- `(120/5) • P1 ≠ 0`. -/
theorem P1_nsmul_24_ne : (24 : ℕ) • P1 ≠ 0 := by
  rw [P1_m24]
  exact Point.some_ne_zero _

/-! ## Root `t = 41`: `y = 7`, `(X, Y) = (89, 35)`, order `40` -/

/-- `(t, y) = (41, 7)` lies on `G = 0` and `F = 0`, and `(X, Y) = (89, 35)` is its image. -/
theorem link2 : G (41 : ZMod 103) 7 = 0 ∧ F (41 : ZMod 103) 7 56 = 0 ∧
    (89 : ZMod 103) * (41 * 7) = -1 ∧ 2 * (35 : ZMod 103) = (7 - 41) * 89 * (89 - 1) := by
  decide

theorem ns_89_35 : E.Nonsingular (89 : ZMod 103) 35 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_103)` over the root `t = 41`. -/
abbrev P2 : E.Point := Point.some (89 : ZMod 103) 35 ns_89_35

theorem P2_m1 : (1 : ℕ) • P2 = Point.some (89 : ZMod 103) 35 ns_89_35 := one_nsmul _
theorem ns_23_28 : E.Nonsingular (23 : ZMod 103) 28 := nonsingular_of (by decide) (by decide)
theorem step15 : Point.some (89 : ZMod 103) 35 ns_89_35 + Point.some (89 : ZMod 103) 35 ns_89_35 = Point.some (23 : ZMod 103) 28 ns_23_28 :=
  dbl_cert (ℓ := (15 : ZMod 103)) ns_89_35 ns_23_28 (by decide) (by decide) (by decide) (by decide)
theorem P2_m2 : (2 : ℕ) • P2 = Point.some (23 : ZMod 103) 28 ns_23_28 :=
  nsmul_step P2_m1 P2_m1 step15 (by norm_num)
theorem ns_91_58 : E.Nonsingular (91 : ZMod 103) 58 := nonsingular_of (by decide) (by decide)
theorem step16 : Point.some (23 : ZMod 103) 28 ns_23_28 + Point.some (23 : ZMod 103) 28 ns_23_28 = Point.some (91 : ZMod 103) 58 ns_91_58 :=
  dbl_cert (ℓ := (26 : ZMod 103)) ns_23_28 ns_91_58 (by decide) (by decide) (by decide) (by decide)
theorem P2_m4 : (4 : ℕ) • P2 = Point.some (91 : ZMod 103) 58 ns_91_58 :=
  nsmul_step P2_m2 P2_m2 step16 (by norm_num)
theorem ns_18_66 : E.Nonsingular (18 : ZMod 103) 66 := nonsingular_of (by decide) (by decide)
theorem step17 : Point.some (91 : ZMod 103) 58 ns_91_58 + Point.some (91 : ZMod 103) 58 ns_91_58 = Point.some (18 : ZMod 103) 66 ns_18_66 :=
  dbl_cert (ℓ := (92 : ZMod 103)) ns_91_58 ns_18_66 (by decide) (by decide) (by decide) (by decide)
theorem P2_m8 : (8 : ℕ) • P2 = Point.some (18 : ZMod 103) 66 ns_18_66 :=
  nsmul_step P2_m4 P2_m4 step17 (by norm_num)
theorem step18 : Point.some (18 : ZMod 103) 66 ns_18_66 + Point.some (18 : ZMod 103) 66 ns_18_66 = Point.some (60 : ZMod 103) 19 ns_60_19 :=
  dbl_cert (ℓ := (74 : ZMod 103)) ns_18_66 ns_60_19 (by decide) (by decide) (by decide) (by decide)
theorem P2_m16 : (16 : ℕ) • P2 = Point.some (60 : ZMod 103) 19 ns_60_19 :=
  nsmul_step P2_m8 P2_m8 step18 (by norm_num)
theorem step19 : Point.some (60 : ZMod 103) 19 ns_60_19 + Point.some (60 : ZMod 103) 19 ns_60_19 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  dbl_cert (ℓ := (70 : ZMod 103)) ns_60_19 ns_18_37 (by decide) (by decide) (by decide) (by decide)
theorem P2_m32 : (32 : ℕ) • P2 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  nsmul_step P2_m16 P2_m16 step19 (by norm_num)
theorem step20 : Point.some (18 : ZMod 103) 37 ns_18_37 + Point.some (18 : ZMod 103) 66 ns_18_66 = (0 : E.Point) :=
  add_zero_cert ns_18_37 ns_18_66 (by decide) (by decide)
theorem P2_m40 : (40 : ℕ) • P2 = (0 : E.Point) :=
  nsmul_step P2_m32 P2_m8 step20 (by norm_num)

/-- `40 • P2 = 0`. -/
theorem P2_nsmul_order : (40 : ℕ) • P2 = 0 := P2_m40
theorem step21 : Point.some (60 : ZMod 103) 19 ns_60_19 + Point.some (91 : ZMod 103) 58 ns_91_58 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  add_cert (ℓ := (81 : ZMod 103)) ns_60_19 ns_91_58 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P2_m20 : (20 : ℕ) • P2 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step P2_m16 P2_m4 step21 (by norm_num)

/-- `(40/2) • P2 ≠ 0`. -/
theorem P2_nsmul_20_ne : (20 : ℕ) • P2 ≠ 0 := by
  rw [P2_m20]
  exact Point.some_ne_zero _

/-- `(40/5) • P2 ≠ 0`. -/
theorem P2_nsmul_8_ne : (8 : ℕ) • P2 ≠ 0 := by
  rw [P2_m8]
  exact Point.some_ne_zero _

/-! ## Root `t = 99`: `y = 45`, `(X, Y) = (99, 78)`, order `24` -/

/-- `(t, y) = (99, 45)` lies on `G = 0` and `F = 0`, and `(X, Y) = (99, 78)` is its image. -/
theorem link3 : G (99 : ZMod 103) 45 = 0 ∧ F (99 : ZMod 103) 45 56 = 0 ∧
    (99 : ZMod 103) * (99 * 45) = -1 ∧ 2 * (78 : ZMod 103) = (45 - 99) * 99 * (99 - 1) := by
  decide

theorem ns_99_78 : E.Nonsingular (99 : ZMod 103) 78 := nonsingular_of (by decide) (by decide)
/-- The point of `E(𝔽_103)` over the root `t = 99`. -/
abbrev P3 : E.Point := Point.some (99 : ZMod 103) 78 ns_99_78

theorem P3_m1 : (1 : ℕ) • P3 = Point.some (99 : ZMod 103) 78 ns_99_78 := one_nsmul _
theorem ns_100_86 : E.Nonsingular (100 : ZMod 103) 86 := nonsingular_of (by decide) (by decide)
theorem step22 : Point.some (99 : ZMod 103) 78 ns_99_78 + Point.some (99 : ZMod 103) 78 ns_99_78 = Point.some (100 : ZMod 103) 86 ns_100_86 :=
  dbl_cert (ℓ := (42 : ZMod 103)) ns_99_78 ns_100_86 (by decide) (by decide) (by decide) (by decide)
theorem P3_m2 : (2 : ℕ) • P3 = Point.some (100 : ZMod 103) 86 ns_100_86 :=
  nsmul_step P3_m1 P3_m1 step22 (by norm_num)
theorem ns_61_41 : E.Nonsingular (61 : ZMod 103) 41 := nonsingular_of (by decide) (by decide)
theorem step23 : Point.some (100 : ZMod 103) 86 ns_100_86 + Point.some (100 : ZMod 103) 86 ns_100_86 = Point.some (61 : ZMod 103) 41 ns_61_41 :=
  dbl_cert (ℓ := (64 : ZMod 103)) ns_100_86 ns_61_41 (by decide) (by decide) (by decide) (by decide)
theorem P3_m4 : (4 : ℕ) • P3 = Point.some (61 : ZMod 103) 41 ns_61_41 :=
  nsmul_step P3_m2 P3_m2 step23 (by norm_num)
theorem ns_76_19 : E.Nonsingular (76 : ZMod 103) 19 := nonsingular_of (by decide) (by decide)
theorem step24 : Point.some (61 : ZMod 103) 41 ns_61_41 + Point.some (61 : ZMod 103) 41 ns_61_41 = Point.some (76 : ZMod 103) 19 ns_76_19 :=
  dbl_cert (ℓ := (99 : ZMod 103)) ns_61_41 ns_76_19 (by decide) (by decide) (by decide) (by decide)
theorem P3_m8 : (8 : ℕ) • P3 = Point.some (76 : ZMod 103) 19 ns_76_19 :=
  nsmul_step P3_m4 P3_m4 step24 (by norm_num)
theorem step25 : Point.some (76 : ZMod 103) 19 ns_76_19 + Point.some (76 : ZMod 103) 19 ns_76_19 = Point.some (76 : ZMod 103) 84 ns_76_84 :=
  dbl_cert (ℓ := (56 : ZMod 103)) ns_76_19 ns_76_84 (by decide) (by decide) (by decide) (by decide)
theorem P3_m16 : (16 : ℕ) • P3 = Point.some (76 : ZMod 103) 84 ns_76_84 :=
  nsmul_step P3_m8 P3_m8 step25 (by norm_num)
theorem step26 : Point.some (76 : ZMod 103) 84 ns_76_84 + Point.some (76 : ZMod 103) 19 ns_76_19 = (0 : E.Point) :=
  add_zero_cert ns_76_84 ns_76_19 (by decide) (by decide)
theorem P3_m24 : (24 : ℕ) • P3 = (0 : E.Point) :=
  nsmul_step P3_m16 P3_m8 step26 (by norm_num)

/-- `24 • P3 = 0`. -/
theorem P3_nsmul_order : (24 : ℕ) • P3 = 0 := P3_m24
theorem step27 : Point.some (76 : ZMod 103) 19 ns_76_19 + Point.some (61 : ZMod 103) 41 ns_61_41 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  add_cert (ℓ := (26 : ZMod 103)) ns_76_19 ns_61_41 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem P3_m12 : (12 : ℕ) • P3 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step P3_m8 P3_m4 step27 (by norm_num)

/-- `(24/2) • P3 ≠ 0`. -/
theorem P3_nsmul_12_ne : (12 : ℕ) • P3 ≠ 0 := by
  rw [P3_m12]
  exact Point.some_ne_zero _

/-- `(24/3) • P3 ≠ 0`. -/
theorem P3_nsmul_8_ne : (8 : ℕ) • P3 ≠ 0 := by
  rw [P3_m8]
  exact Point.some_ne_zero _

/-! ## Root `t = 100`: `y = 94`, `(X, Y) = (61, 41)`, order `6` -/

/-- `(t, y) = (100, 94)` lies on `G = 0` and `F = 0`, and `(X, Y) = (61, 41)` is its image. -/
theorem link4 : G (100 : ZMod 103) 94 = 0 ∧ F (100 : ZMod 103) 94 56 = 0 ∧
    (61 : ZMod 103) * (100 * 94) = -1 ∧ 2 * (41 : ZMod 103) = (94 - 100) * 61 * (61 - 1) := by
  decide

/-- The point of `E(𝔽_103)` over the root `t = 100`. -/
abbrev P4 : E.Point := Point.some (61 : ZMod 103) 41 ns_61_41

theorem P4_m1 : (1 : ℕ) • P4 = Point.some (61 : ZMod 103) 41 ns_61_41 := one_nsmul _
theorem P4_m2 : (2 : ℕ) • P4 = Point.some (76 : ZMod 103) 19 ns_76_19 :=
  nsmul_step P4_m1 P4_m1 step24 (by norm_num)
theorem P4_m4 : (4 : ℕ) • P4 = Point.some (76 : ZMod 103) 84 ns_76_84 :=
  nsmul_step P4_m2 P4_m2 step25 (by norm_num)
theorem P4_m6 : (6 : ℕ) • P4 = (0 : E.Point) :=
  nsmul_step P4_m4 P4_m2 step26 (by norm_num)

/-- `6 • P4 = 0`. -/
theorem P4_nsmul_order : (6 : ℕ) • P4 = 0 := P4_m6
theorem P4_m3 : (3 : ℕ) • P4 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step P4_m2 P4_m1 step27 (by norm_num)

/-- `(6/2) • P4 ≠ 0`. -/
theorem P4_nsmul_3_ne : (3 : ℕ) • P4 ≠ 0 := by
  rw [P4_m3]
  exact Point.some_ne_zero _

/-- `(6/3) • P4 ≠ 0`. -/
theorem P4_nsmul_2_ne : (2 : ℕ) • P4 ≠ 0 := by
  rw [P4_m2]
  exact Point.some_ne_zero _

/-! ## Exact orders -/

/-- The point `P1` has exact order `120` in `E(𝔽_103)`. -/
theorem P1_addOrderOf : addOrderOf P1 = 120 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul P1_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 * 3 ^ 1 * 5 ^ 1 : ℕ) = 120 := by norm_num
  have h : q ∣ 2 ^ 3 * 3 ^ 1 * 5 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h3a | h3b
  · skip
    rcases (Nat.Prime.dvd_mul hq).mp h3a with h2a | h2b
    · skip
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
      exact P1_nsmul_60_ne
    · skip
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
      exact P1_nsmul_40_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h3b)
    exact P1_nsmul_24_ne

/-- The point `P2` has exact order `40` in `E(𝔽_103)`. -/
theorem P2_addOrderOf : addOrderOf P2 = 40 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul P2_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 * 5 ^ 1 : ℕ) = 40 := by norm_num
  have h : q ∣ 2 ^ 3 * 5 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact P2_nsmul_20_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact P2_nsmul_8_ne

/-- The point `P3` has exact order `24` in `E(𝔽_103)`. -/
theorem P3_addOrderOf : addOrderOf P3 = 24 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul P3_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 * 3 ^ 1 : ℕ) = 24 := by norm_num
  have h : q ∣ 2 ^ 3 * 3 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact P3_nsmul_12_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact P3_nsmul_8_ne

/-- The point `P4` has exact order `6` in `E(𝔽_103)`. -/
theorem P4_addOrderOf : addOrderOf P4 = 6 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul P4_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 1 * 3 ^ 1 : ℕ) = 6 := by norm_num
  have h : q ∣ 2 ^ 1 * 3 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact P4_nsmul_3_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact P4_nsmul_2_ne

end P103

end Tower.TangentLine
