import Mathlib
import Tower.EC.Cert
import Tower.TangentLine.Maps

/-!
# The points over the roots of `Q₄` in `E(𝔽_103)`

This file is generated (the generator computes the slopes; Lean checks every step).
`E : Y² = X³ - (7/4) X² + X` over `𝔽_103`, where `-7/4 = 24`; cube root of unity `z = 56`.
For each root `t` of `Q₄`: the point `(t, y)` of the curve `G = 0` with `F = 0`, its image
`(X, Y)` under `X = -1/(t y)`, `Y = (y - t) X (X - 1)/2`, the exact multiples that
determine its order in Mathlib's group `E(𝔽_p)`, and the fact that `(X, Y)` is determined by
`t`.  The last section does the same for the six differences of the four points.
-/

namespace Tower.TangentLine

namespace P103

open WeierstrassCurve.Affine Tower.EC

instance : Fact (Nat.Prime 103) := ⟨by norm_num⟩

/-- The curve `Y² = X³ + 24 X² + X` over `𝔽_103`. -/
def E : WeierstrassCurve.Affine (ZMod 103) := ⟨0, 24, 0, 1, 0⟩

/-- `56` is a primitive cube root of unity in `𝔽_103`. -/
theorem cubeRoot : (56 : ZMod 103) ^ 2 + 56 + 1 = 0 := by decide

/-- Over `𝔽_103` with `w = 56`, the quartic `Q₄` has exactly the four roots `2, 41, 99, 100`. -/
theorem Q4_roots : ∀ t : ZMod 103, Q4 t 56 = 0 ↔ (t = 2 ∨ t = 41 ∨ t = 99 ∨ t = 100) := by
  decide +kernel


/-! ## Root `t = 2`: `y = 60`, `(X, Y) = (6, 46)`, order `120` -/

/-- `(t, y) = (2, 60)` lies on `G = 0` and `F = 0`, and `(X, Y) = (6, 46)` is its image. -/
theorem link1 : G (2 : ZMod 103) 60 = 0 ∧ F (2 : ZMod 103) 60 56 = 0 ∧
    (6 : ZMod 103) * (2 * 60) = -1 ∧ 2 * (46 : ZMod 103) = (60 - 2) * 6 * (6 - 1) := by
  decide

theorem uniq_y1 : ∀ y : ZMod 103, G 2 y = 0 → F 2 y 56 = 0 → y = 60 := by
  decide +kernel
theorem uniq_X1 : ∀ X : ZMod 103, X * (2 * 60) = -1 → X = 6 := by
  decide +kernel
theorem uniq_Y1 : ∀ Y : ZMod 103, 2 * Y = (60 - 2) * 6 * (6 - 1) → Y = 46 := by
  decide +kernel

/-- Over the root `t = 2` the point `(X, Y)` is determined. -/
theorem coords1 (y X Y : ZMod 103) (hG : G 2 y = 0) (hF : F 2 y 56 = 0)
    (hX : X * (2 * y) = -1) (hY : 2 * Y = (y - 2) * X * (X - 1)) : X = 6 ∧ Y = 46 := by
  have hy : y = 60 := uniq_y1 y hG hF
  subst hy
  have hX' : X = 6 := uniq_X1 X hX
  subst hX'
  exact ⟨rfl, uniq_Y1 Y hY⟩

/-- `t = 2` is a simple root of `Q₄`. -/
theorem diag1 : dQ4 (2 : ZMod 103) 2 56 ≠ 0 := by decide

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

/-- `P1` has exact order `120` in `E(𝔽_103)`. -/
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

/-! ## Root `t = 41`: `y = 7`, `(X, Y) = (89, 35)`, order `40` -/

/-- `(t, y) = (41, 7)` lies on `G = 0` and `F = 0`, and `(X, Y) = (89, 35)` is its image. -/
theorem link2 : G (41 : ZMod 103) 7 = 0 ∧ F (41 : ZMod 103) 7 56 = 0 ∧
    (89 : ZMod 103) * (41 * 7) = -1 ∧ 2 * (35 : ZMod 103) = (7 - 41) * 89 * (89 - 1) := by
  decide

theorem uniq_y2 : ∀ y : ZMod 103, G 41 y = 0 → F 41 y 56 = 0 → y = 7 := by
  decide +kernel
theorem uniq_X2 : ∀ X : ZMod 103, X * (41 * 7) = -1 → X = 89 := by
  decide +kernel
theorem uniq_Y2 : ∀ Y : ZMod 103, 2 * Y = (7 - 41) * 89 * (89 - 1) → Y = 35 := by
  decide +kernel

/-- Over the root `t = 41` the point `(X, Y)` is determined. -/
theorem coords2 (y X Y : ZMod 103) (hG : G 41 y = 0) (hF : F 41 y 56 = 0)
    (hX : X * (41 * y) = -1) (hY : 2 * Y = (y - 41) * X * (X - 1)) : X = 89 ∧ Y = 35 := by
  have hy : y = 7 := uniq_y2 y hG hF
  subst hy
  have hX' : X = 89 := uniq_X2 X hX
  subst hX'
  exact ⟨rfl, uniq_Y2 Y hY⟩

/-- `t = 41` is a simple root of `Q₄`. -/
theorem diag2 : dQ4 (41 : ZMod 103) 41 56 ≠ 0 := by decide

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

/-- `P2` has exact order `40` in `E(𝔽_103)`. -/
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

/-! ## Root `t = 99`: `y = 45`, `(X, Y) = (99, 78)`, order `24` -/

/-- `(t, y) = (99, 45)` lies on `G = 0` and `F = 0`, and `(X, Y) = (99, 78)` is its image. -/
theorem link3 : G (99 : ZMod 103) 45 = 0 ∧ F (99 : ZMod 103) 45 56 = 0 ∧
    (99 : ZMod 103) * (99 * 45) = -1 ∧ 2 * (78 : ZMod 103) = (45 - 99) * 99 * (99 - 1) := by
  decide

theorem uniq_y3 : ∀ y : ZMod 103, G 99 y = 0 → F 99 y 56 = 0 → y = 45 := by
  decide +kernel
theorem uniq_X3 : ∀ X : ZMod 103, X * (99 * 45) = -1 → X = 99 := by
  decide +kernel
theorem uniq_Y3 : ∀ Y : ZMod 103, 2 * Y = (45 - 99) * 99 * (99 - 1) → Y = 78 := by
  decide +kernel

/-- Over the root `t = 99` the point `(X, Y)` is determined. -/
theorem coords3 (y X Y : ZMod 103) (hG : G 99 y = 0) (hF : F 99 y 56 = 0)
    (hX : X * (99 * y) = -1) (hY : 2 * Y = (y - 99) * X * (X - 1)) : X = 99 ∧ Y = 78 := by
  have hy : y = 45 := uniq_y3 y hG hF
  subst hy
  have hX' : X = 99 := uniq_X3 X hX
  subst hX'
  exact ⟨rfl, uniq_Y3 Y hY⟩

/-- `t = 99` is a simple root of `Q₄`. -/
theorem diag3 : dQ4 (99 : ZMod 103) 99 56 ≠ 0 := by decide

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

/-- `P3` has exact order `24` in `E(𝔽_103)`. -/
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

/-! ## Root `t = 100`: `y = 94`, `(X, Y) = (61, 41)`, order `6` -/

/-- `(t, y) = (100, 94)` lies on `G = 0` and `F = 0`, and `(X, Y) = (61, 41)` is its image. -/
theorem link4 : G (100 : ZMod 103) 94 = 0 ∧ F (100 : ZMod 103) 94 56 = 0 ∧
    (61 : ZMod 103) * (100 * 94) = -1 ∧ 2 * (41 : ZMod 103) = (94 - 100) * 61 * (61 - 1) := by
  decide

theorem uniq_y4 : ∀ y : ZMod 103, G 100 y = 0 → F 100 y 56 = 0 → y = 94 := by
  decide +kernel
theorem uniq_X4 : ∀ X : ZMod 103, X * (100 * 94) = -1 → X = 61 := by
  decide +kernel
theorem uniq_Y4 : ∀ Y : ZMod 103, 2 * Y = (94 - 100) * 61 * (61 - 1) → Y = 41 := by
  decide +kernel

/-- Over the root `t = 100` the point `(X, Y)` is determined. -/
theorem coords4 (y X Y : ZMod 103) (hG : G 100 y = 0) (hF : F 100 y 56 = 0)
    (hX : X * (100 * y) = -1) (hY : 2 * Y = (y - 100) * X * (X - 1)) : X = 61 ∧ Y = 41 := by
  have hy : y = 94 := uniq_y4 y hG hF
  subst hy
  have hX' : X = 61 := uniq_X4 X hX
  subst hX'
  exact ⟨rfl, uniq_Y4 Y hY⟩

/-- `t = 100` is a simple root of `Q₄`. -/
theorem diag4 : dQ4 (100 : ZMod 103) 100 56 ≠ 0 := by decide

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

/-- `P4` has exact order `6` in `E(𝔽_103)`. -/
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

/-! ## Differences of the four points -/

/-! ### `P1 - P2` -/

theorem ns_89_68 : E.Nonsingular (89 : ZMod 103) 68 := nonsingular_of (by decide) (by decide)
theorem ns_81_88 : E.Nonsingular (81 : ZMod 103) 88 := nonsingular_of (by decide) (by decide)
theorem step28 : Point.some (6 : ZMod 103) 46 ns_6_46 + Point.some (89 : ZMod 103) 68 ns_89_68 = Point.some (81 : ZMod 103) 88 ns_81_88 :=
  add_cert (ℓ := (71 : ZMod 103)) ns_6_46 ns_89_68 ns_81_88 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P1 - P2` as an explicit point. -/
theorem D12_eq : P1 - P2 = Point.some (81 : ZMod 103) 88 ns_81_88 :=
  sub_cert ns_6_46 ns_89_35 ns_89_68 ns_81_88 (by decide) step28

abbrev D12 : E.Point := Point.some (81 : ZMod 103) 88 ns_81_88

theorem D12_m1 : (1 : ℕ) • D12 = Point.some (81 : ZMod 103) 88 ns_81_88 := one_nsmul _
theorem ns_46_84 : E.Nonsingular (46 : ZMod 103) 84 := nonsingular_of (by decide) (by decide)
theorem step29 : Point.some (81 : ZMod 103) 88 ns_81_88 + Point.some (81 : ZMod 103) 88 ns_81_88 = Point.some (46 : ZMod 103) 84 ns_46_84 :=
  dbl_cert (ℓ := (52 : ZMod 103)) ns_81_88 ns_46_84 (by decide) (by decide) (by decide) (by decide)
theorem D12_m2 : (2 : ℕ) • D12 = Point.some (46 : ZMod 103) 84 ns_46_84 :=
  nsmul_step D12_m1 D12_m1 step29 (by norm_num)
theorem ns_19_35 : E.Nonsingular (19 : ZMod 103) 35 := nonsingular_of (by decide) (by decide)
theorem step30 : Point.some (46 : ZMod 103) 84 ns_46_84 + Point.some (46 : ZMod 103) 84 ns_46_84 = Point.some (19 : ZMod 103) 35 ns_19_35 :=
  dbl_cert (ℓ := (54 : ZMod 103)) ns_46_84 ns_19_35 (by decide) (by decide) (by decide) (by decide)
theorem D12_m4 : (4 : ℕ) • D12 = Point.some (19 : ZMod 103) 35 ns_19_35 :=
  nsmul_step D12_m2 D12_m2 step30 (by norm_num)
theorem step31 : Point.some (19 : ZMod 103) 35 ns_19_35 + Point.some (19 : ZMod 103) 35 ns_19_35 = Point.some (79 : ZMod 103) 64 ns_79_64 :=
  dbl_cert (ℓ := (55 : ZMod 103)) ns_19_35 ns_79_64 (by decide) (by decide) (by decide) (by decide)
theorem D12_m8 : (8 : ℕ) • D12 = Point.some (79 : ZMod 103) 64 ns_79_64 :=
  nsmul_step D12_m4 D12_m4 step31 (by norm_num)
theorem step32 : Point.some (79 : ZMod 103) 64 ns_79_64 + Point.some (79 : ZMod 103) 64 ns_79_64 = Point.some (14 : ZMod 103) 56 ns_14_56 :=
  dbl_cert (ℓ := (89 : ZMod 103)) ns_79_64 ns_14_56 (by decide) (by decide) (by decide) (by decide)
theorem D12_m16 : (16 : ℕ) • D12 = Point.some (14 : ZMod 103) 56 ns_14_56 :=
  nsmul_step D12_m8 D12_m8 step32 (by norm_num)
theorem step33 : Point.some (14 : ZMod 103) 56 ns_14_56 + Point.some (79 : ZMod 103) 64 ns_79_64 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  add_cert (ℓ := (54 : ZMod 103)) ns_14_56 ns_79_64 ns_18_37 (by decide) (by decide) (by decide) (by decide)
theorem D12_m24 : (24 : ℕ) • D12 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  nsmul_step D12_m16 D12_m8 step33 (by norm_num)
theorem step34 : Point.some (18 : ZMod 103) 37 ns_18_37 + Point.some (19 : ZMod 103) 35 ns_19_35 = Point.some (46 : ZMod 103) 19 ns_46_19 :=
  add_cert (ℓ := (101 : ZMod 103)) ns_18_37 ns_19_35 ns_46_19 (by decide) (by decide) (by decide) (by decide)
theorem D12_m28 : (28 : ℕ) • D12 = Point.some (46 : ZMod 103) 19 ns_46_19 :=
  nsmul_step D12_m24 D12_m4 step34 (by norm_num)
theorem step35 : Point.some (46 : ZMod 103) 19 ns_46_19 + Point.some (46 : ZMod 103) 84 ns_46_84 = (0 : E.Point) :=
  add_zero_cert ns_46_19 ns_46_84 (by decide) (by decide)
theorem D12_m30 : (30 : ℕ) • D12 = (0 : E.Point) :=
  nsmul_step D12_m28 D12_m2 step35 (by norm_num)

/-- `30 • D12 = 0`. -/
theorem D12_nsmul_order : (30 : ℕ) • D12 = 0 := D12_m30
theorem step36 : Point.some (79 : ZMod 103) 64 ns_79_64 + Point.some (19 : ZMod 103) 35 ns_19_35 = Point.some (60 : ZMod 103) 19 ns_60_19 :=
  add_cert (ℓ := (64 : ZMod 103)) ns_79_64 ns_19_35 ns_60_19 (by decide) (by decide) (by decide) (by decide)
theorem D12_m12 : (12 : ℕ) • D12 = Point.some (60 : ZMod 103) 19 ns_60_19 :=
  nsmul_step D12_m8 D12_m4 step36 (by norm_num)
theorem step37 : Point.some (60 : ZMod 103) 19 ns_60_19 + Point.some (46 : ZMod 103) 84 ns_46_84 = Point.some (14 : ZMod 103) 47 ns_14_47 :=
  add_cert (ℓ := (91 : ZMod 103)) ns_60_19 ns_46_84 ns_14_47 (by decide) (by decide) (by decide) (by decide)
theorem D12_m14 : (14 : ℕ) • D12 = Point.some (14 : ZMod 103) 47 ns_14_47 :=
  nsmul_step D12_m12 D12_m2 step37 (by norm_num)
theorem step38 : Point.some (14 : ZMod 103) 47 ns_14_47 + Point.some (81 : ZMod 103) 88 ns_81_88 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  add_cert (ℓ := (99 : ZMod 103)) ns_14_47 ns_81_88 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D12_m15 : (15 : ℕ) • D12 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step D12_m14 D12_m1 step38 (by norm_num)

/-- `(30/2) • D12 ≠ 0`. -/
theorem D12_nsmul_15_ne : (15 : ℕ) • D12 ≠ 0 := by
  rw [D12_m15]
  exact Point.some_ne_zero _
theorem step39 : Point.some (79 : ZMod 103) 64 ns_79_64 + Point.some (46 : ZMod 103) 84 ns_46_84 = Point.some (76 : ZMod 103) 84 ns_76_84 :=
  add_cert (ℓ := (15 : ZMod 103)) ns_79_64 ns_46_84 ns_76_84 (by decide) (by decide) (by decide) (by decide)
theorem D12_m10 : (10 : ℕ) • D12 = Point.some (76 : ZMod 103) 84 ns_76_84 :=
  nsmul_step D12_m8 D12_m2 step39 (by norm_num)

/-- `(30/3) • D12 ≠ 0`. -/
theorem D12_nsmul_10_ne : (10 : ℕ) • D12 ≠ 0 := by
  rw [D12_m10]
  exact Point.some_ne_zero _
theorem step40 : Point.some (19 : ZMod 103) 35 ns_19_35 + Point.some (46 : ZMod 103) 84 ns_46_84 = Point.some (18 : ZMod 103) 66 ns_18_66 :=
  add_cert (ℓ := (101 : ZMod 103)) ns_19_35 ns_46_84 ns_18_66 (by decide) (by decide) (by decide) (by decide)
theorem D12_m6 : (6 : ℕ) • D12 = Point.some (18 : ZMod 103) 66 ns_18_66 :=
  nsmul_step D12_m4 D12_m2 step40 (by norm_num)

/-- `(30/5) • D12 ≠ 0`. -/
theorem D12_nsmul_6_ne : (6 : ℕ) • D12 ≠ 0 := by
  rw [D12_m6]
  exact Point.some_ne_zero _

/-- `D12` has exact order `30` in `E(𝔽_103)`. -/
theorem D12_addOrderOf : addOrderOf D12 = 30 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D12_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 1 * 3 ^ 1 * 5 ^ 1 : ℕ) = 30 := by norm_num
  have h : q ∣ 2 ^ 1 * 3 ^ 1 * 5 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h3a | h3b
  · skip
    rcases (Nat.Prime.dvd_mul hq).mp h3a with h2a | h2b
    · skip
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
      exact D12_nsmul_15_ne
    · skip
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
      exact D12_nsmul_10_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h3b)
    exact D12_nsmul_6_ne

theorem P1_sub_P2_addOrderOf : addOrderOf (P1 - P2) = 30 := by
  rw [D12_eq]
  exact D12_addOrderOf

theorem P2_sub_P1_addOrderOf : addOrderOf (P2 - P1) = 30 := by
  rw [← neg_sub P1 P2, addOrderOf_neg]
  exact P1_sub_P2_addOrderOf

/-! ### `P1 - P3` -/

theorem ns_99_25 : E.Nonsingular (99 : ZMod 103) 25 := nonsingular_of (by decide) (by decide)
theorem ns_33_93 : E.Nonsingular (33 : ZMod 103) 93 := nonsingular_of (by decide) (by decide)
theorem step41 : Point.some (6 : ZMod 103) 46 ns_6_46 + Point.some (99 : ZMod 103) 25 ns_99_25 = Point.some (33 : ZMod 103) 93 ns_33_93 :=
  add_cert (ℓ := (33 : ZMod 103)) ns_6_46 ns_99_25 ns_33_93 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P1 - P3` as an explicit point. -/
theorem D13_eq : P1 - P3 = Point.some (33 : ZMod 103) 93 ns_33_93 :=
  sub_cert ns_6_46 ns_99_78 ns_99_25 ns_33_93 (by decide) step41

abbrev D13 : E.Point := Point.some (33 : ZMod 103) 93 ns_33_93

theorem D13_m1 : (1 : ℕ) • D13 = Point.some (33 : ZMod 103) 93 ns_33_93 := one_nsmul _
theorem ns_63_78 : E.Nonsingular (63 : ZMod 103) 78 := nonsingular_of (by decide) (by decide)
theorem step42 : Point.some (33 : ZMod 103) 93 ns_33_93 + Point.some (33 : ZMod 103) 93 ns_33_93 = Point.some (63 : ZMod 103) 78 ns_63_78 :=
  dbl_cert (ℓ := (87 : ZMod 103)) ns_33_93 ns_63_78 (by decide) (by decide) (by decide) (by decide)
theorem D13_m2 : (2 : ℕ) • D13 = Point.some (63 : ZMod 103) 78 ns_63_78 :=
  nsmul_step D13_m1 D13_m1 step42 (by norm_num)
theorem step43 : Point.some (63 : ZMod 103) 78 ns_63_78 + Point.some (63 : ZMod 103) 78 ns_63_78 = Point.some (60 : ZMod 103) 19 ns_60_19 :=
  dbl_cert (ℓ := (101 : ZMod 103)) ns_63_78 ns_60_19 (by decide) (by decide) (by decide) (by decide)
theorem D13_m4 : (4 : ℕ) • D13 = Point.some (60 : ZMod 103) 19 ns_60_19 :=
  nsmul_step D13_m2 D13_m2 step43 (by norm_num)
theorem D13_m8 : (8 : ℕ) • D13 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  nsmul_step D13_m4 D13_m4 step19 (by norm_num)
theorem step44 : Point.some (18 : ZMod 103) 37 ns_18_37 + Point.some (18 : ZMod 103) 37 ns_18_37 = Point.some (60 : ZMod 103) 84 ns_60_84 :=
  dbl_cert (ℓ := (29 : ZMod 103)) ns_18_37 ns_60_84 (by decide) (by decide) (by decide) (by decide)
theorem D13_m16 : (16 : ℕ) • D13 = Point.some (60 : ZMod 103) 84 ns_60_84 :=
  nsmul_step D13_m8 D13_m8 step44 (by norm_num)
theorem step45 : Point.some (60 : ZMod 103) 84 ns_60_84 + Point.some (60 : ZMod 103) 19 ns_60_19 = (0 : E.Point) :=
  add_zero_cert ns_60_84 ns_60_19 (by decide) (by decide)
theorem D13_m20 : (20 : ℕ) • D13 = (0 : E.Point) :=
  nsmul_step D13_m16 D13_m4 step45 (by norm_num)

/-- `20 • D13 = 0`. -/
theorem D13_nsmul_order : (20 : ℕ) • D13 = 0 := D13_m20
theorem step46 : Point.some (18 : ZMod 103) 37 ns_18_37 + Point.some (63 : ZMod 103) 78 ns_63_78 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  add_cert (ℓ := (65 : ZMod 103)) ns_18_37 ns_63_78 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D13_m10 : (10 : ℕ) • D13 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step D13_m8 D13_m2 step46 (by norm_num)

/-- `(20/2) • D13 ≠ 0`. -/
theorem D13_nsmul_10_ne : (10 : ℕ) • D13 ≠ 0 := by
  rw [D13_m10]
  exact Point.some_ne_zero _

/-- `(20/5) • D13 ≠ 0`. -/
theorem D13_nsmul_4_ne : (4 : ℕ) • D13 ≠ 0 := by
  rw [D13_m4]
  exact Point.some_ne_zero _

/-- `D13` has exact order `20` in `E(𝔽_103)`. -/
theorem D13_addOrderOf : addOrderOf D13 = 20 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D13_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 2 * 5 ^ 1 : ℕ) = 20 := by norm_num
  have h : q ∣ 2 ^ 2 * 5 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact D13_nsmul_10_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact D13_nsmul_4_ne

theorem P1_sub_P3_addOrderOf : addOrderOf (P1 - P3) = 20 := by
  rw [D13_eq]
  exact D13_addOrderOf

theorem P3_sub_P1_addOrderOf : addOrderOf (P3 - P1) = 20 := by
  rw [← neg_sub P1 P3, addOrderOf_neg]
  exact P1_sub_P3_addOrderOf

/-! ### `P1 - P4` -/

theorem ns_61_62 : E.Nonsingular (61 : ZMod 103) 62 := nonsingular_of (by decide) (by decide)
theorem ns_35_101 : E.Nonsingular (35 : ZMod 103) 101 := nonsingular_of (by decide) (by decide)
theorem step47 : Point.some (6 : ZMod 103) 46 ns_6_46 + Point.some (61 : ZMod 103) 62 ns_61_62 = Point.some (35 : ZMod 103) 101 ns_35_101 :=
  add_cert (ℓ := (34 : ZMod 103)) ns_6_46 ns_61_62 ns_35_101 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P1 - P4` as an explicit point. -/
theorem D14_eq : P1 - P4 = Point.some (35 : ZMod 103) 101 ns_35_101 :=
  sub_cert ns_6_46 ns_61_41 ns_61_62 ns_35_101 (by decide) step47

abbrev D14 : E.Point := Point.some (35 : ZMod 103) 101 ns_35_101

theorem D14_m1 : (1 : ℕ) • D14 = Point.some (35 : ZMod 103) 101 ns_35_101 := one_nsmul _
theorem ns_9_2 : E.Nonsingular (9 : ZMod 103) 2 := nonsingular_of (by decide) (by decide)
theorem step48 : Point.some (35 : ZMod 103) 101 ns_35_101 + Point.some (35 : ZMod 103) 101 ns_35_101 = Point.some (9 : ZMod 103) 2 ns_9_2 :=
  dbl_cert (ℓ := (0 : ZMod 103)) ns_35_101 ns_9_2 (by decide) (by decide) (by decide) (by decide)
theorem D14_m2 : (2 : ℕ) • D14 = Point.some (9 : ZMod 103) 2 ns_9_2 :=
  nsmul_step D14_m1 D14_m1 step48 (by norm_num)
theorem ns_91_45 : E.Nonsingular (91 : ZMod 103) 45 := nonsingular_of (by decide) (by decide)
theorem step49 : Point.some (9 : ZMod 103) 2 ns_9_2 + Point.some (9 : ZMod 103) 2 ns_9_2 = Point.some (91 : ZMod 103) 45 ns_91_45 :=
  dbl_cert (ℓ := (66 : ZMod 103)) ns_9_2 ns_91_45 (by decide) (by decide) (by decide) (by decide)
theorem D14_m4 : (4 : ℕ) • D14 = Point.some (91 : ZMod 103) 45 ns_91_45 :=
  nsmul_step D14_m2 D14_m2 step49 (by norm_num)
theorem step50 : Point.some (91 : ZMod 103) 45 ns_91_45 + Point.some (91 : ZMod 103) 45 ns_91_45 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  dbl_cert (ℓ := (11 : ZMod 103)) ns_91_45 ns_18_37 (by decide) (by decide) (by decide) (by decide)
theorem D14_m8 : (8 : ℕ) • D14 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  nsmul_step D14_m4 D14_m4 step50 (by norm_num)
theorem D14_m16 : (16 : ℕ) • D14 = Point.some (60 : ZMod 103) 84 ns_60_84 :=
  nsmul_step D14_m8 D14_m8 step44 (by norm_num)
theorem step51 : Point.some (60 : ZMod 103) 84 ns_60_84 + Point.some (60 : ZMod 103) 84 ns_60_84 = Point.some (18 : ZMod 103) 66 ns_18_66 :=
  dbl_cert (ℓ := (33 : ZMod 103)) ns_60_84 ns_18_66 (by decide) (by decide) (by decide) (by decide)
theorem D14_m32 : (32 : ℕ) • D14 = Point.some (18 : ZMod 103) 66 ns_18_66 :=
  nsmul_step D14_m16 D14_m16 step51 (by norm_num)
theorem step52 : Point.some (18 : ZMod 103) 66 ns_18_66 + Point.some (18 : ZMod 103) 37 ns_18_37 = (0 : E.Point) :=
  add_zero_cert ns_18_66 ns_18_37 (by decide) (by decide)
theorem D14_m40 : (40 : ℕ) • D14 = (0 : E.Point) :=
  nsmul_step D14_m32 D14_m8 step52 (by norm_num)

/-- `40 • D14 = 0`. -/
theorem D14_nsmul_order : (40 : ℕ) • D14 = 0 := D14_m40
theorem step53 : Point.some (60 : ZMod 103) 84 ns_60_84 + Point.some (91 : ZMod 103) 45 ns_91_45 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  add_cert (ℓ := (22 : ZMod 103)) ns_60_84 ns_91_45 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D14_m20 : (20 : ℕ) • D14 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step D14_m16 D14_m4 step53 (by norm_num)

/-- `(40/2) • D14 ≠ 0`. -/
theorem D14_nsmul_20_ne : (20 : ℕ) • D14 ≠ 0 := by
  rw [D14_m20]
  exact Point.some_ne_zero _

/-- `(40/5) • D14 ≠ 0`. -/
theorem D14_nsmul_8_ne : (8 : ℕ) • D14 ≠ 0 := by
  rw [D14_m8]
  exact Point.some_ne_zero _

/-- `D14` has exact order `40` in `E(𝔽_103)`. -/
theorem D14_addOrderOf : addOrderOf D14 = 40 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D14_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 * 5 ^ 1 : ℕ) = 40 := by norm_num
  have h : q ∣ 2 ^ 3 * 5 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h2a | h2b
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
    exact D14_nsmul_20_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
    exact D14_nsmul_8_ne

theorem P1_sub_P4_addOrderOf : addOrderOf (P1 - P4) = 40 := by
  rw [D14_eq]
  exact D14_addOrderOf

theorem P4_sub_P1_addOrderOf : addOrderOf (P4 - P1) = 40 := by
  rw [← neg_sub P1 P4, addOrderOf_neg]
  exact P1_sub_P4_addOrderOf

/-! ### `P2 - P3` -/

theorem ns_98_77 : E.Nonsingular (98 : ZMod 103) 77 := nonsingular_of (by decide) (by decide)
theorem step54 : Point.some (89 : ZMod 103) 35 ns_89_35 + Point.some (99 : ZMod 103) 25 ns_99_25 = Point.some (98 : ZMod 103) 77 ns_98_77 :=
  add_cert (ℓ := (102 : ZMod 103)) ns_89_35 ns_99_25 ns_98_77 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P2 - P3` as an explicit point. -/
theorem D23_eq : P2 - P3 = Point.some (98 : ZMod 103) 77 ns_98_77 :=
  sub_cert ns_89_35 ns_99_78 ns_99_25 ns_98_77 (by decide) step54

abbrev D23 : E.Point := Point.some (98 : ZMod 103) 77 ns_98_77

theorem D23_m1 : (1 : ℕ) • D23 = Point.some (98 : ZMod 103) 77 ns_98_77 := one_nsmul _
theorem ns_38_33 : E.Nonsingular (38 : ZMod 103) 33 := nonsingular_of (by decide) (by decide)
theorem step55 : Point.some (98 : ZMod 103) 77 ns_98_77 + Point.some (98 : ZMod 103) 77 ns_98_77 = Point.some (38 : ZMod 103) 33 ns_38_33 :=
  dbl_cert (ℓ := (19 : ZMod 103)) ns_98_77 ns_38_33 (by decide) (by decide) (by decide) (by decide)
theorem D23_m2 : (2 : ℕ) • D23 = Point.some (38 : ZMod 103) 33 ns_38_33 :=
  nsmul_step D23_m1 D23_m1 step55 (by norm_num)
theorem step56 : Point.some (38 : ZMod 103) 33 ns_38_33 + Point.some (38 : ZMod 103) 33 ns_38_33 = Point.some (79 : ZMod 103) 64 ns_79_64 :=
  dbl_cert (ℓ := (73 : ZMod 103)) ns_38_33 ns_79_64 (by decide) (by decide) (by decide) (by decide)
theorem D23_m4 : (4 : ℕ) • D23 = Point.some (79 : ZMod 103) 64 ns_79_64 :=
  nsmul_step D23_m2 D23_m2 step56 (by norm_num)
theorem D23_m8 : (8 : ℕ) • D23 = Point.some (14 : ZMod 103) 56 ns_14_56 :=
  nsmul_step D23_m4 D23_m4 step32 (by norm_num)
theorem step57 : Point.some (14 : ZMod 103) 56 ns_14_56 + Point.some (14 : ZMod 103) 56 ns_14_56 = Point.some (46 : ZMod 103) 84 ns_46_84 :=
  dbl_cert (ℓ := (60 : ZMod 103)) ns_14_56 ns_46_84 (by decide) (by decide) (by decide) (by decide)
theorem D23_m16 : (16 : ℕ) • D23 = Point.some (46 : ZMod 103) 84 ns_46_84 :=
  nsmul_step D23_m8 D23_m8 step57 (by norm_num)
theorem D23_m32 : (32 : ℕ) • D23 = Point.some (19 : ZMod 103) 35 ns_19_35 :=
  nsmul_step D23_m16 D23_m16 step30 (by norm_num)
theorem D23_m48 : (48 : ℕ) • D23 = Point.some (18 : ZMod 103) 66 ns_18_66 :=
  nsmul_step D23_m32 D23_m16 step40 (by norm_num)
theorem step58 : Point.some (18 : ZMod 103) 66 ns_18_66 + Point.some (14 : ZMod 103) 56 ns_14_56 = Point.some (79 : ZMod 103) 39 ns_79_39 :=
  add_cert (ℓ := (54 : ZMod 103)) ns_18_66 ns_14_56 ns_79_39 (by decide) (by decide) (by decide) (by decide)
theorem D23_m56 : (56 : ℕ) • D23 = Point.some (79 : ZMod 103) 39 ns_79_39 :=
  nsmul_step D23_m48 D23_m8 step58 (by norm_num)
theorem step59 : Point.some (79 : ZMod 103) 39 ns_79_39 + Point.some (79 : ZMod 103) 64 ns_79_64 = (0 : E.Point) :=
  add_zero_cert ns_79_39 ns_79_64 (by decide) (by decide)
theorem D23_m60 : (60 : ℕ) • D23 = (0 : E.Point) :=
  nsmul_step D23_m56 D23_m4 step59 (by norm_num)

/-- `60 • D23 = 0`. -/
theorem D23_nsmul_order : (60 : ℕ) • D23 = 0 := D23_m60
theorem step60 : Point.some (46 : ZMod 103) 84 ns_46_84 + Point.some (14 : ZMod 103) 56 ns_14_56 = Point.some (60 : ZMod 103) 84 ns_60_84 :=
  add_cert (ℓ := (91 : ZMod 103)) ns_46_84 ns_14_56 ns_60_84 (by decide) (by decide) (by decide) (by decide)
theorem D23_m24 : (24 : ℕ) • D23 = Point.some (60 : ZMod 103) 84 ns_60_84 :=
  nsmul_step D23_m16 D23_m8 step60 (by norm_num)
theorem step61 : Point.some (60 : ZMod 103) 84 ns_60_84 + Point.some (79 : ZMod 103) 64 ns_79_64 = Point.some (19 : ZMod 103) 68 ns_19_68 :=
  add_cert (ℓ := (64 : ZMod 103)) ns_60_84 ns_79_64 ns_19_68 (by decide) (by decide) (by decide) (by decide)
theorem D23_m28 : (28 : ℕ) • D23 = Point.some (19 : ZMod 103) 68 ns_19_68 :=
  nsmul_step D23_m24 D23_m4 step61 (by norm_num)
theorem step62 : Point.some (19 : ZMod 103) 68 ns_19_68 + Point.some (38 : ZMod 103) 33 ns_38_33 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  add_cert (ℓ := (9 : ZMod 103)) ns_19_68 ns_38_33 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D23_m30 : (30 : ℕ) • D23 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step D23_m28 D23_m2 step62 (by norm_num)

/-- `(60/2) • D23 ≠ 0`. -/
theorem D23_nsmul_30_ne : (30 : ℕ) • D23 ≠ 0 := by
  rw [D23_m30]
  exact Point.some_ne_zero _
theorem step63 : Point.some (46 : ZMod 103) 84 ns_46_84 + Point.some (79 : ZMod 103) 64 ns_79_64 = Point.some (76 : ZMod 103) 84 ns_76_84 :=
  add_cert (ℓ := (15 : ZMod 103)) ns_46_84 ns_79_64 ns_76_84 (by decide) (by decide) (by decide) (by decide)
theorem D23_m20 : (20 : ℕ) • D23 = Point.some (76 : ZMod 103) 84 ns_76_84 :=
  nsmul_step D23_m16 D23_m4 step63 (by norm_num)

/-- `(60/3) • D23 ≠ 0`. -/
theorem D23_nsmul_20_ne : (20 : ℕ) • D23 ≠ 0 := by
  rw [D23_m20]
  exact Point.some_ne_zero _
theorem D23_m12 : (12 : ℕ) • D23 = Point.some (18 : ZMod 103) 37 ns_18_37 :=
  nsmul_step D23_m8 D23_m4 step33 (by norm_num)

/-- `(60/5) • D23 ≠ 0`. -/
theorem D23_nsmul_12_ne : (12 : ℕ) • D23 ≠ 0 := by
  rw [D23_m12]
  exact Point.some_ne_zero _

/-- `D23` has exact order `60` in `E(𝔽_103)`. -/
theorem D23_addOrderOf : addOrderOf D23 = 60 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D23_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 2 * 3 ^ 1 * 5 ^ 1 : ℕ) = 60 := by norm_num
  have h : q ∣ 2 ^ 2 * 3 ^ 1 * 5 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h3a | h3b
  · skip
    rcases (Nat.Prime.dvd_mul hq).mp h3a with h2a | h2b
    · skip
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
      exact D23_nsmul_30_ne
    · skip
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
      exact D23_nsmul_20_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h3b)
    exact D23_nsmul_12_ne

theorem P2_sub_P3_addOrderOf : addOrderOf (P2 - P3) = 60 := by
  rw [D23_eq]
  exact D23_addOrderOf

theorem P3_sub_P2_addOrderOf : addOrderOf (P3 - P2) = 60 := by
  rw [← neg_sub P2 P3, addOrderOf_neg]
  exact P2_sub_P3_addOrderOf

/-! ### `P2 - P4` -/

theorem ns_73_82 : E.Nonsingular (73 : ZMod 103) 82 := nonsingular_of (by decide) (by decide)
theorem step64 : Point.some (89 : ZMod 103) 35 ns_89_35 + Point.some (61 : ZMod 103) 62 ns_61_62 = Point.some (73 : ZMod 103) 82 ns_73_82 :=
  add_cert (ℓ := (91 : ZMod 103)) ns_89_35 ns_61_62 ns_73_82 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P2 - P4` as an explicit point. -/
theorem D24_eq : P2 - P4 = Point.some (73 : ZMod 103) 82 ns_73_82 :=
  sub_cert ns_89_35 ns_61_41 ns_61_62 ns_73_82 (by decide) step64

abbrev D24 : E.Point := Point.some (73 : ZMod 103) 82 ns_73_82

theorem D24_m1 : (1 : ℕ) • D24 = Point.some (73 : ZMod 103) 82 ns_73_82 := one_nsmul _
theorem ns_92_74 : E.Nonsingular (92 : ZMod 103) 74 := nonsingular_of (by decide) (by decide)
theorem step65 : Point.some (73 : ZMod 103) 82 ns_73_82 + Point.some (73 : ZMod 103) 82 ns_73_82 = Point.some (92 : ZMod 103) 74 ns_92_74 :=
  dbl_cert (ℓ := (46 : ZMod 103)) ns_73_82 ns_92_74 (by decide) (by decide) (by decide) (by decide)
theorem D24_m2 : (2 : ℕ) • D24 = Point.some (92 : ZMod 103) 74 ns_92_74 :=
  nsmul_step D24_m1 D24_m1 step65 (by norm_num)
theorem ns_30_80 : E.Nonsingular (30 : ZMod 103) 80 := nonsingular_of (by decide) (by decide)
theorem step66 : Point.some (92 : ZMod 103) 74 ns_92_74 + Point.some (92 : ZMod 103) 74 ns_92_74 = Point.some (30 : ZMod 103) 80 ns_30_80 :=
  dbl_cert (ℓ := (49 : ZMod 103)) ns_92_74 ns_30_80 (by decide) (by decide) (by decide) (by decide)
theorem D24_m4 : (4 : ℕ) • D24 = Point.some (30 : ZMod 103) 80 ns_30_80 :=
  nsmul_step D24_m2 D24_m2 step66 (by norm_num)
theorem step67 : Point.some (30 : ZMod 103) 80 ns_30_80 + Point.some (30 : ZMod 103) 80 ns_30_80 = Point.some (14 : ZMod 103) 56 ns_14_56 :=
  dbl_cert (ℓ := (60 : ZMod 103)) ns_30_80 ns_14_56 (by decide) (by decide) (by decide) (by decide)
theorem D24_m8 : (8 : ℕ) • D24 = Point.some (14 : ZMod 103) 56 ns_14_56 :=
  nsmul_step D24_m4 D24_m4 step67 (by norm_num)
theorem D24_m16 : (16 : ℕ) • D24 = Point.some (46 : ZMod 103) 84 ns_46_84 :=
  nsmul_step D24_m8 D24_m8 step57 (by norm_num)
theorem D24_m32 : (32 : ℕ) • D24 = Point.some (19 : ZMod 103) 35 ns_19_35 :=
  nsmul_step D24_m16 D24_m16 step30 (by norm_num)
theorem D24_m64 : (64 : ℕ) • D24 = Point.some (79 : ZMod 103) 64 ns_79_64 :=
  nsmul_step D24_m32 D24_m32 step31 (by norm_num)
theorem D24_m96 : (96 : ℕ) • D24 = Point.some (60 : ZMod 103) 19 ns_60_19 :=
  nsmul_step D24_m64 D24_m32 step36 (by norm_num)
theorem D24_m112 : (112 : ℕ) • D24 = Point.some (14 : ZMod 103) 47 ns_14_47 :=
  nsmul_step D24_m96 D24_m16 step37 (by norm_num)
theorem step68 : Point.some (14 : ZMod 103) 47 ns_14_47 + Point.some (14 : ZMod 103) 56 ns_14_56 = (0 : E.Point) :=
  add_zero_cert ns_14_47 ns_14_56 (by decide) (by decide)
theorem D24_m120 : (120 : ℕ) • D24 = (0 : E.Point) :=
  nsmul_step D24_m112 D24_m8 step68 (by norm_num)

/-- `120 • D24 = 0`. -/
theorem D24_nsmul_order : (120 : ℕ) • D24 = 0 := D24_m120
theorem D24_m48 : (48 : ℕ) • D24 = Point.some (18 : ZMod 103) 66 ns_18_66 :=
  nsmul_step D24_m32 D24_m16 step40 (by norm_num)
theorem D24_m56 : (56 : ℕ) • D24 = Point.some (79 : ZMod 103) 39 ns_79_39 :=
  nsmul_step D24_m48 D24_m8 step58 (by norm_num)
theorem step69 : Point.some (79 : ZMod 103) 39 ns_79_39 + Point.some (30 : ZMod 103) 80 ns_30_80 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  add_cert (ℓ := (37 : ZMod 103)) ns_79_39 ns_30_80 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D24_m60 : (60 : ℕ) • D24 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step D24_m56 D24_m4 step69 (by norm_num)

/-- `(120/2) • D24 ≠ 0`. -/
theorem D24_nsmul_60_ne : (60 : ℕ) • D24 ≠ 0 := by
  rw [D24_m60]
  exact Point.some_ne_zero _
theorem step70 : Point.some (19 : ZMod 103) 35 ns_19_35 + Point.some (14 : ZMod 103) 56 ns_14_56 = Point.some (76 : ZMod 103) 19 ns_76_19 :=
  add_cert (ℓ := (37 : ZMod 103)) ns_19_35 ns_14_56 ns_76_19 (by decide) (by decide) (by decide) (by decide)
theorem D24_m40 : (40 : ℕ) • D24 = Point.some (76 : ZMod 103) 19 ns_76_19 :=
  nsmul_step D24_m32 D24_m8 step70 (by norm_num)

/-- `(120/3) • D24 ≠ 0`. -/
theorem D24_nsmul_40_ne : (40 : ℕ) • D24 ≠ 0 := by
  rw [D24_m40]
  exact Point.some_ne_zero _
theorem D24_m24 : (24 : ℕ) • D24 = Point.some (60 : ZMod 103) 84 ns_60_84 :=
  nsmul_step D24_m16 D24_m8 step60 (by norm_num)

/-- `(120/5) • D24 ≠ 0`. -/
theorem D24_nsmul_24_ne : (24 : ℕ) • D24 ≠ 0 := by
  rw [D24_m24]
  exact Point.some_ne_zero _

/-- `D24` has exact order `120` in `E(𝔽_103)`. -/
theorem D24_addOrderOf : addOrderOf D24 = 120 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D24_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 * 3 ^ 1 * 5 ^ 1 : ℕ) = 120 := by norm_num
  have h : q ∣ 2 ^ 3 * 3 ^ 1 * 5 ^ 1 := by rw [e]; exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h with h3a | h3b
  · skip
    rcases (Nat.Prime.dvd_mul hq).mp h3a with h2a | h2b
    · skip
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2a)
      exact D24_nsmul_60_ne
    · skip
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2b)
      exact D24_nsmul_40_ne
  · skip
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h3b)
    exact D24_nsmul_24_ne

theorem P2_sub_P4_addOrderOf : addOrderOf (P2 - P4) = 120 := by
  rw [D24_eq]
  exact D24_addOrderOf

theorem P4_sub_P2_addOrderOf : addOrderOf (P4 - P2) = 120 := by
  rw [← neg_sub P2 P4, addOrderOf_neg]
  exact P2_sub_P4_addOrderOf

/-! ### `P3 - P4` -/

theorem ns_47_74 : E.Nonsingular (47 : ZMod 103) 74 := nonsingular_of (by decide) (by decide)
theorem step71 : Point.some (99 : ZMod 103) 78 ns_99_78 + Point.some (61 : ZMod 103) 62 ns_61_62 = Point.some (47 : ZMod 103) 74 ns_47_74 :=
  add_cert (ℓ := (98 : ZMod 103)) ns_99_78 ns_61_62 ns_47_74 (by decide) (by decide) (by decide) (by decide)
/-- The difference `P3 - P4` as an explicit point. -/
theorem D34_eq : P3 - P4 = Point.some (47 : ZMod 103) 74 ns_47_74 :=
  sub_cert ns_99_78 ns_61_41 ns_61_62 ns_47_74 (by decide) step71

abbrev D34 : E.Point := Point.some (47 : ZMod 103) 74 ns_47_74

theorem D34_m1 : (1 : ℕ) • D34 = Point.some (47 : ZMod 103) 74 ns_47_74 := one_nsmul _
theorem ns_1_51 : E.Nonsingular (1 : ZMod 103) 51 := nonsingular_of (by decide) (by decide)
theorem step72 : Point.some (47 : ZMod 103) 74 ns_47_74 + Point.some (47 : ZMod 103) 74 ns_47_74 = Point.some (1 : ZMod 103) 51 ns_1_51 :=
  dbl_cert (ℓ := (99 : ZMod 103)) ns_47_74 ns_1_51 (by decide) (by decide) (by decide) (by decide)
theorem D34_m2 : (2 : ℕ) • D34 = Point.some (1 : ZMod 103) 51 ns_1_51 :=
  nsmul_step D34_m1 D34_m1 step72 (by norm_num)
theorem step73 : Point.some (1 : ZMod 103) 51 ns_1_51 + Point.some (1 : ZMod 103) 51 ns_1_51 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  dbl_cert (ℓ := (51 : ZMod 103)) ns_1_51 ns_0_0 (by decide) (by decide) (by decide) (by decide)
theorem D34_m4 : (4 : ℕ) • D34 = Point.some (0 : ZMod 103) 0 ns_0_0 :=
  nsmul_step D34_m2 D34_m2 step73 (by norm_num)
theorem step74 : Point.some (0 : ZMod 103) 0 ns_0_0 + Point.some (0 : ZMod 103) 0 ns_0_0 = (0 : E.Point) :=
  add_zero_cert ns_0_0 ns_0_0 (by decide) (by decide)
theorem D34_m8 : (8 : ℕ) • D34 = (0 : E.Point) :=
  nsmul_step D34_m4 D34_m4 step74 (by norm_num)

/-- `8 • D34 = 0`. -/
theorem D34_nsmul_order : (8 : ℕ) • D34 = 0 := D34_m8

/-- `(8/2) • D34 ≠ 0`. -/
theorem D34_nsmul_4_ne : (4 : ℕ) • D34 ≠ 0 := by
  rw [D34_m4]
  exact Point.some_ne_zero _

/-- `D34` has exact order `8` in `E(𝔽_103)`. -/
theorem D34_addOrderOf : addOrderOf D34 = 8 := by
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul D34_nsmul_order ?_
  intro q hq hdvd
  have e : (2 ^ 3 : ℕ) = 8 := by norm_num
  have h : q ∣ 2 ^ 3 := by rw [e]; exact hdvd
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
  exact D34_nsmul_4_ne

theorem P3_sub_P4_addOrderOf : addOrderOf (P3 - P4) = 8 := by
  rw [D34_eq]
  exact D34_addOrderOf

theorem P4_sub_P3_addOrderOf : addOrderOf (P4 - P3) = 8 := by
  rw [← neg_sub P3 P4, addOrderOf_neg]
  exact P3_sub_P4_addOrderOf

end P103

end Tower.TangentLine
