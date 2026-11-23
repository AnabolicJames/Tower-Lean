import Mathlib
import Tower.RV6.LadderB

/-!
# Power series at `q = e^{-2πy}`: the relations of level six on the imaginary axis

`Level6.lean` proves nine polynomial relations among `E₂, E₄, E₆` at `X, X², X³, X⁶` in
`ℝ⟦X⟧`.  This file evaluates the five of them that involve `E₂` and `E₄` only at `q = e^{-2πy}`,
`y > 0`:

* `cfS F`, `AbsS F`, `evA F y`: the coefficients of a power series, absolute summability of
  `∑ cₙ e^{-2πny}` for every `y > 0`, and the value of that sum (`qa` of `QSeries.lean`);
* `evA_add`, `evA_C_mul`, `evA_mul` (the Cauchy product, `qa_mul`), `evA_expand`
  (`X ↦ X^d` is `y ↦ d y`, `qa_dilate`), `evA_qform`: the value of a quadratic form in four
  series;
* `axis_Rf1 … axis_Rf4`: `E₄(i d y)` for `d = 1, 2, 3, 6` as a quadratic form in the four
  numbers `E₂(iy), E₂(2iy), E₂(3iy), E₂(6iy)`;  `axis_Rf9`: the quadratic relation among these
  four numbers.

The relations are used in the variables `M_d = ∑ σ₁(n) X^{dn}`, `N_d = ∑ σ₃(n) X^{dn}`
(`E₂(X^d) = 1 - 24 M_d`, `E₄(X^d) = 1 + 240 N_d`), in which they have no constant term.

This file is written by `tools/gen_modaxis.py`, which reads the relations from `Level6.lean` and
checks every `linear_combination` in exact arithmetic.
-/

namespace Tower.RV6

open Real

/-! ## The value of a power series on the axis -/

/-- The coefficient sequence of a power series. -/
noncomputable def cfS (F : PowerSeries ℝ) (n : ℕ) : ℝ := PowerSeries.coeff n F

/-- `∑ |cₙ| e^{-2πny}` converges for every `y > 0`. -/
def AbsS (F : PowerSeries ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → Summable fun n : ℕ => |cfS F n| * Real.exp (-(2 * π * (n : ℝ) * y))

/-- The value `∑ cₙ e^{-2πny}` of a power series at `q = e^{-2πy}`. -/
noncomputable def evA (F : PowerSeries ℝ) (y : ℝ) : ℝ := qa (cfS F) y

theorem absS_of_le {F : PowerSeries ℝ} {B : ℝ} {K : ℕ}
    (h : ∀ n : ℕ, |cfS F n| ≤ B * (n : ℝ) ^ K) : AbsS F := by
  intro y hy
  have hs := summable_qa_abs h hy
  exact hs

theorem summable_of_absS {F : PowerSeries ℝ} (h : AbsS F) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => cfS F n * Real.exp (-(2 * π * (n : ℝ) * y)) :=
  summable_of_abs_axis (h y hy)

theorem cfS_add (F G : PowerSeries ℝ) (n : ℕ) : cfS (F + G) n = cfS F n + cfS G n := by
  unfold cfS
  rw [map_add]

theorem cfS_C_mul (c : ℝ) (F : PowerSeries ℝ) (n : ℕ) :
    cfS (PowerSeries.C c * F) n = c * cfS F n := by
  unfold cfS
  exact PowerSeries.coeff_C_mul n F c

theorem cfS_mul (F G : PowerSeries ℝ) (n : ℕ) :
    cfS (F * G) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, cfS F p.1 * cfS G p.2 := by
  unfold cfS
  exact PowerSeries.coeff_mul n F G

theorem cfS_expand (F : PowerSeries ℝ) (d : ℕ) (hd : d ≠ 0) :
    cfS (PowerSeries.expand d hd F) = fun n => if d ∣ n then cfS F (n / d) else 0 := by
  funext n
  unfold cfS
  exact PowerSeries.coeff_expand d hd F

/-! ## Absolute summability -/

theorem absS_add {F G : PowerSeries ℝ} (hF : AbsS F) (hG : AbsS G) : AbsS (F + G) := by
  intro y hy
  have hsum := (hF y hy).add (hG y hy)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
  · exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  · show |cfS (F + G) n| * Real.exp (-(2 * π * (n : ℝ) * y))
      ≤ |cfS F n| * Real.exp (-(2 * π * (n : ℝ) * y))
        + |cfS G n| * Real.exp (-(2 * π * (n : ℝ) * y))
    rw [cfS_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.exp_pos _).le

theorem absS_C_mul (c : ℝ) {F : PowerSeries ℝ} (hF : AbsS F) : AbsS (PowerSeries.C c * F) := by
  intro y hy
  have h := (hF y hy).mul_left |c|
  refine h.congr (fun n => ?_)
  show |c| * (|cfS F n| * Real.exp (-(2 * π * (n : ℝ) * y)))
    = |cfS (PowerSeries.C c * F) n| * Real.exp (-(2 * π * (n : ℝ) * y))
  rw [cfS_C_mul, abs_mul]
  ring

theorem absS_mul {F G : PowerSeries ℝ} (hF : AbsS F) (hG : AbsS G) : AbsS (F * G) := by
  intro y hy
  have hF1 : Summable fun n : ℕ => ‖cfS F n * Real.exp (-(2 * π * (n : ℝ) * y))‖ := by
    refine (hF y hy).congr (fun n => ?_)
    show |cfS F n| * Real.exp (-(2 * π * (n : ℝ) * y))
      = ‖cfS F n * Real.exp (-(2 * π * (n : ℝ) * y))‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hG1 : Summable fun n : ℕ => ‖cfS G n * Real.exp (-(2 * π * (n : ℝ) * y))‖ := by
    refine (hG y hy).congr (fun n => ?_)
    show |cfS G n| * Real.exp (-(2 * π * (n : ℝ) * y))
      = ‖cfS G n * Real.exp (-(2 * π * (n : ℝ) * y))‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hF1 hG1
  refine hs.congr (fun n => ?_)
  show ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        cfS F p.1 * Real.exp (-(2 * π * (p.1 : ℝ) * y))
          * (cfS G p.2 * Real.exp (-(2 * π * (p.2 : ℝ) * y)))‖
    = |cfS (F * G) n| * Real.exp (-(2 * π * (n : ℝ) * y))
  have hsum : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        cfS F p.1 * Real.exp (-(2 * π * (p.1 : ℝ) * y))
          * (cfS G p.2 * Real.exp (-(2 * π * (p.2 : ℝ) * y)))
      = cfS (F * G) n * Real.exp (-(2 * π * (n : ℝ) * y)) := by
    rw [cfS_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp1 : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have he : Real.exp (-(2 * π * (p.1 : ℝ) * y)) * Real.exp (-(2 * π * (p.2 : ℝ) * y))
        = Real.exp (-(2 * π * (n : ℝ) * y)) := by
      rw [← Real.exp_add, ← hp1]
      congr 1
      push_cast
      ring
    rw [← he]
    ring
  rw [hsum, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-! ## The value is additive and multiplicative -/

theorem evA_zero (y : ℝ) : evA 0 y = 0 := by
  have h : ∀ n : ℕ, cfS (0 : PowerSeries ℝ) n * Real.exp (-(2 * π * (n : ℝ) * y)) = 0 := by
    intro n
    unfold cfS
    rw [map_zero, zero_mul]
  unfold evA qa
  first
    | (rw [tsum_congr h]; exact tsum_zero)
    | simp only [h, tsum_zero]

theorem evA_add {F G : PowerSeries ℝ} (hF : AbsS F) (hG : AbsS G) {y : ℝ} (hy : 0 < y) :
    evA (F + G) y = evA F y + evA G y := by
  have h := qa_add (summable_of_absS hF hy) (summable_of_absS hG hy)
  have hc : cfS (F + G) = fun n => cfS F n + cfS G n := funext (cfS_add F G)
  unfold evA
  rw [hc]
  exact h

theorem evA_C_mul (c : ℝ) (F : PowerSeries ℝ) (y : ℝ) :
    evA (PowerSeries.C c * F) y = c * evA F y := by
  have hc : cfS (PowerSeries.C c * F) = fun n => c * cfS F n := funext (cfS_C_mul c F)
  unfold evA
  rw [hc]
  exact qa_const_mul c (cfS F) y

theorem evA_mul {F G : PowerSeries ℝ} (hF : AbsS F) (hG : AbsS G) {y : ℝ} (hy : 0 < y) :
    evA (F * G) y = evA F y * evA G y := by
  have h := qa_mul (hF y hy) (hG y hy)
  have hc : cfS (F * G)
      = fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, cfS F p.1 * cfS G p.2 :=
    funext (cfS_mul F G)
  unfold evA
  rw [hc]
  exact h.symm

theorem evA_add_C_mul {A G : PowerSeries ℝ} (hA : AbsS A) (hG : AbsS G) (c : ℝ) {y : ℝ}
    (hy : 0 < y) : evA (A + PowerSeries.C c * G) y = evA A y + c * evA G y := by
  rw [evA_add hA (absS_C_mul c hG) hy, evA_C_mul]

theorem evA_expand (F : PowerSeries ℝ) (d : ℕ) (hd : d ≠ 0) (y : ℝ) :
    evA (PowerSeries.expand d hd F) y = evA F ((d : ℝ) * y) := by
  unfold evA
  rw [cfS_expand F d hd]
  exact qa_dilate (cfS F) d (Nat.pos_of_ne_zero hd) y

theorem absS_expand {F : PowerSeries ℝ} {B : ℝ} {K : ℕ} (hB : 0 ≤ B)
    (hF : ∀ n : ℕ, |cfS F n| ≤ B * (n : ℝ) ^ K) (d : ℕ) (hd : d ≠ 0) :
    AbsS (PowerSeries.expand d hd F) := by
  refine absS_of_le (B := B) (K := K) (fun n => ?_)
  rw [cfS_expand F d hd]
  exact dil_abs_le hB hF d n

/-- The value of a quadratic form in four series, plus a multiple of a fifth. -/
theorem evA_qform (a1 a2 a3 a6 c11 c12 c13 c16 c22 c23 c26 c33 c36 c66 b : ℝ)
    {M1 M2 M3 M6 N : PowerSeries ℝ} (h1 : AbsS M1) (h2 : AbsS M2) (h3 : AbsS M3) (h6 : AbsS M6)
    (hN : AbsS N) {y : ℝ} (hy : 0 < y) :
    evA (PowerSeries.C a1 * M1 + PowerSeries.C a2 * M2 + PowerSeries.C a3 * M3
        + PowerSeries.C a6 * M6 + PowerSeries.C c11 * (M1 * M1)
        + PowerSeries.C c12 * (M1 * M2) + PowerSeries.C c13 * (M1 * M3)
        + PowerSeries.C c16 * (M1 * M6) + PowerSeries.C c22 * (M2 * M2)
        + PowerSeries.C c23 * (M2 * M3) + PowerSeries.C c26 * (M2 * M6)
        + PowerSeries.C c33 * (M3 * M3) + PowerSeries.C c36 * (M3 * M6)
        + PowerSeries.C c66 * (M6 * M6) + PowerSeries.C b * N) y
      = a1 * evA M1 y + a2 * evA M2 y + a3 * evA M3 y + a6 * evA M6 y
        + c11 * (evA M1 y * evA M1 y) + c12 * (evA M1 y * evA M2 y)
        + c13 * (evA M1 y * evA M3 y) + c16 * (evA M1 y * evA M6 y)
        + c22 * (evA M2 y * evA M2 y) + c23 * (evA M2 y * evA M3 y)
        + c26 * (evA M2 y * evA M6 y) + c33 * (evA M3 y * evA M3 y)
        + c36 * (evA M3 y * evA M6 y) + c66 * (evA M6 y * evA M6 y) + b * evA N y := by
  have s1 := absS_C_mul a1 h1
  have s2 := absS_add s1 (absS_C_mul a2 h2)
  have s3 := absS_add s2 (absS_C_mul a3 h3)
  have s4 := absS_add s3 (absS_C_mul a6 h6)
  have s5 := absS_add s4 (absS_C_mul c11 (absS_mul h1 h1))
  have s6 := absS_add s5 (absS_C_mul c12 (absS_mul h1 h2))
  have s7 := absS_add s6 (absS_C_mul c13 (absS_mul h1 h3))
  have s8 := absS_add s7 (absS_C_mul c16 (absS_mul h1 h6))
  have s9 := absS_add s8 (absS_C_mul c22 (absS_mul h2 h2))
  have s10 := absS_add s9 (absS_C_mul c23 (absS_mul h2 h3))
  have s11 := absS_add s10 (absS_C_mul c26 (absS_mul h2 h6))
  have s12 := absS_add s11 (absS_C_mul c33 (absS_mul h3 h3))
  have s13 := absS_add s12 (absS_C_mul c36 (absS_mul h3 h6))
  have s14 := absS_add s13 (absS_C_mul c66 (absS_mul h6 h6))
  rw [evA_add_C_mul s14 hN b hy, evA_add_C_mul s13 (absS_mul h6 h6) c66 hy,
    evA_add_C_mul s12 (absS_mul h3 h6) c36 hy, evA_add_C_mul s11 (absS_mul h3 h3) c33 hy,
    evA_add_C_mul s10 (absS_mul h2 h6) c26 hy, evA_add_C_mul s9 (absS_mul h2 h3) c23 hy,
    evA_add_C_mul s8 (absS_mul h2 h2) c22 hy, evA_add_C_mul s7 (absS_mul h1 h6) c16 hy,
    evA_add_C_mul s6 (absS_mul h1 h3) c13 hy, evA_add_C_mul s5 (absS_mul h1 h2) c12 hy,
    evA_add_C_mul s4 (absS_mul h1 h1) c11 hy, evA_add_C_mul s3 h6 a6 hy,
    evA_add_C_mul s2 h3 a3 hy, evA_add_C_mul s1 h2 a2 hy, evA_C_mul a1 M1 y,
    evA_mul h1 h1 hy, evA_mul h1 h2 hy, evA_mul h1 h3 hy, evA_mul h1 h6 hy,
    evA_mul h2 h2 hy, evA_mul h2 h3 hy, evA_mul h2 h6 hy, evA_mul h3 h3 hy,
    evA_mul h3 h6 hy, evA_mul h6 h6 hy]

/-! ## The series of `σ₁` and `σ₃` and their dilates -/

theorem cfS_S1 : cfS S1 = sig 1 := funext (fun n => coeff_S1 n)

theorem cfS_S3 : cfS S3 = sig 3 := funext (fun n => coeff_S3 n)

theorem sig1_cfS_le (n : ℕ) : |cfS S1 n| ≤ 1 * (n : ℝ) ^ (1 + 1) := by
  rw [cfS_S1]
  exact sig_abs_le 1 n

theorem sig3_cfS_le (n : ℕ) : |cfS S3 n| ≤ 1 * (n : ℝ) ^ (3 + 1) := by
  rw [cfS_S3]
  exact sig_abs_le 3 n

theorem absS_S1 : AbsS S1 := absS_of_le sig1_cfS_le

theorem absS_S3 : AbsS S3 := absS_of_le sig3_cfS_le

/-- `∑ σ₁(n) X^{2n}`. -/
noncomputable def sM2 : PowerSeries ℝ := PowerSeries.expand 2 two_ne S1

/-- `∑ σ₁(n) X^{3n}`. -/
noncomputable def sM3 : PowerSeries ℝ := PowerSeries.expand 3 three_ne S1

/-- `∑ σ₁(n) X^{6n}`. -/
noncomputable def sM6 : PowerSeries ℝ := PowerSeries.expand 6 six_ne S1

/-- `∑ σ₃(n) X^{2n}`. -/
noncomputable def sN2 : PowerSeries ℝ := PowerSeries.expand 2 two_ne S3

/-- `∑ σ₃(n) X^{3n}`. -/
noncomputable def sN3 : PowerSeries ℝ := PowerSeries.expand 3 three_ne S3

/-- `∑ σ₃(n) X^{6n}`. -/
noncomputable def sN6 : PowerSeries ℝ := PowerSeries.expand 6 six_ne S3

theorem absS_M2 : AbsS sM2 := absS_expand zero_le_one sig1_cfS_le 2 two_ne

theorem absS_M3 : AbsS sM3 := absS_expand zero_le_one sig1_cfS_le 3 three_ne

theorem absS_M6 : AbsS sM6 := absS_expand zero_le_one sig1_cfS_le 6 six_ne

theorem absS_N2 : AbsS sN2 := absS_expand zero_le_one sig3_cfS_le 2 two_ne

theorem absS_N3 : AbsS sN3 := absS_expand zero_le_one sig3_cfS_le 3 three_ne

theorem absS_N6 : AbsS sN6 := absS_expand zero_le_one sig3_cfS_le 6 six_ne

theorem evA_S1 (y : ℝ) : evA S1 y = qa (sig 1) y := by
  unfold evA
  rw [cfS_S1]

theorem evA_S3 (y : ℝ) : evA S3 y = qa (sig 3) y := by
  unfold evA
  rw [cfS_S3]

theorem evA_M2 (y : ℝ) : evA sM2 y = qa (sig 1) (2 * y) := by
  have e := evA_expand S1 2 two_ne y
  rw [Nat.cast_ofNat, evA_S1] at e
  exact e

theorem evA_M3 (y : ℝ) : evA sM3 y = qa (sig 1) (3 * y) := by
  have e := evA_expand S1 3 three_ne y
  rw [Nat.cast_ofNat, evA_S1] at e
  exact e

theorem evA_M6 (y : ℝ) : evA sM6 y = qa (sig 1) (6 * y) := by
  have e := evA_expand S1 6 six_ne y
  rw [Nat.cast_ofNat, evA_S1] at e
  exact e

theorem evA_N2 (y : ℝ) : evA sN2 y = qa (sig 3) (2 * y) := by
  have e := evA_expand S3 2 two_ne y
  rw [Nat.cast_ofNat, evA_S3] at e
  exact e

theorem evA_N3 (y : ℝ) : evA sN3 y = qa (sig 3) (3 * y) := by
  have e := evA_expand S3 3 three_ne y
  rw [Nat.cast_ofNat, evA_S3] at e
  exact e

theorem evA_N6 (y : ℝ) : evA sN6 y = qa (sig 3) (6 * y) := by
  have e := evA_expand S3 6 six_ne y
  rw [Nat.cast_ofNat, evA_S3] at e
  exact e

theorem e2_1_eq : e2_1 = 1 - 24 * S1 := rfl

theorem e2_2_eq : e2_2 = 1 - 24 * sM2 := by
  unfold e2_2 xE sM2
  simp only [map_sub, map_mul, map_one, map_ofNat]

theorem e2_3_eq : e2_3 = 1 - 24 * sM3 := by
  unfold e2_3 xE sM3
  simp only [map_sub, map_mul, map_one, map_ofNat]

theorem e2_6_eq : e2_6 = 1 - 24 * sM6 := by
  unfold e2_6 xE sM6
  simp only [map_sub, map_mul, map_one, map_ofNat]

theorem e4_1_eq : e4_1 = 1 + 240 * S3 := rfl

theorem e4_2_eq : e4_2 = 1 + 240 * sN2 := by
  unfold e4_2 uE sN2
  simp only [map_add, map_mul, map_one, map_ofNat]

theorem e4_3_eq : e4_3 = 1 + 240 * sN3 := by
  unfold e4_3 uE sN3
  simp only [map_add, map_mul, map_one, map_ofNat]

theorem e4_6_eq : e4_6 = 1 + 240 * sN6 := by
  unfold e4_6 uE sN6
  simp only [map_add, map_mul, map_one, map_ofNat]

/-! ## The five relations on the axis -/

/-- The relation `Rf1` of `Level6.lean` at `q = e^{-2πy}`. -/
theorem axis_Rf1 {y : ℝ} (hy : 0 < y) :
    (-17) * (E2im y * E2im (2 * y)) + 24 * (E2im y * E2im (3 * y))
      + 3 * (E2im y * E2im (6 * y)) + 7 * (E2im (2 * y) * E2im (2 * y))
      + (-3) * (E2im (2 * y) * E2im (3 * y)) + 66 * (E2im (2 * y) * E2im (6 * y))
      + 27 * (E2im (3 * y) * E2im (3 * y)) + (-243) * (E2im (3 * y) * E2im (6 * y))
      + 135 * (E2im (6 * y) * E2im (6 * y)) + E4im y = 0 := by
  have h2 : (0 : ℝ) < 2 * y := mul_pos (by norm_num) hy
  have h3 : (0 : ℝ) < 3 * y := mul_pos (by norm_num) hy
  have h6 : (0 : ℝ) < 6 * y := mul_pos (by norm_num) hy
  have hS : (PowerSeries.C (-240 : ℝ) * S1 + PowerSeries.C (-1440 : ℝ) * sM2
        + PowerSeries.C (4032 : ℝ) * sM3 + PowerSeries.C (-2304 : ℝ) * sM6
        + PowerSeries.C (0 : ℝ) * (S1 * S1) + PowerSeries.C (-9792 : ℝ) * (S1 * sM2)
        + PowerSeries.C (13824 : ℝ) * (S1 * sM3) + PowerSeries.C (1728 : ℝ) * (S1 * sM6)
        + PowerSeries.C (4032 : ℝ) * (sM2 * sM2) + PowerSeries.C (-1728 : ℝ) * (sM2 * sM3)
        + PowerSeries.C (38016 : ℝ) * (sM2 * sM6)
        + PowerSeries.C (15552 : ℝ) * (sM3 * sM3)
        + PowerSeries.C (-139968 : ℝ) * (sM3 * sM6)
        + PowerSeries.C (77760 : ℝ) * (sM6 * sM6) + PowerSeries.C (240 : ℝ) * S3
        : PowerSeries ℝ) = 0 := by
    have h := Rf1_eq_zero ram6
    unfold Rf1 at h
    rw [e2_1_eq, e2_2_eq, e2_3_eq, e2_6_eq, e4_1_eq] at h
    simp only [map_neg, map_ofNat, map_zero, map_one]
    linear_combination h
  have hev := evA_qform (-240 : ℝ) (-1440 : ℝ) (4032 : ℝ) (-2304 : ℝ) (0 : ℝ) (-9792 : ℝ) (13824 : ℝ)
    (1728 : ℝ) (4032 : ℝ) (-1728 : ℝ) (38016 : ℝ) (15552 : ℝ) (-139968 : ℝ) (77760 : ℝ)
    (240 : ℝ)
    absS_S1 absS_M2 absS_M3 absS_M6 absS_S3 hy
  rw [hS, evA_zero, evA_S1, evA_M2, evA_M3, evA_M6, evA_S3] at hev
  rw [E2im_eq_qa hy, E2im_eq_qa h2, E2im_eq_qa h3, E2im_eq_qa h6, E4im_eq_qa hy]
  linear_combination (-1 : ℝ) * hev

/-- The relation `Rf2` of `Level6.lean` at `q = e^{-2πy}`. -/
theorem axis_Rf2 {y : ℝ} (hy : 0 < y) :
    (-3) * (E2im y * E2im (2 * y)) + 6 * (E2im y * E2im (3 * y))
      + (-3) * (E2im y * E2im (6 * y)) + (-7) * (E2im (2 * y) * E2im (2 * y))
      + 3 * (E2im (2 * y) * E2im (3 * y)) + 54 * (E2im (2 * y) * E2im (6 * y))
      + 18 * (E2im (3 * y) * E2im (3 * y)) + (-117) * (E2im (3 * y) * E2im (6 * y))
      + 45 * (E2im (6 * y) * E2im (6 * y)) + 4 * (E4im (2 * y)) = 0 := by
  have h2 : (0 : ℝ) < 2 * y := mul_pos (by norm_num) hy
  have h3 : (0 : ℝ) < 3 * y := mul_pos (by norm_num) hy
  have h6 : (0 : ℝ) < 6 * y := mul_pos (by norm_num) hy
  have hS : (PowerSeries.C (0 : ℝ) * S1 + PowerSeries.C (-960 : ℝ) * sM2
        + PowerSeries.C (1728 : ℝ) * sM3 + PowerSeries.C (-576 : ℝ) * sM6
        + PowerSeries.C (0 : ℝ) * (S1 * S1) + PowerSeries.C (-1728 : ℝ) * (S1 * sM2)
        + PowerSeries.C (3456 : ℝ) * (S1 * sM3) + PowerSeries.C (-1728 : ℝ) * (S1 * sM6)
        + PowerSeries.C (-4032 : ℝ) * (sM2 * sM2) + PowerSeries.C (1728 : ℝ) * (sM2 * sM3)
        + PowerSeries.C (31104 : ℝ) * (sM2 * sM6)
        + PowerSeries.C (10368 : ℝ) * (sM3 * sM3)
        + PowerSeries.C (-67392 : ℝ) * (sM3 * sM6)
        + PowerSeries.C (25920 : ℝ) * (sM6 * sM6) + PowerSeries.C (960 : ℝ) * sN2
        : PowerSeries ℝ) = 0 := by
    have h := Rf2_eq_zero ram6
    unfold Rf2 at h
    rw [e2_1_eq, e2_2_eq, e2_3_eq, e2_6_eq, e4_2_eq] at h
    simp only [map_neg, map_ofNat, map_zero, map_one]
    linear_combination h
  have hev := evA_qform (0 : ℝ) (-960 : ℝ) (1728 : ℝ) (-576 : ℝ) (0 : ℝ) (-1728 : ℝ) (3456 : ℝ) (-1728 : ℝ)
    (-4032 : ℝ) (1728 : ℝ) (31104 : ℝ) (10368 : ℝ) (-67392 : ℝ) (25920 : ℝ) (960 : ℝ)
    absS_S1 absS_M2 absS_M3 absS_M6 absS_N2 hy
  rw [hS, evA_zero, evA_S1, evA_M2, evA_M3, evA_M6, evA_N2] at hev
  rw [E2im_eq_qa hy, E2im_eq_qa h2, E2im_eq_qa h3, E2im_eq_qa h6, E4im_eq_qa h2]
  linear_combination (-1 : ℝ) * hev

/-- The relation `Rf3` of `Level6.lean` at `q = e^{-2πy}`. -/
theorem axis_Rf3 {y : ℝ} (hy : 0 < y) :
    (-1) * (E2im y * E2im (2 * y)) + 2 * (E2im y * E2im (3 * y))
      + (-1) * (E2im y * E2im (6 * y)) + (E2im (2 * y) * E2im (2 * y))
      + (E2im (2 * y) * E2im (3 * y)) + (-2) * (E2im (2 * y) * E2im (6 * y))
      + (-9) * (E2im (3 * y) * E2im (3 * y)) + 21 * (E2im (3 * y) * E2im (6 * y))
      + (-15) * (E2im (6 * y) * E2im (6 * y)) + 3 * (E4im (3 * y)) = 0 := by
  have h2 : (0 : ℝ) < 2 * y := mul_pos (by norm_num) hy
  have h3 : (0 : ℝ) < 3 * y := mul_pos (by norm_num) hy
  have h6 : (0 : ℝ) < 6 * y := mul_pos (by norm_num) hy
  have hS : (PowerSeries.C (0 : ℝ) * S1 + PowerSeries.C (0 : ℝ) * sM2
        + PowerSeries.C (-144 : ℝ) * sM3 + PowerSeries.C (288 : ℝ) * sM6
        + PowerSeries.C (0 : ℝ) * (S1 * S1) + PowerSeries.C (-576 : ℝ) * (S1 * sM2)
        + PowerSeries.C (1152 : ℝ) * (S1 * sM3) + PowerSeries.C (-576 : ℝ) * (S1 * sM6)
        + PowerSeries.C (576 : ℝ) * (sM2 * sM2) + PowerSeries.C (576 : ℝ) * (sM2 * sM3)
        + PowerSeries.C (-1152 : ℝ) * (sM2 * sM6)
        + PowerSeries.C (-5184 : ℝ) * (sM3 * sM3)
        + PowerSeries.C (12096 : ℝ) * (sM3 * sM6)
        + PowerSeries.C (-8640 : ℝ) * (sM6 * sM6) + PowerSeries.C (720 : ℝ) * sN3
        : PowerSeries ℝ) = 0 := by
    have h := Rf3_eq_zero ram6
    unfold Rf3 at h
    rw [e2_1_eq, e2_2_eq, e2_3_eq, e2_6_eq, e4_3_eq] at h
    simp only [map_neg, map_ofNat, map_zero, map_one]
    linear_combination h
  have hev := evA_qform (0 : ℝ) (0 : ℝ) (-144 : ℝ) (288 : ℝ) (0 : ℝ) (-576 : ℝ) (1152 : ℝ) (-576 : ℝ)
    (576 : ℝ) (576 : ℝ) (-1152 : ℝ) (-5184 : ℝ) (12096 : ℝ) (-8640 : ℝ) (720 : ℝ)
    absS_S1 absS_M2 absS_M3 absS_M6 absS_N3 hy
  rw [hS, evA_zero, evA_S1, evA_M2, evA_M3, evA_M6, evA_N3] at hev
  rw [E2im_eq_qa hy, E2im_eq_qa h2, E2im_eq_qa h3, E2im_eq_qa h6, E4im_eq_qa h3]
  linear_combination (-1 : ℝ) * hev

/-- The relation `Rf4` of `Level6.lean` at `q = e^{-2πy}`. -/
theorem axis_Rf4 {y : ℝ} (hy : 0 < y) :
    (E2im y * E2im (2 * y)) + (-2) * (E2im y * E2im (3 * y)) + (E2im y * E2im (6 * y))
      + (-1) * (E2im (2 * y) * E2im (2 * y)) + (-1) * (E2im (2 * y) * E2im (3 * y))
      + 2 * (E2im (2 * y) * E2im (6 * y)) + (-6) * (E2im (3 * y) * E2im (3 * y))
      + 39 * (E2im (3 * y) * E2im (6 * y)) + (-45) * (E2im (6 * y) * E2im (6 * y))
      + 12 * (E4im (6 * y)) = 0 := by
  have h2 : (0 : ℝ) < 2 * y := mul_pos (by norm_num) hy
  have h3 : (0 : ℝ) < 3 * y := mul_pos (by norm_num) hy
  have h6 : (0 : ℝ) < 6 * y := mul_pos (by norm_num) hy
  have hS : (PowerSeries.C (0 : ℝ) * S1 + PowerSeries.C (0 : ℝ) * sM2
        + PowerSeries.C (-576 : ℝ) * sM3 + PowerSeries.C (1152 : ℝ) * sM6
        + PowerSeries.C (0 : ℝ) * (S1 * S1) + PowerSeries.C (576 : ℝ) * (S1 * sM2)
        + PowerSeries.C (-1152 : ℝ) * (S1 * sM3) + PowerSeries.C (576 : ℝ) * (S1 * sM6)
        + PowerSeries.C (-576 : ℝ) * (sM2 * sM2) + PowerSeries.C (-576 : ℝ) * (sM2 * sM3)
        + PowerSeries.C (1152 : ℝ) * (sM2 * sM6) + PowerSeries.C (-3456 : ℝ) * (sM3 * sM3)
        + PowerSeries.C (22464 : ℝ) * (sM3 * sM6)
        + PowerSeries.C (-25920 : ℝ) * (sM6 * sM6) + PowerSeries.C (2880 : ℝ) * sN6
        : PowerSeries ℝ) = 0 := by
    have h := Rf4_eq_zero ram6
    unfold Rf4 at h
    rw [e2_1_eq, e2_2_eq, e2_3_eq, e2_6_eq, e4_6_eq] at h
    simp only [map_neg, map_ofNat, map_zero, map_one]
    linear_combination h
  have hev := evA_qform (0 : ℝ) (0 : ℝ) (-576 : ℝ) (1152 : ℝ) (0 : ℝ) (576 : ℝ) (-1152 : ℝ) (576 : ℝ)
    (-576 : ℝ) (-576 : ℝ) (1152 : ℝ) (-3456 : ℝ) (22464 : ℝ) (-25920 : ℝ) (2880 : ℝ)
    absS_S1 absS_M2 absS_M3 absS_M6 absS_N6 hy
  rw [hS, evA_zero, evA_S1, evA_M2, evA_M3, evA_M6, evA_N6] at hev
  rw [E2im_eq_qa hy, E2im_eq_qa h2, E2im_eq_qa h3, E2im_eq_qa h6, E4im_eq_qa h6]
  linear_combination (-1 : ℝ) * hev

/-- The relation `Rf9` of `Level6.lean` at `q = e^{-2πy}`. -/
theorem axis_Rf9 {y : ℝ} (hy : 0 < y) :
    (E2im y * E2im y) + (-8) * (E2im y * E2im (2 * y)) + 6 * (E2im y * E2im (3 * y))
      + 4 * (E2im (2 * y) * E2im (2 * y)) + 24 * (E2im (2 * y) * E2im (6 * y))
      + 9 * (E2im (3 * y) * E2im (3 * y)) + (-72) * (E2im (3 * y) * E2im (6 * y))
      + 36 * (E2im (6 * y) * E2im (6 * y)) = 0 := by
  have h2 : (0 : ℝ) < 2 * y := mul_pos (by norm_num) hy
  have h3 : (0 : ℝ) < 3 * y := mul_pos (by norm_num) hy
  have h6 : (0 : ℝ) < 6 * y := mul_pos (by norm_num) hy
  have hS : (PowerSeries.C (0 : ℝ) * S1 + PowerSeries.C (-576 : ℝ) * sM2
        + PowerSeries.C (1152 : ℝ) * sM3 + PowerSeries.C (-576 : ℝ) * sM6
        + PowerSeries.C (576 : ℝ) * (S1 * S1) + PowerSeries.C (-4608 : ℝ) * (S1 * sM2)
        + PowerSeries.C (3456 : ℝ) * (S1 * sM3) + PowerSeries.C (0 : ℝ) * (S1 * sM6)
        + PowerSeries.C (2304 : ℝ) * (sM2 * sM2) + PowerSeries.C (0 : ℝ) * (sM2 * sM3)
        + PowerSeries.C (13824 : ℝ) * (sM2 * sM6) + PowerSeries.C (5184 : ℝ) * (sM3 * sM3)
        + PowerSeries.C (-41472 : ℝ) * (sM3 * sM6)
        + PowerSeries.C (20736 : ℝ) * (sM6 * sM6) + PowerSeries.C (0 : ℝ) * S3
        : PowerSeries ℝ) = 0 := by
    have h := Rf9_eq_zero ram6
    unfold Rf9 at h
    rw [e2_1_eq, e2_2_eq, e2_3_eq, e2_6_eq] at h
    simp only [map_neg, map_ofNat, map_zero, map_one]
    linear_combination h
  have hev := evA_qform (0 : ℝ) (-576 : ℝ) (1152 : ℝ) (-576 : ℝ) (576 : ℝ) (-4608 : ℝ) (3456 : ℝ) (0 : ℝ)
    (2304 : ℝ) (0 : ℝ) (13824 : ℝ) (5184 : ℝ) (-41472 : ℝ) (20736 : ℝ) (0 : ℝ)
    absS_S1 absS_M2 absS_M3 absS_M6 absS_S3 hy
  rw [hS, evA_zero, evA_S1, evA_M2, evA_M3, evA_M6, evA_S3] at hev
  rw [E2im_eq_qa hy, E2im_eq_qa h2, E2im_eq_qa h3, E2im_eq_qa h6]
  linear_combination (-1 : ℝ) * hev

end Tower.RV6
