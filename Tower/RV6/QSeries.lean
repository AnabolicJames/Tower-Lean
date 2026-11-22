import Mathlib
import Tower.RV6.EisAxis

/-!
# `q`-series on the imaginary axis

`qa C y = ∑_{n ≥ 0} C(n) e^{-2πny}`.  The coefficient functions used in the project (`sig`,
`sigDiv`, …) are functions of the actual exponent `n` and vanish at `0`.

* `summable_qa`, `summable_qa_abs`: absolute convergence for `y > 0` when `|C n| ≤ B n^K`.
* `qa_dilate`: the series of a sequence supported on the multiples of `m` is the series of the
  divided sequence at `m y`.
* `qa_comb4`: a combination of a series and its dilates by `2, 3, 6` is one series.
* `qa_mul`: the product of two series is the series of the Cauchy product.
* `integral_qa`: termwise Mellin transform (from `integral_qseries`).
* `E4im_eq_qa`, `E2im_eq_qa`: the Eisenstein series of `EisAxis.lean` in this notation.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `qa C y = ∑_{n ≥ 0} C(n) e^{-2πny}`. -/
noncomputable def qa (C : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, C n * Real.exp (-(2 * π * (n : ℝ) * y))

theorem exp_nat_axis (y : ℝ) (n : ℕ) :
    Real.exp (-(2 * π * (n : ℝ) * y)) = Real.exp (-(2 * π * y)) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem exp_axis_lt_one {y : ℝ} (hy : 0 < y) : Real.exp (-(2 * π * y)) < 1 := by
  rw [Real.exp_lt_one_iff]
  have h : 0 < 2 * π * y := by positivity
  linarith

/-! ## Convergence -/

theorem summable_qa_abs {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K)
    {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => |C n| * Real.exp (-(2 * π * (n : ℝ) * y)) := by
  have hr0 : 0 ≤ Real.exp (-(2 * π * y)) := (Real.exp_pos _).le
  have hmaj : Summable fun n : ℕ => B * ((n : ℝ) ^ K * Real.exp (-(2 * π * y)) ^ n) :=
    (summable_pow_mul_geometric_of_norm_lt_one K (r := Real.exp (-(2 * π * y)))
      (by rw [Real.norm_of_nonneg hr0]; exact exp_axis_lt_one hy)).mul_left B
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  · show |C n| * Real.exp (-(2 * π * (n : ℝ) * y))
      ≤ B * ((n : ℝ) ^ K * Real.exp (-(2 * π * y)) ^ n)
    rw [exp_nat_axis y n, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hr0 n)

theorem summable_qa {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K)
    {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y)) := by
  refine Summable.of_norm_bounded (summable_qa_abs hC hy) (fun n => ?_)
  show ‖C n * Real.exp (-(2 * π * (n : ℝ) * y))‖ ≤ |C n| * Real.exp (-(2 * π * (n : ℝ) * y))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- If `C 0 = 0` the series starts at `n = 1`; this is the form of `MellinSeries.lean`. -/
theorem qa_eq_shift {C : ℕ → ℝ} (h0 : C 0 = 0) {y : ℝ}
    (hs : Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y))) :
    qa C y = ∑' n : ℕ, C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) := by
  unfold qa
  rw [hs.tsum_eq_zero_add, h0, zero_mul, zero_add]

/-! ## Dilation -/

/-- The series of a sequence supported on the multiples of `m` is a series at `m y`. -/
theorem qa_dilate (A : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (y : ℝ) :
    qa (fun n => if m ∣ n then A (n / m) else 0) y = qa A ((m : ℝ) * y) := by
  unfold qa
  have hg : Function.Injective (fun j : ℕ => m * j) :=
    fun i j hij => Nat.eq_of_mul_eq_mul_left hm hij
  have hsupp : Function.support (fun n : ℕ => (if m ∣ n then A (n / m) else 0)
      * Real.exp (-(2 * π * (n : ℝ) * y))) ⊆ Set.range (fun j : ℕ => m * j) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases hd : m ∣ n
    · obtain ⟨t, ht⟩ := hd
      exact ⟨t, ht.symm⟩
    · exact absurd (by rw [if_neg hd, zero_mul]) hn
  rw [← hg.tsum_eq hsupp]
  refine tsum_congr (fun j => ?_)
  show (if m ∣ m * j then A (m * j / m) else 0) * Real.exp (-(2 * π * ((m * j : ℕ) : ℝ) * y))
    = A j * Real.exp (-(2 * π * (j : ℝ) * ((m : ℝ) * y)))
  rw [if_pos (dvd_mul_right m j), Nat.mul_div_cancel_left j hm]
  congr 2
  push_cast
  ring

theorem dil_abs_le {A : ℕ → ℝ} {B : ℝ} {K : ℕ} (hB : 0 ≤ B) (hA : ∀ n, |A n| ≤ B * (n : ℝ) ^ K)
    (m n : ℕ) : |if m ∣ n then A (n / m) else 0| ≤ B * (n : ℝ) ^ K := by
  split_ifs with h
  · have h1 : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.div_le_self n m
    calc |A (n / m)| ≤ B * ((n / m : ℕ) : ℝ) ^ K := hA (n / m)
      _ ≤ B * (n : ℝ) ^ K :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 K) hB
  · rw [abs_zero]
    exact mul_nonneg hB (pow_nonneg (Nat.cast_nonneg n) K)

/-- A combination of a series and its dilates by `2`, `3`, `6` as one series. -/
theorem qa_comb4 {A : ℕ → ℝ} {B : ℝ} {K : ℕ} (hB : 0 ≤ B) (hA : ∀ n, |A n| ≤ B * (n : ℝ) ^ K)
    (a b c d : ℝ) {y : ℝ} (hy : 0 < y) :
    qa (fun n => a * A n + b * (if 2 ∣ n then A (n / 2) else 0)
        + c * (if 3 ∣ n then A (n / 3) else 0) + d * (if 6 ∣ n then A (n / 6) else 0)) y
      = a * qa A y + b * qa A (2 * y) + c * qa A (3 * y) + d * qa A (6 * y) := by
  have h1 := (summable_qa hA hy).hasSum
  have h2 := (summable_qa (dil_abs_le hB hA 2) hy).hasSum
  have h3 := (summable_qa (dil_abs_le hB hA 3) hy).hasSum
  have h6 := (summable_qa (dil_abs_le hB hA 6) hy).hasSum
  have e2 : qa (fun n => if 2 ∣ n then A (n / 2) else 0) y = qa A (2 * y) := by
    have e := qa_dilate A 2 (by norm_num) y
    rwa [Nat.cast_ofNat] at e
  have e3 : qa (fun n => if 3 ∣ n then A (n / 3) else 0) y = qa A (3 * y) := by
    have e := qa_dilate A 3 (by norm_num) y
    rwa [Nat.cast_ofNat] at e
  have e6 : qa (fun n => if 6 ∣ n then A (n / 6) else 0) y = qa A (6 * y) := by
    have e := qa_dilate A 6 (by norm_num) y
    rwa [Nat.cast_ofNat] at e
  have H := (((h1.mul_left a).add (h2.mul_left b)).add (h3.mul_left c)).add (h6.mul_left d)
  rw [← e2, ← e3, ← e6]
  unfold qa
  calc ∑' n : ℕ, (a * A n + b * (if 2 ∣ n then A (n / 2) else 0)
          + c * (if 3 ∣ n then A (n / 3) else 0) + d * (if 6 ∣ n then A (n / 6) else 0))
          * Real.exp (-(2 * π * (n : ℝ) * y))
      = ∑' n : ℕ, (a * (A n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + b * ((if 2 ∣ n then A (n / 2) else 0) * Real.exp (-(2 * π * (n : ℝ) * y)))
          + c * ((if 3 ∣ n then A (n / 3) else 0) * Real.exp (-(2 * π * (n : ℝ) * y)))
          + d * ((if 6 ∣ n then A (n / 6) else 0) * Real.exp (-(2 * π * (n : ℝ) * y)))) :=
        tsum_congr (fun n => by ring)
    _ = _ := H.tsum_eq

/-! ## Products -/

/-- The product of two absolutely convergent series is the series of the Cauchy product. -/
theorem qa_mul {C D : ℕ → ℝ} {y : ℝ}
    (hC : Summable fun n : ℕ => |C n| * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hD : Summable fun n : ℕ => |D n| * Real.exp (-(2 * π * (n : ℝ) * y))) :
    qa C y * qa D y
      = qa (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, C p.1 * D p.2) y := by
  unfold qa
  have hC' : Summable fun n : ℕ => ‖C n * Real.exp (-(2 * π * (n : ℝ) * y))‖ := by
    refine hC.congr (fun n => ?_)
    show |C n| * Real.exp (-(2 * π * (n : ℝ) * y)) = ‖C n * Real.exp (-(2 * π * (n : ℝ) * y))‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hD' : Summable fun n : ℕ => ‖D n * Real.exp (-(2 * π * (n : ℝ) * y))‖ := by
    refine hD.congr (fun n => ?_)
    show |D n| * Real.exp (-(2 * π * (n : ℝ) * y)) = ‖D n * Real.exp (-(2 * π * (n : ℝ) * y))‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hC' hD']
  refine tsum_congr (fun n => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have he : Real.exp (-(2 * π * (p.1 : ℝ) * y)) * Real.exp (-(2 * π * (p.2 : ℝ) * y))
      = Real.exp (-(2 * π * (n : ℝ) * y)) := by
    rw [← Real.exp_add, ← hp']
    congr 1
    push_cast
    ring
  rw [← he]
  ring

/-! ## Mellin transform -/

/-- Termwise Mellin transform of a series without constant term. -/
theorem integral_qa (C : ℕ → ℝ) (h0 : C 0 = 0) (k : ℕ)
    (hs : Summable fun n : ℕ => |C (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (k + 1))
    (hy : ∀ y : ℝ, 0 < y → Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y))) :
    ∫ y in Set.Ioi (0 : ℝ), qa C y * y ^ k
      = (k.factorial : ℝ) / (2 * π) ^ (k + 1)
        * ∑' n : ℕ, C (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (k + 1) := by
  rw [← integral_qseries (fun n => C (n + 1)) k hs]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy' => ?_)
  show qa C y * y ^ k
    = (∑' n : ℕ, C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y))) * y ^ k
  rw [qa_eq_shift h0 (hy y hy')]

/-! ## The divisor sums and the Eisenstein series -/

theorem sig_zero (k : ℕ) : sig k 0 = 0 := by simp [sig]

/-- `σ_k(n) ≤ n^{k+1}`. -/
theorem sig_le_pow (k n : ℕ) : sig k n ≤ (n : ℝ) ^ (k + 1) := by
  unfold sig
  calc ∑ d ∈ n.divisors, (d : ℝ) ^ k ≤ ∑ _d ∈ n.divisors, (n : ℝ) ^ k :=
        Finset.sum_le_sum (fun d hd =>
          pow_le_pow_left₀ (Nat.cast_nonneg d) (by exact_mod_cast Nat.divisor_le hd) k)
    _ = (n.divisors.card : ℝ) * (n : ℝ) ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (n : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n)
          (pow_nonneg (Nat.cast_nonneg n) k)
    _ = (n : ℝ) ^ (k + 1) := by ring

theorem sig_abs_le (k : ℕ) (n : ℕ) : |sig k n| ≤ 1 * (n : ℝ) ^ (k + 1) := by
  rw [abs_of_nonneg (sig_nonneg k n), one_mul]
  exact sig_le_pow k n

theorem E4im_eq_qa {y : ℝ} (hy : 0 < y) : E4im y = 1 + 240 * qa (sig 3) y := by
  rw [qa_eq_shift (sig_zero 3) (summable_qa (sig_abs_le 3) hy)]
  rfl

theorem E2im_eq_qa {y : ℝ} (hy : 0 < y) : E2im y = 1 - 24 * qa (sig 1) y := by
  rw [qa_eq_shift (sig_zero 1) (summable_qa (sig_abs_le 1) hy)]
  rfl

end Tower.RV6
