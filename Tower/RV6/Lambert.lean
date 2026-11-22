import Mathlib
import Tower.RV6.Defs

/-!
# The Lambert series of `Tower/RV6/Defs.lean` converge

For `y > 0` the series defining `Ecal y = ∑ σ₁(n) e^{-2πny}` and
`DEcal y = ∑ n σ₁(n) e^{-2πny}` are summable, so these definitions are honest sums and not
the default value `0` of a divergent `tsum`.
-/

namespace Tower.RV6

open Real

theorem sigma1_le_sq (n : ℕ) : sigma1 n ≤ n ^ 2 := by
  unfold sigma1
  calc ∑ d ∈ n.divisors, d ≤ ∑ _d ∈ n.divisors, n :=
        Finset.sum_le_sum (fun d hd => Nat.divisor_le hd)
    _ = n.divisors.card * n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n := Nat.mul_le_mul_right n (Nat.card_divisors_le_self n)
    _ = n ^ 2 := (sq n).symm

private theorem exp_neg_lt_one {y : ℝ} (hy : 0 < y) : Real.exp (-2 * π * y) < 1 := by
  rw [Real.exp_lt_one_iff]
  have h : 0 < 2 * π * y := by positivity
  linarith

private theorem exp_nat {y : ℝ} (n : ℕ) :
    Real.exp (-2 * π * n * y) = Real.exp (-2 * π * y) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem summable_Ecal_terms {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => (sigma1 n : ℝ) * Real.exp (-2 * π * n * y)) := by
  have hr0 : 0 ≤ Real.exp (-2 * π * y) := (Real.exp_pos _).le
  have hmaj := summable_pow_mul_geometric_of_norm_lt_one 2 (r := Real.exp (-2 * π * y))
    (by rw [Real.norm_of_nonneg hr0]; exact exp_neg_lt_one hy)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  · show (sigma1 n : ℝ) * Real.exp (-2 * π * n * y) ≤ (n : ℝ) ^ 2 * Real.exp (-2 * π * y) ^ n
    rw [exp_nat]
    have h1 : (sigma1 n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast sigma1_le_sq n
    exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hr0 n)

theorem summable_DEcal_terms {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => (n : ℝ) * (sigma1 n : ℝ) * Real.exp (-2 * π * n * y)) := by
  have hr0 : 0 ≤ Real.exp (-2 * π * y) := (Real.exp_pos _).le
  have hmaj := summable_pow_mul_geometric_of_norm_lt_one 3 (r := Real.exp (-2 * π * y))
    (by rw [Real.norm_of_nonneg hr0]; exact exp_neg_lt_one hy)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le
  · show (n : ℝ) * (sigma1 n : ℝ) * Real.exp (-2 * π * n * y)
      ≤ (n : ℝ) ^ 3 * Real.exp (-2 * π * y) ^ n
    rw [exp_nat]
    have h1 : (sigma1 n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast sigma1_le_sq n
    have h2 : (n : ℝ) * (sigma1 n : ℝ) ≤ (n : ℝ) ^ 3 := by
      calc (n : ℝ) * (sigma1 n : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
        _ = (n : ℝ) ^ 3 := by ring
    exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hr0 n)

end Tower.RV6
