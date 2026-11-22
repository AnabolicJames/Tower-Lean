import Mathlib

/-!
# Termwise Mellin transform of a `q`-series on the imaginary axis

`integral_qseries`: if `∑ |c(n)| / (n+1)^{k+1}` converges, then

`∫₀^∞ (∑ c(n) e^{-2π(n+1)y}) y^k dy = k!/(2π)^{k+1} · ∑ c(n)/(n+1)^{k+1}`.

This is the bridge between a function on the imaginary axis given by a `q`-series and the value
of its Dirichlet series at an integer point of absolute convergence.
-/

namespace Tower.RV6

open Real MeasureTheory Set

/-- `∫₀^∞ e^{-ry} y^k dy = k!/r^{k+1}`. -/
theorem integral_exp_mul_pow {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-(r * y)) * y ^ k = (k.factorial : ℝ) / r ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial] at h
  have e1 : ∀ t : ℝ, t ^ ((k : ℝ) + 1 - 1) * Real.exp (-(r * t))
      = Real.exp (-(r * t)) * t ^ k := by
    intro t
    rw [add_sub_cancel_right, Real.rpow_natCast, mul_comm]
  simp only [e1] at h
  rw [h, ← Nat.cast_add_one, Real.rpow_natCast, one_div_pow]
  ring

/-- Termwise integration of a `q`-series against `y^k`. -/
theorem integral_qseries (c : ℕ → ℝ) (k : ℕ)
    (hs : Summable fun n : ℕ => |c n| / ((n + 1 : ℕ) : ℝ) ^ (k + 1)) :
    ∫ y in Ioi (0 : ℝ), (∑' n : ℕ, c n * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y))) * y ^ k
      = (k.factorial : ℝ) / (2 * π) ^ (k + 1) * ∑' n : ℕ, c n / ((n + 1 : ℕ) : ℝ) ^ (k + 1) := by
  have hr : ∀ n : ℕ, 0 < 2 * π * ((n + 1 : ℕ) : ℝ) := fun n => by positivity
  have hbase : ∀ n : ℕ,
      ∫ y in Ioi (0 : ℝ), Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * y ^ k
        = (k.factorial : ℝ) / (2 * π * ((n + 1 : ℕ) : ℝ)) ^ (k + 1) :=
    fun n => integral_exp_mul_pow (hr n) k
  have hint0 : ∀ n : ℕ, Integrable
      (fun y : ℝ => Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * y ^ k)
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    refine Integrable.of_integral_ne_zero ?_
    rw [hbase n]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) (pow_ne_zero _ (hr n).ne')
  have hint : ∀ n : ℕ, Integrable
      (fun y : ℝ => c n * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * y ^ k))
      (volume.restrict (Ioi (0 : ℝ))) :=
    fun n => Integrable.const_mul (hint0 n) (c n)
  have hnorm : ∀ n : ℕ,
      ∫ y in Ioi (0 : ℝ), ‖c n * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * y ^ k)‖
        = |c n| * ((k.factorial : ℝ) / (2 * π * ((n + 1 : ℕ) : ℝ)) ^ (k + 1)) := by
    intro n
    rw [← hbase n, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := le_of_lt hy
    show ‖c n * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * y ^ k)‖
      = |c n| * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * y ^ k)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hy0 k))]
  have halg : ∀ (a : ℝ) (n : ℕ),
      a * ((k.factorial : ℝ) / (2 * π * ((n + 1 : ℕ) : ℝ)) ^ (k + 1))
        = (k.factorial : ℝ) / (2 * π) ^ (k + 1) * (a / ((n + 1 : ℕ) : ℝ) ^ (k + 1)) := by
    intro a n
    rw [mul_pow, div_mul_div_comm, ← mul_div_assoc, mul_comm a]
  have hsum : Summable fun n : ℕ =>
      ∫ y in Ioi (0 : ℝ), ‖c n * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * y ^ k)‖ := by
    refine (hs.mul_left ((k.factorial : ℝ) / (2 * π) ^ (k + 1))).congr ?_
    intro n
    rw [hnorm n, halg]
  have key := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ n : ℕ,
      ∫ y in Ioi (0 : ℝ), c n * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * y ^ k)
        = (k.factorial : ℝ) / (2 * π) ^ (k + 1) * (c n / ((n + 1 : ℕ) : ℝ) ^ (k + 1)) := by
    intro n
    rw [integral_const_mul, hbase n, halg]
  have hfun : ∀ y : ℝ,
      (∑' n : ℕ, c n * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y))) * y ^ k
        = ∑' n : ℕ, c n * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * y ^ k) := by
    intro y
    rw [← tsum_mul_right]
    exact tsum_congr (fun n => mul_assoc _ _ _)
  simp only [hfun]
  rw [← key.tsum_eq, ← tsum_mul_left]
  exact tsum_congr hval

end Tower.RV6
