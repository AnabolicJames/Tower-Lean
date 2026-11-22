import Mathlib
import Tower.RV6.MellinSeries

/-!
# The kernel integral of the interchange

`PhiN M N j = ∫₀^∞ e^{-πM/(3y) - 2πNy} y^{-j} dy` for `M, N > 0` and a natural number `j`.

* `exp_neg_inv_bound`: `c^k e^{-c/y} ≤ k! y^k`.
* `kernel_le`: the integrand is at most `((j+p)!/(πM/3)^{j+p}) e^{-2πNy} y^p`.
* `integrable_kernel`, `PhiN_le`, `PhiN_nonneg`, `PhiN_pos`.
* `PhiN_scale`: `M^i PhiN M N (i+1) = PhiN 1 (M N) (i+1)`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `c^k e^{-c/y} ≤ k! y^k` for `c, y > 0`. -/
theorem exp_neg_inv_bound {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (k : ℕ) :
    c ^ k * Real.exp (-c / y) ≤ (k.factorial : ℝ) * y ^ k := by
  have hx : 0 ≤ c / y := (div_pos hc hy).le
  have h1 := Real.pow_div_factorial_le_exp hx k
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : (c / y) ^ k ≤ Real.exp (c / y) * (k.factorial : ℝ) := (div_le_iff₀ hk).mp h1
  rw [div_pow] at h2
  have h3 : c ^ k ≤ Real.exp (c / y) * (k.factorial : ℝ) * y ^ k :=
    (div_le_iff₀ (pow_pos hy k)).mp h2
  have h4 : Real.exp (-c / y) * Real.exp (c / y) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  calc c ^ k * Real.exp (-c / y)
      ≤ Real.exp (c / y) * (k.factorial : ℝ) * y ^ k * Real.exp (-c / y) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (k.factorial : ℝ) * y ^ k := by linear_combination ((k.factorial : ℝ) * y ^ k) * h4

/-- Pointwise bound for the integrand of `PhiN`. -/
theorem kernel_le {M N : ℝ} (hM : 0 < M) (j p : ℕ) {y : ℝ} (hy : 0 < y) :
    Real.exp (-(π * M) / (3 * y) - 2 * π * N * y) / y ^ j
      ≤ ((j + p).factorial : ℝ) / (π * M / 3) ^ (j + p)
        * (Real.exp (-(2 * π * N * y)) * y ^ p) := by
  have hc : 0 < π * M / 3 := by positivity
  have hb := exp_neg_inv_bound hc hy (j + p)
  have hE : Real.exp (-(π * M) / (3 * y) - 2 * π * N * y)
      = Real.exp (-(π * M / 3) / y) * Real.exp (-(2 * π * N * y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcp : 0 < (π * M / 3) ^ (j + p) := pow_pos hc _
  have h' : Real.exp (-(π * M / 3) / y)
      ≤ ((j + p).factorial : ℝ) * y ^ (j + p) / (π * M / 3) ^ (j + p) :=
    (le_div_iff₀ hcp).mpr (le_of_eq_of_le (mul_comm _ _) hb)
  rw [hE, div_le_iff₀ (pow_pos hy j)]
  calc Real.exp (-(π * M / 3) / y) * Real.exp (-(2 * π * N * y))
      ≤ ((j + p).factorial : ℝ) * y ^ (j + p) / (π * M / 3) ^ (j + p)
          * Real.exp (-(2 * π * N * y)) :=
        mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
    _ = ((j + p).factorial : ℝ) / (π * M / 3) ^ (j + p)
          * (Real.exp (-(2 * π * N * y)) * y ^ p) * y ^ j := by ring

theorem integrable_exp_mul_pow {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Integrable (fun y : ℝ => Real.exp (-(r * y)) * y ^ k)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_mul_pow hr k]
  exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) (pow_ne_zero _ hr.ne')

theorem measurable_kernel (M N : ℝ) (j : ℕ) :
    Measurable fun y : ℝ => Real.exp (-(π * M) / (3 * y) - 2 * π * N * y) / y ^ j := by
  first
    | fun_prop
    | measurability

/-- The integrand of `PhiN` is integrable on `(0, ∞)`. -/
theorem integrable_kernel {M N : ℝ} (hM : 0 < M) (hN : 0 < N) (j : ℕ) :
    Integrable (fun y : ℝ => Real.exp (-(π * M) / (3 * y) - 2 * π * N * y) / y ^ j)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hr : (0 : ℝ) < 2 * π * N := by positivity
  have hg : Integrable (fun y : ℝ => ((j + 0).factorial : ℝ) / (π * M / 3) ^ (j + 0)
      * (Real.exp (-(2 * π * N * y)) * y ^ 0)) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrable_exp_mul_pow hr 0).const_mul _
  refine hg.mono' (measurable_kernel M N j).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono (fun y hy => ?_)
  have hy' : (0 : ℝ) < y := hy
  show ‖Real.exp (-(π * M) / (3 * y) - 2 * π * N * y) / y ^ j‖
    ≤ ((j + 0).factorial : ℝ) / (π * M / 3) ^ (j + 0) * (Real.exp (-(2 * π * N * y)) * y ^ 0)
  rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (pow_nonneg hy'.le j))]
  exact kernel_le hM j 0 hy'

/-- `PhiN M N j = ∫₀^∞ e^{-πM/(3y) - 2πNy} y^{-j} dy`. -/
noncomputable def PhiN (M N : ℝ) (j : ℕ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), Real.exp (-(π * M) / (3 * y) - 2 * π * N * y) / y ^ j

theorem PhiN_nonneg (M N : ℝ) (j : ℕ) : 0 ≤ PhiN M N j := by
  unfold PhiN
  refine setIntegral_nonneg measurableSet_Ioi (fun y hy => ?_)
  have hy' : (0 : ℝ) < y := hy
  exact div_nonneg (Real.exp_pos _).le (pow_nonneg hy'.le j)

theorem PhiN_le {M N : ℝ} (hM : 0 < M) (hN : 0 < N) (j p : ℕ) :
    PhiN M N j ≤ ((j + p).factorial : ℝ) / (π * M / 3) ^ (j + p)
      * ((p.factorial : ℝ) / (2 * π * N) ^ (p + 1)) := by
  unfold PhiN
  have hr : (0 : ℝ) < 2 * π * N := by positivity
  have hg : IntegrableOn (fun y : ℝ => ((j + p).factorial : ℝ) / (π * M / 3) ^ (j + p)
      * (Real.exp (-(2 * π * N * y)) * y ^ p)) (Set.Ioi (0 : ℝ)) :=
    (integrable_exp_mul_pow hr p).const_mul _
  have h := setIntegral_mono_on (integrable_kernel hM hN j) hg measurableSet_Ioi
    (fun y hy => kernel_le hM j p hy)
  rw [integral_const_mul, integral_exp_mul_pow hr p] at h
  exact h

theorem PhiN_pos {M N : ℝ} (hM : 0 < M) (hN : 0 < N) (j : ℕ) : 0 < PhiN M N j := by
  unfold PhiN
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun y : ℝ => Real.exp (-(π * M) / (3 * y) - 2 * π * N * y) / y ^ j := by
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun y hy => ?_)
    have hy' : (0 : ℝ) < y := hy
    exact div_nonneg (Real.exp_pos _).le (pow_nonneg hy'.le j)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn (integrable_kernel hM hN j)]
  have hsub : Set.Ioi (0 : ℝ)
      ⊆ Function.support (fun y : ℝ => Real.exp (-(π * M) / (3 * y) - 2 * π * N * y) / y ^ j) := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    rw [Function.mem_support]
    exact (div_pos (Real.exp_pos _) (pow_pos hy' j)).ne'
  rw [Set.inter_eq_right.mpr hsub, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- `M^i PhiN M N (i+1) = PhiN 1 (M N) (i+1)`: the substitution `y = M v`. -/
theorem PhiN_scale {M : ℝ} (hM : 0 < M) (N : ℝ) (i : ℕ) :
    M ^ i * PhiN M N (i + 1) = PhiN 1 (M * N) (i + 1) := by
  unfold PhiN
  have key : M * ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-(π * M) / (3 * (M * x)) - 2 * π * N * (M * x)) / (M * x) ^ (i + 1)
      = ∫ y in Set.Ioi (0 : ℝ), Real.exp (-(π * M) / (3 * y) - 2 * π * N * y) / y ^ (i + 1) := by
    have h := integral_comp_mul_left_Ioi'
      (fun y : ℝ => Real.exp (-(π * M) / (3 * y) - 2 * π * N * y) / y ^ (i + 1)) (0 : ℝ) hM
    rw [mul_zero, smul_eq_mul] at h
    exact h
  have hcongr : ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-(π * M) / (3 * (M * x)) - 2 * π * N * (M * x)) / (M * x) ^ (i + 1)
      = ∫ x in Set.Ioi (0 : ℝ), (M ^ (i + 1))⁻¹
          * (Real.exp (-(π * 1) / (3 * x) - 2 * π * (M * N) * x) / x ^ (i + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have e1 : -(π * M) / (3 * (M * x)) = -(π * 1) / (3 * x) := by
      have e : -(π * M) / (3 * (M * x)) = M * (-(π * 1)) / (M * (3 * x)) := by ring
      rw [e, mul_div_mul_left _ _ hM.ne']
    have e2 : 2 * π * N * (M * x) = 2 * π * (M * N) * x := by ring
    show Real.exp (-(π * M) / (3 * (M * x)) - 2 * π * N * (M * x)) / (M * x) ^ (i + 1)
      = (M ^ (i + 1))⁻¹ * (Real.exp (-(π * 1) / (3 * x) - 2 * π * (M * N) * x) / x ^ (i + 1))
    rw [e1, e2, mul_pow]
    ring
  have hM0 : M ^ (i + 1) ≠ 0 := pow_ne_zero _ hM.ne'
  have hcoef : M ^ i * (M * (M ^ (i + 1))⁻¹) = 1 := by
    rw [← mul_assoc, ← pow_succ, mul_inv_cancel₀ hM0]
  have gen : ∀ I : ℝ, M ^ i * (M * ((M ^ (i + 1))⁻¹ * I)) = I := by
    intro I
    linear_combination I * hcoef
  rw [← key, hcongr, integral_const_mul]
  exact gen _

end Tower.RV6
