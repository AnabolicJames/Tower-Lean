import Mathlib
import Tower.RV6.BMReduce

/-!
# Bounds for the limit `LimBM`

Explicit bounds, with explicit constants, on the functions of the modular side of Rung B:

* the tail bound at any base point (`qa_abs_le_tail_at`); monotonicity of `q`-series with
  nonnegative coefficients; `|Wq y| ≤ 4 qb y` for `Wq y = qb y - qb 2y + qb 3y - qb 6y`;
* `log_xm_fricke : log xm(y) = π/(6y) - 3 Wq(1/(6y))`;
* at the cusp `y ≥ 1`: `1/xm(y) ≤ e^{πy + 12 qb 1}`, `|g₄(y)| ≤ 640 S₃ e^{-2π(y-1)}`,
  `|𝒜₁(y)| ≤ 80 T(1)`;
* near `y = 0`: `|xm(y)^{-s} - e^{-πs/(6y)}| / (162 y⁶) ≤ K` for `0 < y ≤ 1`, `0 ≤ s ≤ 1`
  (`pole_part_le`);
* the integrand `FS s y = g₄ 𝒜₁ xm^{-s} - e^{-πs/(6y)}/(162y⁶)` of `JS s - poleS s`, its continuity
  on `(0, ∞)`, its limit `f0 y = g₄ 𝒜₁ - 1/(162y⁶)` as `s → 0+`, and the dominations on `(0, 1]`
  and on `(1, ∞)`;
* `integrableOn_f0`: the integrand of `D₀₁` is integrable (the pieces of `RungC1.lean`).
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## Tail bound at a base point, monotonicity -/

/-- If every `n` has `D n = 0` or `c ≤ n`, then for `y ≥ y₀ > 0`
`|∑ D(n) e^{-2πny}| ≤ e^{-2πc(y-y₀)} ∑ |D(n)| e^{-2πny₀}`. -/
theorem qa_abs_le_tail_at {D : ℕ → ℝ} {B : ℝ} {K : ℕ}
    (hD : ∀ n : ℕ, |D n| ≤ B * (n : ℝ) ^ K) (c : ℝ) (hc : ∀ n : ℕ, D n = 0 ∨ c ≤ (n : ℝ))
    {y0 y : ℝ} (hy0 : 0 < y0) (hy : y0 ≤ y) :
    |qa D y| ≤ Real.exp (-(2 * π * c * (y - y0)))
      * ∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * y0)) := by
  have hyp : (0 : ℝ) < y := lt_of_lt_of_le hy0 hy
  have hs1 : Summable fun n : ℕ => |D n| * Real.exp (-(2 * π * (n : ℝ) * y0)) :=
    summable_qa_abs hD hy0
  have hsy : Summable fun n : ℕ => |D n| * Real.exp (-(2 * π * (n : ℝ) * y)) :=
    summable_qa_abs hD hyp
  have hA : ∀ n : ℕ, |D n * Real.exp (-(2 * π * (n : ℝ) * y))|
      = |D n| * Real.exp (-(2 * π * (n : ℝ) * y)) := by
    intro n
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have habs : Summable fun n : ℕ => |D n * Real.exp (-(2 * π * (n : ℝ) * y))| :=
    hsy.congr (fun n => (hA n).symm)
  have hterm : ∀ n : ℕ, |D n * Real.exp (-(2 * π * (n : ℝ) * y))|
      ≤ Real.exp (-(2 * π * c * (y - y0))) * (|D n| * Real.exp (-(2 * π * (n : ℝ) * y0))) := by
    intro n
    rw [hA n]
    rcases hc n with h0 | hcn
    · have e1 : |D n| = 0 := by rw [h0, abs_zero]
      refine le_of_eq ?_
      rw [e1, zero_mul, zero_mul, mul_zero]
    · have hE : Real.exp (-(2 * π * (n : ℝ) * y))
          ≤ Real.exp (-(2 * π * c * (y - y0))) * Real.exp (-(2 * π * (n : ℝ) * y0)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h2pi : (0 : ℝ) ≤ 2 * π := mul_nonneg (by norm_num) Real.pi_pos.le
        have hprod : 0 ≤ 2 * π * (((n : ℝ) - c) * (y - y0)) :=
          mul_nonneg h2pi (mul_nonneg (sub_nonneg.mpr hcn) (sub_nonneg.mpr hy))
        have key : -(2 * π * c * (y - y0)) + -(2 * π * (n : ℝ) * y0) - -(2 * π * (n : ℝ) * y)
            = 2 * π * (((n : ℝ) - c) * (y - y0)) := by ring
        linarith
      calc |D n| * Real.exp (-(2 * π * (n : ℝ) * y))
          ≤ |D n| * (Real.exp (-(2 * π * c * (y - y0)))
              * Real.exp (-(2 * π * (n : ℝ) * y0))) :=
            mul_le_mul_of_nonneg_left hE (abs_nonneg _)
        _ = Real.exp (-(2 * π * c * (y - y0)))
              * (|D n| * Real.exp (-(2 * π * (n : ℝ) * y0))) := by ring
  calc |qa D y| = |∑' n : ℕ, D n * Real.exp (-(2 * π * (n : ℝ) * y))| := rfl
    _ ≤ ∑' n : ℕ, |D n * Real.exp (-(2 * π * (n : ℝ) * y))| := abs_tsum_le_tsum_abs habs
    _ ≤ ∑' n : ℕ, Real.exp (-(2 * π * c * (y - y0)))
          * (|D n| * Real.exp (-(2 * π * (n : ℝ) * y0))) :=
        Summable.tsum_le_tsum hterm habs (hs1.mul_left _)
    _ = Real.exp (-(2 * π * c * (y - y0)))
          * ∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * y0)) := tsum_mul_left

theorem qa_nonneg_of {C : ℕ → ℝ} (hnn : ∀ n : ℕ, 0 ≤ C n) (y : ℝ) : 0 ≤ qa C y := by
  unfold qa
  exact tsum_nonneg (fun n => mul_nonneg (hnn n) (Real.exp_pos _).le)

theorem qa_anti_of {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n : ℕ, |C n| ≤ B * (n : ℝ) ^ K)
    (hnn : ∀ n : ℕ, 0 ≤ C n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : qa C b ≤ qa C a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  unfold qa
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_qa hC hb) (summable_qa hC ha)
  show C n * Real.exp (-(2 * π * (n : ℝ) * b)) ≤ C n * Real.exp (-(2 * π * (n : ℝ) * a))
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hnn n)
  have h2 : 0 ≤ 2 * π * (n : ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_left hab h2
  linarith

theorem sigq_nonneg (n : ℕ) : 0 ≤ sigq n := by
  unfold sigq
  exact div_nonneg (sig_nonneg 1 n) (Nat.cast_nonneg n)

theorem sigq_zero_or (n : ℕ) : sigq n = 0 ∨ (1 : ℝ) ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · left
    rw [h]
    exact sigq_zero
  · right
    exact Nat.one_le_cast.mpr (Nat.succ_le_of_lt h)

theorem sig_zero_or (k n : ℕ) : sig k n = 0 ∨ (1 : ℝ) ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · left
    rw [h]
    exact sig_zero k
  · right
    exact Nat.one_le_cast.mpr (Nat.succ_le_of_lt h)

theorem qb_nonneg (y : ℝ) : 0 ≤ qb y := qa_nonneg_of sigq_nonneg y

theorem qb_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : qb b ≤ qb a :=
  qa_anti_of sigq_abs_le sigq_nonneg ha hab

/-- `qb y - qb 2y + qb 3y - qb 6y`, so that `log xm y = log 8 - πy + 3 Wq y`. -/
noncomputable def Wq (y : ℝ) : ℝ := qb y - qb (2 * y) + qb (3 * y) - qb (6 * y)

theorem abs_Wq_le {y : ℝ} (hy : 0 < y) : |Wq y| ≤ 4 * qb y := by
  have h2 := qb_anti hy (by linarith : y ≤ 2 * y)
  have h3 := qb_anti hy (by linarith : y ≤ 3 * y)
  have h6 := qb_anti hy (by linarith : y ≤ 6 * y)
  have n1 := qb_nonneg y
  have n2 := qb_nonneg (2 * y)
  have n3 := qb_nonneg (3 * y)
  have n6 := qb_nonneg (6 * y)
  unfold Wq
  rw [abs_le]
  constructor <;> linarith

/-! ## `log xm` near `y = 0`, and `xm` at the cusp -/

theorem log_xm_fricke {y : ℝ} (hy : 0 < y) :
    Real.log (xm y) = π / (6 * y) - 3 * Wq (1 / (6 * y)) := by
  have hf := xm_mul_fricke hy
  have hl : Real.log (xm y * xm (1 / (6 * y))) = Real.log 8 := by rw [hf]
  rw [Real.log_mul (xm_pos y).ne' (xm_pos _).ne', log_xm (1 / (6 * y))] at hl
  unfold Wq
  linear_combination hl

theorem inv_xm_le {y : ℝ} (hy : 1 ≤ y) : (xm y)⁻¹ ≤ Real.exp (π * y + 12 * qb 1) := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have e : (xm y)⁻¹ = Real.exp (-(Real.log (xm y))) := by
    rw [Real.exp_neg, Real.exp_log (xm_pos y)]
  rw [e]
  refine Real.exp_le_exp.mpr ?_
  have hl := log_xm y
  have hW := abs_Wq_le hy0
  have hq := qb_anti one_pos hy
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hWl : -|Wq y| ≤ Wq y := (abs_le.mp le_rfl).1
  unfold Wq at hW hWl
  linarith

/-! ## `g₄` and `𝒜₁` at the cusp -/

/-- `∑ σ₃(n) e^{-2πn}`. -/
noncomputable def S3c : ℝ := ∑' n : ℕ, |sig 3 n| * Real.exp (-(2 * π * (n : ℝ) * 1))

theorem qa_sig3_le {y : ℝ} (hy : 1 ≤ y) :
    qa (sig 3) y ≤ Real.exp (-(2 * π * 1 * (y - 1))) * S3c := by
  have h := qa_abs_le_tail (sig_abs_le 3) 1 (sig_zero_or 3) hy
  exact le_trans (le_abs_self _) h

theorem abs_g4_le {y : ℝ} (hy : 1 ≤ y) :
    |g4 y| ≤ 640 * S3c * Real.exp (-(2 * π * 1 * (y - 1))) := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  rw [g4_eq_g4E hy0, g4E_eq_qa hy0]
  have q1 := qa_sig3_le hy
  have a2 := qa_anti_of (sig_abs_le 3) (sig_nonneg 3) hy0 (by linarith : y ≤ 2 * y)
  have a3 := qa_anti_of (sig_abs_le 3) (sig_nonneg 3) hy0 (by linarith : y ≤ 3 * y)
  have a6 := qa_anti_of (sig_abs_le 3) (sig_nonneg 3) hy0 (by linarith : y ≤ 6 * y)
  have n1 := qa_nonneg_of (sig_nonneg 3) y
  have n2 := qa_nonneg_of (sig_nonneg 3) (2 * y)
  have n3 := qa_nonneg_of (sig_nonneg 3) (3 * y)
  have n6 := qa_nonneg_of (sig_nonneg 3) (6 * y)
  rw [abs_le]
  constructor <;> linarith

theorem Tint_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Tint b ≤ Tint a := by
  unfold Tint
  refine setIntegral_mono_set (integrableOn_Tint ha) ?_ (Set.Ioi_subset_Ioi hab).eventuallySubset
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
  have ht0 : 0 < t := lt_trans ha (Set.mem_Ioi.mp ht)
  show (0 : ℝ) ≤ t * qa (sig 3) t
  exact mul_nonneg ht0.le (qa_nonneg_of (sig_nonneg 3) t)

theorem abs_A1_le {y : ℝ} (hy : 1 ≤ y) : |A1 y| ≤ 80 * Tint 1 := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  rw [A1_eq_A1E hy0, A1E_direct hy0]
  have t1 := Tint_anti one_pos hy
  have t2 := Tint_anti one_pos (by linarith : (1 : ℝ) ≤ 2 * y)
  have t3 := Tint_anti one_pos (by linarith : (1 : ℝ) ≤ 3 * y)
  have t6 := Tint_anti one_pos (by linarith : (1 : ℝ) ≤ 6 * y)
  have p1 := Tint_pos hy0
  have p2 := Tint_pos (by linarith : (0 : ℝ) < 2 * y)
  have p3 := Tint_pos (by linarith : (0 : ℝ) < 3 * y)
  have p6 := Tint_pos (by linarith : (0 : ℝ) < 6 * y)
  rw [abs_le]
  constructor <;> linarith

/-! ## Three elementary inequalities -/

theorem rpow_neg_le {x s : ℝ} (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x ^ (-s) ≤ 1 + x⁻¹ := by
  have hinv : 0 ≤ x⁻¹ := (inv_pos.mpr hx).le
  rcases le_or_gt 1 x with h | h
  · have h1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    linarith
  · have h1 : x ^ (-s) ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx h.le (by linarith)
    rw [Real.rpow_neg_one] at h1
    linarith

/-- `|e^t - 1| ≤ |t| e^{|t|}`. -/
theorem abs_expm1_le_mul (t : ℝ) : |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  rcases le_or_gt 0 t with h | h
  · have h0 := Real.add_one_le_exp t
    rw [abs_of_nonneg h, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp t - 1)]
    have h1 := Real.add_one_le_exp (-t)
    have h2 : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
    linarith
  · have h0 := Real.add_one_le_exp t
    have he : Real.exp t ≤ 1 := exp_le_one_of_nonpos h.le
    rw [abs_of_neg h, abs_of_nonpos (by linarith : Real.exp t - 1 ≤ 0)]
    have h2 : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ -t)
    linarith

/-- `w⁶ e^{-2πw} ≤ 6!/(2π)⁶` for `w ≥ 0`. -/
theorem pow_six_exp_le {w : ℝ} (hw : 0 ≤ w) :
    w ^ 6 * Real.exp (-(2 * π * w)) ≤ 720 / (2 * π) ^ 6 := by
  have h2pi : 0 < 2 * π := mul_pos (by norm_num) Real.pi_pos
  have hx : 0 ≤ 2 * π * w := mul_nonneg h2pi.le hw
  have h := Real.pow_div_factorial_le_exp hx 6
  have h6 : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [h6, div_le_iff₀ (by norm_num : (0 : ℝ) < 720)] at h
  have hEE : Real.exp (2 * π * w) * Real.exp (-(2 * π * w)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h3 := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(2 * π * w))).le
  have hp6 : 0 < (2 * π) ^ 6 := pow_pos h2pi 6
  rw [le_div_iff₀ hp6]
  have e1 : w ^ 6 * Real.exp (-(2 * π * w)) * (2 * π) ^ 6
      = (2 * π * w) ^ 6 * Real.exp (-(2 * π * w)) := by ring
  rw [e1]
  linarith

/-! ## The pole part near `y = 0` -/

/-- `∑ (σ₁(n)/n) e^{-2πn/6}`. -/
noncomputable def Sq6 : ℝ := ∑' n : ℕ, |sigq n| * Real.exp (-(2 * π * (n : ℝ) * (1 / 6)))

theorem Sq6_nonneg : 0 ≤ Sq6 :=
  tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)

/-- **The pole part is bounded near `y = 0`.** -/
theorem pole_part_le : ∃ Kb : ℝ, ∀ y : ℝ, y ∈ Set.Ioc (0 : ℝ) 1 → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    |xm y ^ (-s) - Real.exp (-(π * s / (6 * y)))| / (162 * y ^ 6) ≤ Kb := by
  refine ⟨3456 * Real.exp (12 * qb (1 / 6)) * Sq6 * (Real.exp (π / 3) * (720 / (2 * π) ^ 6)),
    fun y hy s hs0 hs1 => ?_⟩
  have hy0 : 0 < y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have h6y : (0 : ℝ) < 6 * y := mul_pos (by norm_num) hy0
  have hw : 0 < 1 / (6 * y) := one_div_pos.mpr h6y
  have hw6 : 1 / 6 ≤ 1 / (6 * y) := one_div_le_one_div_of_le h6y (by linarith)
  have hA : xm y ^ (-s)
      = Real.exp (-(π * s / (6 * y))) * Real.exp (3 * s * Wq (1 / (6 * y))) := by
    rw [Real.rpow_def_of_pos (xm_pos y), log_xm_fricke hy0, ← Real.exp_add]
    congr 1
    ring
  have hE0 : 0 < Real.exp (-(π * s / (6 * y))) := Real.exp_pos _
  have hE1 : Real.exp (-(π * s / (6 * y))) ≤ 1 := by
    refine exp_le_one_of_nonpos ?_
    have : 0 ≤ π * s / (6 * y) := div_nonneg (mul_nonneg Real.pi_pos.le hs0) h6y.le
    linarith
  have hB : |xm y ^ (-s) - Real.exp (-(π * s / (6 * y)))|
      ≤ |Real.exp (3 * s * Wq (1 / (6 * y))) - 1| := by
    rw [hA]
    have e : Real.exp (-(π * s / (6 * y))) * Real.exp (3 * s * Wq (1 / (6 * y)))
          - Real.exp (-(π * s / (6 * y)))
        = Real.exp (-(π * s / (6 * y))) * (Real.exp (3 * s * Wq (1 / (6 * y))) - 1) := by ring
    rw [e, abs_mul, abs_of_pos hE0]
    exact mul_le_of_le_one_left (abs_nonneg _) hE1
  have hW := abs_Wq_le hw
  have hq := qb_anti (by norm_num : (0 : ℝ) < 1 / 6) hw6
  have hqn := qb_nonneg (1 / (6 * y))
  have hC1 := abs_expm1_le_mul (3 * s * Wq (1 / (6 * y)))
  have hsW := mul_le_mul_of_nonneg_right hs1 (abs_nonneg (Wq (1 / (6 * y))))
  have habs : |3 * s * Wq (1 / (6 * y))| ≤ 12 * qb (1 / (6 * y)) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonneg hs0]
    linarith
  have hexp : Real.exp |3 * s * Wq (1 / (6 * y))| ≤ Real.exp (12 * qb (1 / 6)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hC : |Real.exp (3 * s * Wq (1 / (6 * y))) - 1|
      ≤ 12 * qb (1 / (6 * y)) * Real.exp (12 * qb (1 / 6)) :=
    le_trans hC1 (mul_le_mul habs hexp (Real.exp_pos _).le (by linarith))
  have hT := qa_abs_le_tail_at sigq_abs_le 1 sigq_zero_or (by norm_num : (0 : ℝ) < 1 / 6) hw6
  have hqT : qb (1 / (6 * y)) ≤ Real.exp (-(2 * π * 1 * (1 / (6 * y) - 1 / 6))) * Sq6 :=
    le_trans (le_abs_self _) hT
  have hG : (1 / (6 * y)) ^ 6 * Real.exp (-(2 * π * 1 * (1 / (6 * y) - 1 / 6)))
      ≤ Real.exp (π / 3) * (720 / (2 * π) ^ 6) := by
    have e : Real.exp (-(2 * π * 1 * (1 / (6 * y) - 1 / 6)))
        = Real.exp (π / 3) * Real.exp (-(2 * π * (1 / (6 * y)))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    have h := pow_six_exp_le hw.le
    have hp := Real.exp_pos (π / 3)
    calc (1 / (6 * y)) ^ 6 * (Real.exp (π / 3) * Real.exp (-(2 * π * (1 / (6 * y)))))
        = Real.exp (π / 3) * ((1 / (6 * y)) ^ 6 * Real.exp (-(2 * π * (1 / (6 * y))))) := by
          ring
      _ ≤ Real.exp (π / 3) * (720 / (2 * π) ^ 6) := mul_le_mul_of_nonneg_left h hp.le
  have hF : 1 / (162 * y ^ 6) = 288 * (1 / (6 * y)) ^ 6 := by ring
  have hw6n : (0 : ℝ) ≤ 288 * (1 / (6 * y)) ^ 6 := by positivity
  rw [div_eq_mul_one_div, hF]
  have hstep1 := mul_le_mul_of_nonneg_right (le_trans hB hC) hw6n
  have hK0 : (0 : ℝ) ≤ 3456 * Real.exp (12 * qb (1 / 6)) * (1 / (6 * y)) ^ 6 := by positivity
  have hq2a := mul_le_mul_of_nonneg_left hqT hK0
  have hq2 : 12 * qb (1 / (6 * y)) * Real.exp (12 * qb (1 / 6)) * (288 * (1 / (6 * y)) ^ 6)
      ≤ 3456 * Real.exp (12 * qb (1 / 6)) * Sq6
        * ((1 / (6 * y)) ^ 6 * Real.exp (-(2 * π * 1 * (1 / (6 * y) - 1 / 6)))) := by
    linarith
  have hK1 : (0 : ℝ) ≤ 3456 * Real.exp (12 * qb (1 / 6)) * Sq6 :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) Sq6_nonneg
  have hq3 := mul_le_mul_of_nonneg_left hG hK1
  linarith

/-! ## Continuity -/

theorem continuousAt_qa_mul {C : ℕ → ℝ} {B : ℝ} {K : ℕ}
    (hC : ∀ n : ℕ, |C n| ≤ B * (n : ℝ) ^ K) {d : ℝ} (hd : 0 < d) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (fun t : ℝ => qa C (d * t)) y := by
  have h0 : ContinuousAt (qa C) (d * y) :=
    (continuousOn_qa_Ioi hC).continuousAt (Ioi_mem_nhds (mul_pos hd hy))
  have hl : ContinuousAt (fun t : ℝ => d * t) y := (continuous_const.mul continuous_id).continuousAt
  have hc := ContinuousAt.comp (g := qa C) (f := fun t : ℝ => d * t) h0 hl
  exact hc

theorem continuousAt_g4 {y : ℝ} (hy : 0 < y) : ContinuousAt g4 y := by
  have c1 : ContinuousAt (qa (sig 3)) y :=
    (continuousOn_qa_Ioi (sig_abs_le 3)).continuousAt (Ioi_mem_nhds hy)
  have c2 := continuousAt_qa_mul (sig_abs_le 3) (by norm_num : (0 : ℝ) < 2) hy
  have c3 := continuousAt_qa_mul (sig_abs_le 3) (by norm_num : (0 : ℝ) < 3) hy
  have c6 := continuousAt_qa_mul (sig_abs_le 3) (by norm_num : (0 : ℝ) < 6) hy
  have k1 : ContinuousAt (fun t : ℝ => qa (sig 3) t - qa (sig 3) (2 * t)) y := c1.sub c2
  have k2 : ContinuousAt (fun t : ℝ => qa (sig 3) t - qa (sig 3) (2 * t)
      - 9 * qa (sig 3) (3 * t)) y := k1.sub (c3.const_mul 9)
  have k3 : ContinuousAt (fun t : ℝ => qa (sig 3) t - qa (sig 3) (2 * t)
      - 9 * qa (sig 3) (3 * t) + 9 * qa (sig 3) (6 * t)) y := k2.add (c6.const_mul 9)
  have k : ContinuousAt (fun t : ℝ => 32 * (qa (sig 3) t - qa (sig 3) (2 * t)
      - 9 * qa (sig 3) (3 * t) + 9 * qa (sig 3) (6 * t))) y := k3.const_mul 32
  refine k.congr ?_
  filter_upwards [Ioi_mem_nhds hy] with t ht
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  rw [g4_eq_g4E ht0, g4E_eq_qa ht0]

theorem continuousAt_Tint_mul {d : ℝ} (hd : 0 < d) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (fun t : ℝ => Tint (d * t)) y := by
  have c1 := continuousAt_qa_mul bound_sig3_div hd hy
  have c2 := continuousAt_qa_mul bound_sig3_div_sq hd hy
  have cl : ContinuousAt (fun t : ℝ => d * t) y := (continuous_const.mul continuous_id).continuousAt
  have k1 : ContinuousAt (fun t : ℝ => d * t * qa (fun n => sig 3 n / (n : ℝ)) (d * t)) y :=
    cl.mul c1
  have k : ContinuousAt (fun t : ℝ => d * t * qa (fun n => sig 3 n / (n : ℝ)) (d * t) / (2 * π)
      + qa (fun n => sig 3 n / (n : ℝ) ^ 2) (d * t) / (4 * π ^ 2)) y :=
    (k1.div_const (2 * π)).add (c2.div_const (4 * π ^ 2))
  refine k.congr ?_
  filter_upwards [Ioi_mem_nhds hy] with t ht
  have ht0 : 0 < d * t := mul_pos hd (Set.mem_Ioi.mp ht)
  rw [Tint_eq ht0]

theorem continuousAt_A1 {y : ℝ} (hy : 0 < y) : ContinuousAt A1 y := by
  have c1 := continuousAt_Tint_mul one_pos hy
  have c2 := continuousAt_Tint_mul (by norm_num : (0 : ℝ) < 2) hy
  have c3 := continuousAt_Tint_mul (by norm_num : (0 : ℝ) < 3) hy
  have c6 := continuousAt_Tint_mul (by norm_num : (0 : ℝ) < 6) hy
  have k1 : ContinuousAt (fun t : ℝ => Tint (1 * t) - Tint (2 * t) / 4) y :=
    c1.sub (c2.div_const 4)
  have k2 : ContinuousAt (fun t : ℝ => Tint (1 * t) - Tint (2 * t) / 4 - Tint (3 * t)) y :=
    k1.sub c3
  have k3 : ContinuousAt (fun t : ℝ => Tint (1 * t) - Tint (2 * t) / 4 - Tint (3 * t)
      + Tint (6 * t) / 4) y := k2.add (c6.div_const 4)
  have k : ContinuousAt (fun t : ℝ => 32 * (Tint (1 * t) - Tint (2 * t) / 4 - Tint (3 * t)
      + Tint (6 * t) / 4)) y := k3.const_mul 32
  refine k.congr ?_
  filter_upwards [Ioi_mem_nhds hy] with t ht
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  rw [A1_eq_A1E ht0, A1E_direct ht0, one_mul]

/-! ## The integrand of `JS - poleS` -/

/-- `g₄ 𝒜₁ xm^{-s} - e^{-πs/(6y)}/(162 y⁶)`. -/
noncomputable def FS (s y : ℝ) : ℝ :=
  g4 y * A1 y * xm y ^ (-s) - Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6)

/-- The integrand of `D₀₁`. -/
noncomputable def f0 (y : ℝ) : ℝ := g4 y * A1 y - 1 / (162 * y ^ 6)

theorem continuousAt_FS (s : ℝ) {y : ℝ} (hy : 0 < y) : ContinuousAt (FS s) y := by
  have cg := continuousAt_g4 hy
  have ca := continuousAt_A1 hy
  have cx : ContinuousAt xm y := (hasDerivAt_xm hy).continuousAt
  have cr : ContinuousAt (fun t : ℝ => xm t ^ (-s)) y := cx.rpow_const (Or.inl (xm_pos y).ne')
  have h6y : (6 : ℝ) * y ≠ 0 := (mul_pos (by norm_num) hy).ne'
  have h162 : (162 : ℝ) * y ^ 6 ≠ 0 := (mul_pos (by norm_num) (pow_pos hy 6)).ne'
  have c6 : ContinuousAt (fun t : ℝ => 6 * t) y := (continuous_const.mul continuous_id).continuousAt
  have cq : ContinuousAt (fun t : ℝ => π * s / (6 * t)) y :=
    ContinuousAt.div continuousAt_const c6 h6y
  have cqn : ContinuousAt (fun t : ℝ => -(π * s / (6 * t))) y := cq.neg
  have ce0 := ContinuousAt.comp (g := Real.exp) (f := fun t : ℝ => -(π * s / (6 * t)))
    Real.continuous_exp.continuousAt cqn
  have ce : ContinuousAt (fun t : ℝ => Real.exp (-(π * s / (6 * t)))) y := ce0
  have cp : ContinuousAt (fun t : ℝ => 162 * t ^ 6) y :=
    (continuous_const.mul (continuous_pow 6)).continuousAt
  have cd : ContinuousAt (fun t : ℝ => Real.exp (-(π * s / (6 * t))) / (162 * t ^ 6)) y :=
    ContinuousAt.div ce cp h162
  have k : ContinuousAt (fun t : ℝ => g4 t * A1 t * xm t ^ (-s)
      - Real.exp (-(π * s / (6 * t))) / (162 * t ^ 6)) y := ((cg.mul ca).mul cr).sub cd
  exact k

theorem continuousOn_FS (s : ℝ) : ContinuousOn (FS s) (Set.Ioi 0) :=
  fun y hy => (continuousAt_FS s (Set.mem_Ioi.mp hy)).continuousWithinAt

/-- `FS s y → f0 y` as `s → 0+`. -/
theorem tendsto_FS {y : ℝ} (hy : 0 < y) :
    Filter.Tendsto (fun s : ℝ => FS s y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f0 y)) := by
  have hc : Continuous (fun s : ℝ => g4 y * A1 y * Real.exp (Real.log (xm y) * -s)
      - Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6)) := by fun_prop
  have ht := hc.tendsto 0
  simp only [neg_zero, mul_zero, zero_div, Real.exp_zero, mul_one] at ht
  refine (tendsto_nhdsWithin_of_tendsto_nhds ht).congr (fun s => ?_)
  show g4 y * A1 y * Real.exp (Real.log (xm y) * -s)
      - Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6) = FS s y
  unfold FS
  rw [Real.rpow_def_of_pos (xm_pos y)]

/-! ## The dominations -/

theorem FS_bound_Ioc {Kb : ℝ} (hKb : ∀ y : ℝ, y ∈ Set.Ioc (0 : ℝ) 1 → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      |xm y ^ (-s) - Real.exp (-(π * s / (6 * y)))| / (162 * y ^ 6) ≤ Kb)
    {y s : ℝ} (hy : y ∈ Set.Ioc (0 : ℝ) 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |FS s y| ≤ (1 + (xm 1)⁻¹) * |f0 y| + Kb := by
  have hy0 : 0 < y := hy.1
  have hX0 : 0 ≤ xm y ^ (-s) := Real.rpow_nonneg (xm_pos y).le _
  have hX : xm y ^ (-s) ≤ 1 + (xm 1)⁻¹ := by
    have h1 := rpow_neg_le (xm_pos y) hs0 hs1
    have hanti : xm 1 ≤ xm y :=
      strictAntiOn_xm.antitoneOn (Set.mem_Ioi.mpr hy0) (Set.mem_Ioi.mpr one_pos) hy.2
    have hinv : (xm y)⁻¹ ≤ (xm 1)⁻¹ := inv_anti₀ (xm_pos 1) hanti
    linarith
  have hp : 0 < 162 * y ^ 6 := mul_pos (by norm_num) (pow_pos hy0 6)
  have hdec : FS s y = f0 y * xm y ^ (-s)
      + (xm y ^ (-s) - Real.exp (-(π * s / (6 * y)))) / (162 * y ^ 6) := by
    unfold FS f0
    ring
  rw [hdec]
  calc |f0 y * xm y ^ (-s) + (xm y ^ (-s) - Real.exp (-(π * s / (6 * y)))) / (162 * y ^ 6)|
      ≤ |f0 y * xm y ^ (-s)|
        + |(xm y ^ (-s) - Real.exp (-(π * s / (6 * y)))) / (162 * y ^ 6)| := abs_add_le _ _
    _ = |f0 y| * xm y ^ (-s)
        + |xm y ^ (-s) - Real.exp (-(π * s / (6 * y)))| / (162 * y ^ 6) := by
        rw [abs_mul, abs_of_nonneg hX0, abs_div, abs_of_pos hp]
    _ ≤ |f0 y| * (1 + (xm 1)⁻¹) + Kb :=
        add_le_add (mul_le_mul_of_nonneg_left hX (abs_nonneg _)) (hKb y hy s hs0 hs1)
    _ = (1 + (xm 1)⁻¹) * |f0 y| + Kb := by ring

theorem FS_bound_Ioi {y s : ℝ} (hy : 1 < y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |FS s y| ≤ 640 * S3c * (80 * Tint 1) * (Real.exp (-(2 * π * 1 * (y - 1)))
      + Real.exp (-(2 * π * 1 * (y - 1))) * Real.exp (π * y + 12 * qb 1)) + 1 / (162 * y ^ 6) := by
  have hy0 : 0 < y := lt_trans one_pos hy
  have hg := abs_g4_le hy.le
  have ha := abs_A1_le hy.le
  have hX0 : 0 ≤ xm y ^ (-s) := Real.rpow_nonneg (xm_pos y).le _
  have hX : xm y ^ (-s) ≤ 1 + Real.exp (π * y + 12 * qb 1) := by
    have h1 := rpow_neg_le (xm_pos y) hs0 hs1
    have h2 := inv_xm_le hy.le
    linarith
  have hp : 0 < 162 * y ^ 6 := mul_pos (by norm_num) (pow_pos hy0 6)
  have hE1 : Real.exp (-(π * s / (6 * y))) ≤ 1 := by
    refine exp_le_one_of_nonpos ?_
    have : 0 ≤ π * s / (6 * y) :=
      div_nonneg (mul_nonneg Real.pi_pos.le hs0) (mul_pos (by norm_num) hy0).le
    linarith
  have hEd : Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6) ≤ 1 / (162 * y ^ 6) :=
    div_le_div_of_nonneg_right hE1 hp.le
  have hEn : 0 ≤ Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6) :=
    div_nonneg (Real.exp_pos _).le hp.le
  have hga : |g4 y| * |A1 y| ≤ 640 * S3c * Real.exp (-(2 * π * 1 * (y - 1))) * (80 * Tint 1) :=
    mul_le_mul hg ha (abs_nonneg _) (le_trans (abs_nonneg _) hg)
  have hgaX : |g4 y| * |A1 y| * xm y ^ (-s)
      ≤ 640 * S3c * Real.exp (-(2 * π * 1 * (y - 1))) * (80 * Tint 1)
        * (1 + Real.exp (π * y + 12 * qb 1)) :=
    mul_le_mul hga hX hX0 (le_trans (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hga)
  have htri := abs_add_le (g4 y * A1 y * xm y ^ (-s))
    (-(Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6)))
  rw [abs_neg, ← sub_eq_add_neg] at htri
  unfold FS
  calc |g4 y * A1 y * xm y ^ (-s) - Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6)|
      ≤ |g4 y * A1 y * xm y ^ (-s)| + |Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6)| := htri
    _ = |g4 y| * |A1 y| * xm y ^ (-s) + Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hX0, abs_of_nonneg hEn]
    _ ≤ 640 * S3c * Real.exp (-(2 * π * 1 * (y - 1))) * (80 * Tint 1)
          * (1 + Real.exp (π * y + 12 * qb 1)) + 1 / (162 * y ^ 6) := add_le_add hgaX hEd
    _ = 640 * S3c * (80 * Tint 1) * (Real.exp (-(2 * π * 1 * (y - 1)))
          + Real.exp (-(2 * π * 1 * (y - 1))) * Real.exp (π * y + 12 * qb 1))
          + 1 / (162 * y ^ 6) := by ring

/-! ## The integrand of `D₀₁` is integrable -/

theorem integrableOn_f0 : IntegrableOn f0 (Set.Ioi 0) := by
  have hL : Integrable (fun y : ℝ => (-(8 / 9) * (∑ k ∈ Finset.range 4, cG k * dv k * (Tint (dv k / (6 * y)) / y ^ 4)) + 64 / 81 * (1 / (2 * π)) * ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 2 * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y)) / y ^ 3) + 64 / 81 * (1 / (4 * π ^ 2)) * ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y)) / y ^ 4))) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.add (Integrable.add (Integrable.const_mul lin_TC.1 (-(8 / 9)))
      (Integrable.const_mul bilin_S3.1 (64 / 81 * (1 / (2 * π)))))
      (Integrable.const_mul bilin_S4.1 (64 / 81 * (1 / (4 * π ^ 2))))
  refine hL.congr ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => ?_)
  have hy0 : 0 < y := Set.mem_Ioi.mp hy
  have h := D01E_integrand hy0
  rw [← g4_eq_g4E hy0, ← A1_eq_A1E hy0] at h
  exact h.symm

end Tower.RV6
