import Mathlib
import Tower.RV6.Defs

/-!
# The modified Bessel functions `I₀`, `I₁` as power series

`besselI0`, `besselI1` of `Defs.lean` are power series in `t`.  With `s = (t/2)²`,

`I₀(t) = A(s)`, `I₁(t) = (t/2) B(s)`,  `A(s) = ∑ s^k/(k!)²`,  `B(s) = ∑ s^k/(k!(k+1)!)`.

* `hasDerivAt_fact_series`: a power series whose coefficients are bounded by `1/k!` is
  differentiated termwise, everywhere.
* `hasDerivAt_Aser : A' = B`, `hasDerivAt_mul_Bser : (s B(s))' = A(s)`.
* `hasDerivAt_besselI0 : I₀' = I₁`, `hasDerivAt_mul_besselI1 : (t I₁(t))' = t I₀(t)`.
* `one_le_besselI0`, `besselI1_nonneg`, `besselI0_zero`, `besselI1_zero`, continuity.
-/

namespace Tower.RV6

open Real

/-! ## Power series with coefficients bounded by `1/k!` -/

theorem fact_ge_one (k : ℕ) : (1 : ℝ) ≤ (k.factorial : ℝ) :=
  Nat.one_le_cast.mpr (Nat.succ_le_of_lt (Nat.factorial_pos k))

theorem summable_fact_series {c : ℕ → ℝ} (hc : ∀ k, |c k| ≤ 1 / (k.factorial : ℝ)) (x : ℝ) :
    Summable fun k : ℕ => c k * x ^ k := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |x|) (fun k => ?_)
  show ‖c k * x ^ k‖ ≤ |x| ^ k / (k.factorial : ℝ)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |c k| * |x| ^ k ≤ 1 / (k.factorial : ℝ) * |x| ^ k :=
        mul_le_mul_of_nonneg_right (hc k) (pow_nonneg (abs_nonneg x) k)
    _ = |x| ^ k / (k.factorial : ℝ) := by ring

/-- Termwise differentiation of `∑ c(k) x^k` when `|c(k)| ≤ 1/k!`. -/
theorem hasDerivAt_fact_series {c : ℕ → ℝ} (hc : ∀ k, |c k| ≤ 1 / (k.factorial : ℝ)) (s : ℝ) :
    HasDerivAt (fun x : ℝ => ∑' k : ℕ, c k * x ^ k)
      (∑' k : ℕ, c (k + 1) * ((k : ℝ) + 1) * s ^ k) s := by
  have hR0 : (0 : ℝ) ≤ |s| + 1 := by positivity
  have hu1 : Summable fun k : ℕ => (|s| + 1) ^ k / (k.factorial : ℝ) :=
    Real.summable_pow_div_factorial (|s| + 1)
  have hu : Summable fun k : ℕ => (k : ℝ) * (|s| + 1) ^ (k - 1) / (k.factorial : ℝ) := by
    refine (summable_nat_add_iff 1).mp ?_
    refine hu1.congr (fun k => ?_)
    show (|s| + 1) ^ k / (k.factorial : ℝ)
      = ((k + 1 : ℕ) : ℝ) * (|s| + 1) ^ (k + 1 - 1) / ((k + 1).factorial : ℝ)
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    rw [mul_div_mul_left _ _ hk]
  have hs : s ∈ Set.Ioo (-(|s| + 1)) (|s| + 1) := by
    have h1 : |s| < |s| + 1 := by linarith
    have h2 := abs_lt.mp h1
    exact ⟨h2.1, h2.2⟩
  have hg : ∀ (k : ℕ) (x : ℝ), x ∈ Set.Ioo (-(|s| + 1)) (|s| + 1) →
      HasDerivAt (fun y : ℝ => c k * y ^ k) (c k * ((k : ℝ) * x ^ (k - 1))) x := by
    intro k x _
    exact (hasDerivAt_pow k x).const_mul (c k)
  have hg' : ∀ (k : ℕ) (x : ℝ), x ∈ Set.Ioo (-(|s| + 1)) (|s| + 1) →
      ‖c k * ((k : ℝ) * x ^ (k - 1))‖ ≤ (k : ℝ) * (|s| + 1) ^ (k - 1) / (k.factorial : ℝ) := by
    intro k x hx
    have hxR : |x| ≤ |s| + 1 := (abs_lt.mpr ⟨hx.1, hx.2⟩).le
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpow : |x| ^ (k - 1) ≤ (|s| + 1) ^ (k - 1) :=
      pow_le_pow_left₀ (abs_nonneg x) hxR (k - 1)
    have hf0 : (0 : ℝ) ≤ 1 / (k.factorial : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hk0, abs_pow]
    calc |c k| * ((k : ℝ) * |x| ^ (k - 1))
        ≤ 1 / (k.factorial : ℝ) * ((k : ℝ) * (|s| + 1) ^ (k - 1)) :=
          mul_le_mul (hc k) (mul_le_mul_of_nonneg_left hpow hk0)
            (mul_nonneg hk0 (pow_nonneg (abs_nonneg x) (k - 1))) hf0
      _ = (k : ℝ) * (|s| + 1) ^ (k - 1) / (k.factorial : ℝ) := by ring
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' hs
    (summable_fact_series hc s) hs
  have hsumm : Summable fun k : ℕ => c k * ((k : ℝ) * s ^ (k - 1)) :=
    Summable.of_norm_bounded hu (fun k => hg' k s hs)
  have hre : ∑' k : ℕ, c k * ((k : ℝ) * s ^ (k - 1))
      = ∑' k : ℕ, c (k + 1) * ((k : ℝ) + 1) * s ^ k := by
    rw [hsumm.tsum_eq_zero_add, Nat.cast_zero, zero_mul, mul_zero, zero_add]
    refine tsum_congr (fun k => ?_)
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  exact key.congr_deriv hre

/-! ## The coefficients -/

/-- `1/(k!)²`. -/
noncomputable def cA (k : ℕ) : ℝ := 1 / ((k.factorial : ℝ) * (k.factorial : ℝ))

/-- `1/(k!(k+1)!)`. -/
noncomputable def cB (k : ℕ) : ℝ := 1 / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))

/-- The coefficients of `s B(s)`: `0, cB 0, cB 1, …`. -/
noncomputable def cD (k : ℕ) : ℝ := if k = 0 then 0 else cB (k - 1)

theorem cA_nonneg (k : ℕ) : 0 ≤ cA k := by
  unfold cA
  positivity

theorem cB_nonneg (k : ℕ) : 0 ≤ cB k := by
  unfold cB
  positivity

theorem cA_le (k : ℕ) : |cA k| ≤ 1 / (k.factorial : ℝ) := by
  have h1 := fact_ge_one k
  have hpos : (0 : ℝ) < (k.factorial : ℝ) := by linarith
  have hle : (k.factorial : ℝ) ≤ (k.factorial : ℝ) * (k.factorial : ℝ) := by nlinarith
  rw [abs_of_nonneg (cA_nonneg k)]
  exact one_div_le_one_div_of_le hpos hle

theorem cB_le (k : ℕ) : |cB k| ≤ 1 / (k.factorial : ℝ) := by
  have h1 := fact_ge_one k
  have h2 := fact_ge_one (k + 1)
  have hpos : (0 : ℝ) < (k.factorial : ℝ) := by linarith
  have hle : (k.factorial : ℝ) ≤ (k.factorial : ℝ) * ((k + 1).factorial : ℝ) := by nlinarith
  rw [abs_of_nonneg (cB_nonneg k)]
  exact one_div_le_one_div_of_le hpos hle

theorem cD_zero : cD 0 = 0 := by simp [cD]

theorem cD_succ (k : ℕ) : cD (k + 1) = cB k := by simp [cD]

theorem cD_le (k : ℕ) : |cD k| ≤ 1 / (k.factorial : ℝ) := by
  cases k with
  | zero =>
    rw [cD_zero, abs_zero]
    positivity
  | succ m =>
    have h1 := fact_ge_one m
    have h2 := fact_ge_one (m + 1)
    have hpos : (0 : ℝ) < ((m + 1).factorial : ℝ) := by linarith
    have hle : ((m + 1).factorial : ℝ) ≤ (m.factorial : ℝ) * ((m + 1).factorial : ℝ) := by
      nlinarith
    rw [cD_succ, abs_of_nonneg (cB_nonneg m)]
    exact one_div_le_one_div_of_le hpos hle

/-- `(k+1)/((k+1)!)² = 1/(k!(k+1)!)`. -/
theorem cA_succ_mul (k : ℕ) : cA (k + 1) * ((k : ℝ) + 1) = cB k := by
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by linarith [fact_ge_one k]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have e : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  unfold cA cB
  rw [e, div_mul_eq_mul_div, one_mul,
    div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- `(k+1)/(k!(k+1)!) = 1/(k!)²`. -/
theorem cB_mul (k : ℕ) : cB k * ((k : ℝ) + 1) = cA k := by
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by linarith [fact_ge_one k]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have e : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  unfold cA cB
  rw [e, div_mul_eq_mul_div, one_mul,
    div_eq_div_iff (by positivity) (by positivity)]
  ring

/-! ## The two series in `s` -/

/-- `A(x) = ∑ x^k/(k!)²`. -/
noncomputable def Aser (x : ℝ) : ℝ := ∑' k : ℕ, cA k * x ^ k

/-- `B(x) = ∑ x^k/(k!(k+1)!)`. -/
noncomputable def Bser (x : ℝ) : ℝ := ∑' k : ℕ, cB k * x ^ k

theorem hasDerivAt_Aser (s : ℝ) : HasDerivAt Aser (Bser s) s := by
  have h := hasDerivAt_fact_series cA_le s
  have e : ∑' k : ℕ, cA (k + 1) * ((k : ℝ) + 1) * s ^ k = ∑' k : ℕ, cB k * s ^ k :=
    tsum_congr (fun k => by rw [cA_succ_mul])
  exact h.congr_deriv e

theorem mul_Bser_eq (x : ℝ) : x * Bser x = ∑' k : ℕ, cD k * x ^ k := by
  rw [(summable_fact_series cD_le x).tsum_eq_zero_add, cD_zero, zero_mul, zero_add]
  unfold Bser
  rw [← tsum_mul_left]
  refine tsum_congr (fun k => ?_)
  rw [cD_succ, pow_succ]
  ring

theorem hasDerivAt_mul_Bser (s : ℝ) : HasDerivAt (fun x : ℝ => x * Bser x) (Aser s) s := by
  have h := hasDerivAt_fact_series cD_le s
  have e : ∑' k : ℕ, cD (k + 1) * ((k : ℝ) + 1) * s ^ k = ∑' k : ℕ, cA k * s ^ k :=
    tsum_congr (fun k => by rw [cD_succ, cB_mul])
  have hf : (fun x : ℝ => x * Bser x) = fun x : ℝ => ∑' k : ℕ, cD k * x ^ k :=
    funext mul_Bser_eq
  rw [hf]
  exact h.congr_deriv e

theorem continuous_Bser : Continuous Bser :=
  continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_fact_series cB_le s).continuousAt)

/-! ## `I₀` and `I₁` -/

theorem besselI0_eq (t : ℝ) : besselI0 t = Aser (t / 2 * (t / 2)) := by
  unfold besselI0 Aser
  refine tsum_congr (fun k => ?_)
  unfold cA
  ring

theorem besselI1_eq (t : ℝ) : besselI1 t = t / 2 * Bser (t / 2 * (t / 2)) := by
  unfold besselI1 Bser
  rw [← tsum_mul_left]
  refine tsum_congr (fun k => ?_)
  unfold cB
  ring

/-- `I₀' = I₁`. -/
theorem hasDerivAt_besselI0 (t : ℝ) : HasDerivAt besselI0 (besselI1 t) t := by
  have hin0 := ((hasDerivAt_id' t).div_const 2).mul ((hasDerivAt_id' t).div_const 2)
  have hin : HasDerivAt (fun x : ℝ => x / 2 * (x / 2))
      (1 / 2 * (t / 2) + t / 2 * (1 / 2)) t := hin0
  have hA := hasDerivAt_Aser (t / 2 * (t / 2))
  have hcomp0 := hA.comp t hin
  have hcomp : HasDerivAt (fun x : ℝ => Aser (x / 2 * (x / 2)))
      (Bser (t / 2 * (t / 2)) * (1 / 2 * (t / 2) + t / 2 * (1 / 2))) t := hcomp0
  have hfun : besselI0 = fun x : ℝ => Aser (x / 2 * (x / 2)) := funext besselI0_eq
  rw [hfun, besselI1_eq]
  exact hcomp.congr_deriv (by ring)

/-- `(t I₁(t))' = t I₀(t)`. -/
theorem hasDerivAt_mul_besselI1 (t : ℝ) :
    HasDerivAt (fun x : ℝ => x * besselI1 x) (t * besselI0 t) t := by
  have hin0 := ((hasDerivAt_id' t).div_const 2).mul ((hasDerivAt_id' t).div_const 2)
  have hin : HasDerivAt (fun x : ℝ => x / 2 * (x / 2))
      (1 / 2 * (t / 2) + t / 2 * (1 / 2)) t := hin0
  have hD := hasDerivAt_mul_Bser (t / 2 * (t / 2))
  have hcomp0 := hD.comp t hin
  have hcomp : HasDerivAt (fun x : ℝ => x / 2 * (x / 2) * Bser (x / 2 * (x / 2)))
      (Aser (t / 2 * (t / 2)) * (1 / 2 * (t / 2) + t / 2 * (1 / 2))) t := hcomp0
  have h2 := hcomp.const_mul 2
  have hfun : (fun x : ℝ => x * besselI1 x)
      = fun x : ℝ => 2 * (x / 2 * (x / 2) * Bser (x / 2 * (x / 2))) := by
    funext x
    rw [besselI1_eq]
    ring
  rw [hfun, besselI0_eq]
  exact h2.congr_deriv (by ring)

theorem continuous_besselI0 : Continuous besselI0 :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_besselI0 t).continuousAt)

theorem continuous_besselI1 : Continuous besselI1 := by
  have hs : Continuous fun x : ℝ => x / 2 * (x / 2) :=
    (continuous_id.div_const 2).mul (continuous_id.div_const 2)
  have h : Continuous fun x : ℝ => x / 2 * Bser (x / 2 * (x / 2)) :=
    (continuous_id.div_const 2).mul (continuous_Bser.comp hs)
  have hfun : besselI1 = fun x : ℝ => x / 2 * Bser (x / 2 * (x / 2)) := funext besselI1_eq
  rw [hfun]
  exact h

theorem cA_zero : cA 0 = 1 := by simp [cA]

/-- `A(x) ≥ 1` for `x ≥ 0`. -/
theorem one_le_Aser {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Aser x := by
  have h := (summable_fact_series cA_le x).le_tsum 0
    (fun j _ => mul_nonneg (cA_nonneg j) (pow_nonneg hx j))
  have h' : cA 0 * x ^ 0 ≤ Aser x := h
  rw [cA_zero, pow_zero, mul_one] at h'
  exact h'

theorem Bser_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Bser x :=
  tsum_nonneg (fun k => mul_nonneg (cB_nonneg k) (pow_nonneg hx k))

/-- `I₀(t) ≥ 1`. -/
theorem one_le_besselI0 (t : ℝ) : 1 ≤ besselI0 t := by
  rw [besselI0_eq]
  exact one_le_Aser (mul_self_nonneg (t / 2))

theorem besselI0_pos (t : ℝ) : 0 < besselI0 t := lt_of_lt_of_le one_pos (one_le_besselI0 t)

/-- `I₁(t) ≥ 0` for `t ≥ 0`. -/
theorem besselI1_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ besselI1 t := by
  rw [besselI1_eq]
  exact mul_nonneg (by linarith) (Bser_nonneg (mul_self_nonneg (t / 2)))

theorem besselI1_zero : besselI1 0 = 0 := by
  rw [besselI1_eq, zero_div, zero_mul]

theorem besselI0_zero : besselI0 0 = 1 := by
  rw [besselI0_eq, zero_div, zero_mul]
  unfold Aser
  rw [(summable_fact_series cA_le 0).tsum_eq_zero_add, cA_zero, pow_zero, mul_one]
  have hz : ∀ k : ℕ, cA (k + 1) * (0 : ℝ) ^ (k + 1) = 0 := by
    intro k
    rw [zero_pow (Nat.succ_ne_zero k), mul_zero]
  rw [tsum_congr hz, tsum_zero, add_zero]

end Tower.RV6
