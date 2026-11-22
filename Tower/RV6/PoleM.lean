import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselI
import Tower.RV6.BesselK
import Tower.RV6.BesselW
import Tower.RV6.BesselR
import Tower.RV6.KZero
import Tower.RV6.LadderA2
import Tower.RV6.MellinU
import Tower.RV6.RungA2P

/-!
# The pole of `M_{a,b}(s)` at `s = 0`: pointwise bounds

After the reflection `u = a₀ - y` the Mellin integrand of `M_{a,b}` becomes
`H(y) e^{-sy}` with `H(y) = I₀(e^{a₀-y})^a K₀(e^{a₀-y})^b`.  This file proves what
`RungA2M.lean` needs about `H`:

* `abs_besselIK_sub_pow_le`: for `y ≥ 0`, `|H(y) - y^b| ≤ D e^{-y/2}` (`a = a'+1`, `b = b'+2`,
  `D = poleD a' b'`), from `|K₀(e^{a₀-y}) - y| ≤ e^{a₀-y}/2` (`KZero.lean`), `I₀(t) - 1 ≤ t e^t`,
  `|x^{n+1} - z^{n+1}| ≤ (n+1) M^n |x - z|` and `x^n ≤ n! δ^{-n} e^{δx}`;
* `besselIK_mul_exp_le_of_nonpos`: for `y ≤ 0`, `H(y) e^{-y} ≤ D' e^y` (`D' = poleDneg b'`), given `I₀^a K₀^b ≤ t^{-b}`
  (`besselIK_le_inv_pow`: `K₀ ≤ K₁ ≤ 1/t` and `I₀ K₀ ≤ 1/t`);
* `integral_pow_mul_exp_neg`: `∫₀^∞ y^b e^{-sy} dy = b!/s^{b+1}` (Mathlib's Gamma integral).
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## Two elementary inequalities -/

/-- `|x^{n+1} - z^{n+1}| ≤ (n+1) M^n |x - z|` for `0 ≤ x, z ≤ M`. -/
theorem abs_pow_succ_sub_pow_succ_le {x z M : ℝ} (hx0 : 0 ≤ x) (hxM : x ≤ M) (hz0 : 0 ≤ z)
    (hzM : z ≤ M) (n : ℕ) :
    |x ^ (n + 1) - z ^ (n + 1)| ≤ ((n : ℝ) + 1) * M ^ n * |x - z| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : 0 ≤ |x - z| := abs_nonneg _
    have hM : 0 ≤ M := le_trans hx0 hxM
    have hxn0 : 0 ≤ x ^ (n + 1) := pow_nonneg hx0 (n + 1)
    have hxn : x ^ (n + 1) ≤ M ^ (n + 1) := pow_le_pow_left₀ hx0 hxM (n + 1)
    have key : x ^ (n + 1 + 1) - z ^ (n + 1 + 1)
        = x ^ (n + 1) * (x - z) + z * (x ^ (n + 1) - z ^ (n + 1)) := by ring
    have h1 : |x ^ (n + 1) * (x - z)| ≤ M ^ (n + 1) * |x - z| := by
      rw [abs_mul, abs_of_nonneg hxn0]
      exact mul_le_mul_of_nonneg_right hxn hd
    have h2 : |z * (x ^ (n + 1) - z ^ (n + 1))|
        ≤ M * (((n : ℝ) + 1) * M ^ n * |x - z|) := by
      rw [abs_mul, abs_of_nonneg hz0]
      exact mul_le_mul hzM ih (abs_nonneg _) hM
    have h3 := abs_add_le (x ^ (n + 1) * (x - z)) (z * (x ^ (n + 1) - z ^ (n + 1)))
    have e : M ^ (n + 1) * |x - z| + M * (((n : ℝ) + 1) * M ^ n * |x - z|)
        = (((n + 1 : ℕ) : ℝ) + 1) * M ^ (n + 1) * |x - z| := by
      push_cast
      ring
    rw [key, ← e]
    linarith

/-- `x^n ≤ n! δ^{-n} e^{δx}` for `x ≥ 0` and `δ > 0`. -/
theorem pow_le_factorial_mul_exp {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ n ≤ (n.factorial : ℝ) * (1 / δ) ^ n * Real.exp (δ * x) := by
  have hx' : 0 ≤ δ * x := mul_nonneg hδ.le hx
  have h1 : (δ * x) ^ n / (n.factorial : ℝ) ≤ Real.exp (δ * x) :=
    Real.pow_div_factorial_le_exp (x := δ * x) hx' n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have h2 : (δ * x) ^ n ≤ Real.exp (δ * x) * (n.factorial : ℝ) := (div_le_iff₀ hf).mp h1
  have hone : 1 / δ * (δ * x) = x := by
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
  have hd : (1 / δ) ^ n * (δ * x) ^ n = x ^ n := by
    rw [← mul_pow, hone]
  have hp : (0 : ℝ) ≤ (1 / δ) ^ n := pow_nonneg (one_div_nonneg.mpr hδ.le) n
  have h3 : (1 / δ) ^ n * (δ * x) ^ n
      ≤ (1 / δ) ^ n * (Real.exp (δ * x) * (n.factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 hp
  rw [hd] at h3
  have e : (1 / δ) ^ n * (Real.exp (δ * x) * (n.factorial : ℝ))
      = (n.factorial : ℝ) * (1 / δ) ^ n * Real.exp (δ * x) := by ring
  rw [e] at h3
  exact h3

/-! ## `K₀` and `I₀` at `e^{a₀ - y}` -/

theorem a0_eq : a0 = Real.log 2 + eulerW := rfl

/-- `|K₀(e^{a₀ - y}) - y| ≤ e^{a₀ - y}/2`. -/
theorem abs_besselK0_exp_sub_le (y : ℝ) :
    |besselK0 (Real.exp (a0 - y)) - y| ≤ Real.exp (a0 - y) / 2 := by
  have hE : 0 < Real.exp (a0 - y) := Real.exp_pos _
  have h := abs_besselK0_add_log_le hE
  have hl : Real.log (Real.exp (a0 - y) / 2) = a0 - y - Real.log 2 := by
    rw [Real.log_div hE.ne' two_ne_zero, Real.log_exp]
  have e : besselK0 (Real.exp (a0 - y)) + (a0 - y - Real.log 2) - eulerW
      = besselK0 (Real.exp (a0 - y)) - y := by
    linear_combination a0_eq
  rw [hl, e] at h
  exact h

/-- `I₀(t) - 1 ≤ t e^t` for `t > 0`. -/
theorem besselI0_sub_one_le {t : ℝ} (ht : 0 < t) : besselI0 t - 1 ≤ t * Real.exp t := by
  have h1 := besselI0_le_exp ht
  have h2 := Real.add_one_le_exp (-t)
  have hE : 0 < Real.exp t := Real.exp_pos t
  have h3 := mul_le_mul_of_nonneg_right h2 hE.le
  have e : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [e] at h3
  have e2 : (-t + 1) * Real.exp t = Real.exp t - t * Real.exp t := by ring
  rw [e2] at h3
  linarith

/-- `K₀(t) ≤ 1/t` for `t > 0`. -/
theorem besselK0_le_inv {t : ℝ} (ht : 0 < t) : besselK0 t ≤ 1 / t := by
  have h1 := besselK0_le_besselK1 ht
  have h2 := mul_besselK1_le_one ht
  have h3 := mul_le_mul_of_nonneg_right h1 ht.le
  have e : besselK1 t * t = t * besselK1 t := mul_comm (besselK1 t) t
  rw [e] at h3
  rw [le_div_iff₀ ht]
  exact le_trans h3 h2

/-- `I₀(t)^a K₀(t)^{a+d} ≤ t^{-(a+d)}` for `t > 0`. -/
theorem besselIK_le_inv_pow (a d : ℕ) {t : ℝ} (ht : 0 < t) :
    besselI0 t ^ a * besselK0 t ^ (a + d) ≤ (1 / t) ^ (a + d) := by
  have hIK := besselI0_mul_besselK0_le ht
  have hK := besselK0_le_inv ht
  have hK0 : 0 ≤ besselK0 t := besselK0_nonneg t
  have hI0 : 0 ≤ besselI0 t := (besselI0_pos t).le
  have hinv : 0 ≤ 1 / t := (one_div_pos.mpr ht).le
  have h1 : (besselI0 t * besselK0 t) ^ a ≤ (1 / t) ^ a :=
    pow_le_pow_left₀ (mul_nonneg hI0 hK0) hIK a
  have h2 : besselK0 t ^ d ≤ (1 / t) ^ d := pow_le_pow_left₀ hK0 hK d
  have h12 : (besselI0 t * besselK0 t) ^ a * besselK0 t ^ d ≤ (1 / t) ^ a * (1 / t) ^ d :=
    mul_le_mul h1 h2 (pow_nonneg hK0 d) (pow_nonneg hinv a)
  have eL : besselI0 t ^ a * besselK0 t ^ (a + d)
      = (besselI0 t * besselK0 t) ^ a * besselK0 t ^ d := by
    rw [pow_add (besselK0 t) a d, mul_pow (besselI0 t) (besselK0 t) a]
    ring
  have eR : (1 / t) ^ (a + d) = (1 / t) ^ a * (1 / t) ^ d := pow_add (1 / t) a d
  rw [eL, eR]
  exact h12

/-! ## The model integral -/

/-- `∫₀^∞ y^b e^{-sy} dy = b!/s^{b+1}` for `s > 0`. -/
theorem integral_pow_mul_exp_neg (b : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ y in Set.Ioi (0 : ℝ), y ^ b * Real.exp (-(s * y)) = (b.factorial : ℝ) / s ^ (b + 1) := by
  have hb : (0 : ℝ) < (b : ℝ) + 1 := Nat.cast_add_one_pos b
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hb hs
  have hfun : (fun t : ℝ => t ^ ((b : ℝ) + 1 - 1) * Real.exp (-(s * t)))
      = fun t : ℝ => t ^ b * Real.exp (-(s * t)) := by
    funext t
    show t ^ ((b : ℝ) + 1 - 1) * Real.exp (-(s * t)) = t ^ b * Real.exp (-(s * t))
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [hfun] at h
  have e : (1 / s) ^ ((b : ℝ) + 1) = (1 / s) ^ (b + 1) := by
    rw [← Nat.cast_add_one, Real.rpow_natCast]
  rw [h, Real.Gamma_nat_eq_factorial, e, one_div, inv_pow, div_eq_mul_inv,
    mul_comm ((s ^ (b + 1))⁻¹) (b.factorial : ℝ)]

/-- `y^b e^{-sy}` is integrable on `(0, ∞)` for `s > 0`. -/
theorem integrableOn_pow_mul_exp_neg (b : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun y : ℝ => y ^ b * Real.exp (-(s * y))) (Set.Ioi (0 : ℝ)) := by
  have h := integral_pow_mul_exp_neg b hs
  have hne : ∫ y in Set.Ioi (0 : ℝ), y ^ b * Real.exp (-(s * y)) ≠ 0 := by
    rw [h]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)) (pow_ne_zero (b + 1) hs.ne')
  exact Integrable.of_integral_ne_zero hne

/-! ## The bound for `y ≥ 0` -/

/-- The algebraic core of the bound for `I^{a'+1} K^{b'+2} - y^{b'+2}`. -/
theorem core_sub_pow_le {I K y t P M G1 G2 E : ℝ} (a' b' : ℕ)
    (hI1 : 1 ≤ I) (hIM : I ≤ M) (hI' : I - 1 ≤ t * M) (hK0 : 0 ≤ K) (hKP : K ≤ P)
    (hy : 0 ≤ y) (hyP : y ≤ P) (hKy : |K - y| ≤ t / 2) (ht : 0 ≤ t)
    (hG1 : P ^ (b' + 1) ≤ G1 * E) (hG2 : P ^ (b' + 1 + 1) ≤ G2 * E) :
    |I ^ (a' + 1) * K ^ (b' + 1 + 1) - y ^ (b' + 1 + 1)|
      ≤ (((a' : ℝ) + 1) * M ^ a' * M * G2 + (((b' + 1 : ℕ) : ℝ) + 1) / 2 * G1) * (t * E) := by
  have hI0 : 0 ≤ I := le_trans zero_le_one hI1
  have hM1 : 1 ≤ M := le_trans hI1 hIM
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have hP0 : 0 ≤ P := le_trans hy hyP
  have hca : (0 : ℝ) ≤ (a' : ℝ) + 1 := by positivity
  have hcb : (0 : ℝ) ≤ ((b' + 1 : ℕ) : ℝ) + 1 := by positivity
  have hA0 : |I ^ (a' + 1) - 1 ^ (a' + 1)| ≤ ((a' : ℝ) + 1) * M ^ a' * |I - 1| :=
    abs_pow_succ_sub_pow_succ_le hI0 hIM zero_le_one hM1 a'
  rw [one_pow, abs_of_nonneg (sub_nonneg.mpr hI1)] at hA0
  have hcA : 0 ≤ ((a' : ℝ) + 1) * M ^ a' := mul_nonneg hca (pow_nonneg hM0 a')
  have hA : |I ^ (a' + 1) - 1| ≤ ((a' : ℝ) + 1) * M ^ a' * (t * M) :=
    le_trans hA0 (mul_le_mul_of_nonneg_left hI' hcA)
  have hB0 : |K ^ (b' + 1 + 1) - y ^ (b' + 1 + 1)|
      ≤ (((b' + 1 : ℕ) : ℝ) + 1) * P ^ (b' + 1) * |K - y| :=
    abs_pow_succ_sub_pow_succ_le hK0 hKP hy hyP (b' + 1)
  have hcB : 0 ≤ (((b' + 1 : ℕ) : ℝ) + 1) * P ^ (b' + 1) :=
    mul_nonneg hcb (pow_nonneg hP0 (b' + 1))
  have hB : |K ^ (b' + 1 + 1) - y ^ (b' + 1 + 1)|
      ≤ (((b' + 1 : ℕ) : ℝ) + 1) * P ^ (b' + 1) * (t / 2) :=
    le_trans hB0 (mul_le_mul_of_nonneg_left hKy hcB)
  have hKn0 : 0 ≤ K ^ (b' + 1 + 1) := pow_nonneg hK0 (b' + 1 + 1)
  have hC : K ^ (b' + 1 + 1) ≤ P ^ (b' + 1 + 1) := pow_le_pow_left₀ hK0 hKP (b' + 1 + 1)
  have hAnn : 0 ≤ ((a' : ℝ) + 1) * M ^ a' * (t * M) := mul_nonneg hcA (mul_nonneg ht hM0)
  have h1 : |(I ^ (a' + 1) - 1) * K ^ (b' + 1 + 1)|
      ≤ ((a' : ℝ) + 1) * M ^ a' * (t * M) * P ^ (b' + 1 + 1) := by
    rw [abs_mul, abs_of_nonneg hKn0]
    exact mul_le_mul hA hC hKn0 hAnn
  have hT1 : ((a' : ℝ) + 1) * M ^ a' * (t * M) * P ^ (b' + 1 + 1)
      ≤ ((a' : ℝ) + 1) * M ^ a' * (t * M) * (G2 * E) := mul_le_mul_of_nonneg_left hG2 hAnn
  have ht2 : (0 : ℝ) ≤ t / 2 := by linarith
  have hT2 : (((b' + 1 : ℕ) : ℝ) + 1) * P ^ (b' + 1) * (t / 2)
      ≤ (((b' + 1 : ℕ) : ℝ) + 1) * (G1 * E) * (t / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG1 hcb) ht2
  have key : I ^ (a' + 1) * K ^ (b' + 1 + 1) - y ^ (b' + 1 + 1)
      = (I ^ (a' + 1) - 1) * K ^ (b' + 1 + 1) + (K ^ (b' + 1 + 1) - y ^ (b' + 1 + 1)) := by
    ring
  have h3 := abs_add_le ((I ^ (a' + 1) - 1) * K ^ (b' + 1 + 1))
    (K ^ (b' + 1 + 1) - y ^ (b' + 1 + 1))
  have e : ((a' : ℝ) + 1) * M ^ a' * (t * M) * (G2 * E)
        + (((b' + 1 : ℕ) : ℝ) + 1) * (G1 * E) * (t / 2)
      = (((a' : ℝ) + 1) * M ^ a' * M * G2 + (((b' + 1 : ℕ) : ℝ) + 1) / 2 * G1) * (t * E) := by
    ring
  rw [key, ← e]
  linarith

/-- The constant of `abs_besselIK_sub_pow_le`. -/
noncomputable def poleD (a' b' : ℕ) : ℝ :=
  (((a' : ℝ) + 1) * Real.exp (Real.exp a0) ^ a' * Real.exp (Real.exp a0)
      * (((b' + 1 + 1).factorial : ℝ) * (1 / (1 / 2 : ℝ)) ^ (b' + 1 + 1)
        * Real.exp (Real.exp a0 / 4))
    + (((b' + 1 : ℕ) : ℝ) + 1) / 2
      * (((b' + 1).factorial : ℝ) * (1 / (1 / 2 : ℝ)) ^ (b' + 1) * Real.exp (Real.exp a0 / 4)))
    * Real.exp a0

/-- `P^n ≤ (n! 2^n e^{c/4}) e^{y/2}` for `P = y + c/2`, `c = e^{a₀}`, `y ≥ 0`. -/
theorem shifted_pow_le (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (y + Real.exp a0 / 2) ^ n
      ≤ ((n.factorial : ℝ) * (1 / (1 / 2 : ℝ)) ^ n * Real.exp (Real.exp a0 / 4))
        * Real.exp (1 / 2 * y) := by
  have hc : 0 < Real.exp a0 := Real.exp_pos _
  have hP0 : 0 ≤ y + Real.exp a0 / 2 := by linarith
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hEsplit : Real.exp (Real.exp a0 / 4) * Real.exp (1 / 2 * y)
      = Real.exp (1 / 2 * (y + Real.exp a0 / 2)) := exp_mul_exp_of_add_eq (by ring)
  have h := pow_le_factorial_mul_exp hhalf n hP0
  rw [← hEsplit] at h
  have e : (n.factorial : ℝ) * (1 / (1 / 2 : ℝ)) ^ n
        * (Real.exp (Real.exp a0 / 4) * Real.exp (1 / 2 * y))
      = ((n.factorial : ℝ) * (1 / (1 / 2 : ℝ)) ^ n * Real.exp (Real.exp a0 / 4))
        * Real.exp (1 / 2 * y) := by ring
  rw [e] at h
  exact h

/-- For `y ≥ 0`: `|I₀(e^{a₀-y})^{a'+1} K₀(e^{a₀-y})^{b'+2} - y^{b'+2}| ≤ D e^{-y/2}`. -/
theorem abs_besselIK_sub_pow_le (a' b' : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    |besselI0 (Real.exp (a0 - y)) ^ (a' + 1) * besselK0 (Real.exp (a0 - y)) ^ (b' + 1 + 1)
        - y ^ (b' + 1 + 1)| ≤ poleD a' b' * Real.exp (-(1 / 2) * y) := by
  have ht : 0 < Real.exp (a0 - y) := Real.exp_pos _
  have hc : 0 < Real.exp a0 := Real.exp_pos _
  have htle : Real.exp (a0 - y) ≤ Real.exp a0 := Real.exp_le_exp.mpr (by linarith)
  have hI1 : 1 ≤ besselI0 (Real.exp (a0 - y)) := one_le_besselI0 _
  have hIM : besselI0 (Real.exp (a0 - y)) ≤ Real.exp (Real.exp a0) :=
    le_trans (besselI0_le_exp ht) (Real.exp_le_exp.mpr htle)
  have hI' : besselI0 (Real.exp (a0 - y)) - 1 ≤ Real.exp (a0 - y) * Real.exp (Real.exp a0) :=
    le_trans (besselI0_sub_one_le ht)
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htle) ht.le)
  have hK0 : 0 ≤ besselK0 (Real.exp (a0 - y)) := besselK0_nonneg _
  have hKy := abs_besselK0_exp_sub_le y
  have hKP : besselK0 (Real.exp (a0 - y)) ≤ y + Real.exp a0 / 2 := by
    have h := (abs_le.mp hKy).2
    linarith
  have hyP : y ≤ y + Real.exp a0 / 2 := by linarith
  have hcore := core_sub_pow_le (I := besselI0 (Real.exp (a0 - y)))
    (K := besselK0 (Real.exp (a0 - y))) (y := y) (t := Real.exp (a0 - y))
    (P := y + Real.exp a0 / 2) (M := Real.exp (Real.exp a0))
    (G1 := ((b' + 1).factorial : ℝ) * (1 / (1 / 2 : ℝ)) ^ (b' + 1) * Real.exp (Real.exp a0 / 4))
    (G2 := ((b' + 1 + 1).factorial : ℝ) * (1 / (1 / 2 : ℝ)) ^ (b' + 1 + 1)
      * Real.exp (Real.exp a0 / 4))
    (E := Real.exp (1 / 2 * y)) a' b' hI1 hIM hI' hK0 hKP hy hyP hKy ht.le
    (shifted_pow_le (b' + 1) hy) (shifted_pow_le (b' + 1 + 1) hy)
  have hTE : Real.exp (a0 - y) * Real.exp (1 / 2 * y)
      = Real.exp a0 * Real.exp (-(1 / 2) * y) := by
    have h1 : Real.exp (a0 - y) * Real.exp (1 / 2 * y) = Real.exp (a0 - 1 / 2 * y) :=
      exp_mul_exp_of_add_eq (by ring)
    have h2 : Real.exp a0 * Real.exp (-(1 / 2) * y) = Real.exp (a0 - 1 / 2 * y) :=
      exp_mul_exp_of_add_eq (by ring)
    rw [h1, h2]
  rw [hTE] at hcore
  refine le_trans hcore (le_of_eq ?_)
  unfold poleD
  ring

/-! ## The bound for `y ≤ 0` -/

/-- The constant of `besselIK_mul_exp_le_of_nonpos`. -/
noncomputable def poleDneg (b' : ℕ) : ℝ := (1 / Real.exp a0) ^ b' * Real.exp (-(2 * a0))

/-- For `y ≤ 0`, if `I₀^a K₀^{b'+2} ≤ t^{-(b'+2)}`: `H(y) e^{-y} ≤ D' e^y` (`D' = poleDneg b'`). -/
theorem besselIK_mul_exp_le_of_nonpos {a : ℕ} (b' : ℕ)
    (hab : ∀ t : ℝ, 0 < t →
      besselI0 t ^ a * besselK0 t ^ (b' + 1 + 1) ≤ (1 / t) ^ (b' + 1 + 1))
    {y : ℝ} (hy : y ≤ 0) :
    |besselI0 (Real.exp (a0 - y)) ^ a * besselK0 (Real.exp (a0 - y)) ^ (b' + 1 + 1)|
        * Real.exp (-y) ≤ poleDneg b' * Real.exp y := by
  have ht : 0 < Real.exp (a0 - y) := Real.exp_pos _
  have hc : 0 < Real.exp a0 := Real.exp_pos _
  have hct : Real.exp a0 ≤ Real.exp (a0 - y) := Real.exp_le_exp.mpr (by linarith)
  have h := hab (Real.exp (a0 - y)) ht
  have hnn : 0 ≤ besselI0 (Real.exp (a0 - y)) ^ a
      * besselK0 (Real.exp (a0 - y)) ^ (b' + 1 + 1) :=
    mul_nonneg (pow_nonneg (besselI0_pos _).le a) (pow_nonneg (besselK0_nonneg _) (b' + 1 + 1))
  have hinv : 1 / Real.exp (a0 - y) ≤ 1 / Real.exp a0 := one_div_le_one_div_of_le hc hct
  have hinv0 : 0 ≤ 1 / Real.exp (a0 - y) := (one_div_pos.mpr ht).le
  have hpow : (1 / Real.exp (a0 - y)) ^ b' ≤ (1 / Real.exp a0) ^ b' :=
    pow_le_pow_left₀ hinv0 hinv b'
  have esplit : (1 / Real.exp (a0 - y)) ^ (b' + 1 + 1)
      = (1 / Real.exp (a0 - y)) ^ b'
        * (1 / Real.exp (a0 - y) * (1 / Real.exp (a0 - y))) := by ring
  have esq : 1 / Real.exp (a0 - y) * (1 / Real.exp (a0 - y))
      = Real.exp (-(2 * a0)) * Real.exp (2 * y) := by
    have e1 : 1 / Real.exp (a0 - y) = Real.exp (-(a0 - y)) := by
      rw [one_div, Real.exp_neg]
    have h1 : Real.exp (-(a0 - y)) * Real.exp (-(a0 - y)) = Real.exp (-(2 * a0) + 2 * y) :=
      exp_mul_exp_of_add_eq (by ring)
    have h2 : Real.exp (-(2 * a0)) * Real.exp (2 * y) = Real.exp (-(2 * a0) + 2 * y) :=
      exp_mul_exp_of_add_eq rfl
    rw [e1, h1, h2]
  have hsq0 : 0 ≤ 1 / Real.exp (a0 - y) * (1 / Real.exp (a0 - y)) := mul_nonneg hinv0 hinv0
  have h2 : (1 / Real.exp (a0 - y)) ^ (b' + 1 + 1)
      ≤ (1 / Real.exp a0) ^ b' * (Real.exp (-(2 * a0)) * Real.exp (2 * y)) := by
    rw [esplit, ← esq]
    exact mul_le_mul_of_nonneg_right hpow hsq0
  have hEy : 0 < Real.exp (-y) := Real.exp_pos _
  have h3 := mul_le_mul_of_nonneg_right (le_trans h h2) hEy.le
  have e2y : Real.exp (2 * y) * Real.exp (-y) = Real.exp y := exp_mul_exp_of_add_eq (by ring)
  have e : (1 / Real.exp a0) ^ b' * (Real.exp (-(2 * a0)) * Real.exp (2 * y)) * Real.exp (-y)
      = (1 / Real.exp a0) ^ b' * Real.exp (-(2 * a0))
        * (Real.exp (2 * y) * Real.exp (-y)) := by ring
  rw [e, e2y] at h3
  rw [abs_of_nonneg hnn]
  unfold poleDneg
  exact h3

end Tower.RV6
