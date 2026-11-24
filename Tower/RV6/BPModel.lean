import Mathlib
import Tower.RV6.BPLamPhi
import Tower.RV6.PoleM
import Tower.RV6.BesselL5
import Tower.RV6.HankelDom
import Tower.RV6.ZeroG

/-!
# RungBP, step 6: the model of `θ²f` and `θg` near `0`

On `0 < t ≤ 1`, with `Lc(t) = log(c/t) = a₀ - log t` and `E(t) = 1 + log(2/t)`:

* `0 < a₀ ≤ Lc(t) ≤ E(t)` (`a₀ = log 2 - γ ∈ (0.026, 0.194)`);
* `|K₀ - Lc| ≤ t/2`, `|tK₁ - 1| ≤ t`, `|I₀ - 1| ≤ e t`, `|tI₁| ≤ B₁ t`;
* `|θ²f - 6 Lc| ≤ C t E³` (`thF2_model`) and `|θg + 2 Lc| ≤ C t E²` (`thG1_model`), from the identities
  `θ²f - 6Lc = 6(I₀-1)K₀(tK₁)² + 6(K₀-Lc)(tK₁)² + 6Lc(tK₁-1)(tK₁+1) - 6(tI₁)K₀²(tK₁) + 4t²I₀K₀³` and
  `θg + 2Lc = 2I₀(tI₁)K₀² - 2(I₀-1)(I₀+1)K₀(tK₁) - 2(K₀-Lc)(tK₁) - 2Lc(tK₁-1)`, proved over real variables.
-/

namespace Tower.RV6

open Real

/-- `log(c/t) = a₀ - log t`, `c = e^{a₀}`. -/
noncomputable def Lc (t : ℝ) : ℝ := a0 - Real.log t

/-- `E(t) = 1 + log(2/t)`. -/
noncomputable def Eb (t : ℝ) : ℝ := 1 + Real.log (2 / t)

theorem a0_pos : 0 < a0 := by
  rw [a0_eq_gamma]
  have h1 := Real.log_two_gt_d9
  have h2 := Real.eulerMascheroniConstant_lt_two_thirds
  norm_num at h1
  linarith

theorem a0_lt_one_add_log_two : a0 < 1 + Real.log 2 := by
  rw [a0_eq_gamma]
  have h := Real.one_half_lt_eulerMascheroniConstant
  linarith

theorem one_le_Eb {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ Eb t := one_le_log_term ht ht1

theorem Lc_pos {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 0 < Lc t := by
  have h := Real.log_nonpos ht.le ht1
  have h0 := a0_pos
  unfold Lc
  linarith

theorem Lc_le_Eb {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : Lc t ≤ Eb t := by
  have h := a0_lt_one_add_log_two
  unfold Lc Eb
  rw [Real.log_div (by norm_num) ht.ne']
  linarith

theorem abs_Lc_le_Eb {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : |Lc t| ≤ Eb t := by
  rw [abs_of_pos (Lc_pos ht ht1)]
  exact Lc_le_Eb ht ht1

theorem abs_besselK0_sub_Lc {t : ℝ} (ht : 0 < t) : |besselK0 t - Lc t| ≤ t / 2 := by
  have h := abs_besselK0_add_log_le ht
  have e : besselK0 t - Lc t = besselK0 t + Real.log (t / 2) - eulerW := by
    unfold Lc
    rw [a0, Real.log_div ht.ne' (by norm_num)]
    ring
  rw [e]
  exact h

theorem abs_mul_besselK1_sub_one {t : ℝ} (ht : 0 < t) : |t * besselK1 t - 1| ≤ t := by
  have h1 := mul_besselK1_le_one ht
  have h2 := exp_neg_le_mul_besselK1 ht
  have h3 := Real.add_one_le_exp (-t)
  rw [abs_le]
  constructor <;> linarith

theorem abs_mul_besselK1_le_one {t : ℝ} (ht : 0 < t) : |t * besselK1 t| ≤ 1 := by
  have h1 := mul_besselK1_le_one ht
  have h2 := exp_neg_le_mul_besselK1 ht
  have h3 := Real.exp_pos (-t)
  rw [abs_of_nonneg (by linarith)]
  exact h1

theorem abs_besselI0_sub_one {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |besselI0 t - 1| ≤ Real.exp 1 * t := by
  have h1 := besselI0_sub_one_le ht
  have h2 := one_le_besselI0 t
  have h3 : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.2 ht1
  have h4 := mul_le_mul_of_nonneg_left h3 ht.le
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem abs_mul_besselI1_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |t * besselI1 t| ≤ Bser 1 * t := by
  have h1 := besselI1_le_mul ht.le ht1
  have h2 := besselI1_nonneg ht.le
  have hB := Bser_one_nonneg
  rw [abs_of_nonneg (mul_nonneg ht.le h2)]
  have h3 := mul_le_mul_of_nonneg_left ht1 (mul_nonneg ht.le hB)
  calc t * besselI1 t ≤ t * (t * Bser 1) := mul_le_mul_of_nonneg_left h1 ht.le
    _ ≤ Bser 1 * t := by nlinarith

theorem abs_mul_le_of {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- The model bound for `θ²f` over real variables. -/
theorem model_F_bound {t I b K k L E e1 B : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hE : 1 ≤ E)
    (he1 : 0 ≤ e1) (hB : 0 ≤ B) (hI : |I| ≤ e1) (hIa : |I - 1| ≤ e1 * t) (hb : |b| ≤ B * t)
    (hK : |K| ≤ E) (hKa : |K - L| ≤ t / 2) (hk : |k| ≤ 1) (hka : |k - 1| ≤ t) (hL : |L| ≤ E) :
    |2 * ((-3) * (b * K ^ 2 * k) + 3 * (I * K * k ^ 2)) + 4 * (t ^ 2 * (I * K ^ 3)) - 6 * L|
      ≤ (10 * e1 + 15 + 6 * B) * t * E ^ 3 := by
  have e : 2 * ((-3) * (b * K ^ 2 * k) + 3 * (I * K * k ^ 2)) + 4 * (t ^ 2 * (I * K ^ 3)) - 6 * L
      = 6 * ((I - 1) * K * k ^ 2) + 6 * ((K - L) * k ^ 2) + 6 * (L * (k - 1) * (k + 1))
        - 6 * (b * K ^ 2 * k) + 4 * (t ^ 2 * (I * K ^ 3)) := by ring
  have hk2 : |k ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hk
  have hk1 : |k + 1| ≤ 2 := (abs_add_le k 1).trans (by rw [abs_one]; linarith)
  have hK2 : |K ^ 2| ≤ E ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hK 2
  have hK3 : |K ^ 3| ≤ E ^ 3 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hK 3
  have ht2 : |t ^ 2| ≤ t := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have a1 : |(I - 1) * K * k ^ 2| ≤ e1 * t * E * 1 := abs_mul_le_of (abs_mul_le_of hIa hK) hk2
  have a2 : |(K - L) * k ^ 2| ≤ t / 2 * 1 := abs_mul_le_of hKa hk2
  have a3 : |L * (k - 1) * (k + 1)| ≤ E * t * 2 := abs_mul_le_of (abs_mul_le_of hL hka) hk1
  have a4 : |b * K ^ 2 * k| ≤ B * t * E ^ 2 * 1 := abs_mul_le_of (abs_mul_le_of hb hK2) hk
  have a5 : |t ^ 2 * (I * K ^ 3)| ≤ t * (e1 * E ^ 3) := abs_mul_le_of ht2 (abs_mul_le_of hI hK3)
  have hE2 : E ≤ E ^ 3 := by nlinarith
  have hE3 : E ^ 2 ≤ E ^ 3 := by nlinarith
  have hE4 : 1 ≤ E ^ 3 := by nlinarith
  have s1 := mul_le_mul_of_nonneg_left hE2 (mul_nonneg he1 ht.le)
  have s2 := mul_le_mul_of_nonneg_left hE3 (mul_nonneg hB ht.le)
  have s3 := mul_le_mul_of_nonneg_left hE4 ht.le
  have s4 := mul_le_mul_of_nonneg_left hE2 ht.le
  rw [e]
  rw [abs_le] at a1 a2 a3 a4 a5 ⊢
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, s1, s2, s3, s4]

theorem thF2_eq_alg (t : ℝ) :
    thF2 t = 2 * ((-3) * ((t * besselI1 t) * besselK0 t ^ 2 * (t * besselK1 t))
      + 3 * (besselI0 t * besselK0 t * (t * besselK1 t) ^ 2))
      + 4 * (t ^ 2 * (besselI0 t * besselK0 t ^ 3)) := rfl

/-- **`|θ²f - 6 log(c/t)| ≤ C t E³`** on `(0, 1]`. -/
theorem thF2_model : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
    |thF2 t - 6 * Lc t| ≤ C * t * Eb t ^ 3 :=
  ⟨10 * Real.exp 1 + 15 + 6 * Bser 1, fun t ht ht1 => by
    rw [thF2_eq_alg]
    exact model_F_bound ht ht1 (one_le_Eb ht ht1) (Real.exp_pos 1).le Bser_one_nonneg
      (ity_besselI0.2.1 t ht ht1) (abs_besselI0_sub_one ht ht1) (abs_mul_besselI1_le ht ht1)
      (kty_besselK0.2.1 t ht ht1) (abs_besselK0_sub_Lc ht) (abs_mul_besselK1_le_one ht)
      (abs_mul_besselK1_sub_one ht) (abs_Lc_le_Eb ht ht1)⟩

/-- The model bound for `θg` over real variables. -/
theorem model_G_bound {t I b K k L E e1 B : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hE : 1 ≤ E)
    (he1 : 0 ≤ e1) (hB : 0 ≤ B) (hI : |I| ≤ e1) (hIa : |I - 1| ≤ e1 * t) (hb : |b| ≤ B * t)
    (hK : |K| ≤ E) (hKa : |K - L| ≤ t / 2) (hk : |k| ≤ 1) (hka : |k - 1| ≤ t) (hL : |L| ≤ E) :
    |2 * (I * b * K ^ 2) + (-2) * (I ^ 2 * K * k) + 2 * L|
      ≤ (2 * e1 * B + 2 * e1 * (e1 + 1) + 3) * t * E ^ 2 := by
  have e : 2 * (I * b * K ^ 2) + (-2) * (I ^ 2 * K * k) + 2 * L
      = 2 * (I * b * K ^ 2) - 2 * ((I - 1) * (I + 1) * K * k) - 2 * ((K - L) * k)
        - 2 * (L * (k - 1)) := by ring
  have hI1 : |I + 1| ≤ e1 + 1 := (abs_add_le I 1).trans (by rw [abs_one]; linarith)
  have hK2 : |K ^ 2| ≤ E ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hK 2
  have a1 : |I * b * K ^ 2| ≤ e1 * (B * t) * E ^ 2 := abs_mul_le_of (abs_mul_le_of hI hb) hK2
  have a2 : |(I - 1) * (I + 1) * K * k| ≤ e1 * t * (e1 + 1) * E * 1 :=
    abs_mul_le_of (abs_mul_le_of (abs_mul_le_of hIa hI1) hK) hk
  have a3 : |(K - L) * k| ≤ t / 2 * 1 := abs_mul_le_of hKa hk
  have a4 : |L * (k - 1)| ≤ E * t := abs_mul_le_of hL hka
  have hE2 : E ≤ E ^ 2 := by nlinarith
  have hE4 : 1 ≤ E ^ 2 := by nlinarith
  have s1 := mul_le_mul_of_nonneg_left hE2 (mul_nonneg (mul_nonneg he1 (by linarith : (0 : ℝ) ≤ e1 + 1)) ht.le)
  have s3 := mul_le_mul_of_nonneg_left hE4 ht.le
  have s4 := mul_le_mul_of_nonneg_left hE2 ht.le
  rw [e]
  rw [abs_le] at a1 a2 a3 a4 ⊢
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, s1, s3, s4]

theorem thG1_eq_alg (t : ℝ) :
    thG1 t = 2 * (besselI0 t * (t * besselI1 t) * besselK0 t ^ 2)
      + (-2) * (besselI0 t ^ 2 * besselK0 t * (t * besselK1 t)) := rfl

/-- **`|θg + 2 log(c/t)| ≤ C t E²`** on `(0, 1]`. -/
theorem thG1_model : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
    |thG1 t + 2 * Lc t| ≤ C * t * Eb t ^ 2 :=
  ⟨2 * Real.exp 1 * Bser 1 + 2 * Real.exp 1 * (Real.exp 1 + 1) + 3, fun t ht ht1 => by
    rw [thG1_eq_alg]
    exact model_G_bound ht ht1 (one_le_Eb ht ht1) (Real.exp_pos 1).le Bser_one_nonneg
      (ity_besselI0.2.1 t ht ht1) (abs_besselI0_sub_one ht ht1) (abs_mul_besselI1_le ht ht1)
      (kty_besselK0.2.1 t ht ht1) (abs_besselK0_sub_Lc ht) (abs_mul_besselK1_le_one ht)
      (abs_mul_besselK1_sub_one ht) (abs_Lc_le_Eb ht ht1)⟩

/-- `|θ²f| ≤ C E³` on `(0, 1]`. -/
theorem abs_thF2_le_log : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → |thF2 t| ≤ C * Eb t ^ 3 := by
  obtain ⟨C, hC⟩ := thF2_model
  refine ⟨|C| + 6, fun t ht ht1 => ?_⟩
  have h := hC t ht ht1
  have hE := one_le_Eb ht ht1
  have hL := abs_Lc_le_Eb ht ht1
  have hE3 : Eb t ≤ Eb t ^ 3 := le_self_pow₀ hE (by norm_num)
  have hE0 : 0 ≤ Eb t ^ 3 := pow_nonneg (by linarith) 3
  have h1 : C * t * Eb t ^ 3 ≤ |C| * Eb t ^ 3 := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg ht.le hE0)
    have h2 := mul_le_mul_of_nonneg_left ht1 (mul_nonneg (abs_nonneg C) hE0)
    nlinarith
  calc |thF2 t| = |(thF2 t - 6 * Lc t) + 6 * Lc t| := by
        congr 1
        ring
    _ ≤ |thF2 t - 6 * Lc t| + |6 * Lc t| := abs_add_le _ _
    _ ≤ (|C| + 6) * Eb t ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
        nlinarith

/-- `|θg| ≤ C E²` on `(0, 1]`. -/
theorem abs_thG1_le_log : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → |thG1 t| ≤ C * Eb t ^ 2 := by
  obtain ⟨C, hC⟩ := thG1_model
  refine ⟨|C| + 2, fun t ht ht1 => ?_⟩
  have h := hC t ht ht1
  have hE := one_le_Eb ht ht1
  have hL := abs_Lc_le_Eb ht ht1
  have hE2 : Eb t ≤ Eb t ^ 2 := by nlinarith
  have hE0 : 0 ≤ Eb t ^ 2 := by positivity
  have h1 : C * t * Eb t ^ 2 ≤ |C| * Eb t ^ 2 := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg ht.le hE0)
    have h2 := mul_le_mul_of_nonneg_left ht1 (mul_nonneg (abs_nonneg C) hE0)
    nlinarith
  calc |thG1 t| = |(thG1 t + 2 * Lc t) + -(2 * Lc t)| := by
        congr 1
        ring
    _ ≤ |thG1 t + 2 * Lc t| + |-(2 * Lc t)| := abs_add_le _ _
    _ ≤ (|C| + 2) * Eb t ^ 2 := by
        rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith

end Tower.RV6
