import Mathlib
import Tower.RV6.BPGammaRatio
import Tower.RV6.Dirichlet

/-!
# RungBP, step 5: `Q(s) = 1 + ζ(3) s³/12 + ζ(5) s⁵/80 + O(s⁶)`

* `|log((1 + x)/(1 - x)) - 2x - 2x³/3 - 2x⁵/5| ≤ 4|x|⁷` for `|x| ≤ 1/2`
  (Mathlib's `abs_log_sub_add_sum_range_le` at `±x`, six terms).
* With `x = u/(k + 1)`, `0 ≤ u ≤ 1/2`, and `zN m = ∑_{k ≥ 0} (k + 1)^{-m}`:
  `|∑_k φ_k(u) - (2/3) u³ zN 3 - (2/5) u⁵ zN 5| ≤ 4 u⁷ zN 7` (`tsum_phiK_expansion`);
  at `u = s/2`: `|ℓ(s) - s³ zN 3/12 - s⁵ zN 5/80| ≤ s⁷ zN 7/32` (`ellQ_expansion`).
* `zN m ≤ π²/6 < 2` for `m ≥ 2`, `|e^y - 1 - y| ≤ y²` for `|y| ≤ 1`:
  `|Q(s) - 1 - s³ zN 3/12 - s⁵ ζ(5)/80| ≤ s⁶` on `0 < s ≤ 1` (`expQ_expansion`).
-/

namespace Tower.RV6

open Real

theorem abs_log_ratio_sub_le7 {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log ((1 + x) / (1 - x)) - 2 * x - 2 * x ^ 3 / 3 - 2 * x ^ 5 / 5| ≤ 4 * |x| ^ 7 := by
  have hx1' : |x| < 1 := by linarith
  have h1 : |(∑ i ∈ Finset.range 6, x ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - x)|
      ≤ |x| ^ 7 / (1 - |x|) := Real.abs_log_sub_add_sum_range_le hx1' 6
  have h2 : |(∑ i ∈ Finset.range 6, (-x) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -x)|
      ≤ |-x| ^ 7 / (1 - |-x|) := Real.abs_log_sub_add_sum_range_le (by rwa [abs_neg]) 6
  have e1 : (∑ i ∈ Finset.range 6, x ^ (i + 1) / ((i : ℝ) + 1))
      = x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 + x ^ 6 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat]
    ring
  have e2 : (∑ i ∈ Finset.range 6, (-x) ^ (i + 1) / ((i : ℝ) + 1))
      = -x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 + x ^ 6 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat]
    ring
  rw [e1] at h1
  rw [e2, abs_neg, sub_neg_eq_add] at h2
  have hx1 : 0 < 1 - x := by
    have := le_abs_self x
    linarith
  have hx2 : 0 < 1 + x := by
    have := neg_abs_le x
    linarith
  have hb : |x| ^ 7 / (1 - |x|) ≤ 2 * |x| ^ 7 := by
    rw [div_le_iff₀ (show (0 : ℝ) < 1 - |x| by linarith)]
    have h7 : 0 ≤ |x| ^ 7 := by positivity
    have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - |x| by linarith) h7
    nlinarith [h]
  rw [Real.log_div hx2.ne' hx1.ne']
  have e : Real.log (1 + x) - Real.log (1 - x) - 2 * x - 2 * x ^ 3 / 3 - 2 * x ^ 5 / 5
      = (-x + x ^ 2 / 2 - x ^ 3 / 3 + x ^ 4 / 4 - x ^ 5 / 5 + x ^ 6 / 6 + Real.log (1 + x))
        - (x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 + x ^ 6 / 6 + Real.log (1 - x)) := by
    ring
  rw [e]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hb]

/-- `|φ_k(u) - (2/3) u³/(k+1)³ - (2/5) u⁵/(k+1)⁵| ≤ 4 u⁷/(k+1)⁷` for `0 ≤ u ≤ 1/2`. -/
theorem abs_phiK_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (k : ℕ) :
    |phiK u k - 2 / 3 * u ^ 3 * (1 / ((k : ℝ) + 1) ^ 3)
        - 2 / 5 * u ^ 5 * (1 / ((k : ℝ) + 1) ^ 5)|
      ≤ 4 * u ^ 7 * (1 / ((k : ℝ) + 1) ^ 7) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hx0 : 0 ≤ u / ((k : ℝ) + 1) := div_nonneg hu0 hk0.le
  have hxu : u / ((k : ℝ) + 1) ≤ u := div_le_self hu0 hk1
  have h := abs_log_ratio_sub_le7 (x := u / ((k : ℝ) + 1)) (by rw [abs_of_nonneg hx0]; linarith)
  rw [abs_of_nonneg hx0] at h
  have e : phiK u k - 2 / 3 * u ^ 3 * (1 / ((k : ℝ) + 1) ^ 3)
        - 2 / 5 * u ^ 5 * (1 / ((k : ℝ) + 1) ^ 5)
      = Real.log ((1 + u / ((k : ℝ) + 1)) / (1 - u / ((k : ℝ) + 1))) - 2 * (u / ((k : ℝ) + 1))
        - 2 * (u / ((k : ℝ) + 1)) ^ 3 / 3 - 2 * (u / ((k : ℝ) + 1)) ^ 5 / 5 := by
    rw [phiK_eq]
    simp only [div_pow]
    ring
  have e7 : 4 * (u / ((k : ℝ) + 1)) ^ 7 = 4 * u ^ 7 * (1 / ((k : ℝ) + 1) ^ 7) := by
    rw [div_pow]
    ring
  rw [e, ← e7]
  exact h

/-- `zN m = ∑_{k ≥ 0} 1/(k + 1)^m`. -/
noncomputable def zN (m : ℕ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ m

theorem summable_zN {m : ℕ} (hm : 2 ≤ m) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ m) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < m))
  refine h.congr fun k => ?_
  simp only [Nat.cast_add, Nat.cast_one]

theorem zN_nonneg (m : ℕ) : 0 ≤ zN m :=
  tsum_nonneg fun k => by positivity

theorem zN_two : zN 2 = π ^ 2 / 6 := by
  rw [zN, ← tsum_inv_pow_two_shift]
  exact tsum_congr fun k => by simp only [Nat.cast_add, Nat.cast_one]

theorem zN_five : zN 5 = zeta5 := by
  rw [zN, ← tsum_inv_pow_five_shift]
  exact tsum_congr fun k => by simp only [Nat.cast_add, Nat.cast_one]

theorem zN_le_two {m : ℕ} (hm : 2 ≤ m) : zN m ≤ 2 := by
  have hle : zN m ≤ zN 2 := by
    refine Summable.tsum_le_tsum (fun k => ?_) (summable_zN hm) (summable_zN le_rfl)
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hk1 hm)
  rw [zN_two] at hle
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  nlinarith

/-- `|∑_k φ_k(u) - (2/3) u³ zN 3 - (2/5) u⁵ zN 5| ≤ 4 u⁷ zN 7` for `0 ≤ u ≤ 1/2`. -/
theorem tsum_phiK_expansion {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    |∑' k, phiK u k - 2 / 3 * u ^ 3 * zN 3 - 2 / 5 * u ^ 5 * zN 5| ≤ 4 * u ^ 7 * zN 7 := by
  have hS := summable_phiK hu0 (by linarith : u < 1)
  have hA := (summable_zN (by norm_num : 2 ≤ 3)).mul_left (2 / 3 * u ^ 3)
  have hB := (summable_zN (by norm_num : 2 ≤ 5)).mul_left (2 / 5 * u ^ 5)
  have hC := (summable_zN (by norm_num : 2 ≤ 7)).mul_left (4 * u ^ 7)
  have hR := (hS.sub hA).sub hB
  have hsum : ∑' k, (phiK u k - 2 / 3 * u ^ 3 * (1 / ((k : ℝ) + 1) ^ 3)
        - 2 / 5 * u ^ 5 * (1 / ((k : ℝ) + 1) ^ 5))
      = ∑' k, phiK u k - 2 / 3 * u ^ 3 * zN 3 - 2 / 5 * u ^ 5 * zN 5 := by
    rw [(hS.sub hA).tsum_sub hB, hS.tsum_sub hA, tsum_mul_left, tsum_mul_left, zN, zN]
  have hsumC : ∑' k : ℕ, 4 * u ^ 7 * (1 / ((k : ℝ) + 1) ^ 7) = 4 * u ^ 7 * zN 7 := by
    rw [tsum_mul_left, zN]
  have hle := fun k => abs_le.1 (abs_phiK_sub_le hu0 hu1 k)
  have h1 := Summable.tsum_le_tsum (fun k => (hle k).2) hR hC
  have h2 := Summable.tsum_le_tsum (fun k => (hle k).1) hC.neg hR
  rw [tsum_neg] at h2
  rw [hsum, hsumC] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- `|ℓ(s) - s³ zN 3/12 - s⁵ zN 5/80| ≤ s⁷ zN 7/32` for `0 < s ≤ 1`. -/
theorem ellQ_expansion {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    |ellQ s - s ^ 3 / 12 * zN 3 - s ^ 5 / 80 * zN 5| ≤ s ^ 7 / 32 * zN 7 := by
  have h := tsum_phiK_expansion (u := s / 2) (by positivity) (by linarith)
  have e1 : s ^ 3 / 12 * zN 3 = 2 / 3 * (s / 2) ^ 3 * zN 3 := by ring
  have e2 : s ^ 5 / 80 * zN 5 = 2 / 5 * (s / 2) ^ 5 * zN 5 := by ring
  have e3 : s ^ 7 / 32 * zN 7 = 4 * (s / 2) ^ 7 * zN 7 := by ring
  rw [e1, e2, e3, ellQ]
  exact h

/-- `|exp ℓ(s) - 1 - s³ zN 3/12 - s⁵ zN 5/80| ≤ s⁶` for `0 < s ≤ 1`. -/
theorem expQ_expansion {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    |Real.exp (ellQ s) - 1 - s ^ 3 / 12 * zN 3 - s ^ 5 / 80 * zN 5| ≤ s ^ 6 := by
  have h := abs_le.1 (ellQ_expansion hs0 hs1)
  have z3 := zN_le_two (by norm_num : 2 ≤ 3)
  have z5 := zN_le_two (by norm_num : 2 ≤ 5)
  have z7 := zN_le_two (by norm_num : 2 ≤ 7)
  have s3 : 0 ≤ s ^ 3 := by positivity
  have s5 : 0 ≤ s ^ 5 := by positivity
  have s7 : 0 ≤ s ^ 7 := by positivity
  have hp3 : s ^ 3 * zN 3 ≤ s ^ 3 * 2 := mul_le_mul_of_nonneg_left z3 s3
  have hp5 : s ^ 5 * zN 5 ≤ s ^ 5 * 2 := mul_le_mul_of_nonneg_left z5 s5
  have hp7 : s ^ 7 * zN 7 ≤ s ^ 7 * 2 := mul_le_mul_of_nonneg_left z7 s7
  have hq3 : 0 ≤ s ^ 3 * zN 3 := mul_nonneg s3 (zN_nonneg 3)
  have hq5 : 0 ≤ s ^ 5 * zN 5 := mul_nonneg s5 (zN_nonneg 5)
  have hq7 : 0 ≤ s ^ 7 * zN 7 := mul_nonneg s7 (zN_nonneg 7)
  have h53 : s ^ 5 ≤ s ^ 3 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  have h73 : s ^ 7 ≤ s ^ 3 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  have h76 : s ^ 7 ≤ s ^ 6 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  have h31 : s ^ 3 ≤ 1 := pow_le_one₀ hs0.le hs1
  have hl : |ellQ s| ≤ s ^ 3 / 2 := by
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hl1 : |ellQ s| ≤ 1 := by linarith
  have he := abs_le.1 (Real.abs_exp_sub_one_sub_id_le hl1)
  have hsq : ellQ s ^ 2 ≤ s ^ 6 / 4 := by
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hl 2
    rw [sq_abs] at h2
    have e : (s ^ 3 / 2) ^ 2 = s ^ 6 / 4 := by ring
    linarith
  rw [abs_le]
  constructor <;> linarith [he.1, he.2, h.1, h.2]

/-- **`Q(s) = e^{a₀ s} s j(s) = 1 + zN 3 s³/12 + ζ(5) s⁵/80 + O(s⁶)`**: the error is at most
`s⁶` on `0 < s ≤ 1`. -/
theorem qQ_expansion {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    |Real.exp (a0 * s) * (s * jS s) - 1 - s ^ 3 / 12 * zN 3 - s ^ 5 / 80 * zeta5| ≤ s ^ 6 := by
  rw [expQ_eq hs0 (by linarith), ← zN_five]
  exact expQ_expansion hs0 hs1

end Tower.RV6
