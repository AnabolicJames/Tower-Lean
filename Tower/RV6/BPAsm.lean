import Mathlib
import Tower.RV6.BPD
import Tower.RV6.ZhouG
import Tower.RV6.RungA2M
import Tower.RV6.BPLamPhi
import Tower.RV6.BPQexp
import Tower.RV6.BPPhi
import Tower.RV6.BPLam

/-!
# RungBP assembled; RV(6) without hypotheses

With `R = s j(s)`, `Q = e^{a₀ s} R`, `x = a₀ s`:
* `R (3/5) s M₃₅ = 72 Q/s⁵ + (3/5) s Q E₁`, `|E₁| ≤ C` (RungA2M);
* `j H_m = 24 Q (Φ - E)/s⁴ + E₂` (`2Λ(0) = Φ - s T₁ - E`), `|E₂| ≤ C s`;
* `pairS - 72/s⁵ = R (4/5) P + B₂ + B₃ + Err` (`pairS_decomp`), `B₂ → -(3/5)ζ(5)`, `B₃ → (3/4)ζ(5)`, `Err → 0`.
Hence `pairS(s) - 72/s⁵ → R₆₂/2 + (3/20) ζ(5)` (`rungBP`) and `μ₆ = 648/π⁶ L(f,5)` (`rv6`).
-/

namespace Tower.RV6

open Real MeasureTheory Set Filter Topology

theorem lamS_zero_le {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) : 0 ≤ lamS s 0 ∧ lamS s 0 ≤ s ^ 2 / 2 := by
  have hb := fun n : ℕ => lam_term_le h0 h2 (by norm_num : (-1 : ℝ) ≤ 0) n
  refine ⟨tsum_nonneg fun n => (hb n).1, ?_⟩
  have hle : lamS s 0 ≤ ∑' n : ℕ, s ^ 2 / 4 * (1 / ((n : ℝ) + 1) ^ 2) :=
    Summable.tsum_le_tsum (fun n => (hb n).2) (summable_lam_term h0 h2 (by norm_num))
      ((summable_zN (m := 2) le_rfl).mul_left _)
  rw [tsum_mul_left] at hle
  have hz : zN 2 ≤ 2 := zN_le_two le_rfl
  have e : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 = zN 2 := rfl
  rw [e] at hle
  nlinarith [sq_nonneg s]

theorem t1S_le {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) : 0 ≤ t1S s ∧ t1S s ≤ s ^ 2 / 2 := by
  have hb : ∀ n : ℕ, bk s (n + 1) ^ 2 / (4 * ((n : ℝ) + 1) ^ 2) ≤ s ^ 2 / 4 * (1 / ((n : ℝ) + 1) ^ 2) :=
    fun n => by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hd : 1 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith
      exact (div_le_self (sq_nonneg _) hd).trans (bk_sq_le h0 h2 n)
  refine ⟨tsum_nonneg fun n => div_nonneg (sq_nonneg _) (by positivity), ?_⟩
  have hle : t1S s ≤ ∑' n : ℕ, s ^ 2 / 4 * (1 / ((n : ℝ) + 1) ^ 2) :=
    Summable.tsum_le_tsum hb (summable_t1_term h0 h2) ((summable_zN (m := 2) le_rfl).mul_left _)
  rw [tsum_mul_left] at hle
  have hz : zN 2 ≤ 2 := zN_le_two le_rfl
  have e : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 = zN 2 := rfl
  rw [e] at hle
  nlinarith [sq_nonneg s]

theorem abs_exp_neg_lin_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.exp (-x) * (x + 1) - 1| ≤ 3 * x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := -x) (by rw [abs_neg, abs_of_nonneg hx0]; exact hx1)
  rw [show (-x) ^ 2 = x ^ 2 by ring] at h
  have e : Real.exp (-x) * (x + 1) - 1 = (Real.exp (-x) - 1 - -x) * (x + 1) + -(x ^ 2) := by ring
  rw [e]
  have h2 : |(Real.exp (-x) - 1 - -x) * (x + 1)| ≤ 2 * x ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x + 1)]
    nlinarith [mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ x + 1),
      mul_le_mul_of_nonneg_left hx1 (sq_nonneg x)]
  calc |(Real.exp (-x) - 1 - -x) * (x + 1) + -(x ^ 2)|
      ≤ |(Real.exp (-x) - 1 - -x) * (x + 1)| + |-(x ^ 2)| := abs_add_le _ _
    _ ≤ 2 * x ^ 2 + x ^ 2 := by rw [abs_neg, abs_of_nonneg (sq_nonneg x)]; linarith
    _ = 3 * x ^ 2 := by ring

theorem abs_exp_neg_quad_sub_le {x : ℝ} (hx0 : 0 ≤ x) :
    |Real.exp (-x) * (x * x + 2 * x + 2) - 2| ≤ x ^ 3 := by
  rcases hx0.eq_or_lt with h | h
  · subst h
    simp
  · have hd : ∀ y ∈ Ioo (0 : ℝ) x, HasDerivAt (fun y : ℝ => Real.exp (-y) * (y * y + 2 * y + 2))
        (-(y * y * Real.exp (-y))) y := by
      intro y _
      have h1 := (hasDerivAt_neg y).exp
      have h2 := (((hasDerivAt_id' y).mul (hasDerivAt_id' y)).add ((hasDerivAt_id' y).const_mul 2)).add_const 2
      convert h1.mul h2 using 1
      ring
    have hc : ContinuousOn (fun y : ℝ => Real.exp (-y) * (y * y + 2 * y + 2)) (Icc 0 x) := by
      fun_prop
    obtain ⟨c, hcI, hcd⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => Real.exp (-y) * (y * y + 2 * y + 2))
      (fun y : ℝ => -(y * y * Real.exp (-y))) h hc hd
    have hx' : x ≠ 0 := h.ne'
    have hcd' : -(c * c * Real.exp (-c))
        = (Real.exp (-x) * (x * x + 2 * x + 2) - Real.exp (-0) * (0 * 0 + 2 * 0 + 2)) / (x - 0) := hcd
    have key : Real.exp (-x) * (x * x + 2 * x + 2) - 2 = -(c * c * Real.exp (-c)) * x := by
      rw [hcd']
      simp only [neg_zero, Real.exp_zero, mul_zero, zero_add, add_zero, one_mul, sub_zero]
      rw [div_mul_cancel₀ _ hx']
    rw [key, abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (mul_self_nonneg c) (Real.exp_pos _).le),
      abs_of_pos h]
    have he : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hcI.1])
    have hcc : c * c ≤ x * x := mul_self_le_mul_self hcI.1.le hcI.2.le
    calc c * c * Real.exp (-c) * x ≤ x * x * 1 * x := by
          refine mul_le_mul_of_nonneg_right ?_ h.le
          exact mul_le_mul hcc he (Real.exp_pos _).le (mul_self_nonneg x)
      _ = x ^ 3 := by ring

theorem a0_lt_one : a0 < 1 := by
  rw [a0_eq_gamma]
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h2 := Real.one_half_lt_eulerMascheroniConstant
  linarith

theorem tendsto_of_abs_sub_le {f : ℝ → ℝ} {L C : ℝ}
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → |f s - L| ≤ C * s) : Tendsto f (𝓝[>] 0) (𝓝 L) := by
  have hlim : Tendsto (fun s : ℝ => C * s) (𝓝[>] 0) (𝓝 0) := by
    have h0 := (((continuous_const : Continuous fun _ : ℝ => C).mul continuous_id).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h0
  have h1 : Tendsto (fun s : ℝ => f s - L) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
    rw [Real.norm_eq_abs]
    exact h s hs.1 hs.2.le
  have h2 := h1.add_const L
  simpa using h2

/-- `Q(s) = e^{a₀ s} s j(s)`. -/
noncomputable def qF (s : ℝ) : ℝ := Real.exp (a0 * s) * (s * jS s)

/-- `B₂ = 72 (Q - 1)/s⁵ - 24 Q Φ/s⁴`. -/
noncomputable def b2F (s : ℝ) : ℝ := 72 * (qF s - 1) / s ^ 5 - 24 * qF s * phiS s / s ^ 4

/-- `B₃ = 24 Q E/s⁴`. -/
noncomputable def b3F (s : ℝ) : ℝ := 24 * qF s * (eS s / s ^ 4)

/-- `E₂ = 24 Q [Λ(0)(e^{-x}(x² + 2x + 2) - 2)/s⁴ + T₁ (e^{-x}(x + 1) - 1)/s³]`, `x = a₀ s`. -/
noncomputable def e2F (s : ℝ) : ℝ :=
  24 * qF s * (lamS s 0 * (Real.exp (-a0 * s) * ((a0 * s) * (a0 * s) + 2 * (a0 * s) + 2) - 2) / s ^ 4
    + t1S s * (Real.exp (-a0 * s) * (a0 * s + 1) - 1) / s ^ 3)

/-- `Err = (3/5) s Q E₁ - E₂ - j (H - H_m)`. -/
noncomputable def errF (s : ℝ) : ℝ :=
  3 / 5 * s * qF s * (Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6) - e2F s - jS s * (hH s - hM s)

theorem qF_mul_exp (s : ℝ) : qF s * Real.exp (-a0 * s) = s * jS s := by
  unfold qF
  rw [mul_right_comm, ← Real.exp_add, show a0 * s + -a0 * s = 0 by ring, Real.exp_zero, one_mul]

/-- **The decomposition** `pairS - 72/s⁵ = R (4/5) P + B₂ + B₃ + Err` for `0 < s ≤ 1`. -/
theorem pairS_decomp {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    pairS s - 72 / s ^ 5 = s * jS s * (4 / 5 * mellP s) + b2F s + b3F s + errF s := by
  have hs : s ≠ 0 := hs0.ne'
  have hQe := qF_mul_exp s
  have hΛ := two_lamS_zero hs0 hs1
  have step1 : s * jS s * (3 / 5 * s * mellM 3 5 s)
      = 72 * qF s / s ^ 5 + 3 / 5 * s * qF s * (Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6) := by
    have c0 : 3 / 5 * s * qF s * (120 / s ^ 6) = 72 * qF s / s ^ 5 := by
      field_simp
      all_goals ring
    linear_combination (-(3 / 5) * s * mellM 3 5 s) * hQe + c0
  have step2 : jS s * hM s = 24 * qF s * (phiS s - eS s) / s ^ 4 + e2F s := by
    rw [hM_eq hs0 hs1]
    unfold e2F
    have c1 : s * ((a0 * s) * (a0 * s) + 2 * (a0 * s) + 2) / s ^ 4
        = a0 ^ 2 / s + 2 * a0 / s ^ 2 + 2 / s ^ 3 := by
      field_simp
      all_goals ring
    have c2 : s * (a0 * s + 1) / s ^ 3 = a0 / s + 1 / s ^ 2 := by
      field_simp
      all_goals ring
    have c3 : s * t1S s / s ^ 4 = t1S s / s ^ 3 := by
      field_simp
      all_goals ring
    linear_combination (-24 * lamS s 0 * ((a0 * s) * (a0 * s) + 2 * (a0 * s) + 2) / s ^ 4
        - 24 * t1S s * (a0 * s + 1) / s ^ 3) * hQe + (-24 * jS s * lamS s 0) * c1
      + (-24 * jS s * t1S s) * c2 + (24 * qF s / s ^ 4) * hΛ + (-24 * qF s) * c3
  rw [pairS_eq_sB_sub_H hs0 hs1, bB_eq hs0 hs1]
  unfold b2F b3F errF
  linear_combination step1 - step2

/-- **RungBP**: `pairS(s) - 72/s⁵ → R₆₂/2 + (3/20) ζ(5)` as `s → 0⁺`. -/
theorem rungBP : RungBP := by
  obtain ⟨K, hK⟩ := hH_sub_hM_le
  obtain ⟨-, -, ⟨C1, hC1⟩⟩ := rungA2M
  have hz3 := zN_nonneg 3
  have hz5 : 0 ≤ zeta5 := by rw [← zN_five]; exact zN_nonneg 5
  have hz7 := zN_nonneg 7
  have ha0 := a0_pos
  have ha1 := a0_lt_one
  -- `Q`
  have hQ : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 < qF s ∧ qF s ≤ 2 + zN 3 + zeta5 ∧
      |qF s - 1| ≤ (zN 3 / 12 + zeta5 / 80 + 1) * s ^ 3 := by
    intro s hs0 hs1
    have hq' : |qF s - 1 - s ^ 3 / 12 * zN 3 - s ^ 5 / 80 * zeta5| ≤ s ^ 6 := qQ_expansion hs0 hs1
    have hpos : 0 < qF s := mul_pos (Real.exp_pos _) (mul_pos hs0 (jS_pos hs0 (by linarith)))
    have h3 : s ^ 3 ≤ 1 := pow_le_one₀ hs0.le hs1
    have h5 : s ^ 5 ≤ s ^ 3 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    have h6 : s ^ 6 ≤ s ^ 3 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    have h30 : 0 ≤ s ^ 3 := pow_nonneg hs0.le 3
    have h50 : 0 ≤ s ^ 5 := pow_nonneg hs0.le 5
    rw [abs_le] at hq'
    refine ⟨hpos, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_right h3 hz3, mul_le_mul_of_nonneg_right (h5.trans h3) hz5]
    · rw [abs_le]
      constructor
      · nlinarith [mul_nonneg h30 hz3, mul_nonneg h50 hz5]
      · nlinarith [mul_le_mul_of_nonneg_right h5 hz5]
  -- `Φ`
  have hΦ : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ phiS s - s ^ 2 / 4 * zN 3 - s ^ 4 / 16 * zeta5 ∧
      phiS s - s ^ 2 / 4 * zN 3 - s ^ 4 / 16 * zeta5 ≤ s ^ 6 / 48 * zN 7 := by
    intro s hs0 hs1
    have h := phiS_expansion hs0.le hs1
    rw [zN_five] at h
    exact h
  -- `B₂`
  have hB2 : ∀ s : ℝ, 0 < s → s ≤ 1 → |b2F s - -(3 / 5 * zeta5)| ≤
      (72 + zN 7 / 2 + (zN 3 / 12 + zeta5 / 80 + 1) * (zN 3 / 4 + zeta5 / 16 + zN 7 / 48) * 24) * s := by
    intro s hs0 hs1
    obtain ⟨_, _, hQ3⟩ := hQ s hs0 hs1
    have hq' : |qF s - 1 - s ^ 3 / 12 * zN 3 - s ^ 5 / 80 * zeta5| ≤ s ^ 6 := qQ_expansion hs0 hs1
    obtain ⟨hp1, hp2⟩ := hΦ s hs0 hs1
    have hs : s ≠ 0 := hs0.ne'
    have e : b2F s - -(3 / 5 * zeta5) = 72 * ((qF s - 1 - s ^ 3 / 12 * zN 3 - s ^ 5 / 80 * zeta5) / s ^ 5)
        - 24 * ((phiS s - s ^ 2 / 4 * zN 3 - s ^ 4 / 16 * zeta5) / s ^ 4)
        - 24 * ((qF s - 1) * phiS s / s ^ 4) := by
      unfold b2F
      field_simp
      all_goals ring
    have h20 : 0 ≤ s ^ 2 := pow_nonneg hs0.le 2
    have h40 : 0 ≤ s ^ 4 := pow_nonneg hs0.le 4
    have h42 : s ^ 4 ≤ s ^ 2 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    have h62 : s ^ 6 ≤ s ^ 2 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    have h65 : s ^ 6 ≤ s ^ 5 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    have hΦ0 : 0 ≤ phiS s := by nlinarith [mul_nonneg h20 hz3, mul_nonneg h40 hz5]
    have hΦ1 : phiS s ≤ (zN 3 / 4 + zeta5 / 16 + zN 7 / 48) * s ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right h42 hz5, mul_le_mul_of_nonneg_right h62 hz7]
    have b1 : |(qF s - 1 - s ^ 3 / 12 * zN 3 - s ^ 5 / 80 * zeta5) / s ^ 5| ≤ s := by
      rw [abs_div, abs_of_pos (pow_pos hs0 5), div_le_iff₀ (pow_pos hs0 5)]
      calc _ ≤ s ^ 6 := hq'
        _ = s * s ^ 5 := by ring
    have b2 : |(phiS s - s ^ 2 / 4 * zN 3 - s ^ 4 / 16 * zeta5) / s ^ 4| ≤ zN 7 / 48 * s := by
      rw [abs_div, abs_of_pos (pow_pos hs0 4), abs_of_nonneg hp1, div_le_iff₀ (pow_pos hs0 4)]
      nlinarith [mul_le_mul_of_nonneg_right h65 hz7]
    have b3 : |(qF s - 1) * phiS s / s ^ 4|
        ≤ (zN 3 / 12 + zeta5 / 80 + 1) * (zN 3 / 4 + zeta5 / 16 + zN 7 / 48) * s := by
      rw [abs_div, abs_mul, abs_of_nonneg hΦ0, abs_of_pos (pow_pos hs0 4), div_le_iff₀ (pow_pos hs0 4)]
      calc |qF s - 1| * phiS s
          ≤ ((zN 3 / 12 + zeta5 / 80 + 1) * s ^ 3) * ((zN 3 / 4 + zeta5 / 16 + zN 7 / 48) * s ^ 2) :=
            mul_le_mul hQ3 hΦ1 hΦ0 (by positivity)
        _ = (zN 3 / 12 + zeta5 / 80 + 1) * (zN 3 / 4 + zeta5 / 16 + zN 7 / 48) * s * s ^ 4 := by ring
    have a1 := abs_le.1 b1
    have a2 := abs_le.1 b2
    have a3 := abs_le.1 b3
    rw [e, abs_le]
    constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  -- the error
  have hE : ∀ s : ℝ, 0 < s → s ≤ 1 → |errF s - 0| ≤
      (3 / 5 * (2 + zN 3 + zeta5) * |C1| + 24 * (2 + zN 3 + zeta5) * (a0 ^ 3 / 2 + 3 * a0 ^ 2 / 2)
        + (2 + zN 3 + zeta5) * |K|) * s := by
    intro s hs0 hs1
    obtain ⟨hQp, hQm, _⟩ := hQ s hs0 hs1
    have hs2 : s ≤ 2 := by linarith
    obtain ⟨hL0, hL1⟩ := lamS_zero_le hs0.le hs2
    obtain ⟨hT0, hT1⟩ := t1S_le hs0.le hs2
    have hx0 : 0 ≤ a0 * s := by positivity
    have hx1 : a0 * s ≤ 1 := by nlinarith
    have hX2 : |Real.exp (-a0 * s) * ((a0 * s) * (a0 * s) + 2 * (a0 * s) + 2) - 2| ≤ a0 ^ 3 * s ^ 3 := by
      rw [neg_mul, ← mul_pow]
      exact abs_exp_neg_quad_sub_le hx0
    have hX1 : |Real.exp (-a0 * s) * (a0 * s + 1) - 1| ≤ 3 * a0 ^ 2 * s ^ 2 := by
      rw [neg_mul]
      have h := abs_exp_neg_lin_sub_le hx0 hx1
      rw [mul_pow] at h
      linarith
    have bA : |lamS s 0 * (Real.exp (-a0 * s) * ((a0 * s) * (a0 * s) + 2 * (a0 * s) + 2) - 2) / s ^ 4|
        ≤ a0 ^ 3 / 2 * s := by
      rw [abs_div, abs_mul, abs_of_nonneg hL0, abs_of_pos (pow_pos hs0 4), div_le_iff₀ (pow_pos hs0 4)]
      calc lamS s 0 * |Real.exp (-a0 * s) * ((a0 * s) * (a0 * s) + 2 * (a0 * s) + 2) - 2|
          ≤ (s ^ 2 / 2) * (a0 ^ 3 * s ^ 3) := mul_le_mul hL1 hX2 (abs_nonneg _) (by positivity)
        _ = a0 ^ 3 / 2 * s * s ^ 4 := by ring
    have bB : |t1S s * (Real.exp (-a0 * s) * (a0 * s + 1) - 1) / s ^ 3| ≤ 3 * a0 ^ 2 / 2 * s := by
      rw [abs_div, abs_mul, abs_of_nonneg hT0, abs_of_pos (pow_pos hs0 3), div_le_iff₀ (pow_pos hs0 3)]
      calc t1S s * |Real.exp (-a0 * s) * (a0 * s + 1) - 1|
          ≤ (s ^ 2 / 2) * (3 * a0 ^ 2 * s ^ 2) := mul_le_mul hT1 hX1 (abs_nonneg _) (by positivity)
        _ = 3 * a0 ^ 2 / 2 * s * s ^ 3 := by ring
    have p2 : |e2F s| ≤ 24 * (2 + zN 3 + zeta5) * (a0 ^ 3 / 2 + 3 * a0 ^ 2 / 2) * s := by
      have hAB := (abs_add_le _ _).trans (add_le_add bA bB)
      unfold e2F
      rw [abs_mul, abs_mul, abs_of_pos hQp, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
      calc 24 * qF s * |lamS s 0 * (Real.exp (-a0 * s) * ((a0 * s) * (a0 * s) + 2 * (a0 * s) + 2) - 2) / s ^ 4
            + t1S s * (Real.exp (-a0 * s) * (a0 * s + 1) - 1) / s ^ 3|
          ≤ 24 * (2 + zN 3 + zeta5) * (a0 ^ 3 / 2 * s + 3 * a0 ^ 2 / 2 * s) :=
            mul_le_mul (by linarith) hAB (abs_nonneg _) (by positivity)
        _ = 24 * (2 + zN 3 + zeta5) * (a0 ^ 3 / 2 + 3 * a0 ^ 2 / 2) * s := by ring
    have p1 : |3 / 5 * s * qF s * (Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6)|
        ≤ 3 / 5 * (2 + zN 3 + zeta5) * |C1| * s := by
      have hc := (hC1 s hs0 hs1).trans (le_abs_self C1)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 / 5 * s * qF s)]
      calc 3 / 5 * s * qF s * |Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6|
          ≤ 3 / 5 * s * (2 + zN 3 + zeta5) * |C1| :=
            mul_le_mul (mul_le_mul_of_nonneg_left hQm (by positivity)) hc (abs_nonneg _) (by positivity)
        _ = 3 / 5 * (2 + zN 3 + zeta5) * |C1| * s := by ring
    have p3 : |jS s * (hH s - hM s)| ≤ (2 + zN 3 + zeta5) * |K| * s := by
      have hj := jS_pos hs0 (by linarith)
      have hR : s * jS s ≤ 2 + zN 3 + zeta5 := by
        rw [← qF_mul_exp]
        have he : Real.exp (-a0 * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        have he0 := Real.exp_pos (-a0 * s)
        nlinarith
      have hD := (hK s hs0 hs1).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg s))
      rw [abs_mul, abs_of_pos hj]
      calc jS s * |hH s - hM s| ≤ jS s * (|K| * s ^ 2) := mul_le_mul_of_nonneg_left hD hj.le
        _ = (s * jS s) * |K| * s := by ring
        _ ≤ (2 + zN 3 + zeta5) * |K| * s :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR (abs_nonneg _)) hs0.le
    have q1 := abs_le.1 p1
    have q2 := abs_le.1 p2
    have q3 := abs_le.1 p3
    rw [sub_zero, abs_le]
    unfold errF
    constructor <;> nlinarith [q1.1, q1.2, q2.1, q2.2, q3.1, q3.2]
  -- the limits
  have hQlim : Tendsto qF (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_of_abs_sub_le (C := zN 3 / 12 + zeta5 / 80 + 1) (fun s hs0 hs1 => ?_)
    have h := (hQ s hs0 hs1).2.2
    have h3 : s ^ 3 ≤ s := by
      have := pow_le_pow_of_le_one hs0.le hs1 (show 1 ≤ 3 by norm_num)
      rwa [pow_one] at this
    exact h.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have he : Tendsto (fun s : ℝ => Real.exp (-a0 * s)) (𝓝[>] 0) (𝓝 1) := by
    have h := ((by fun_prop : Continuous fun s : ℝ => Real.exp (-a0 * s)).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  have hR : Tendsto (fun s : ℝ => s * jS s) (𝓝[>] 0) (𝓝 1) := by
    have h := hQlim.mul he
    rw [mul_one] at h
    exact h.congr (fun s => qF_mul_exp s)
  have hP : Tendsto (fun s : ℝ => 4 / 5 * mellP s) (𝓝[>] 0) (𝓝 (R62 / 2)) := by
    have h := tendsto_mellP.const_mul (1 / 2)
    rw [show (1 : ℝ) / 2 * R62 = R62 / 2 by ring] at h
    exact h.congr (fun s => by ring)
  have t1 := hR.mul hP
  have t2 : Tendsto b2F (𝓝[>] 0) (𝓝 (-(3 / 5 * zeta5))) := tendsto_of_abs_sub_le hB2
  have t3 : Tendsto b3F (𝓝[>] 0) (𝓝 (24 * 1 * (zN 5 / 32))) :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (24 : ℝ)) (𝓝[>] 0) (𝓝 24)).mul hQlim).mul tendsto_eS_div
  have t4 : Tendsto errF (𝓝[>] 0) (𝓝 0) := tendsto_of_abs_sub_le hE
  have hsum := ((t1.add t2).add t3).add t4
  have hlim : 1 * (R62 / 2) + -(3 / 5 * zeta5) + 24 * 1 * (zN 5 / 32) + 0 = R62 / 2 + 3 / 20 * zeta5 := by
    rw [zN_five]
    ring
  rw [hlim] at hsum
  unfold RungBP
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
  exact (pairS_decomp hs.1 hs.2.le).symm

/-- **RV(6)**: `μ₆ = 648/π⁶ · L(f, 5)`, with no hypotheses. -/
theorem rv6 : mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_rungBP rungBP

end Tower.RV6
