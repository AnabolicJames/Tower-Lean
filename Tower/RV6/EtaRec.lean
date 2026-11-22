import Mathlib
import Tower.RV6.Defs
import Tower.RV6.PsiW
import Tower.RV6.Ladder3
import Tower.RV6.Ser
import Tower.RV6.Level6
import Tower.RV6.Ramanujan

/-!
# Rung E″: the divisor-sum coefficients `psiW` are those of the eta product

`aCoeff n` is the coefficient of `qⁿ` in `q ∏ ((1 - q^k)(1 - q^{2k})(1 - q^{3k})(1 - q^{6k}))²`.
This file proves `rungEW : ∀ n, aCoeff n = psiW n` in the ring `ℝ⟦X⟧`, with no modular forms of
level 6:

* `PsiS_Gamf`: `25920 ∑ psiW(n) Xⁿ` is the polynomial `Gamf` of `Level6.lean` in the twelve
  series `E₂, E₄, E₆` at `X, X², X³, X⁶`.
* `theta_PsiS`: hence `12 θΨ = (E₂(X) + 2E₂(X²) + 3E₂(X³) + 6E₂(X⁶)) Ψ` (from `thetaGam_scaled`
  and `ram6`), i.e. `rec_psi`: `(n - 1) psiW(n) = -2 ∑_{i+j=n} psiW(i) qE(j)`.
* `theta_HN`: the truncated eta product `H_N` satisfies `θH_N = H_N (1 + L_N)`, and the
  coefficients of `L_N` up to `X^N` are `-2 qE(j)` (`coeff_LN_all`), so the coefficients of `H_N`
  up to `X^N` satisfy the same recurrence (`rec_HN`).
* `rec_unique`: the recurrence with `c(0) = 0`, `c(1) = 1` has one solution.
* `rungEW`, and `rv6_of_bessel`: the six-step theorem from the three Bessel-side rungs alone.
-/

namespace Tower.RV6

open Real

/-! ## The series of `psiW` in terms of the twelve series -/

/-- `∑ Fc(n) Xⁿ`. -/
noncomputable def PhiS : PowerSeries ℝ := PowerSeries.mk Fc

/-- `∑ sW(n) Xⁿ`. -/
noncomputable def SigS : PowerSeries ℝ := PowerSeries.mk sW

/-- `∑ psiW(n) Xⁿ`. -/
noncomputable def PsiS : PowerSeries ℝ := PowerSeries.mk psiW

/-- Coefficients of `𝔈(τ) + 2𝔈(2τ) + 3𝔈(3τ) + 6𝔈(6τ)`, `𝔈 = ∑ σ₁(n) qⁿ`. -/
noncomputable def qE (n : ℕ) : ℝ :=
  sig 1 n + 2 * (if 2 ∣ n then sig 1 (n / 2) else 0) + 3 * (if 3 ∣ n then sig 1 (n / 3) else 0)
    + 6 * (if 6 ∣ n then sig 1 (n / 6) else 0)

/-- `∑ qE(n) Xⁿ`. -/
noncomputable def QS : PowerSeries ℝ := PowerSeries.mk qE

theorem coeff_PhiS (n : ℕ) : PowerSeries.coeff n PhiS = Fc n := PowerSeries.coeff_mk n _

theorem coeff_SigS (n : ℕ) : PowerSeries.coeff n SigS = sW n := PowerSeries.coeff_mk n _

theorem coeff_PsiS (n : ℕ) : PowerSeries.coeff n PsiS = psiW n := PowerSeries.coeff_mk n _

theorem coeff_QS (n : ℕ) : PowerSeries.coeff n QS = qE n := PowerSeries.coeff_mk n _

theorem coeff_PhiS_PhiS (n : ℕ) : PowerSeries.coeff n (PhiS * PhiS) = conv Fc Fc n :=
  coeff_mk_mul_mk Fc Fc n

theorem coeff_PsiS_QS (n : ℕ) : PowerSeries.coeff n (PsiS * QS) = conv psiW qE n :=
  coeff_mk_mul_mk psiW qE n

theorem PhiS_eq : PhiS = S1 - 2 * PowerSeries.expand 2 two_ne S1
    - 27 * PowerSeries.expand 3 three_ne S1 + 54 * PowerSeries.expand 6 six_ne S1 := by
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_expand, coeff_S1,
    coeff_PhiS]
  unfold Fc
  ring

theorem QS_eq : QS = S1 + 2 * PowerSeries.expand 2 two_ne S1
    + 3 * PowerSeries.expand 3 three_ne S1 + 6 * PowerSeries.expand 6 six_ne S1 := by
  ext n
  simp only [map_add, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_expand, coeff_S1, coeff_QS]
  unfold qE
  ring

theorem SigS_eq : 54 * SigS + 11 * S3 + 44 * PowerSeries.expand 2 two_ne S3
    = 1701 * PowerSeries.expand 3 three_ne S3 + 6804 * PowerSeries.expand 6 six_ne S3 := by
  ext n
  simp only [map_add, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_expand, coeff_S3,
    coeff_SigS]
  unfold sW
  ring

theorem PsiS_eq : 54 * PsiS = 54 * SigS + 65 * PhiS - 30 * (PhiS * PhiS) := by
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, coeff_SigS, coeff_PhiS, coeff_PsiS,
    coeff_PhiS_PhiS]
  unfold psiW
  ring

/-- `25920 ∑ psiW(n) Xⁿ` is the polynomial `Gamf` in the twelve series. -/
theorem PsiS_Gamf :
    25920 * PsiS = Gamf e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have h1 := PhiS_eq
  have h2 := SigS_eq
  have h3 := PsiS_eq
  simp only [Gamf, e2_1, e2_2, e2_3, e2_6, e4_1, e4_2, e4_3, e4_6, xE, uE, map_sub, map_add,
    map_mul, map_one, map_ofNat]
  linear_combination 480 * h3 + 480 * h2
    + (31200 - 14400 * (PhiS + (S1 - 2 * PowerSeries.expand 2 two_ne S1
      - 27 * PowerSeries.expand 3 three_ne S1 + 54 * PowerSeries.expand 6 six_ne S1))) * h1

theorem ofNat_mul_cancel {A B : PowerSeries ℝ}
    (h : (25920 : PowerSeries ℝ) * A = 25920 * B) : A = B := by
  ext n
  have hn := congrArg (fun t => PowerSeries.coeff n t) h
  simp only [PowerSeries.coeff_ofNat_mul] at hn
  exact mul_left_cancel₀ (by norm_num : (25920 : ℝ) ≠ 0) hn

/-- `12 θΨ = (E₂(X) + 2E₂(X²) + 3E₂(X³) + 6E₂(X⁶)) Ψ`. -/
theorem theta_PsiS : 12 * theta PsiS = (e2_1 + 2 * e2_2 + 3 * e2_3 + 6 * e2_6) * PsiS := by
  have h := thetaGam_scaled ram6
  rw [← PsiS_Gamf] at h
  have ht : theta (25920 * PsiS) = 25920 * theta PsiS := by
    rw [theta_mul, theta_ofNat, zero_mul, zero_add]
  rw [ht] at h
  have hc : (25920 : PowerSeries ℝ) * (12 * theta PsiS)
      = 25920 * ((e2_1 + 2 * e2_2 + 3 * e2_3 + 6 * e2_6) * PsiS) := by
    linear_combination h
  exact ofNat_mul_cancel hc

theorem P_eq : e2_1 + 2 * e2_2 + 3 * e2_3 + 6 * e2_6 = 12 - 24 * QS := by
  rw [QS_eq]
  simp only [e2_1, e2_2, e2_3, e2_6, xE, map_sub, map_mul, map_one, map_ofNat]
  ring

/-- The recurrence of `psiW`: `(n - 1) psiW(n) = -2 ∑_{i+j=n} psiW(i) qE(j)`. -/
theorem rec_psi (n : ℕ) : ((n : ℝ) - 1) * psiW n = -2 * conv psiW qE n := by
  have h := theta_PsiS
  rw [P_eq] at h
  have h' : 12 * theta PsiS = 12 * PsiS - 24 * (PsiS * QS) := by linear_combination h
  have hc := congrArg (fun t => PowerSeries.coeff n t) h'
  simp only [map_sub, PowerSeries.coeff_ofNat_mul, coeff_theta, coeff_PsiS, coeff_PsiS_QS] at hc
  linear_combination (1 / 12 : ℝ) * hc

/-! ## Values at `0` and `1` -/

theorem qE_zero : qE 0 = 0 := by
  unfold qE
  rw [if_pos (dvd_zero 2), if_pos (dvd_zero 3), if_pos (dvd_zero 6), Nat.zero_div, Nat.zero_div,
    Nat.zero_div, sig_zero]
  norm_num

theorem Fc_one : Fc 1 = 1 := by
  unfold Fc
  rw [if_neg (by decide : ¬ (2 : ℕ) ∣ 1), if_neg (by decide : ¬ (3 : ℕ) ∣ 1),
    if_neg (by decide : ¬ (6 : ℕ) ∣ 1), sig1_vals.2.1]
  norm_num

theorem sW_one : sW 1 = -(11 / 54) := by
  unfold sW
  rw [if_neg (by decide : ¬ (2 : ℕ) ∣ 1), if_neg (by decide : ¬ (3 : ℕ) ∣ 1),
    if_neg (by decide : ¬ (6 : ℕ) ∣ 1), sig3_vals.2.1]
  norm_num

theorem convFF_one : conv Fc Fc 1 = 0 := by
  unfold conv
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have hp' : p.1 + p.2 = 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rcases Nat.eq_zero_or_pos p.1 with h | h
  · rw [h, Fc_zero, zero_mul]
  · have h2 : p.2 = 0 := by omega
    rw [h2, Fc_zero, mul_zero]

theorem psiW_one : psiW 1 = 1 := by
  unfold psiW
  rw [sW_one, Fc_one, convFF_one]
  norm_num

/-! ## The factors `1 - X^m` and their logarithmic derivatives -/

/-- `1 - X^m`. -/
noncomputable def fac (m : ℕ) : PowerSeries ℝ := 1 - PowerSeries.X ^ m

/-- `∑_{i ≥ 0} X^{m i} = 1/(1 - X^m)` for `m ≠ 0`. -/
noncomputable def geoD (m : ℕ) : PowerSeries ℝ :=
  if hm : m ≠ 0 then PowerSeries.expand m hm (PowerSeries.mk 1) else 0

/-- `θ(1 - X^m)/(1 - X^m) = m (1 - 1/(1 - X^m))`. -/
noncomputable def gl (m : ℕ) : PowerSeries ℝ := (m : PowerSeries ℝ) * (1 - geoD m)

theorem geoD_eq (m : ℕ) (hm : m ≠ 0) :
    geoD m = PowerSeries.expand m hm (PowerSeries.mk 1) := by
  unfold geoD
  rw [dif_pos hm]

theorem fac_mul_geoD (m : ℕ) (hm : m ≠ 0) : fac m * geoD m = 1 := by
  have h := congrArg (fun t => PowerSeries.expand m hm t)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℝ)
  simp only [map_mul, map_sub, map_one, PowerSeries.expand_X] at h
  rw [geoD_eq m hm]
  unfold fac
  linear_combination h

theorem coeff_geoD (m j : ℕ) (hm : m ≠ 0) :
    PowerSeries.coeff j (geoD m) = if m ∣ j then 1 else 0 := by
  rw [geoD_eq m hm, PowerSeries.coeff_expand]
  by_cases h : m ∣ j
  · rw [if_pos h, if_pos h]
    simp only [PowerSeries.coeff_mk, Pi.one_apply]
  · rw [if_neg h, if_neg h]

theorem theta_X_pow (m : ℕ) :
    theta ((PowerSeries.X : PowerSeries ℝ) ^ m) = (m : PowerSeries ℝ) * PowerSeries.X ^ m := by
  ext n
  rw [coeff_theta, coeff_natCast_mul, PowerSeries.coeff_X_pow]
  by_cases h : n = m
  · rw [if_pos h, h]
  · rw [if_neg h, mul_zero, mul_zero]

theorem theta_X : theta (PowerSeries.X : PowerSeries ℝ) = PowerSeries.X := by
  have h := theta_X_pow 1
  rw [pow_one, Nat.cast_one, one_mul] at h
  exact h

theorem theta_fac (m : ℕ) (hm : m ≠ 0) : theta (fac m) = fac m * gl m := by
  have h := fac_mul_geoD m hm
  unfold gl
  unfold fac at h ⊢
  rw [theta_sub, theta_one, theta_X_pow]
  linear_combination (m : PowerSeries ℝ) * h

theorem coeff_gl (m j : ℕ) (hm : m ≠ 0) (hj : j ≠ 0) :
    PowerSeries.coeff j (gl m) = -((m : ℝ) * (if m ∣ j then 1 else 0)) := by
  unfold gl
  rw [coeff_natCast_mul, map_sub, coeff_geoD m j hm, PowerSeries.coeff_one, if_neg hj]
  ring

theorem coeff_gl_zero (m : ℕ) (hm : m ≠ 0) : PowerSeries.coeff 0 (gl m) = 0 := by
  unfold gl
  rw [coeff_natCast_mul, map_sub, coeff_geoD m 0 hm, PowerSeries.coeff_one,
    if_pos (rfl : (0 : ℕ) = 0), if_pos (dvd_zero m), sub_self, mul_zero]

theorem cc_fac (m : ℕ) (hm : m ≠ 0) : PowerSeries.constantCoeff (fac m) = 1 := by
  unfold fac
  rw [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow hm, sub_zero]

/-! ## The truncated eta product -/

/-- `(1 - X^k)(1 - X^{2k})(1 - X^{3k})(1 - X^{6k})`. -/
noncomputable def Bk (k : ℕ) : PowerSeries ℝ := fac k * fac (2 * k) * fac (3 * k) * fac (6 * k)

/-- The logarithmic `θ`-derivative of `Bk k`. -/
noncomputable def Gk (k : ℕ) : PowerSeries ℝ := gl k + gl (2 * k) + gl (3 * k) + gl (6 * k)

/-- `X ∏_{k ≤ N} ((1 - X^k)(1 - X^{2k})(1 - X^{3k})(1 - X^{6k}))²`. -/
noncomputable def HN (N : ℕ) : PowerSeries ℝ := PowerSeries.X * ∏ k ∈ Finset.Icc 1 N, Bk k ^ 2

/-- The logarithmic `θ`-derivative of `HN N`, minus one. -/
noncomputable def LN (N : ℕ) : PowerSeries ℝ := ∑ k ∈ Finset.Icc 1 N, 2 * Gk k

theorem theta_Bk (k : ℕ) (hk : k ≠ 0) : theta (Bk k) = Bk k * Gk k := by
  have h1 := theta_fac k hk
  have h2 := theta_fac (2 * k) (by omega)
  have h3 := theta_fac (3 * k) (by omega)
  have h6 := theta_fac (6 * k) (by omega)
  unfold Bk Gk
  rw [theta_mul, theta_mul, theta_mul, h1, h2, h3, h6]
  ring

theorem cc_Bk (k : ℕ) (hk : k ≠ 0) : PowerSeries.constantCoeff (Bk k) = 1 := by
  unfold Bk
  rw [map_mul, map_mul, map_mul, cc_fac k hk, cc_fac (2 * k) (by omega),
    cc_fac (3 * k) (by omega), cc_fac (6 * k) (by omega)]
  norm_num

/-- The logarithmic derivative of a finite product of squares. -/
theorem theta_prod_sq (f g : ℕ → PowerSeries ℝ) (s : Finset ℕ)
    (h : ∀ k ∈ s, theta (f k) = f k * g k) :
    theta (∏ k ∈ s, f k ^ 2) = (∏ k ∈ s, f k ^ 2) * ∑ k ∈ s, 2 * g k := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, theta_one, mul_zero]
  | insert a s ha ih =>
    have h1 : theta (f a ^ 2) = f a ^ 2 * (2 * g a) := by
      rw [pow_two, theta_mul, h a (Finset.mem_insert_self a s)]
      ring
    have h2 := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, theta_mul, h1, h2]
    ring

theorem theta_HN (N : ℕ) : theta (HN N) = HN N * (1 + LN N) := by
  have hp : theta (∏ k ∈ Finset.Icc 1 N, Bk k ^ 2)
      = (∏ k ∈ Finset.Icc 1 N, Bk k ^ 2) * ∑ k ∈ Finset.Icc 1 N, 2 * Gk k :=
    theta_prod_sq Bk Gk (Finset.Icc 1 N) (fun k hk => theta_Bk k (by
      have h1 := (Finset.mem_Icc.mp hk).1
      omega))
  unfold HN LN
  rw [theta_mul, theta_X, hp]
  ring

theorem coeff_HN_zero (N : ℕ) : PowerSeries.coeff 0 (HN N) = 0 := by
  unfold HN
  exact PowerSeries.coeff_zero_X_mul _

theorem coeff_HN_one (N : ℕ) : PowerSeries.coeff 1 (HN N) = 1 := by
  unfold HN
  have h := PowerSeries.coeff_succ_X_mul 0 (∏ k ∈ Finset.Icc 1 N, Bk k ^ 2)
  rw [zero_add] at h
  rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
  refine Finset.prod_eq_one (fun k hk => ?_)
  have hk0 : k ≠ 0 := by
    have h1 := (Finset.mem_Icc.mp hk).1
    omega
  rw [map_pow, cc_Bk k hk0, one_pow]

/-! ## Divisor sums -/

/-- `∑_{k ≤ N, dk | j} k = σ₁(j/d)` if `d | j`, and `0` otherwise, for `1 ≤ j ≤ N`. -/
theorem sum_Icc_dvd (d j N : ℕ) (hd : d ≠ 0) (hj : j ≠ 0) (hjN : j ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * (if d * k ∣ j then 1 else 0)
      = if d ∣ j then sig 1 (j / d) else 0 := by
  have hcongr : ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * (if d * k ∣ j then 1 else 0)
      = ∑ k ∈ Finset.Icc 1 N, (if d * k ∣ j then (k : ℝ) else 0) :=
    Finset.sum_congr rfl (fun k _ => by rw [mul_ite, mul_one, mul_zero])
  rw [hcongr]
  by_cases hdj : d ∣ j
  · rw [if_pos hdj]
    obtain ⟨j', hjeq⟩ := hdj
    subst hjeq
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have h1d : 1 ≤ d := hdpos
    have hj' : j' ≠ 0 := by
      intro h0
      apply hj
      rw [h0, Nat.mul_zero]
    have hj'pos : 0 < j' := Nat.pos_of_ne_zero hj'
    have h3 : j' ≤ d * j' := by
      have h4 := Nat.mul_le_mul_right j' h1d
      rw [one_mul] at h4
      exact h4
    have hset : Finset.filter (fun k => d * k ∣ d * j') (Finset.Icc 1 N) = j'.divisors := by
      ext k
      rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, mul_dvd_mul_iff_left hd]
      constructor
      · rintro ⟨-, hk⟩
        exact ⟨hk, hj'⟩
      · rintro ⟨hk, -⟩
        have h1 : 0 < k := Nat.pos_of_dvd_of_pos hk hj'pos
        have h2 : k ≤ j' := Nat.le_of_dvd hj'pos hk
        exact ⟨⟨h1, le_trans h2 (le_trans h3 hjN)⟩, hk⟩
    rw [Nat.mul_div_cancel_left j' hdpos, ← Finset.sum_filter]
    unfold sig
    exact Finset.sum_congr hset (fun k _ => (pow_one (k : ℝ)).symm)
  · rw [if_neg hdj]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hn : ¬ d * k ∣ j := fun h => hdj (dvd_trans (dvd_mul_right d k) h)
    rw [if_neg hn]

theorem sum_Icc_dvd_one (j N : ℕ) (hj : j ≠ 0) (hjN : j ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * (if k ∣ j then 1 else 0) = sig 1 j := by
  have h := sum_Icc_dvd 1 j N one_ne_zero hj hjN
  simp only [one_mul, one_dvd, if_true, Nat.div_one] at h
  exact h

/-! ## The coefficients of `L_N` -/

theorem coeff_Gk (k j : ℕ) (hk : k ≠ 0) (hj : j ≠ 0) :
    PowerSeries.coeff j (Gk k)
      = -((k : ℝ) * (if k ∣ j then 1 else 0)) - 2 * ((k : ℝ) * (if 2 * k ∣ j then 1 else 0))
        - 3 * ((k : ℝ) * (if 3 * k ∣ j then 1 else 0))
        - 6 * ((k : ℝ) * (if 6 * k ∣ j then 1 else 0)) := by
  unfold Gk
  rw [map_add, map_add, map_add, coeff_gl k j hk hj, coeff_gl (2 * k) j (by omega) hj,
    coeff_gl (3 * k) j (by omega) hj, coeff_gl (6 * k) j (by omega) hj]
  push_cast
  ring

theorem coeff_LN (N j : ℕ) (hj : j ≠ 0) (hjN : j ≤ N) :
    PowerSeries.coeff j (LN N) = -2 * qE j := by
  have hterm : ∀ k ∈ Finset.Icc 1 N, PowerSeries.coeff j (2 * Gk k)
      = (-2) * ((k : ℝ) * (if k ∣ j then 1 else 0))
        + (-4) * ((k : ℝ) * (if 2 * k ∣ j then 1 else 0))
        + (-6) * ((k : ℝ) * (if 3 * k ∣ j then 1 else 0))
        + (-12) * ((k : ℝ) * (if 6 * k ∣ j then 1 else 0)) := by
    intro k hk
    have hk0 : k ≠ 0 := by
      have h1 := (Finset.mem_Icc.mp hk).1
      omega
    rw [PowerSeries.coeff_ofNat_mul, coeff_Gk k j hk0 hj]
    ring
  have hmap : PowerSeries.coeff j (LN N)
      = ∑ k ∈ Finset.Icc 1 N, PowerSeries.coeff j (2 * Gk k) := by
    unfold LN
    rw [map_sum]
  have hsum : ∑ k ∈ Finset.Icc 1 N, PowerSeries.coeff j (2 * Gk k)
      = (-2) * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * (if k ∣ j then 1 else 0)
        + (-4) * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * (if 2 * k ∣ j then 1 else 0)
        + (-6) * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * (if 3 * k ∣ j then 1 else 0)
        + (-12) * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * (if 6 * k ∣ j then 1 else 0) := by
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hmap, hsum, sum_Icc_dvd_one j N hj hjN, sum_Icc_dvd 2 j N two_ne hj hjN,
    sum_Icc_dvd 3 j N three_ne hj hjN, sum_Icc_dvd 6 j N six_ne hj hjN]
  unfold qE
  ring

theorem coeff_LN_zero (N : ℕ) : PowerSeries.coeff 0 (LN N) = 0 := by
  unfold LN
  rw [map_sum]
  refine Finset.sum_eq_zero (fun k hk => ?_)
  have hk0 : k ≠ 0 := by
    have h1 := (Finset.mem_Icc.mp hk).1
    omega
  unfold Gk
  rw [PowerSeries.coeff_ofNat_mul, map_add, map_add, map_add, coeff_gl_zero k hk0,
    coeff_gl_zero (2 * k) (by omega), coeff_gl_zero (3 * k) (by omega),
    coeff_gl_zero (6 * k) (by omega)]
  norm_num

theorem coeff_LN_all (N j : ℕ) (hjN : j ≤ N) : PowerSeries.coeff j (LN N) = -2 * qE j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [coeff_LN_zero, qE_zero, mul_zero]
  · exact coeff_LN N j (by omega) hjN

/-- The recurrence of the coefficients of `H_N` up to `X^N`. -/
theorem rec_HN (N n : ℕ) (hn : n ≤ N) :
    ((n : ℝ) - 1) * PowerSeries.coeff n (HN N)
      = -2 * conv (fun i => PowerSeries.coeff i (HN N)) qE n := by
  have h1 : PowerSeries.coeff n (theta (HN N)) = PowerSeries.coeff n (HN N * (1 + LN N)) := by
    rw [theta_HN N]
  have h2 : PowerSeries.coeff n (HN N * (1 + LN N))
      = PowerSeries.coeff n (HN N) + PowerSeries.coeff n (HN N * LN N) := by
    rw [mul_add, mul_one, map_add]
  have h3 : PowerSeries.coeff n (HN N * LN N)
      = -2 * conv (fun i => PowerSeries.coeff i (HN N)) qE n := by
    rw [PowerSeries.coeff_mul]
    unfold conv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    show PowerSeries.coeff p.1 (HN N) * PowerSeries.coeff p.2 (LN N)
      = -2 * (PowerSeries.coeff p.1 (HN N) * qE p.2)
    rw [coeff_LN_all N p.2 (by omega)]
    ring
  rw [coeff_theta, h2, h3] at h1
  linear_combination h1

/-! ## Uniqueness of the solution of the recurrence -/

theorem rec_unique (N : ℕ) (a b : ℕ → ℝ) (ha0 : a 0 = 0) (hb0 : b 0 = 0) (h1 : a 1 = b 1)
    (ha : ∀ n ≤ N, ((n : ℝ) - 1) * a n = -2 * conv a qE n)
    (hb : ∀ n ≤ N, ((n : ℝ) - 1) * b n = -2 * conv b qE n) :
    ∀ n ≤ N, a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    match n, ih, hn with
    | 0, _, _ => rw [ha0, hb0]
    | 1, _, _ => exact h1
    | m + 2, ih, hn =>
      have hconv : conv a qE (m + 2) = conv b qE (m + 2) := by
        unfold conv
        refine Finset.sum_congr rfl (fun p hp => ?_)
        have hp' : p.1 + p.2 = m + 2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rcases Nat.lt_or_ge p.1 (m + 2) with hlt | hge
        · rw [ih p.1 hlt (by omega)]
        · have hp2 : p.2 = 0 := by omega
          rw [hp2, qE_zero, mul_zero, mul_zero]
      have e1 := ha (m + 2) hn
      have e2 := hb (m + 2) hn
      rw [hconv] at e1
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hpos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) - 1 := by
        push_cast
        linarith
      exact mul_left_cancel₀ hpos.ne' (e1.trans e2.symm)

/-! ## From `ℤ[X]` to `ℝ⟦X⟧` -/

/-- The ring homomorphism `ℤ[X] → ℝ⟦X⟧`. -/
noncomputable def toSer : Polynomial ℤ →+* PowerSeries ℝ :=
  (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (Int.castRingHom ℝ))

theorem toSer_apply (p : Polynomial ℤ) :
    toSer p = ((Polynomial.map (Int.castRingHom ℝ) p : Polynomial ℝ) : PowerSeries ℝ) := rfl

theorem coeff_toSer (p : Polynomial ℤ) (n : ℕ) :
    PowerSeries.coeff n (toSer p) = ((p.coeff n : ℤ) : ℝ) := by
  have h2 : (Int.castRingHom ℝ) (p.coeff n) = ((p.coeff n : ℤ) : ℝ) := eq_intCast _ _
  rw [toSer_apply, Polynomial.coeff_coe, Polynomial.coeff_map, h2]

theorem toSer_X : toSer (Polynomial.X : Polynomial ℤ) = PowerSeries.X := by
  rw [toSer_apply, Polynomial.map_X, Polynomial.coe_X]

theorem toSer_prod (N : ℕ) :
    toSer ((Polynomial.X : Polynomial ℤ) * ∏ k ∈ Finset.Icc 1 N,
      ((1 - Polynomial.X ^ k) * (1 - Polynomial.X ^ (2 * k)) * (1 - Polynomial.X ^ (3 * k)) *
        (1 - Polynomial.X ^ (6 * k))) ^ 2) = HN N := by
  unfold HN Bk fac
  simp only [map_mul, map_prod, map_pow, map_sub, map_one, toSer_X]

/-- `a(N)` is the coefficient of `X^N` in the truncated product `H_N`. -/
theorem aCoeff_eq (N : ℕ) : (aCoeff N : ℝ) = PowerSeries.coeff N (HN N) := by
  unfold aCoeff
  rw [← toSer_prod N, coeff_toSer]

/-! ## Rung E″ and the six-step theorem from the Bessel side -/

theorem coeff_HN_eq_psiW (N : ℕ) : ∀ n ≤ N, PowerSeries.coeff n (HN N) = psiW n :=
  rec_unique N (fun i => PowerSeries.coeff i (HN N)) psiW (coeff_HN_zero N) psiW_zero
    ((coeff_HN_one N).trans psiW_one.symm) (fun m hm => rec_HN N m hm) (fun m _ => rec_psi m)

/-- **Rung E″.** The divisor-sum coefficients `psiW` are the coefficients of the eta product
`(η(τ) η(2τ) η(3τ) η(6τ))²`. -/
theorem rungEW : RungEW := by
  unfold RungEW
  intro n
  rw [aCoeff_eq n]
  exact coeff_HN_eq_psiW n n le_rfl

/-- The six-step theorem `μ₆ = (648/π⁶) L(f, 5)` from the three Bessel-side rungs. -/
theorem rv6_of_bessel (hA1 : RungA1) (hA2 : RungA2) (hB : RungB) :
    mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_bessel_and_E hA1 hA2 hB rungEW

end Tower.RV6
