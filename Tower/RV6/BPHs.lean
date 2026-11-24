import Mathlib
import Tower.RV6.BPKernel

/-!
# RungBP, step 3 (second half): `M_s` and the series of `h_s`

* `b_k(s) = binom(s/2, k)` (`bk`, Mathlib's `Ring.choose`): `b_{k+1} = b_k (s/2 - k)/(k + 1)`, `|b_k| ≤ 1` and
  `|b_k| ≤ (s/2)/k` (`k ≥ 1`) for `0 ≤ s ≤ 2`;
* Parseval for an absolutely summable real sequence (`integral_norm_sq_tsum`):
  `∫₀¹ |∑ cₙ e(θ)ⁿ|² dθ = ∑ cₙ²`;
* the binomial series (`rpow_rhoN_one_eq`): `|1 + r e(θ)|^s = |∑ bₙ rⁿ e(θ)ⁿ|²` for `0 ≤ r < 1`, so
  `M_s(1, r) = ∑ bₙ² r²ⁿ` (`angM_one_eq_tsum`) and `h_s(w) = M_s(1, √w) - 1 = ∑_{n ≥ 1} bₙ² wⁿ` with
  `0 ≤ h_s(w) ≤ (s²/2) w` on `[0, 1)`;
* `M_s(τ, t) = τ^s M_s(1, t/τ)` (`angM_homog`) and `M_s(τ, t) = M_s(t, τ)` (`angM_symm`).
-/

namespace Tower.RV6

open Real Filter MeasureTheory
open scoped ComplexConjugate

/-! ## The coefficients -/

/-- `b_k(s) = binom(s/2, k)`. -/
noncomputable def bk (s : ℝ) (k : ℕ) : ℝ := Ring.choose (s / 2) k

theorem choose_succ_real (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) = Ring.choose a n * (a - n) / (n + 1) := by
  have h1 : (descPochhammer ℤ (n + 1)).smeval a = (descPochhammer ℤ n).smeval a * (a - n) := by
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_natCast]
    simp
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, h1, Nat.factorial_succ, smul_eq_mul, smul_eq_mul]
  push_cast
  rw [mul_inv]
  ring

theorem bk_zero (s : ℝ) : bk s 0 = 1 := Ring.choose_zero_right _

theorem bk_one (s : ℝ) : bk s 1 = s / 2 := Ring.choose_one_right _

theorem bk_succ (s : ℝ) (n : ℕ) : bk s (n + 1) = bk s n * (s / 2 - n) / (n + 1) :=
  choose_succ_real _ _

theorem abs_bk_le_one {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) (n : ℕ) : |bk s n| ≤ 1 := by
  induction n with
  | zero => rw [bk_zero, abs_one]
  | succ n ih =>
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hle : |s / 2 - n| ≤ n + 1 := by
      rw [abs_le]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      constructor <;> linarith
    rw [bk_succ, abs_div, abs_mul, abs_of_pos hn1, div_le_one hn1]
    calc |bk s n| * |s / 2 - n| ≤ 1 * (n + 1) := mul_le_mul ih hle (abs_nonneg _) zero_le_one
      _ = n + 1 := one_mul _

theorem abs_bk_le {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) {n : ℕ} (hn : 1 ≤ n) :
    |bk s n| ≤ s / 2 / n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [bk_one, abs_of_nonneg (by linarith)]
    norm_num
  | succ n hn ih =>
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hle : |s / 2 - n| ≤ n := by
      rw [abs_le]
      constructor <;> linarith
    rw [bk_succ, abs_div, abs_mul, abs_of_pos hn1]
    push_cast
    have hnpos : (0 : ℝ) < n := by linarith
    calc |bk s n| * |s / 2 - n| / (n + 1) ≤ s / 2 / n * n / (n + 1) := by
          apply div_le_div_of_nonneg_right _ hn1.le
          exact mul_le_mul ih hle (abs_nonneg _) (div_nonneg (by linarith) hnpos.le)
      _ = s / 2 / (n + 1) := by
          rw [div_mul_cancel₀ _ hnpos.ne']

/-! ## Parseval for an absolutely summable sequence -/

theorem conj_cexpR (y : ℝ) : conj (cexpR y) = cexpR (-y) := by
  unfold cexpR
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem cexpR_pow (y : ℝ) (k : ℕ) : cexpR y ^ k = cexpR (k * y) := by
  unfold cexpR
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `∫₀¹ e(mθ) dθ = [m = 0]` for an integer `m`. -/
theorem integral_cexpR_int (m : ℤ) :
    ∫ θ in Set.Ioc (0 : ℝ) 1, cexpR (2 * π * (m * θ)) = if m = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hm
  · subst hm
    have hfun : (fun θ : ℝ => cexpR (2 * π * (((0 : ℤ) : ℝ) * θ))) = fun _ : ℝ => (1 : ℂ) := by
      funext θ
      unfold cexpR
      simp
    rw [hfun, intervalIntegral.integral_const]
    simp
  · have hc : (2 * π * (m : ℂ) * Complex.I) ≠ 0 := by
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hm' : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) hm') Complex.I_ne_zero
    have hfun : (fun θ : ℝ => cexpR (2 * π * (m * θ)))
        = fun θ : ℝ => Complex.exp ((2 * π * (m : ℂ) * Complex.I) * θ) := by
      funext θ
      unfold cexpR
      congr 1
      push_cast
      ring
    rw [hfun, integral_exp_mul_complex hc]
    have e1 : Complex.exp (2 * π * (m : ℂ) * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      have e : (2 * π * (m : ℂ) * Complex.I * ((1 : ℝ) : ℂ)) = (m : ℂ) * (2 * π * Complex.I) := by
        push_cast
        ring
      rw [e]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [e1]
    simp

/-- `∫₀¹ e(θ)ᵏ conj(e(θ))ˡ dθ = [k = l]`. -/
theorem integral_pow_conj_pow (k l : ℕ) :
    ∫ θ in Set.Ioc (0 : ℝ) 1, cexpR (2 * π * θ) ^ k * conj (cexpR (2 * π * θ)) ^ l
      = if k = l then 1 else 0 := by
  have hfun : (fun θ : ℝ => cexpR (2 * π * θ) ^ k * conj (cexpR (2 * π * θ)) ^ l)
      = fun θ : ℝ => cexpR (2 * π * ((((k : ℤ) - l : ℤ) : ℝ) * θ)) := by
    funext θ
    rw [conj_cexpR, cexpR_pow, cexpR_pow, ← cexpR_add]
    congr 1
    push_cast
    ring
  rw [hfun, integral_cexpR_int]
  have h : ((k : ℤ) - l = 0) ↔ k = l := by
    constructor
    · intro h
      omega
    · intro h
      omega
  simp only [h]

/-- The terms of `|∑ cₙ e(θ)ⁿ|²` as a double series. -/
noncomputable def parG (c : ℕ → ℝ) (p : ℕ × ℕ) (θ : ℝ) : ℂ :=
  ((c p.1 : ℂ) * cexpR (2 * π * θ) ^ p.1) * conj ((c p.2 : ℂ) * cexpR (2 * π * θ) ^ p.2)

theorem continuous_cexpR_two_pi : Continuous fun θ : ℝ => cexpR (2 * π * θ) := by
  have h1 : Continuous fun θ : ℝ => 2 * π * θ := continuous_const.mul continuous_id
  exact continuous_cexpR.comp h1

/-- **Parseval**: `∫₀¹ |∑ cₙ e(θ)ⁿ|² dθ = ∑ cₙ²` for `∑ |cₙ| < ∞`. -/
theorem integral_norm_sq_tsum {c : ℕ → ℝ} (hc : Summable fun n => |c n|) :
    ∫ θ in Set.Ioc (0 : ℝ) 1, ‖∑' n, (c n : ℂ) * cexpR (2 * π * θ) ^ n‖ ^ 2
      = ∑' n, c n ^ 2 := by
  have hfn : ∀ (θ : ℝ) (n : ℕ), ‖(c n : ℂ) * cexpR (2 * π * θ) ^ n‖ = |c n| := by
    intro θ n
    rw [norm_mul, norm_pow, norm_cexpR, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hfc : ∀ (θ : ℝ) (n : ℕ), ‖conj ((c n : ℂ) * cexpR (2 * π * θ) ^ n)‖ = |c n| := by
    intro θ n
    rw [Complex.norm_conj, hfn]
  have hpt : ∀ θ : ℝ, ‖∑' n, (c n : ℂ) * cexpR (2 * π * θ) ^ n‖ ^ 2
      = (∑' p, parG c p θ).re := by
    intro θ
    have h1 : (∑' n, (c n : ℂ) * cexpR (2 * π * θ) ^ n)
        * (∑' n, conj ((c n : ℂ) * cexpR (2 * π * θ) ^ n)) = ∑' p, parG c p θ :=
      tsum_mul_tsum_of_summable_norm (hc.congr (fun n => (hfn θ n).symm))
        (hc.congr (fun n => (hfc θ n).symm))
    rw [← Complex.conj_tsum, Complex.mul_conj'] at h1
    rw [← h1, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hGn : ∀ (p : ℕ × ℕ) (θ : ℝ), ‖parG c p θ‖ = |c p.1| * |c p.2| := by
    intro p θ
    unfold parG
    rw [norm_mul, hfn, hfc]
  have hGc : ∀ p : ℕ × ℕ, Continuous (parG c p) := by
    intro p
    have he := continuous_cexpR_two_pi
    have h1 : Continuous fun θ : ℝ => (c p.1 : ℂ) * cexpR (2 * π * θ) ^ p.1 :=
      continuous_const.mul (he.pow p.1)
    have h2 : Continuous fun θ : ℝ => (c p.2 : ℂ) * cexpR (2 * π * θ) ^ p.2 :=
      continuous_const.mul (he.pow p.2)
    exact h1.mul (Complex.continuous_conj.comp h2)
  have hcn : Summable fun n : ℕ => ‖|c n|‖ := by
    refine hc.congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_abs]
  have hsumG : Summable fun p : ℕ × ℕ => |c p.1| * |c p.2| :=
    summable_mul_of_summable_norm (f := fun n : ℕ => |c n|) (g := fun n : ℕ => |c n|) hcn hcn
  have hcont : Continuous fun θ : ℝ => ∑' p, parG c p θ :=
    continuous_tsum hGc hsumG (fun p θ => (hGn p θ).le)
  have hintS : Integrable (fun θ : ℝ => ∑' p, parG c p θ)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := hcont.integrableOn_Ioc
  have hGint : ∀ p : ℕ × ℕ, Integrable (parG c p) ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    fun p => (hGc p).integrableOn_Ioc
  have hone : ∀ a : ℝ, ∫ _ in Set.Ioc (0 : ℝ) 1, a = a := by
    intro a
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const]
    simp
  have hsumint : Summable fun p : ℕ × ℕ => ∫ θ in Set.Ioc (0 : ℝ) 1, ‖parG c p θ‖ := by
    refine hsumG.congr (fun p => ?_)
    have hfun : (fun θ : ℝ => ‖parG c p θ‖) = fun _ : ℝ => |c p.1| * |c p.2| := funext (hGn p)
    rw [hfun, hone]
  have hGval : ∀ p : ℕ × ℕ, ∫ θ in Set.Ioc (0 : ℝ) 1, parG c p θ
      = ((c p.1 * c p.2 : ℝ) : ℂ) * (if p.1 = p.2 then 1 else 0) := by
    intro p
    have hfun : (fun θ : ℝ => parG c p θ) = fun θ : ℝ => ((c p.1 * c p.2 : ℝ) : ℂ)
        * (cexpR (2 * π * θ) ^ p.1 * conj (cexpR (2 * π * θ)) ^ p.2) := by
      funext θ
      unfold parG
      rw [map_mul, map_pow, Complex.conj_ofReal]
      push_cast
      ring
    rw [hfun, integral_const_mul, integral_pow_conj_pow]
  -- the diagonal
  have hdiag : ∑' p : ℕ × ℕ, ((c p.1 * c p.2 : ℝ) : ℂ) * (if p.1 = p.2 then 1 else 0)
      = ∑' k : ℕ, ((c k ^ 2 : ℝ) : ℂ) := by
    have hinj : Function.Injective (fun k : ℕ => (k, k)) := fun a b h => congrArg Prod.fst h
    have hsupp : Function.support
        (fun p : ℕ × ℕ => ((c p.1 * c p.2 : ℝ) : ℂ) * (if p.1 = p.2 then 1 else 0))
        ⊆ Set.range (fun k : ℕ => (k, k)) := by
      intro p hp
      by_cases h : p.1 = p.2
      · exact ⟨p.1, Prod.ext rfl h⟩
      · exfalso
        apply hp
        simp [h]
    rw [← hinj.tsum_eq hsupp]
    congr 1
    funext k
    show ((c k * c k : ℝ) : ℂ) * (if k = k then 1 else 0) = ((c k ^ 2 : ℝ) : ℂ)
    rw [if_pos rfl, mul_one, sq]
  calc ∫ θ in Set.Ioc (0 : ℝ) 1, ‖∑' n, (c n : ℂ) * cexpR (2 * π * θ) ^ n‖ ^ 2
      = ∫ θ in Set.Ioc (0 : ℝ) 1, (∑' p, parG c p θ).re :=
        setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hpt θ)
    _ = (∫ θ in Set.Ioc (0 : ℝ) 1, ∑' p, parG c p θ).re :=
        Complex.reCLM.integral_comp_comm hintS
    _ = (∑' p, ∫ θ in Set.Ioc (0 : ℝ) 1, parG c p θ).re := by
        rw [integral_tsum_of_summable_integral_norm hGint hsumint]
    _ = (∑' k : ℕ, ((c k ^ 2 : ℝ) : ℂ)).re := by
        rw [← hdiag]
        congr 1
        exact tsum_congr hGval
    _ = ∑' n, c n ^ 2 := by
        rw [← Complex.ofReal_tsum, Complex.ofReal_re]

/-! ## The binomial series -/

theorem hasSum_binomial (s : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((bk s n : ℝ) : ℂ) * z ^ n) ((1 + z) ^ (((s / 2 : ℝ)) : ℂ)) := by
  have hy : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hz
  have hb := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := ((s / 2 : ℝ) : ℂ))).hasSum hy
  have he : ∀ n : ℕ, binomialSeries ℂ ((s / 2 : ℝ) : ℂ) n (fun _ => z)
      = ((bk s n : ℝ) : ℂ) * z ^ n := by
    intro n
    rw [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, bk,
      Complex.ofReal_choose]
  rw [funext he, zero_add] at hb
  exact hb

/-- `|1 + r e(θ)|^s = |∑ bₙ rⁿ e(θ)ⁿ|²` for `0 ≤ r < 1`. -/
theorem rpow_rhoN_one_eq {s r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    rhoN 1 r θ ^ s = ‖∑' n, ((bk s n * r ^ n : ℝ) : ℂ) * cexpR (2 * π * θ) ^ n‖ ^ 2 := by
  have hzn : ‖(r : ℂ) * cexpR (2 * π * θ)‖ < 1 := by
    rw [norm_mul, norm_cexpR, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0]
    exact hr1
  have hb := hasSum_binomial s hzn
  have hsum : ∑' n, ((bk s n * r ^ n : ℝ) : ℂ) * cexpR (2 * π * θ) ^ n
      = (1 + (r : ℂ) * cexpR (2 * π * θ)) ^ (((s / 2 : ℝ)) : ℂ) := by
    rw [← hb.tsum_eq]
    congr 1
    funext n
    push_cast
    ring
  have hρ : rhoN 1 r θ = ‖1 + (r : ℂ) * cexpR (2 * π * θ)‖ := by
    show ‖((1 : ℝ) : ℂ) + (r : ℂ) * cexpR (2 * π * θ)‖ = _
    rw [Complex.ofReal_one]
  rw [hsum, Complex.norm_cpow_real, hρ, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

theorem summable_abs_bk_mul {s r : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => |bk s n * r ^ n| := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one hr0 hr1)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hr0 n)]
  calc |bk s n| * r ^ n ≤ 1 * r ^ n :=
        mul_le_mul_of_nonneg_right (abs_bk_le_one hs0 hs2 n) (pow_nonneg hr0 n)
    _ = r ^ n := one_mul _

/-- **`M_s(1, r) = ∑ bₙ² r²ⁿ`** for `0 ≤ s ≤ 2`, `0 ≤ r < 1`. -/
theorem angM_one_eq_tsum {s r : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    angM s 1 r = ∑' n, (bk s n * r ^ n) ^ 2 := by
  unfold angM
  rw [setIntegral_congr_fun measurableSet_Ioc (fun θ _ => rpow_rhoN_one_eq hr0 hr1 θ)]
  exact integral_norm_sq_tsum (summable_abs_bk_mul hs0 hs2 hr0 hr1)

/-! ## `h_s` -/

/-- `h_s(w) = M_s(1, √w) - 1`. -/
noncomputable def hS (s w : ℝ) : ℝ := angM s 1 (Real.sqrt w) - 1

theorem summable_bk_sq {s w : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Summable fun n : ℕ => bk s (n + 1) ^ 2 * w ^ (n + 1) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (pow_nonneg hw0 _))
    (fun n => ?_) ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hw0 hw1))
  have h1 := abs_bk_le_one hs0 hs2 (n + 1)
  have h2 : bk s (n + 1) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (bk s (n + 1))]
  calc bk s (n + 1) ^ 2 * w ^ (n + 1) ≤ 1 * w ^ (n + 1) :=
        mul_le_mul_of_nonneg_right h2 (pow_nonneg hw0 _)
    _ = w ^ (n + 1) := one_mul _

/-- **`h_s(w) = ∑_{n ≥ 1} bₙ² wⁿ`** for `0 ≤ s ≤ 2`, `0 ≤ w < 1`. -/
theorem hS_eq_tsum {s w : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    hS s w = ∑' n : ℕ, bk s (n + 1) ^ 2 * w ^ (n + 1) := by
  have hr0 := Real.sqrt_nonneg w
  have hr1 : Real.sqrt w < 1 := by
    rw [Real.sqrt_lt' one_pos]
    simpa using hw1
  have e1 : ∀ n : ℕ, (bk s n * Real.sqrt w ^ n) ^ 2 = bk s n ^ 2 * w ^ n := by
    intro n
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt hw0]
  have hsq : Summable fun n : ℕ => (bk s n * Real.sqrt w ^ n) ^ 2 := by
    refine (summable_nat_add_iff 1).mp ?_
    exact (summable_bk_sq hs0 hs2 hw0 hw1).congr (fun n => (e1 (n + 1)).symm)
  unfold hS
  rw [angM_one_eq_tsum hs0 hs2 hr0 hr1, hsq.tsum_eq_zero_add, e1 0, bk_zero]
  simp only [e1]
  ring

theorem hS_nonneg {s w : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    0 ≤ hS s w := by
  rw [hS_eq_tsum hs0 hs2 hw0 hw1]
  exact tsum_nonneg (fun n => mul_nonneg (sq_nonneg _) (pow_nonneg hw0 _))

/-- **`h_s(w) ≤ (s²/2) w`** for `0 ≤ s ≤ 2`, `0 ≤ w < 1`. -/
theorem hS_le {s w : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    hS s w ≤ s ^ 2 / 2 * w := by
  have hz : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6) := by
    have h := hasSum_zeta_two
    rw [← hasSum_nat_add_iff' 1] at h
    simpa using h
  have hzs : Summable fun n : ℕ => s ^ 2 / 4 * w * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    hz.summable.mul_left _
  have hterm : ∀ n : ℕ, bk s (n + 1) ^ 2 * w ^ (n + 1)
      ≤ s ^ 2 / 4 * w * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hb := abs_bk_le hs0 hs2 (Nat.succ_le_succ (Nat.zero_le n))
    have hb2 : bk s (n + 1) ^ 2 ≤ (s / 2 / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hw : w ^ (n + 1) ≤ w := by
      calc w ^ (n + 1) = w ^ n * w := pow_succ w n
        _ ≤ 1 * w := mul_le_mul_of_nonneg_right (pow_le_one₀ hw0 hw1.le) hw0
        _ = w := one_mul w
    have e : (s / 2 / ((n + 1 : ℕ) : ℝ)) ^ 2 * w = s ^ 2 / 4 * w * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      ring
    calc bk s (n + 1) ^ 2 * w ^ (n + 1) ≤ (s / 2 / ((n + 1 : ℕ) : ℝ)) ^ 2 * w :=
          mul_le_mul hb2 hw (pow_nonneg hw0 _) (sq_nonneg _)
      _ = _ := e
  have hle := Summable.tsum_le_tsum hterm (summable_bk_sq hs0 hs2 hw0 hw1) hzs
  rw [tsum_mul_left, hz.tsum_eq] at hle
  rw [hS_eq_tsum hs0 hs2 hw0 hw1]
  have hπ : π ^ 2 / 6 ≤ 2 := by
    have h1 := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  have hsw : 0 ≤ s ^ 2 / 4 * w := mul_nonneg (by positivity) hw0
  calc ∑' n : ℕ, bk s (n + 1) ^ 2 * w ^ (n + 1) ≤ s ^ 2 / 4 * w * (π ^ 2 / 6) := hle
    _ ≤ s ^ 2 / 4 * w * 2 := mul_le_mul_of_nonneg_left hπ hsw
    _ = s ^ 2 / 2 * w := by ring

/-! ## Homogeneity and symmetry of `M_s` -/

theorem rhoN_homog {τ : ℝ} (hτ : 0 < τ) (t θ : ℝ) : rhoN τ t θ = τ * rhoN 1 (t / τ) θ := by
  have hτc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  have hinv : (τ : ℂ) * (τ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hτc
  have e : (τ : ℂ) + t * cexpR (2 * π * θ)
      = (τ : ℂ) * (((1 : ℝ) : ℂ) + ((t / τ : ℝ) : ℂ) * cexpR (2 * π * θ)) := by
    push_cast
    linear_combination (-((t : ℂ) * cexpR (2 * π * θ))) * hinv
  unfold rhoN
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le]

/-- `M_s(τ, t) = τ^s M_s(1, t/τ)` for `τ > 0`. -/
theorem angM_homog {s τ : ℝ} (hτ : 0 < τ) (t : ℝ) : angM s τ t = τ ^ s * angM s 1 (t / τ) := by
  unfold angM
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
  show rhoN τ t θ ^ s = τ ^ s * rhoN 1 (t / τ) θ ^ s
  rw [rhoN_homog hτ, Real.mul_rpow hτ.le (rhoN_nonneg _ _ _)]

theorem cexpR_two_pi_add_one (θ : ℝ) : cexpR (2 * π * (θ + 1)) = cexpR (2 * π * θ) := by
  have h1 : cexpR (2 * π) = 1 := by
    unfold cexpR
    have e : ((2 * π : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I := by push_cast; ring
    rw [e]
    exact Complex.exp_two_pi_mul_I
  rw [mul_add, mul_one, cexpR_add, h1, mul_one]

theorem rhoN_add_one (τ t θ : ℝ) : rhoN τ t (θ + 1) = rhoN τ t θ := by
  unfold rhoN
  rw [cexpR_two_pi_add_one]

theorem rhoN_swap (τ t θ : ℝ) : rhoN τ t θ = rhoN t τ (-θ) := by
  have hprod : cexpR (2 * π * (-θ)) * cexpR (2 * π * θ) = 1 := by
    rw [← cexpR_add]
    have e : 2 * π * (-θ) + 2 * π * θ = 0 := by ring
    rw [e]
    unfold cexpR
    simp
  have e : (t : ℂ) + τ * cexpR (2 * π * (-θ))
      = cexpR (2 * π * (-θ)) * ((τ : ℂ) + t * cexpR (2 * π * θ)) := by
    linear_combination (-(t : ℂ)) * hprod
  unfold rhoN
  rw [e, norm_mul, norm_cexpR, one_mul]

/-- **`M_s(τ, t) = M_s(t, τ)`**. -/
theorem angM_symm (s τ t : ℝ) : angM s τ t = angM s t τ := by
  have hper : Function.Periodic (fun θ : ℝ => rhoN t τ θ ^ s) 1 := by
    intro θ
    show rhoN t τ (θ + 1) ^ s = rhoN t τ θ ^ s
    rw [rhoN_add_one]
  unfold angM
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  have h1 : ∫ θ in (0 : ℝ)..1, rhoN τ t θ ^ s = ∫ θ in (0 : ℝ)..1, rhoN t τ (-θ) ^ s := by
    congr 1
    funext θ
    exact congrArg (· ^ s) (rhoN_swap τ t θ)
  have h3 := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (f := fun θ : ℝ => rhoN t τ θ ^ s)
  have h2 := hper.intervalIntegral_add_eq (-1) 0
  norm_num at h2 h3
  rw [h1, h3, h2]

end Tower.RV6
