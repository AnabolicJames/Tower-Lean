import Mathlib
import Tower.RV6.QSeries
import Tower.RV6.Eichler

/-!
# `q`-series on the imaginary axis, second part

* `continuousOn_qa_Ioi`: `qa C` is continuous on `(0, ∞)`.
* `integrable_qa_pow`: `qa C y · y^k` is integrable on `(0, ∞)` when `∑ |C(n)|/n^{k+1}` converges.
* `hasDerivAt_qa`: termwise differentiation, `(qa C)'(y) = -2π qa (n C(n)) y`.
* `qa_add`, `qa_const_mul`: linearity in the coefficients.
* `conv`, `qa_conv`: the Cauchy product under polynomial bounds; `conv_abs_le_gen`,
  `conv_poly_bound`: bounds for it; `conv_mul_index`:
  `∑_{i+j=n} a(i) j a(j) = (n/2) ∑_{i+j=n} a(i) a(j)`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## Continuity -/

theorem continuousOn_qa_Ioi {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K) :
    ContinuousOn (qa C) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hmem : Set.Ici (x / 2) ∈ nhds x := Ici_mem_nhds (by linarith)
  exact ((continuousOn_qa hC (by linarith : (0 : ℝ) < x / 2)).continuousAt hmem).continuousWithinAt

/-! ## Integrability -/

/-- `qa C y · y^k` is integrable on `(0, ∞)` when `∑ |C(n)|/n^{k+1}` converges: it is dominated
by the series of the absolute values, whose integral is that sum. -/
theorem integrable_qa_pow {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K)
    (h0 : C 0 = 0) (k : ℕ)
    (hs : Summable fun n : ℕ => |C (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (k + 1)) :
    Integrable (fun y : ℝ => qa C y * y ^ k) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  by_cases hz : ∀ n : ℕ, C (n + 1) = 0
  · have hC0 : ∀ n : ℕ, C n = 0 := by
      intro n
      cases n with
      | zero => exact h0
      | succ m => exact hz m
    have hfun : (fun y : ℝ => qa C y * y ^ k) = fun _ => (0 : ℝ) := by
      funext y
      simp only [qa, hC0, zero_mul, tsum_zero]
    rw [hfun]
    first
      | exact integrable_zero _
      | exact integrable_zero _ _ _
      | simp
  · push_neg at hz
    obtain ⟨m, hm⟩ := hz
    have hA : ∀ n : ℕ, |(|C n|)| ≤ B * (n : ℝ) ^ K := fun n => by
      rw [abs_abs]
      exact hC n
    have hs' : Summable fun n : ℕ => |(|C (n + 1)|)| / ((n + 1 : ℕ) : ℝ) ^ (k + 1) :=
      hs.congr (fun n => by rw [abs_abs])
    have hval := integral_qa (fun n : ℕ => |C n|) (by simp [h0]) k hs'
      (fun y hy => summable_qa hA hy)
    have hpos : 0 < ∑' n : ℕ, |C (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (k + 1) :=
      hs.tsum_pos (fun n => div_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) m
        (div_pos (abs_pos.mpr hm) (pow_pos (by exact_mod_cast Nat.succ_pos m) _))
    have hg : Integrable (fun y : ℝ => qa (fun n : ℕ => |C n|) y * y ^ k)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      refine Integrable.of_integral_ne_zero ?_
      rw [hval]
      have hc : (0 : ℝ) < (k.factorial : ℝ) / (2 * π) ^ (k + 1) :=
        div_pos (by exact_mod_cast Nat.factorial_pos k) (by positivity)
      exact (mul_pos hc hpos).ne'
    refine hg.mono'
      (((continuousOn_qa_Ioi hC).mul (continuous_pow k).continuousOn).aestronglyMeasurable
        measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    have hyk : (0 : ℝ) ≤ y ^ k := pow_nonneg hy0.le k
    show ‖qa C y * y ^ k‖ ≤ qa (fun n : ℕ => |C n|) y * y ^ k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hyk]
    refine mul_le_mul_of_nonneg_right ?_ hyk
    have hsn : Summable fun n : ℕ => ‖C n * Real.exp (-(2 * π * (n : ℝ) * y))‖ := by
      refine (summable_qa_abs hC hy0).congr (fun n => ?_)
      show |C n| * Real.exp (-(2 * π * (n : ℝ) * y)) = ‖C n * Real.exp (-(2 * π * (n : ℝ) * y))‖
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h2 : ∑' n : ℕ, ‖C n * Real.exp (-(2 * π * (n : ℝ) * y))‖
        = qa (fun n : ℕ => |C n|) y := by
      unfold qa
      refine tsum_congr (fun n => ?_)
      show ‖C n * Real.exp (-(2 * π * (n : ℝ) * y))‖ = |C n| * Real.exp (-(2 * π * (n : ℝ) * y))
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := norm_tsum_le_tsum_norm hsn
    rw [Real.norm_eq_abs, h2] at h1
    exact h1

/-! ## Termwise differentiation -/

/-- `(qa C)'(y) = -2π qa (n C(n)) y` for `y > 0`. -/
theorem hasDerivAt_qa {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (qa C) (-(2 * π) * qa (fun n => (n : ℝ) * C n) y) y := by
  have hε : (0 : ℝ) < y / 2 := by linarith
  have hC' : ∀ n : ℕ, |(n : ℝ) * C n| ≤ B * (n : ℝ) ^ (K + 1) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [abs_mul, abs_of_nonneg hn0]
    calc (n : ℝ) * |C n| ≤ (n : ℝ) * (B * (n : ℝ) ^ K) :=
          mul_le_mul_of_nonneg_left (hC n) hn0
      _ = B * (n : ℝ) ^ (K + 1) := by ring
  have hu : Summable fun n : ℕ =>
      (2 * π) * (|(n : ℝ) * C n| * Real.exp (-(2 * π * (n : ℝ) * (y / 2)))) :=
    (summable_qa_abs hC' hε).mul_left (2 * π)
  have hg : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioi (y / 2) →
      HasDerivAt (fun s : ℝ => C n * Real.exp (-(2 * π * (n : ℝ) * s)))
        (C n * (Real.exp (-(2 * π * (n : ℝ) * t)) * (-(2 * π * (n : ℝ) * 1)))) t := by
    intro n t _
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(2 * π * (n : ℝ) * s)))
        (Real.exp (-(2 * π * (n : ℝ) * t)) * (-(2 * π * (n : ℝ) * 1))) t :=
      (((hasDerivAt_id' t).const_mul (2 * π * (n : ℝ))).neg).exp
    exact h1.const_mul (C n)
  have hg' : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioi (y / 2) →
      ‖C n * (Real.exp (-(2 * π * (n : ℝ) * t)) * (-(2 * π * (n : ℝ) * 1)))‖
        ≤ (2 * π) * (|(n : ℝ) * C n| * Real.exp (-(2 * π * (n : ℝ) * (y / 2)))) := by
    intro n t ht
    have ht' : y / 2 < t := ht
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) ≤ 2 * π * (n : ℝ) := by positivity
    have hexp : Real.exp (-(2 * π * (n : ℝ) * t)) ≤ Real.exp (-(2 * π * (n : ℝ) * (y / 2))) := by
      refine Real.exp_le_exp.mpr ?_
      have h3 := mul_le_mul_of_nonneg_left ht'.le h2
      linarith
    have hE : 0 ≤ Real.exp (-(2 * π * (n : ℝ) * t)) := (Real.exp_pos _).le
    have habs : |(n : ℝ) * C n| = (n : ℝ) * |C n| := by rw [abs_mul, abs_of_nonneg hn0]
    have h21 : (0 : ℝ) ≤ 2 * π * (n : ℝ) * 1 := by positivity
    have hnorm : ‖C n * (Real.exp (-(2 * π * (n : ℝ) * t)) * (-(2 * π * (n : ℝ) * 1)))‖
        = (2 * π) * ((n : ℝ) * |C n| * Real.exp (-(2 * π * (n : ℝ) * t))) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg hE, abs_of_nonneg h21]
      ring
    rw [hnorm, habs]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hexp (mul_nonneg hn0 (abs_nonneg _))) (by positivity)
  have hmem : y ∈ Set.Ioi (y / 2) := by
    show y / 2 < y
    linarith
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hg hg' hmem
    (summable_qa hC hy) hmem
  have hval : ∑' n : ℕ, C n * (Real.exp (-(2 * π * (n : ℝ) * y)) * (-(2 * π * (n : ℝ) * 1)))
      = -(2 * π) * qa (fun n => (n : ℝ) * C n) y := by
    unfold qa
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    show C n * (Real.exp (-(2 * π * (n : ℝ) * y)) * (-(2 * π * (n : ℝ) * 1)))
      = -(2 * π) * ((n : ℝ) * C n * Real.exp (-(2 * π * (n : ℝ) * y)))
    ring
  have key' : HasDerivAt (qa C)
      (∑' n : ℕ, C n * (Real.exp (-(2 * π * (n : ℝ) * y)) * (-(2 * π * (n : ℝ) * 1)))) y := key
  exact key'.congr_deriv hval

/-! ## Linearity in the coefficients -/

theorem qa_add {C D : ℕ → ℝ} {y : ℝ}
    (hC : Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hD : Summable fun n : ℕ => D n * Real.exp (-(2 * π * (n : ℝ) * y))) :
    qa (fun n => C n + D n) y = qa C y + qa D y := by
  have h := hC.tsum_add hD
  unfold qa
  rw [← h]
  refine tsum_congr (fun n => ?_)
  show (C n + D n) * Real.exp (-(2 * π * (n : ℝ) * y))
    = C n * Real.exp (-(2 * π * (n : ℝ) * y)) + D n * Real.exp (-(2 * π * (n : ℝ) * y))
  ring

theorem qa_const_mul (c : ℝ) (C : ℕ → ℝ) (y : ℝ) :
    qa (fun n => c * C n) y = c * qa C y := by
  unfold qa
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  show c * C n * Real.exp (-(2 * π * (n : ℝ) * y)) = c * (C n * Real.exp (-(2 * π * (n : ℝ) * y)))
  ring

/-! ## Cauchy products -/

/-- The Cauchy product of two sequences. -/
noncomputable def conv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

theorem conv_abs_le_gen (a b : ℕ → ℝ) (n : ℕ) (A B : ℝ) (ha : ∀ i ≤ n, |a i| ≤ A)
    (hb : ∀ i ≤ n, |b i| ≤ B) : |conv a b n| ≤ ((n : ℝ) + 1) * (A * B) := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (ha 0 (Nat.zero_le n))
  show |∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2| ≤ ((n : ℝ) + 1) * (A * B)
  calc |∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2|
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, |a p.1 * b p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal n, A * B := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rw [abs_mul]
        exact mul_le_mul (ha p.1 (by omega)) (hb p.2 (by omega)) (abs_nonneg _) hA0
    _ = ((n : ℝ) + 1) * (A * B) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul, Nat.cast_add_one]

/-- A polynomial bound for the Cauchy product of two sequences of polynomial growth. -/
theorem conv_poly_bound {a b : ℕ → ℝ} {A B : ℝ} {p q : ℕ} (ha0 : a 0 = 0)
    (ha : ∀ n, |a n| ≤ A * (n : ℝ) ^ p) (hb : ∀ n, |b n| ≤ B * (n : ℝ) ^ q) (n : ℕ) :
    |conv a b n| ≤ 2 * (A * B) * (n : ℝ) ^ (p + q + 1) := by
  have hA0 : 0 ≤ A := by
    have h := le_trans (abs_nonneg (a 1)) (ha 1)
    rw [Nat.cast_one, one_pow, mul_one] at h
    exact h
  have hB0 : 0 ≤ B := by
    have h := le_trans (abs_nonneg (b 1)) (hb 1)
    rw [Nat.cast_one, one_pow, mul_one] at h
    exact h
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have h1 := conv_abs_le_gen a b 0 0 (|b 0|)
      (fun i hi => le_of_eq (by rw [Nat.le_zero.mp hi, ha0, abs_zero]))
      (fun i hi => le_of_eq (by rw [Nat.le_zero.mp hi]))
    have h2 : |conv a b 0| ≤ 0 := by
      calc |conv a b 0| ≤ (((0 : ℕ) : ℝ) + 1) * (0 * |b 0|) := h1
        _ = 0 := by ring
    exact le_trans h2 (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hA0 hB0))
      (pow_nonneg (Nat.cast_nonneg _) _))
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
    have h1 := conv_abs_le_gen a b n (A * (n : ℝ) ^ p) (B * (n : ℝ) ^ q)
      (fun i hi => le_trans (ha i) (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg i) (by exact_mod_cast hi) p) hA0))
      (fun i hi => le_trans (hb i) (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg i) (by exact_mod_cast hi) q) hB0))
    have hnn : (0 : ℝ) ≤ A * (n : ℝ) ^ p * (B * (n : ℝ) ^ q) :=
      mul_nonneg (mul_nonneg hA0 (pow_nonneg hn0 p)) (mul_nonneg hB0 (pow_nonneg hn0 q))
    calc |conv a b n| ≤ ((n : ℝ) + 1) * (A * (n : ℝ) ^ p * (B * (n : ℝ) ^ q)) := h1
      _ ≤ (2 * (n : ℝ)) * (A * (n : ℝ) ^ p * (B * (n : ℝ) ^ q)) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
      _ = 2 * (A * B) * (n : ℝ) ^ (p + q + 1) := by ring

/-- The product of two series of polynomial growth is the series of the Cauchy product. -/
theorem qa_conv {C D : ℕ → ℝ} {B B' : ℝ} {K K' : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K)
    (hD : ∀ n, |D n| ≤ B' * (n : ℝ) ^ K') {y : ℝ} (hy : 0 < y) :
    qa C y * qa D y = qa (conv C D) y :=
  qa_mul (summable_qa_abs hC hy) (summable_qa_abs hD hy)

/-- `∑_{i+j=n} a(i) j a(j) = (n/2) ∑_{i+j=n} a(i) a(j)`. -/
theorem conv_mul_index (a : ℕ → ℝ) (n : ℕ) :
    conv a (fun j => (j : ℝ) * a j) n = (n : ℝ) / 2 * conv a a n := by
  have hswap : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * ((p.2 : ℝ) * a p.2)
      = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.2 * ((p.1 : ℝ) * a p.1) :=
    Finset.Nat.sum_antidiagonal_swap (n := n) (f := fun p : ℕ × ℕ => a p.2 * ((p.1 : ℝ) * a p.1))
  have hsum : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * ((p.2 : ℝ) * a p.2)
        + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.2 * ((p.1 : ℝ) * a p.1)
      = (n : ℝ) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * a p.2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hc : (n : ℝ) = (p.1 : ℝ) + (p.2 : ℝ) := by rw [← hp', Nat.cast_add]
    rw [hc]
    ring
  show ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * ((p.2 : ℝ) * a p.2)
    = (n : ℝ) / 2 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * a p.2
  linear_combination (1 / 2 : ℝ) * hsum + (1 / 2 : ℝ) * hswap

end Tower.RV6
