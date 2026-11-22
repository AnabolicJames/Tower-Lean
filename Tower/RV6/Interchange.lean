import Mathlib
import Tower.RV6.QSeries
import Tower.RV6.Regroup
import Tower.RV6.Arith
import Tower.RV6.PhiKernel

/-!
# The interchange of Lemma 5.1, in single-index form

For coefficient sequences `A, B` of polynomial growth with `A 0 = B 0 = 0` and `e, f > 0`:

* `integral_qa_mul` (Tonelli):
  `∫₀^∞ qa A (e/(6y)) qa B (f y) y^{-(i+1)} dy = ∑_{m,n ≥ 1} A(m) B(n) PhiN (e m) (f n) (i+1)`,
  the family being absolutely summable.
* `integral_qa_mul_regroup`:
  `e^i · (that integral) = ∑_{N ≥ 1} PhiN 1 (e f N) (i+1) / N^i · ∑_{mn = N} A(m) B(n) n^i`.
* `swap_qa`: if `∑_{mn=N} A(m) B(n) n^i = ∑_{mn=N} A'(m) B'(n) n^i` for all `N`, then
  `e^i ∫ qa A (e/(6y)) qa B (f y) y^{-(i+1)} = f^i ∫ qa A' (f/(6y)) qa B' (e y) y^{-(i+1)}`.
* `interchange_three`, `interchange_four`: the two instances for the divisor sums, by the
  arithmetic identity `conv_sig_identity`.
-/

namespace Tower.RV6

open Real MeasureTheory

theorem pow_ratio_le {x : ℝ} (hx1 : 1 ≤ x) {K q : ℕ} (hq : K + 2 ≤ q) :
    x ^ K / x ^ q ≤ 1 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  rw [div_le_div_iff₀ (pow_pos hx0 q) (pow_pos hx0 2), one_mul, ← pow_add]
  exact pow_le_pow_right₀ hx1 hq

theorem summable_qa_shift_norm {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K)
    {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => ‖C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * x))‖ := by
  have h := (summable_nat_add_iff 1).mpr (summable_qa_abs hC hx)
  refine h.congr (fun n => ?_)
  show |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * x))
    = ‖C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * x))‖
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- The product of the two series, at `e/(6y)` and at `f y`, as a double series. -/
theorem qa_mul_fricke {A B : ℕ → ℝ} {CA CB : ℝ} {KA KB : ℕ}
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hA : ∀ n, |A n| ≤ CA * (n : ℝ) ^ KA) (hB : ∀ n, |B n| ≤ CB * (n : ℝ) ^ KB)
    {e f y : ℝ} (he : 0 < e) (hf : 0 < f) (hy : 0 < y) :
    qa A (e / (6 * y)) * qa B (f * y) = ∑' p : ℕ × ℕ, A (p.1 + 1) * B (p.2 + 1) * Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) := by
  have hx : 0 < e / (6 * y) := by positivity
  have hfy : 0 < f * y := by positivity
  rw [qa_eq_shift hA0 (summable_qa hA hx), qa_eq_shift hB0 (summable_qa hB hfy)]
  have h := tsum_mul_tsum_of_summable_norm (summable_qa_shift_norm hA hx)
    (summable_qa_shift_norm hB hfy)
  rw [h]
  refine tsum_congr (fun p => ?_)
  have hexp : Real.exp (-(2 * π * ((p.1 + 1 : ℕ) : ℝ) * (e / (6 * y))))
        * Real.exp (-(2 * π * ((p.2 + 1 : ℕ) : ℝ) * (f * y)))
      = Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

/-- **Tonelli.**  Termwise integration of the product of the two series. -/
theorem integral_qa_mul {A B : ℕ → ℝ} {CA CB : ℝ} {KA KB : ℕ}
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hA : ∀ n, |A n| ≤ CA * (n : ℝ) ^ KA) (hB : ∀ n, |B n| ≤ CB * (n : ℝ) ^ KB)
    {e f : ℝ} (he : 0 < e) (hf : 0 < f) (i : ℕ) :
    Summable (fun p : ℕ × ℕ => |A (p.1 + 1) * B (p.2 + 1)| * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1)) ∧
    ∫ y in Set.Ioi (0 : ℝ), qa A (e / (6 * y)) * qa B (f * y) / y ^ (i + 1)
      = ∑' p : ℕ × ℕ, A (p.1 + 1) * B (p.2 + 1) * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1) := by
  have hCA : 0 ≤ CA := by
    have h1 := hA 1
    rw [Nat.cast_one, one_pow, mul_one] at h1
    exact (abs_nonneg _).trans h1
  have hCB : 0 ≤ CB := by
    have h1 := hB 1
    rw [Nat.cast_one, one_pow, mul_one] at h1
    exact (abs_nonneg _).trans h1
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := fun n => by exact_mod_cast Nat.succ_pos n
  have hone : ∀ n : ℕ, (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
    fun n => by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hs2 : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 :=
    (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  obtain ⟨Wu, hWu⟩ : ∃ W : ℝ, W = CA * (((i + 1 + (KA + KB + 1)).factorial : ℝ) / (π * e / 3) ^ (i + 1 + (KA + KB + 1))) :=
    ⟨_, rfl⟩
  obtain ⟨Wv, hWv⟩ : ∃ W : ℝ, W = CB * (((KA + KB + 1).factorial : ℝ) / (2 * π * f) ^ (KA + KB + 1 + 1)) :=
    ⟨_, rfl⟩
  have hWu0 : 0 ≤ Wu := by
    rw [hWu]
    positivity
  have hWv0 : 0 ≤ Wv := by
    rw [hWv]
    positivity
  have alg : ∀ a b c d F : ℝ, a * b * (F / (c * d)) = a * (F / c) * (b / d) := by
    intro a b c d F
    ring
  have hU : ∀ m : ℕ, CA * ((m + 1 : ℕ) : ℝ) ^ KA
      * (((i + 1 + (KA + KB + 1)).factorial : ℝ) / (π * (e * ((m + 1 : ℕ) : ℝ)) / 3) ^ (i + 1 + (KA + KB + 1)))
      ≤ Wu * (1 / ((m + 1 : ℕ) : ℝ) ^ 2) := by
    intro m
    have hr := pow_ratio_le (hone m) (K := KA) (q := i + 1 + (KA + KB + 1)) (by omega)
    have hb : π * (e * ((m + 1 : ℕ) : ℝ)) / 3 = (π * e / 3) * ((m + 1 : ℕ) : ℝ) := by ring
    rw [hb, mul_pow, alg, ← hWu]
    exact mul_le_mul_of_nonneg_left hr hWu0
  have hV : ∀ n : ℕ, CB * ((n + 1 : ℕ) : ℝ) ^ KB
      * (((KA + KB + 1).factorial : ℝ) / (2 * π * (f * ((n + 1 : ℕ) : ℝ))) ^ (KA + KB + 1 + 1))
      ≤ Wv * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have hr := pow_ratio_le (hone n) (K := KB) (q := KA + KB + 1 + 1) (by omega)
    have hb : 2 * π * (f * ((n + 1 : ℕ) : ℝ)) = (2 * π * f) * ((n + 1 : ℕ) : ℝ) := by ring
    rw [hb, mul_pow, alg, ← hWv]
    exact mul_le_mul_of_nonneg_left hr hWv0
  have hbound : ∀ p : ℕ × ℕ, |A (p.1 + 1) * B (p.2 + 1)| * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1)
      ≤ Wu * (1 / ((p.1 + 1 : ℕ) : ℝ) ^ 2) * (Wv * (1 / ((p.2 + 1 : ℕ) : ℝ) ^ 2)) := by
    intro p
    have hΦ := PhiN_le (mul_pos he (hpos p.1)) (mul_pos hf (hpos p.2)) (i + 1) (KA + KB + 1)
    have hAB : |A (p.1 + 1) * B (p.2 + 1)| ≤ CA * ((p.1 + 1 : ℕ) : ℝ) ^ KA * (CB * ((p.2 + 1 : ℕ) : ℝ) ^ KB) := by
      rw [abs_mul]
      exact mul_le_mul (hA (p.1 + 1)) (hB (p.2 + 1)) (abs_nonneg _)
        (mul_nonneg hCA (pow_nonneg (hpos p.1).le _))
    have hD1 : (0 : ℝ) ≤ ((i + 1 + (KA + KB + 1)).factorial : ℝ) / (π * (e * ((p.1 + 1 : ℕ) : ℝ)) / 3) ^ (i + 1 + (KA + KB + 1)) :=
      div_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (mul_nonneg he.le (hpos p.1).le))
          (by norm_num)) _)
    have hD2 : (0 : ℝ) ≤ ((KA + KB + 1).factorial : ℝ) / (2 * π * (f * ((p.2 + 1 : ℕ) : ℝ))) ^ (KA + KB + 1 + 1) :=
      div_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
          (mul_nonneg hf.le (hpos p.2).le)) _)
    have hAB0 : (0 : ℝ) ≤ CA * ((p.1 + 1 : ℕ) : ℝ) ^ KA * (CB * ((p.2 + 1 : ℕ) : ℝ) ^ KB) :=
      mul_nonneg (mul_nonneg hCA (pow_nonneg (hpos p.1).le _))
        (mul_nonneg hCB (pow_nonneg (hpos p.2).le _))
    calc |A (p.1 + 1) * B (p.2 + 1)| * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1)
        ≤ CA * ((p.1 + 1 : ℕ) : ℝ) ^ KA * (CB * ((p.2 + 1 : ℕ) : ℝ) ^ KB)
            * (((i + 1 + (KA + KB + 1)).factorial : ℝ) / (π * (e * ((p.1 + 1 : ℕ) : ℝ)) / 3) ^ (i + 1 + (KA + KB + 1))
              * (((KA + KB + 1).factorial : ℝ) / (2 * π * (f * ((p.2 + 1 : ℕ) : ℝ))) ^ (KA + KB + 1 + 1))) :=
          mul_le_mul hAB hΦ (PhiN_nonneg _ _ _) hAB0
      _ = CA * ((p.1 + 1 : ℕ) : ℝ) ^ KA * (((i + 1 + (KA + KB + 1)).factorial : ℝ) / (π * (e * ((p.1 + 1 : ℕ) : ℝ)) / 3) ^ (i + 1 + (KA + KB + 1)))
            * (CB * ((p.2 + 1 : ℕ) : ℝ) ^ KB
              * (((KA + KB + 1).factorial : ℝ) / (2 * π * (f * ((p.2 + 1 : ℕ) : ℝ))) ^ (KA + KB + 1 + 1))) :=
          mul_mul_mul_comm _ _ _ _
      _ ≤ Wu * (1 / ((p.1 + 1 : ℕ) : ℝ) ^ 2) * (Wv * (1 / ((p.2 + 1 : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul (hU p.1) (hV p.2)
            (mul_nonneg (mul_nonneg hCB (pow_nonneg (hpos p.2).le _)) hD2)
            (mul_nonneg hWu0 (div_nonneg zero_le_one (pow_nonneg (hpos p.1).le _)))
  have hmaj : Summable fun p : ℕ × ℕ => Wu * (1 / ((p.1 + 1 : ℕ) : ℝ) ^ 2) * (Wv * (1 / ((p.2 + 1 : ℕ) : ℝ) ^ 2)) := by
    have hnu : Summable fun m : ℕ => ‖Wu * (1 / ((m + 1 : ℕ) : ℝ) ^ 2)‖ := by
      refine (hs2.mul_left Wu).congr (fun m => ?_)
      show Wu * (1 / ((m + 1 : ℕ) : ℝ) ^ 2) = ‖Wu * (1 / ((m + 1 : ℕ) : ℝ) ^ 2)‖
      rw [Real.norm_of_nonneg
        (mul_nonneg hWu0 (div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg _) _)))]
    have hnv : Summable fun n : ℕ => ‖Wv * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)‖ := by
      refine (hs2.mul_left Wv).congr (fun n => ?_)
      show Wv * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) = ‖Wv * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)‖
      rw [Real.norm_of_nonneg
        (mul_nonneg hWv0 (div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg _) _)))]
    have h := summable_mul_of_summable_norm hnu hnv
    exact h
  have hsummable : Summable (fun p : ℕ × ℕ => |A (p.1 + 1) * B (p.2 + 1)| * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1)) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (abs_nonneg _) (PhiN_nonneg _ _ _)) hbound hmaj
  refine ⟨hsummable, ?_⟩
  have hint : ∀ p : ℕ × ℕ, Integrable (fun y : ℝ => A (p.1 + 1) * B (p.2 + 1) * (Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) / y ^ (i + 1)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun p => (integrable_kernel (mul_pos he (hpos p.1)) (mul_pos hf (hpos p.2)) (i + 1)).const_mul _
  have hnorm : ∀ p : ℕ × ℕ,
      ∫ y in Set.Ioi (0 : ℝ), ‖A (p.1 + 1) * B (p.2 + 1) * (Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) / y ^ (i + 1))‖ = |A (p.1 + 1) * B (p.2 + 1)| * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1) := by
    intro p
    unfold PhiN
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    show ‖A (p.1 + 1) * B (p.2 + 1) * (Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) / y ^ (i + 1))‖ = |A (p.1 + 1) * B (p.2 + 1)| * (Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) / y ^ (i + 1))
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (div_nonneg (Real.exp_pos _).le (pow_nonneg hy0.le _))]
  have hsumInt : Summable fun p : ℕ × ℕ =>
      ∫ y in Set.Ioi (0 : ℝ), ‖A (p.1 + 1) * B (p.2 + 1) * (Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) / y ^ (i + 1))‖ :=
    hsummable.congr (fun p => (hnorm p).symm)
  have key := hasSum_integral_of_summable_integral_norm hint hsumInt
  have hval : ∀ p : ℕ × ℕ,
      ∫ y in Set.Ioi (0 : ℝ), A (p.1 + 1) * B (p.2 + 1) * (Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) / y ^ (i + 1)) = A (p.1 + 1) * B (p.2 + 1) * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1) := by
    intro p
    unfold PhiN
    rw [integral_const_mul]
  have hfun : ∀ y ∈ Set.Ioi (0 : ℝ), qa A (e / (6 * y)) * qa B (f * y) / y ^ (i + 1)
      = ∑' p : ℕ × ℕ, A (p.1 + 1) * B (p.2 + 1) * (Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) / y ^ (i + 1)) := by
    intro y hy
    rw [qa_mul_fricke hA0 hB0 hA hB he hf hy, ← tsum_div_const]
    exact tsum_congr (fun p => mul_div_assoc _ _ _)
  calc ∫ y in Set.Ioi (0 : ℝ), qa A (e / (6 * y)) * qa B (f * y) / y ^ (i + 1)
      = ∫ y in Set.Ioi (0 : ℝ), ∑' p : ℕ × ℕ, A (p.1 + 1) * B (p.2 + 1) * (Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) / y ^ (i + 1)) :=
        setIntegral_congr_fun measurableSet_Ioi hfun
    _ = ∑' p : ℕ × ℕ, ∫ y in Set.Ioi (0 : ℝ), A (p.1 + 1) * B (p.2 + 1) * (Real.exp (-(π * (e * ((p.1 + 1 : ℕ) : ℝ))) / (3 * y) - 2 * π * (f * ((p.2 + 1 : ℕ) : ℝ)) * y) / y ^ (i + 1)) := key.tsum_eq.symm
    _ = ∑' p : ℕ × ℕ, A (p.1 + 1) * B (p.2 + 1) * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1) := tsum_congr hval

/-- **Regrouped form**: the double series summed along `mn = N`. -/
theorem integral_qa_mul_regroup {A B : ℕ → ℝ} {CA CB : ℝ} {KA KB : ℕ}
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hA : ∀ n, |A n| ≤ CA * (n : ℝ) ^ KA) (hB : ∀ n, |B n| ≤ CB * (n : ℝ) ^ KB)
    {e f : ℝ} (he : 0 < e) (hf : 0 < f) (i : ℕ) :
    e ^ i * ∫ y in Set.Ioi (0 : ℝ), qa A (e / (6 * y)) * qa B (f * y) / y ^ (i + 1)
      = ∑' N : ℕ, PhiN 1 (e * f * ((N + 1 : ℕ) : ℝ)) (i + 1) / ((N + 1 : ℕ) : ℝ) ^ i
          * ∑ x ∈ (N + 1).divisorsAntidiagonal, A x.1 * B x.2 * (x.2 : ℝ) ^ i := by
  obtain ⟨hsum, hint⟩ := integral_qa_mul hA0 hB0 hA hB he hf i
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := fun n => by exact_mod_cast Nat.succ_pos n
  have hterm : ∀ p : ℕ × ℕ, e ^ i * (A (p.1 + 1) * B (p.2 + 1) * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1)) = A (p.1 + 1) * B (p.2 + 1) * (PhiN 1 (e * ((p.1 + 1 : ℕ) : ℝ) * (f * ((p.2 + 1 : ℕ) : ℝ))) (i + 1) / ((p.1 + 1 : ℕ) : ℝ) ^ i) := by
    intro p
    have hs := PhiN_scale (mul_pos he (hpos p.1)) (f * ((p.2 + 1 : ℕ) : ℝ)) i
    rw [mul_pow] at hs
    have hxi : ((p.1 + 1 : ℕ) : ℝ) ^ i ≠ 0 := pow_ne_zero _ (hpos p.1).ne'
    have h2 : e ^ i * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1) = PhiN 1 (e * ((p.1 + 1 : ℕ) : ℝ) * (f * ((p.2 + 1 : ℕ) : ℝ))) (i + 1) / ((p.1 + 1 : ℕ) : ℝ) ^ i := by
      rw [eq_div_iff hxi]
      linear_combination hs
    rw [← h2]
    ring
  have h0 : Summable fun p : ℕ × ℕ => A (p.1 + 1) * B (p.2 + 1) * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1) := by
    refine Summable.of_norm_bounded hsum (fun p => ?_)
    show ‖A (p.1 + 1) * B (p.2 + 1) * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1)‖ ≤ |A (p.1 + 1) * B (p.2 + 1)| * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (PhiN_nonneg _ _ _)]
  have hGs : Summable fun p : ℕ × ℕ => A (p.1 + 1) * B (p.2 + 1) * (PhiN 1 (e * ((p.1 + 1 : ℕ) : ℝ) * (f * ((p.2 + 1 : ℕ) : ℝ))) (i + 1) / ((p.1 + 1 : ℕ) : ℝ) ^ i) :=
    (h0.mul_left (e ^ i)).congr hterm
  have hre := tsum_prod_eq_tsum_divisorsAntidiagonal
    (fun a b : ℕ => A a * B b * (PhiN 1 (e * (a : ℝ) * (f * (b : ℝ))) (i + 1) / (a : ℝ) ^ i)) hGs
  rw [hint, ← tsum_mul_left, tsum_congr hterm]
  refine hre.trans ?_
  refine tsum_congr (fun N => ?_)
  show ∑ x ∈ (N + 1).divisorsAntidiagonal,
        A x.1 * B x.2 * (PhiN 1 (e * (x.1 : ℝ) * (f * (x.2 : ℝ))) (i + 1) / (x.1 : ℝ) ^ i)
      = PhiN 1 (e * f * ((N + 1 : ℕ) : ℝ)) (i + 1) / ((N + 1 : ℕ) : ℝ) ^ i
        * ∑ x ∈ (N + 1).divisorsAntidiagonal, A x.1 * B x.2 * (x.2 : ℝ) ^ i
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  obtain ⟨hx1, hx2⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hb : (x.2 : ℝ) ≠ 0 := by
    have h : x.2 ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hx1
      exact hx2 hx1.symm
    exact_mod_cast h
  have hN : ((N + 1 : ℕ) : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by exact_mod_cast hx1.symm
  have harg : e * (x.1 : ℝ) * (f * (x.2 : ℝ)) = e * f * ((N + 1 : ℕ) : ℝ) := by
    rw [hN]
    ring
  have hdiv : ∀ Φ a b : ℝ, b ≠ 0 → Φ / a = Φ / (a * b) * b := by
    intro Φ a b hb'
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hb']
  rw [harg, hN, mul_pow, hdiv _ _ _ (pow_ne_zero i hb)]
  ring

/-- **The interchange.** -/
theorem swap_qa {A B A' B' : ℕ → ℝ} {CA CB CA' CB' : ℝ} {KA KB KA' KB' : ℕ}
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hA'0 : A' 0 = 0) (hB'0 : B' 0 = 0)
    (hA : ∀ n, |A n| ≤ CA * (n : ℝ) ^ KA) (hB : ∀ n, |B n| ≤ CB * (n : ℝ) ^ KB)
    (hA' : ∀ n, |A' n| ≤ CA' * (n : ℝ) ^ KA') (hB' : ∀ n, |B' n| ≤ CB' * (n : ℝ) ^ KB')
    (i : ℕ)
    (H : ∀ N : ℕ, ∑ x ∈ (N + 1).divisorsAntidiagonal, A x.1 * B x.2 * (x.2 : ℝ) ^ i
        = ∑ x ∈ (N + 1).divisorsAntidiagonal, A' x.1 * B' x.2 * (x.2 : ℝ) ^ i)
    {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    e ^ i * ∫ y in Set.Ioi (0 : ℝ), qa A (e / (6 * y)) * qa B (f * y) / y ^ (i + 1)
      = f ^ i * ∫ y in Set.Ioi (0 : ℝ), qa A' (f / (6 * y)) * qa B' (e * y) / y ^ (i + 1) := by
  rw [integral_qa_mul_regroup hA0 hB0 hA hB he hf i,
    integral_qa_mul_regroup hA'0 hB'0 hA' hB' hf he i]
  refine tsum_congr (fun N => ?_)
  rw [H N, mul_comm f e]

/-- For non-negative coefficients with `A 1, B 1 > 0` the integrand is integrable: its integral
is a sum of non-negative terms with a positive one. -/
theorem integrable_qa_mul {A B : ℕ → ℝ} {CA CB : ℝ} {KA KB : ℕ}
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hA : ∀ n, |A n| ≤ CA * (n : ℝ) ^ KA) (hB : ∀ n, |B n| ≤ CB * (n : ℝ) ^ KB)
    {e f : ℝ} (he : 0 < e) (hf : 0 < f) (i : ℕ)
    (hAnn : ∀ n, 0 ≤ A n) (hBnn : ∀ n, 0 ≤ B n) (hA1 : 0 < A 1) (hB1 : 0 < B 1) :
    Integrable (fun y : ℝ => qa A (e / (6 * y)) * qa B (f * y) / y ^ (i + 1))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  obtain ⟨hsum, hint⟩ := integral_qa_mul hA0 hB0 hA hB he hf i
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := fun n => by exact_mod_cast Nat.succ_pos n
  refine Integrable.of_integral_ne_zero ?_
  rw [hint]
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ A (p.1 + 1) * B (p.2 + 1) * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1) :=
    fun p => mul_nonneg (mul_nonneg (hAnn _) (hBnn _)) (PhiN_nonneg _ _ _)
  have hs : Summable fun p : ℕ × ℕ => A (p.1 + 1) * B (p.2 + 1) * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1) := by
    refine hsum.congr (fun p => ?_)
    show |A (p.1 + 1) * B (p.2 + 1)| * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1) = A (p.1 + 1) * B (p.2 + 1) * PhiN (e * ((p.1 + 1 : ℕ) : ℝ)) (f * ((p.2 + 1 : ℕ) : ℝ)) (i + 1)
    rw [abs_of_nonneg (mul_nonneg (hAnn _) (hBnn _))]
  have h00 : 0 < A (0 + 1) * B (0 + 1)
      * PhiN (e * ((0 + 1 : ℕ) : ℝ)) (f * ((0 + 1 : ℕ) : ℝ)) (i + 1) :=
    mul_pos (mul_pos hA1 hB1) (PhiN_pos (mul_pos he (hpos 0)) (mul_pos hf (hpos 0)) (i + 1))
  exact (hs.tsum_pos hnn (0, 0) h00).ne'

/-! ## The two instances for the divisor sums -/

theorem abs_div_le_abs (x d : ℝ) (hd : d = 0 ∨ 1 ≤ d) : |x / d| ≤ |x| := by
  rcases hd with h | h
  · rw [h, div_zero, abs_zero]
    exact abs_nonneg x
  · rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < d)]
    exact div_le_self (abs_nonneg x) h

theorem natCast_zero_or_one_le (n : ℕ) : (n : ℝ) = 0 ∨ 1 ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · left
    exact_mod_cast h
  · right
    have h1 : 1 ≤ n := h
    exact_mod_cast h1

theorem bound_sig3_div (n : ℕ) : |sig 3 n / (n : ℝ)| ≤ 1 * (n : ℝ) ^ (3 + 1) :=
  (abs_div_le_abs _ _ (natCast_zero_or_one_le n)).trans (sig_abs_le 3 n)

theorem bound_sig3_div_sq (n : ℕ) : |sig 3 n / (n : ℝ) ^ 2| ≤ 1 * (n : ℝ) ^ (3 + 1) := by
  refine (abs_div_le_abs _ _ ?_).trans (sig_abs_le 3 n)
  rcases natCast_zero_or_one_le n with h | h
  · left
    rw [h]
    norm_num
  · right
    exact one_le_pow₀ h

theorem bound_mul_sig1 (n : ℕ) : |(n : ℝ) * sig 1 n| ≤ 1 * (n : ℝ) ^ 3 := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [abs_of_nonneg (mul_nonneg h0 (sig_nonneg 1 n)), one_mul]
  calc (n : ℝ) * sig 1 n ≤ (n : ℝ) * (n : ℝ) ^ (1 + 1) :=
        mul_le_mul_of_nonneg_left (sig_le_pow 1 n) h0
    _ = (n : ℝ) ^ 3 := by ring

theorem sig_one_pos (k : ℕ) : 0 < sig k 1 := by
  simp [sig]

/-- The interchange with `y⁻³`:
`e² ∫ S₃(e/(6y)) U₁(f y) y⁻³ dy = f² ∫ 𝔈(f/(6y)) D𝔈(e y) y⁻³ dy`. -/
theorem interchange_three {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    e ^ 2 * ∫ y in Set.Ioi (0 : ℝ),
        qa (sig 3) (e / (6 * y)) * qa (fun n => sig 3 n / (n : ℝ)) (f * y) / y ^ 3
      = f ^ 2 * ∫ y in Set.Ioi (0 : ℝ),
        qa (sig 1) (f / (6 * y)) * qa (fun n => (n : ℝ) * sig 1 n) (e * y) / y ^ 3 := by
  have H : ∀ N : ℕ, ∑ x ∈ (N + 1).divisorsAntidiagonal,
        sig 3 x.1 * (sig 3 x.2 / (x.2 : ℝ)) * (x.2 : ℝ) ^ 2
      = ∑ x ∈ (N + 1).divisorsAntidiagonal,
        sig 1 x.1 * ((x.2 : ℝ) * sig 1 x.2) * (x.2 : ℝ) ^ 2 := by
    intro N
    have hL : ∑ x ∈ (N + 1).divisorsAntidiagonal,
          sig 3 x.1 * (sig 3 x.2 / (x.2 : ℝ)) * (x.2 : ℝ) ^ 2
        = ∑ x ∈ (N + 1).divisorsAntidiagonal, sig 3 x.1 * sig 3 x.2 * (x.2 : ℝ) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      obtain ⟨hx1, hx2⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have hb : (x.2 : ℝ) ≠ 0 := by
        have h : x.2 ≠ 0 := by
          rintro h
          rw [h, mul_zero] at hx1
          exact hx2 hx1.symm
        exact_mod_cast h
      have hdm : sig 3 x.2 / (x.2 : ℝ) * (x.2 : ℝ) = sig 3 x.2 := div_mul_cancel₀ _ hb
      linear_combination (sig 3 x.1 * (x.2 : ℝ)) * hdm
    have hR : ∑ x ∈ (N + 1).divisorsAntidiagonal,
          sig 1 x.1 * ((x.2 : ℝ) * sig 1 x.2) * (x.2 : ℝ) ^ 2
        = ∑ x ∈ (N + 1).divisorsAntidiagonal, sig 1 x.1 * sig 1 x.2 * (x.2 : ℝ) ^ 3 :=
      Finset.sum_congr rfl (fun x _ => by ring)
    rw [hL, hR]
    exact conv_sig_identity (N + 1)
  exact swap_qa (A := sig 3) (B := fun n => sig 3 n / (n : ℝ)) (A' := sig 1)
    (B' := fun n => (n : ℝ) * sig 1 n) (sig_zero 3) (by simp [sig_zero]) (sig_zero 1)
    (by simp [sig_zero]) (sig_abs_le 3) bound_sig3_div (sig_abs_le 1) bound_mul_sig1 2 H he hf

/-- The interchange with `y⁻⁴`:
`e³ ∫ S₃(e/(6y)) U₂(f y) y⁻⁴ dy = f³ ∫ 𝔈(f/(6y)) 𝔈(e y) y⁻⁴ dy`. -/
theorem interchange_four {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    e ^ 3 * ∫ y in Set.Ioi (0 : ℝ),
        qa (sig 3) (e / (6 * y)) * qa (fun n => sig 3 n / (n : ℝ) ^ 2) (f * y) / y ^ 4
      = f ^ 3 * ∫ y in Set.Ioi (0 : ℝ),
        qa (sig 1) (f / (6 * y)) * qa (sig 1) (e * y) / y ^ 4 := by
  have H : ∀ N : ℕ, ∑ x ∈ (N + 1).divisorsAntidiagonal,
        sig 3 x.1 * (sig 3 x.2 / (x.2 : ℝ) ^ 2) * (x.2 : ℝ) ^ 3
      = ∑ x ∈ (N + 1).divisorsAntidiagonal, sig 1 x.1 * sig 1 x.2 * (x.2 : ℝ) ^ 3 := by
    intro N
    have hL : ∑ x ∈ (N + 1).divisorsAntidiagonal,
          sig 3 x.1 * (sig 3 x.2 / (x.2 : ℝ) ^ 2) * (x.2 : ℝ) ^ 3
        = ∑ x ∈ (N + 1).divisorsAntidiagonal, sig 3 x.1 * sig 3 x.2 * (x.2 : ℝ) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      obtain ⟨hx1, hx2⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have hb : (x.2 : ℝ) ≠ 0 := by
        have h : x.2 ≠ 0 := by
          rintro h
          rw [h, mul_zero] at hx1
          exact hx2 hx1.symm
        exact_mod_cast h
      have hdm : sig 3 x.2 / (x.2 : ℝ) ^ 2 * (x.2 : ℝ) ^ 2 = sig 3 x.2 :=
        div_mul_cancel₀ _ (pow_ne_zero 2 hb)
      linear_combination (sig 3 x.1 * (x.2 : ℝ)) * hdm
    rw [hL]
    exact conv_sig_identity (N + 1)
  exact swap_qa (A := sig 3) (B := fun n => sig 3 n / (n : ℝ) ^ 2) (A' := sig 1) (B' := sig 1)
    (sig_zero 3) (by simp [sig_zero]) (sig_zero 1) (sig_zero 1) (sig_abs_le 3)
    bound_sig3_div_sq (sig_abs_le 1) (sig_abs_le 1) 3 H he hf

end Tower.RV6
