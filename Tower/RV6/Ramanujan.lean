import Mathlib
import Tower.RV6.EisAxis
import Tower.RV6.QSeries
import Tower.RV6.QCalc
import Tower.RV6.Ser
import Tower.RV6.Level6

/-!
# Ramanujan's identities for `E₂, E₄, E₆` in the ring `ℝ⟦X⟧`

Mathlib proves `D E₂ = (E₂² - E₄)/12`, `D E₄ = (E₂E₄ - E₆)/3`, `D E₆ = (E₂E₆ - E₄²)/2` for the
functions on the upper half plane (`Derivative.normalizedDerivOfComplex_E₂/E₄/E₆`).  This file
carries them to formal power series, where rung E″ is proved:

* `qa_coeff_unique`: a `q`-series with polynomially bounded coefficients that vanishes for all
  `y > 0` has zero coefficients.
* `D_axis`: the normalised derivative `D = (2πi)⁻¹ d/dz` at `z = iy` of a function that is real on
  the imaginary axis is `-(2π)⁻¹ d/dy`.
* `E6_axis`: `E₆(iy) = E₂(iy) E₄(iy) - 720 ∑ n σ₃(n) e^{-2πny}`.
* `c2_zero`, `c6_zero`: the two identities between the coefficients.
* `ram_base2 : 12 θx = x² - u`, `ram_base6 : 2 θv = x v - u²` for `x = 1 - 24 ∑ σ₁(n) Xⁿ`,
  `u = 1 + 240 ∑ σ₃(n) Xⁿ`, `v = x u - 3 θu`, and `ram6 : Ram6`, the hypothesis of `Level6.lean`.
-/

namespace Tower.RV6

open Real
open EisensteinSeries
open UpperHalfPlane hiding I

/-! ## A `q`-series that vanishes for all `y > 0` has zero coefficients -/

/-- A real number bounded by `S e^{-t}` for all `t ≥ 0` is zero. -/
theorem eq_zero_of_exp_decay {a S : ℝ} (h : ∀ t : ℝ, 0 ≤ t → |a| ≤ S * Real.exp (-t)) :
    a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.mpr ha
  have hS : |a| ≤ S := by
    have h0 := h 0 le_rfl
    rw [neg_zero, Real.exp_zero, mul_one] at h0
    exact h0
  have hS0 : 0 < S := lt_of_lt_of_le hpos hS
  have ht0 : 0 ≤ S / |a| := (div_pos hS0 hpos).le
  have h1 := h (S / |a|) ht0
  have h2 : S / |a| + 1 ≤ Real.exp (S / |a|) := Real.add_one_le_exp (S / |a|)
  have h3 : Real.exp (-(S / |a|)) * Real.exp (S / |a|) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h5 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (S / |a|)).le
  have h4 : |a| * Real.exp (S / |a|) ≤ S := by
    calc |a| * Real.exp (S / |a|) ≤ S * Real.exp (-(S / |a|)) * Real.exp (S / |a|) := h5
      _ = S * (Real.exp (-(S / |a|)) * Real.exp (S / |a|)) := by ring
      _ = S := by rw [h3, mul_one]
  have h6 : |a| * (S / |a| + 1) ≤ S := le_trans (mul_le_mul_of_nonneg_left h2 hpos.le) h4
  have h7 : |a| * (S / |a|) = S := mul_div_cancel₀ S hpos.ne'
  have h8 : |a| * (S / |a| + 1) = S + |a| := by rw [mul_add, mul_one, h7]
  rw [h8] at h6
  linarith

theorem summable_of_abs_axis {C : ℕ → ℝ} {y : ℝ}
    (h : Summable fun n : ℕ => |C n| * Real.exp (-(2 * π * (n : ℝ) * y))) :
    Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y)) := by
  refine Summable.of_norm_bounded h (fun n => ?_)
  show ‖C n * Real.exp (-(2 * π * (n : ℝ) * y))‖ ≤ |C n| * Real.exp (-(2 * π * (n : ℝ) * y))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- The series with its constant term split off. -/
theorem qa_eq_zero_add {C : ℕ → ℝ} {y : ℝ}
    (hs : Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y))) :
    qa C y = C 0 + ∑' n : ℕ, C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) := by
  unfold qa
  rw [hs.tsum_eq_zero_add, Nat.cast_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]

theorem abs_tsum_le_tsum_abs {f : ℕ → ℝ} (hf : Summable fun n => |f n|) :
    |∑' n, f n| ≤ ∑' n, |f n| := by
  have hn : Summable fun n => ‖f n‖ := hf.congr (fun n => (Real.norm_eq_abs (f n)).symm)
  have h := norm_tsum_le_tsum_norm hn
  simp only [Real.norm_eq_abs] at h
  exact h

/-- If the series vanishes for all `y > 0`, its constant term is zero. -/
theorem qa_zero_coeff {C : ℕ → ℝ}
    (hs : ∀ y : ℝ, 0 < y → Summable fun n : ℕ => |C n| * Real.exp (-(2 * π * (n : ℝ) * y)))
    (h : ∀ y : ℝ, 0 < y → qa C y = 0) : C 0 = 0 := by
  have hs1 := hs 1 one_pos
  have hsh0 := (summable_nat_add_iff 1).mpr hs1
  have hsh : Summable fun n : ℕ =>
      |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * 1)) := hsh0
  refine eq_zero_of_exp_decay
    (S := ∑' n : ℕ, |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * 1))) (fun t ht => ?_)
  have hpi : 0 < 2 * π := by positivity
  have hs0 : 0 ≤ t / (2 * π) := div_nonneg ht hpi.le
  have hy : 0 < 1 + t / (2 * π) := by linarith
  have hts : 2 * π * (t / (2 * π)) = t := mul_div_cancel₀ t hpi.ne'
  have hsum := hs (1 + t / (2 * π)) hy
  have e0 := qa_eq_zero_add (summable_of_abs_axis hsum)
  rw [h (1 + t / (2 * π)) hy] at e0
  have hC0 := eq_neg_of_add_eq_zero_left e0.symm
  rw [hC0, abs_neg]
  have hshs0 := (summable_nat_add_iff 1).mpr hsum
  have hshs : Summable fun n : ℕ =>
      |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π)))) := hshs0
  have hA : ∀ n : ℕ,
      |C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π))))|
        = |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π)))) := by
    intro n
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have habs : Summable fun n : ℕ =>
      |C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π))))| :=
    hshs.congr (fun n => (hA n).symm)
  have hterm : ∀ n : ℕ,
      |C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π))))|
        ≤ |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * 1)) * Real.exp (-t) := by
    intro n
    have hE : Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π))))
        ≤ Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * 1)) * Real.exp (-t) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        linarith
      have hprod := mul_le_mul_of_nonneg_right hn1 ht
      rw [one_mul] at hprod
      have e : 2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π))
          = 2 * π * ((n + 1 : ℕ) : ℝ) * 1 + ((n + 1 : ℕ) : ℝ) * (2 * π * (t / (2 * π))) := by
        ring
      rw [e, hts]
      linarith
    calc |C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π))))|
        = |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π)))) := hA n
      _ ≤ |C (n + 1)| * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * 1)) * Real.exp (-t)) :=
          mul_le_mul_of_nonneg_left hE (abs_nonneg _)
      _ = |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * 1)) * Real.exp (-t) := by ring
  calc |∑' n : ℕ, C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π))))|
      ≤ ∑' n : ℕ, |C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * (1 + t / (2 * π))))| :=
        abs_tsum_le_tsum_abs habs
    _ ≤ ∑' n : ℕ, |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * 1)) * Real.exp (-t) :=
        Summable.tsum_le_tsum hterm habs (hsh.mul_right _)
    _ = (∑' n : ℕ, |C (n + 1)| * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * 1))) * Real.exp (-t) :=
        tsum_mul_right

/-- A series without constant term is `e^{-2πy}` times the series of the shifted coefficients. -/
theorem qa_shift_factor {C : ℕ → ℝ} (h0 : C 0 = 0) {y : ℝ}
    (hs : Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y))) :
    qa C y = Real.exp (-(2 * π * y)) * qa (fun n => C (n + 1)) y := by
  rw [qa_eq_shift h0 hs]
  unfold qa
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  have e : Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y))
      = Real.exp (-(2 * π * y)) * Real.exp (-(2 * π * (n : ℝ) * y)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  show C (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y))
    = Real.exp (-(2 * π * y)) * (C (n + 1) * Real.exp (-(2 * π * (n : ℝ) * y)))
  rw [e]
  ring

theorem qa_coeff_unique_aux : ∀ (n : ℕ) (C : ℕ → ℝ),
    (∀ y : ℝ, 0 < y → Summable fun m : ℕ => |C m| * Real.exp (-(2 * π * (m : ℝ) * y))) →
    (∀ y : ℝ, 0 < y → qa C y = 0) → C n = 0
  | 0, C, hs, h => qa_zero_coeff hs h
  | n + 1, C, hs, h => by
    have h0 : C 0 = 0 := qa_zero_coeff hs h
    have hs' : ∀ y : ℝ, 0 < y →
        Summable fun m : ℕ => |C (m + 1)| * Real.exp (-(2 * π * (m : ℝ) * y)) := by
      intro y hy
      have a0 := (summable_nat_add_iff 1).mpr (hs y hy)
      have a1 : Summable fun m : ℕ =>
          |C (m + 1)| * Real.exp (-(2 * π * ((m + 1 : ℕ) : ℝ) * y)) := a0
      have a2 := a1.mul_left (Real.exp (2 * π * y))
      refine a2.congr (fun m => ?_)
      have e : Real.exp (2 * π * y) * Real.exp (-(2 * π * ((m + 1 : ℕ) : ℝ) * y))
          = Real.exp (-(2 * π * (m : ℝ) * y)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      show Real.exp (2 * π * y) * (|C (m + 1)| * Real.exp (-(2 * π * ((m + 1 : ℕ) : ℝ) * y)))
        = |C (m + 1)| * Real.exp (-(2 * π * (m : ℝ) * y))
      rw [← e]
      ring
    have h' : ∀ y : ℝ, 0 < y → qa (fun m => C (m + 1)) y = 0 := by
      intro y hy
      have e1 := qa_shift_factor h0 (summable_of_abs_axis (hs y hy))
      rw [h y hy] at e1
      exact (mul_eq_zero.mp e1.symm).resolve_left (Real.exp_pos _).ne'
    exact qa_coeff_unique_aux n (fun m => C (m + 1)) hs' h'

/-- A `q`-series with polynomially bounded coefficients that vanishes for all `y > 0` has zero
coefficients. -/
theorem qa_coeff_unique {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K)
    (h : ∀ y : ℝ, 0 < y → qa C y = 0) (n : ℕ) : C n = 0 :=
  qa_coeff_unique_aux n C (fun _ hy => summable_qa_abs hC hy) h

/-! ## Sequences of polynomial growth -/

/-- Polynomial growth with exponent at least one (so the sequence vanishes at `0`). -/
def PolyBdd (C : ℕ → ℝ) : Prop :=
  ∃ (B : ℝ) (K : ℕ), 0 ≤ B ∧ 1 ≤ K ∧ ∀ n : ℕ, |C n| ≤ B * (n : ℝ) ^ K

theorem poly_mono {C : ℕ → ℝ} {B : ℝ} {K K' : ℕ} (hB : 0 ≤ B) (hK : 1 ≤ K) (hKK : K ≤ K')
    (hC : ∀ n : ℕ, |C n| ≤ B * (n : ℝ) ^ K) (n : ℕ) : |C n| ≤ B * (n : ℝ) ^ K' := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have h0 := hC 0
    rw [Nat.cast_zero, zero_pow (by omega), mul_zero] at h0
    rw [Nat.cast_zero, zero_pow (by omega), mul_zero]
    exact h0
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    exact le_trans (hC n) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hKK) hB)

theorem polyBdd_zero {C : ℕ → ℝ} (hC : PolyBdd C) : C 0 = 0 := by
  obtain ⟨B, K, -, hK, h⟩ := hC
  have h0 := h 0
  rw [Nat.cast_zero, zero_pow (by omega), mul_zero] at h0
  exact abs_nonpos_iff.mp h0

theorem polyBdd_sig (k : ℕ) : PolyBdd (sig k) :=
  ⟨1, k + 1, zero_le_one, Nat.le_add_left 1 k, sig_abs_le k⟩

theorem polyBdd_const_mul {C : ℕ → ℝ} (c : ℝ) (hC : PolyBdd C) : PolyBdd (fun n => c * C n) := by
  obtain ⟨B, K, hB, hK, h⟩ := hC
  refine ⟨|c| * B, K, mul_nonneg (abs_nonneg c) hB, hK, fun n => ?_⟩
  show |c * C n| ≤ |c| * B * (n : ℝ) ^ K
  calc |c * C n| = |c| * |C n| := abs_mul c (C n)
    _ ≤ |c| * (B * (n : ℝ) ^ K) := mul_le_mul_of_nonneg_left (h n) (abs_nonneg c)
    _ = |c| * B * (n : ℝ) ^ K := by ring

theorem polyBdd_add {C D : ℕ → ℝ} (hC : PolyBdd C) (hD : PolyBdd D) :
    PolyBdd (fun n => C n + D n) := by
  obtain ⟨B1, K1, hB1, hK1, h1⟩ := hC
  obtain ⟨B2, K2, hB2, hK2, h2⟩ := hD
  refine ⟨B1 + B2, K1 + K2, add_nonneg hB1 hB2, le_trans hK1 (Nat.le_add_right K1 K2),
    fun n => ?_⟩
  have a1 := poly_mono hB1 hK1 (Nat.le_add_right K1 K2) h1 n
  have a2 := poly_mono hB2 hK2 (Nat.le_add_left K2 K1) h2 n
  show |C n + D n| ≤ (B1 + B2) * (n : ℝ) ^ (K1 + K2)
  calc |C n + D n| ≤ |C n| + |D n| := abs_add_le (C n) (D n)
    _ ≤ B1 * (n : ℝ) ^ (K1 + K2) + B2 * (n : ℝ) ^ (K1 + K2) := add_le_add a1 a2
    _ = (B1 + B2) * (n : ℝ) ^ (K1 + K2) := by ring

theorem polyBdd_mulIdx {C : ℕ → ℝ} (hC : PolyBdd C) : PolyBdd (fun n => (n : ℝ) * C n) := by
  obtain ⟨B, K, hB, hK, h⟩ := hC
  refine ⟨B, K + 1, hB, Nat.le_add_left 1 K, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  show |(n : ℝ) * C n| ≤ B * (n : ℝ) ^ (K + 1)
  rw [abs_mul, abs_of_nonneg hn0]
  calc (n : ℝ) * |C n| ≤ (n : ℝ) * (B * (n : ℝ) ^ K) := mul_le_mul_of_nonneg_left (h n) hn0
    _ = B * (n : ℝ) ^ (K + 1) := by ring

theorem polyBdd_conv {C D : ℕ → ℝ} (hC : PolyBdd C) (hD : PolyBdd D) : PolyBdd (conv C D) := by
  have hz := polyBdd_zero hC
  obtain ⟨B1, K1, hB1, hK1, h1⟩ := hC
  obtain ⟨B2, K2, hB2, hK2, h2⟩ := hD
  exact ⟨2 * (B1 * B2), K1 + K2 + 1, mul_nonneg zero_le_two (mul_nonneg hB1 hB2),
    Nat.le_add_left 1 (K1 + K2), conv_poly_bound hz h1 h2⟩

theorem polyBdd_summable {C : ℕ → ℝ} (hC : PolyBdd C) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y)) := by
  obtain ⟨B, K, -, -, h⟩ := hC
  exact summable_qa h hy

theorem polyBdd_qa_mul {C D : ℕ → ℝ} (hC : PolyBdd C) (hD : PolyBdd D) {y : ℝ} (hy : 0 < y) :
    qa C y * qa D y = qa (conv C D) y := by
  obtain ⟨B1, K1, -, -, h1⟩ := hC
  obtain ⟨B2, K2, -, -, h2⟩ := hD
  exact qa_conv h1 h2 hy

theorem polyBdd_hasDerivAt {C : ℕ → ℝ} (hC : PolyBdd C) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (qa C) (-(2 * π) * qa (fun n => (n : ℝ) * C n) y) y := by
  obtain ⟨B, K, -, -, h⟩ := hC
  exact hasDerivAt_qa h hy

theorem polyBdd_unique {C : ℕ → ℝ} (hC : PolyBdd C) (h : ∀ y : ℝ, 0 < y → qa C y = 0) (n : ℕ) :
    C n = 0 := by
  obtain ⟨B, K, -, -, hb⟩ := hC
  exact qa_coeff_unique hb h n

/-! ## Linearity in the coefficients -/

theorem qa_lin4 {A B C D : ℕ → ℝ} {y : ℝ}
    (hA : Summable fun n : ℕ => A n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hB : Summable fun n : ℕ => B n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hC : Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hD : Summable fun n : ℕ => D n * Real.exp (-(2 * π * (n : ℝ) * y))) (a b c d : ℝ) :
    qa (fun n => a * A n + b * B n + c * C n + d * D n) y
      = a * qa A y + b * qa B y + c * qa C y + d * qa D y := by
  have H := (((hA.hasSum.mul_left a).add (hB.hasSum.mul_left b)).add
    (hC.hasSum.mul_left c)).add (hD.hasSum.mul_left d)
  unfold qa
  calc ∑' n : ℕ, (a * A n + b * B n + c * C n + d * D n) * Real.exp (-(2 * π * (n : ℝ) * y))
      = ∑' n : ℕ, (a * (A n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + b * (B n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + c * (C n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + d * (D n * Real.exp (-(2 * π * (n : ℝ) * y)))) :=
        tsum_congr (fun n => by ring)
    _ = _ := H.tsum_eq

theorem qa_lin6 {A B C D E F : ℕ → ℝ} {y : ℝ}
    (hA : Summable fun n : ℕ => A n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hB : Summable fun n : ℕ => B n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hC : Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hD : Summable fun n : ℕ => D n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hE : Summable fun n : ℕ => E n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hF : Summable fun n : ℕ => F n * Real.exp (-(2 * π * (n : ℝ) * y))) (a b c d e f : ℝ) :
    qa (fun n => a * A n + b * B n + c * C n + d * D n + e * E n + f * F n) y
      = a * qa A y + b * qa B y + c * qa C y + d * qa D y + e * qa E y + f * qa F y := by
  have H := (((((hA.hasSum.mul_left a).add (hB.hasSum.mul_left b)).add
    (hC.hasSum.mul_left c)).add (hD.hasSum.mul_left d)).add (hE.hasSum.mul_left e)).add
    (hF.hasSum.mul_left f)
  unfold qa
  calc ∑' n : ℕ, (a * A n + b * B n + c * C n + d * D n + e * E n + f * F n)
        * Real.exp (-(2 * π * (n : ℝ) * y))
      = ∑' n : ℕ, (a * (A n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + b * (B n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + c * (C n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + d * (D n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + e * (E n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + f * (F n * Real.exp (-(2 * π * (n : ℝ) * y)))) :=
        tsum_congr (fun n => by ring)
    _ = _ := H.tsum_eq

/-! ## The normalised derivative on the imaginary axis -/

/-- `D = (2πi)⁻¹ d/dz` at `z = iy`, for a function equal to the real function `f` on the
imaginary axis: if `f'(y) = -2π d` then `(D F)(iy) = d`. -/
theorem D_axis {F : ℍ → ℂ} {f : ℝ → ℝ} {d y : ℝ} (hy : 0 < y) (z : ℍ)
    (hz : (z : ℂ) = Complex.I * y)
    (hF : DifferentiableAt ℂ (F ∘ UpperHalfPlane.ofComplex) (z : ℂ))
    (hFf : ∀ t : ℝ, 0 < t →
      (F ∘ UpperHalfPlane.ofComplex) (Complex.I * t) = ((f t : ℝ) : ℂ))
    (hf : HasDerivAt f (-(2 * π) * d) y) :
    Derivative.normalizedDerivOfComplex F z = (d : ℂ) := by
  have hg0 := hF.hasDerivAt
  rw [hz] at hg0
  have hγ0 := ((hasDerivAt_id' y).ofReal_comp).const_mul Complex.I
  have hγ : HasDerivAt (fun t : ℝ => Complex.I * ((t : ℝ) : ℂ))
      (Complex.I * ((1 : ℝ) : ℂ)) y := hγ0
  have hcomp := hg0.comp y hγ
  have hreal := hf.ofReal_comp
  have heq : ((F ∘ UpperHalfPlane.ofComplex) ∘ fun t : ℝ => Complex.I * ((t : ℝ) : ℂ))
      =ᶠ[nhds y] (fun t : ℝ => ((f t : ℝ) : ℂ)) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) (fun t ht => hFf t ht)
  have huniq := hcomp.unique (hreal.congr_of_eventuallyEq heq)
  show (2 * (π : ℂ) * Complex.I)⁻¹ * deriv (F ∘ UpperHalfPlane.ofComplex) (z : ℂ) = (d : ℂ)
  rw [hz, inv_mul_eq_iff_eq_mul₀ Complex.two_pi_I_ne_zero]
  push_cast at huniq
  linear_combination (-Complex.I) * huniq
    + deriv (F ∘ UpperHalfPlane.ofComplex) (Complex.I * (y : ℂ)) * Complex.I_mul_I

/-- A point `iy` of the upper half plane at which `F ∘ ofComplex` is `F`. -/
theorem comp_ofComplex_axis (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ w : ℍ, (w : ℂ) = Complex.I * t
      ∧ (F ∘ UpperHalfPlane.ofComplex) (Complex.I * t) = F w := by
  have him : 0 < (Complex.I * (t : ℂ)).im := by simpa using ht
  refine ⟨UpperHalfPlane.mk (Complex.I * t) him, UpperHalfPlane.coe_mk _ _, ?_⟩
  show F (UpperHalfPlane.ofComplex (Complex.I * t)) = F (UpperHalfPlane.mk (Complex.I * t) him)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]

/-- The derivative of `a + b ∑ C(n) e^{-2πny}`. -/
theorem hasDerivAt_const_add_qa {C : ℕ → ℝ} (hC : PolyBdd C) {g : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ t : ℝ, 0 < t → g t = a + b * qa C t) {y : ℝ} (hy : 0 < y) :
    HasDerivAt g (-(2 * π) * (b * qa (fun n => (n : ℝ) * C n) y)) y := by
  have h1 := ((polyBdd_hasDerivAt hC hy).const_mul b).const_add a
  have h2 : HasDerivAt (fun t : ℝ => a + b * qa C t)
      (b * (-(2 * π) * qa (fun n => (n : ℝ) * C n) y)) y := h1
  have heq : g =ᶠ[nhds y] (fun t : ℝ => a + b * qa C t) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) (fun t ht => hg t ht)
  have h3 := h2.congr_of_eventuallyEq heq
  have e : b * (-(2 * π) * qa (fun n => (n : ℝ) * C n) y)
      = -(2 * π) * (b * qa (fun n => (n : ℝ) * C n) y) := by ring
  rw [e] at h3
  exact h3

/-! ## `D E₂`, `D E₄` and the value of `E₆` on the imaginary axis -/

theorem D_E2_axis {y : ℝ} (hy : 0 < y) (z : ℍ) (hz : (z : ℂ) = Complex.I * y) :
    Derivative.normalizedDerivOfComplex EisensteinSeries.E2 z
      = (((-24) * qa (fun n => (n : ℝ) * sig 1 n) y : ℝ) : ℂ) := by
  refine D_axis (f := E2im) hy z hz
    (UpperHalfPlane.mdifferentiableAt_iff.mp (E2_mdifferentiable z)) ?_ ?_
  · intro t ht
    obtain ⟨p, hp, hFp⟩ := comp_ofComplex_axis EisensteinSeries.E2 ht
    rw [hFp]
    exact E2_axis p hp
  · exact hasDerivAt_const_add_qa (polyBdd_sig 1) (a := 1) (b := -24)
      (fun t ht => by rw [E2im_eq_qa ht]; ring) hy

theorem D_E4_axis {y : ℝ} (hy : 0 < y) (z : ℍ) (hz : (z : ℂ) = Complex.I * y) :
    Derivative.normalizedDerivOfComplex (ModularForm.E₄ : ℍ → ℂ) z
      = ((240 * qa (fun n => (n : ℝ) * sig 3 n) y : ℝ) : ℂ) := by
  refine D_axis (f := E4im) hy z hz
    (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo ModularForm.E₄ z)) ?_ ?_
  · intro t ht
    obtain ⟨p, hp, hFp⟩ := comp_ofComplex_axis (ModularForm.E₄ : ℍ → ℂ) ht
    rw [hFp]
    exact E4_axis p hp
  · exact hasDerivAt_const_add_qa (polyBdd_sig 3) (a := 1) (b := 240)
      (fun t ht => E4im_eq_qa ht) hy

/-- Ramanujan's identity for `E₂` on the imaginary axis. -/
theorem ram2_axis {y : ℝ} (hy : 0 < y) :
    (-24) * qa (fun n => (n : ℝ) * sig 1 n) y = 12⁻¹ * (E2im y ^ 2 - E4im y) := by
  obtain ⟨z, hz, -⟩ := axis_point hy
  have h := congrFun Derivative.normalizedDerivOfComplex_E₂ z
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul] at h
  rw [D_E2_axis hy z hz, E2_axis z hz, E4_axis z hz] at h
  have hc : ((12⁻¹ * (E2im y ^ 2 - E4im y) : ℝ) : ℂ)
      = 12⁻¹ * ((E2im y : ℂ) ^ 2 - (E4im y : ℂ)) := by
    first
      | (push_cast; ring)
      | push_cast
  exact Complex.ofReal_injective (h.trans hc.symm)

/-- `E₆(iy)` as a real function: `E₂(iy) E₄(iy) - 720 ∑ n σ₃(n) e^{-2πny}`. -/
noncomputable def E6im (y : ℝ) : ℝ :=
  E2im y * E4im y - 720 * qa (fun n => (n : ℝ) * sig 3 n) y

/-- Mathlib's `E₆` at `z = iy` is `E6im y` (from Ramanujan's identity for `E₄`). -/
theorem E6_axis {y : ℝ} (hy : 0 < y) (z : ℍ) (hz : (z : ℂ) = Complex.I * y) :
    ModularForm.E₆ z = ((E6im y : ℝ) : ℂ) := by
  have h := congrFun Derivative.normalizedDerivOfComplex_E₄ z
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul] at h
  rw [D_E4_axis hy z hz, E2_axis z hz, E4_axis z hz] at h
  unfold E6im
  push_cast at h ⊢
  linear_combination (3 : ℂ) * h

/-! ## The coefficients of `E₆` -/

/-- The coefficients of `E₆ - 1`: `240 σ₃ - 24 σ₁ - 5760 σ₁∗σ₃ - 720 n σ₃`. -/
noncomputable def wE (n : ℕ) : ℝ :=
  240 * sig 3 n + (-24) * sig 1 n + (-5760) * conv (sig 1) (sig 3) n
    + (-720) * ((n : ℝ) * sig 3 n)

theorem polyBdd_wE : PolyBdd wE := by
  have h := polyBdd_add (polyBdd_add (polyBdd_add (polyBdd_const_mul 240 (polyBdd_sig 3))
    (polyBdd_const_mul (-24) (polyBdd_sig 1)))
    (polyBdd_const_mul (-5760) (polyBdd_conv (polyBdd_sig 1) (polyBdd_sig 3))))
    (polyBdd_const_mul (-720) (polyBdd_mulIdx (polyBdd_sig 3)))
  exact h

theorem qa_wE {y : ℝ} (hy : 0 < y) :
    qa wE y = 240 * qa (sig 3) y + (-24) * qa (sig 1) y
      + (-5760) * qa (conv (sig 1) (sig 3)) y
      + (-720) * qa (fun n => (n : ℝ) * sig 3 n) y := by
  have h := qa_lin4 (polyBdd_summable (polyBdd_sig 3) hy) (polyBdd_summable (polyBdd_sig 1) hy)
    (polyBdd_summable (polyBdd_conv (polyBdd_sig 1) (polyBdd_sig 3)) hy)
    (polyBdd_summable (polyBdd_mulIdx (polyBdd_sig 3)) hy) 240 (-24) (-5760) (-720)
  exact h

theorem E6im_eq_qa {y : ℝ} (hy : 0 < y) : E6im y = 1 + 1 * qa wE y := by
  have hm := polyBdd_qa_mul (polyBdd_sig 1) (polyBdd_sig 3) hy
  unfold E6im
  rw [qa_wE hy, ← hm, E2im_eq_qa hy, E4im_eq_qa hy]
  ring

theorem D_E6_axis {y : ℝ} (hy : 0 < y) (z : ℍ) (hz : (z : ℂ) = Complex.I * y) :
    Derivative.normalizedDerivOfComplex (ModularForm.E₆ : ℍ → ℂ) z
      = ((1 * qa (fun n => (n : ℝ) * wE n) y : ℝ) : ℂ) := by
  refine D_axis (f := E6im) hy z hz
    (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo ModularForm.E₆ z)) ?_ ?_
  · intro t ht
    obtain ⟨p, hp, hFp⟩ := comp_ofComplex_axis (ModularForm.E₆ : ℍ → ℂ) ht
    rw [hFp]
    exact E6_axis ht p hp
  · exact hasDerivAt_const_add_qa polyBdd_wE (a := 1) (b := 1)
      (fun t ht => E6im_eq_qa ht) hy

/-- Ramanujan's identity for `E₆` on the imaginary axis. -/
theorem ram6_axis {y : ℝ} (hy : 0 < y) :
    1 * qa (fun n => (n : ℝ) * wE n) y = 2⁻¹ * (E2im y * E6im y - E4im y ^ 2) := by
  obtain ⟨z, hz, -⟩ := axis_point hy
  have h := congrFun Derivative.normalizedDerivOfComplex_E₆ z
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul] at h
  rw [D_E6_axis hy z hz, E2_axis z hz, E4_axis z hz, E6_axis hy z hz] at h
  have hc : ((2⁻¹ * (E2im y * E6im y - E4im y ^ 2) : ℝ) : ℂ)
      = 2⁻¹ * ((E2im y : ℂ) * (E6im y : ℂ) - (E4im y : ℂ) ^ 2) := by
    first
      | (push_cast; ring)
      | push_cast
  exact Complex.ofReal_injective (h.trans hc.symm)

/-! ## The two identities between the coefficients -/

/-- `288 n σ₁ - 48 σ₁ + 576 σ₁∗σ₁ - 240 σ₃`, which is zero. -/
noncomputable def c2 (n : ℕ) : ℝ :=
  288 * ((n : ℝ) * sig 1 n) + (-48) * sig 1 n + 576 * conv (sig 1) (sig 1) n
    + (-240) * sig 3 n

theorem polyBdd_c2 : PolyBdd c2 := by
  have h := polyBdd_add (polyBdd_add (polyBdd_add
    (polyBdd_const_mul 288 (polyBdd_mulIdx (polyBdd_sig 1)))
    (polyBdd_const_mul (-48) (polyBdd_sig 1)))
    (polyBdd_const_mul 576 (polyBdd_conv (polyBdd_sig 1) (polyBdd_sig 1))))
    (polyBdd_const_mul (-240) (polyBdd_sig 3))
  exact h

theorem qa_c2 {y : ℝ} (hy : 0 < y) :
    qa c2 y = 288 * qa (fun n => (n : ℝ) * sig 1 n) y + (-48) * qa (sig 1) y
      + 576 * qa (conv (sig 1) (sig 1)) y + (-240) * qa (sig 3) y := by
  have h := qa_lin4 (polyBdd_summable (polyBdd_mulIdx (polyBdd_sig 1)) hy)
    (polyBdd_summable (polyBdd_sig 1) hy)
    (polyBdd_summable (polyBdd_conv (polyBdd_sig 1) (polyBdd_sig 1)) hy)
    (polyBdd_summable (polyBdd_sig 3) hy) 288 (-48) 576 (-240)
  exact h

theorem qa_c2_zero {y : ℝ} (hy : 0 < y) : qa c2 y = 0 := by
  have h := ram2_axis hy
  have hm := polyBdd_qa_mul (polyBdd_sig 1) (polyBdd_sig 1) hy
  rw [E2im_eq_qa hy, E4im_eq_qa hy] at h
  rw [qa_c2 hy, ← hm]
  linear_combination (-12 : ℝ) * h

/-- `576 σ₁∗σ₁ = 240 σ₃ + 48 σ₁ - 288 n σ₁` (as `c2 n = 0`). -/
theorem c2_zero (n : ℕ) : c2 n = 0 :=
  polyBdd_unique polyBdd_c2 (fun _ hy => qa_c2_zero hy) n

/-- `2 n w - w + 24 σ₁ + 24 σ₁∗w + 480 σ₃ + 57600 σ₃∗σ₃`, which is zero. -/
noncomputable def c6 (n : ℕ) : ℝ :=
  2 * ((n : ℝ) * wE n) + (-1) * wE n + 24 * sig 1 n + 24 * conv (sig 1) wE n + 480 * sig 3 n
    + 57600 * conv (sig 3) (sig 3) n

theorem polyBdd_c6 : PolyBdd c6 := by
  have h := polyBdd_add (polyBdd_add (polyBdd_add (polyBdd_add (polyBdd_add
    (polyBdd_const_mul 2 (polyBdd_mulIdx polyBdd_wE)) (polyBdd_const_mul (-1) polyBdd_wE))
    (polyBdd_const_mul 24 (polyBdd_sig 1)))
    (polyBdd_const_mul 24 (polyBdd_conv (polyBdd_sig 1) polyBdd_wE)))
    (polyBdd_const_mul 480 (polyBdd_sig 3)))
    (polyBdd_const_mul 57600 (polyBdd_conv (polyBdd_sig 3) (polyBdd_sig 3)))
  exact h

theorem qa_c6 {y : ℝ} (hy : 0 < y) :
    qa c6 y = 2 * qa (fun n => (n : ℝ) * wE n) y + (-1) * qa wE y + 24 * qa (sig 1) y
      + 24 * qa (conv (sig 1) wE) y + 480 * qa (sig 3) y
      + 57600 * qa (conv (sig 3) (sig 3)) y := by
  have h := qa_lin6 (polyBdd_summable (polyBdd_mulIdx polyBdd_wE) hy)
    (polyBdd_summable polyBdd_wE hy) (polyBdd_summable (polyBdd_sig 1) hy)
    (polyBdd_summable (polyBdd_conv (polyBdd_sig 1) polyBdd_wE) hy)
    (polyBdd_summable (polyBdd_sig 3) hy)
    (polyBdd_summable (polyBdd_conv (polyBdd_sig 3) (polyBdd_sig 3)) hy) 2 (-1) 24 24 480 57600
  exact h

theorem qa_c6_zero {y : ℝ} (hy : 0 < y) : qa c6 y = 0 := by
  have h := ram6_axis hy
  have hm1 := polyBdd_qa_mul (polyBdd_sig 1) polyBdd_wE hy
  have hm3 := polyBdd_qa_mul (polyBdd_sig 3) (polyBdd_sig 3) hy
  rw [E2im_eq_qa hy, E4im_eq_qa hy, E6im_eq_qa hy] at h
  rw [qa_c6 hy, ← hm1, ← hm3]
  linear_combination (2 : ℝ) * h

/-- `2 n w = w - 24 σ₁ - 24 σ₁∗w - 480 σ₃ - 57600 σ₃∗σ₃` (as `c6 n = 0`). -/
theorem c6_zero (n : ℕ) : c6 n = 0 :=
  polyBdd_unique polyBdd_c6 (fun _ hy => qa_c6_zero hy) n

/-! ## The identities in `ℝ⟦X⟧` -/

theorem coeff_S1 (n : ℕ) : PowerSeries.coeff n S1 = sig 1 n := PowerSeries.coeff_mk n _

theorem coeff_S3 (n : ℕ) : PowerSeries.coeff n S3 = sig 3 n := PowerSeries.coeff_mk n _

/-- The series `∑ w(n) Xⁿ = E₆ - 1`. -/
noncomputable def WE : PowerSeries ℝ := PowerSeries.mk wE

theorem coeff_WE (n : ℕ) : PowerSeries.coeff n WE = wE n := PowerSeries.coeff_mk n _

/-- The coefficients of a product of two series are the Cauchy product. -/
theorem coeff_mk_mul_mk (a b : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) = conv a b n := by
  rw [PowerSeries.coeff_mul]
  unfold conv
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]

theorem coeff_S1_S1 (n : ℕ) : PowerSeries.coeff n (S1 * S1) = conv (sig 1) (sig 1) n :=
  coeff_mk_mul_mk (sig 1) (sig 1) n

theorem coeff_S1_S3 (n : ℕ) : PowerSeries.coeff n (S1 * S3) = conv (sig 1) (sig 3) n :=
  coeff_mk_mul_mk (sig 1) (sig 3) n

theorem coeff_S3_S3 (n : ℕ) : PowerSeries.coeff n (S3 * S3) = conv (sig 3) (sig 3) n :=
  coeff_mk_mul_mk (sig 3) (sig 3) n

theorem coeff_S1_WE (n : ℕ) : PowerSeries.coeff n (S1 * WE) = conv (sig 1) wE n :=
  coeff_mk_mul_mk (sig 1) wE n

theorem ser_K2 : 576 * (S1 * S1) = 240 * S3 + 48 * S1 - 288 * theta S1 := by
  ext n
  have h := c2_zero n
  unfold c2 at h
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, coeff_theta, coeff_S1, coeff_S3, coeff_S1_S1]
  linear_combination h

theorem ser_WE : WE = 240 * S3 - 24 * S1 - 5760 * (S1 * S3) - 720 * theta S3 := by
  ext n
  simp only [map_sub, PowerSeries.coeff_ofNat_mul, coeff_theta, coeff_S1, coeff_S3, coeff_S1_S3, coeff_WE]
  unfold wE
  ring

theorem vE_eq : vE = 1 + WE := by
  rw [ser_WE]
  unfold vE xE uE
  simp only [theta_add, theta_mul, theta_one, theta_ofNat]
  ring

theorem ser_K6 :
    2 * theta WE = WE - 24 * S1 - 24 * (S1 * WE) - 480 * S3 - 57600 * (S3 * S3) := by
  ext n
  have h := c6_zero n
  unfold c6 at h
  simp only [map_sub, PowerSeries.coeff_ofNat_mul, coeff_theta, coeff_S1, coeff_S3, coeff_WE, coeff_S1_WE,
    coeff_S3_S3]
  linear_combination h

/-- Ramanujan's identity for `E₂` in `ℝ⟦X⟧`. -/
theorem ram_base2 : 12 * theta xE = xE * xE - uE := by
  have ht : theta xE = -(24 * theta S1) := by
    unfold xE
    simp only [theta_sub, theta_mul, theta_one, theta_ofNat]
    ring
  rw [ht]
  unfold xE uE
  linear_combination (-1 : PowerSeries ℝ) * ser_K2

/-- Ramanujan's identity for `E₆` in `ℝ⟦X⟧`. -/
theorem ram_base6 : 2 * theta vE = xE * vE - uE * uE := by
  rw [vE_eq]
  have ht : theta (1 + WE) = theta WE := by
    rw [theta_add, theta_one, zero_add]
  rw [ht]
  unfold xE uE
  linear_combination ser_K6

/-- Ramanujan's identities for `E₂, E₄, E₆` at `q, q², q³, q⁶`. -/
theorem ram6 : Ram6 := ram6_of_base ram_base2 ram_base6

end Tower.RV6
