import Mathlib
import Tower.RV6.Defs
import Tower.RV6.Interchange
import Tower.RV6.Eichler2

/-!
# The Fricke split of the double Eisenstein integral (rung C1 in Eisenstein form)

`D01E = ∫₀^∞ (g₄(iy) 𝒜₁(y) - 1/(162 y⁶)) dy`, with `g₄ = g4E` and `𝒜₁ = A1E`.

**`D01E_eq`:  `D01E = -(104/(27π³)) ζ(5) + (64/9)(J₁/(2π) + J₂/(4π²))`.**

The proof follows the paper (Section 5), with `K₁ = 0` replaced by the inversion formula of the
partial Eichler integral:

1. `g₄(iy) = 1/(9y⁴) + (6y)⁻⁴ ĝ(i/(6y))` (`g4E_fricke`).
2. Against `1/(9y⁴)` the integral `𝒜₁` is taken in its Fricke form (`A1E_fricke`); the term
   `1/(162y⁶)` cancels and what is left integrates to `-(104/(27π³)) ζ(5)` (`integral_Tint_fricke`).
3. Against `(6y)⁻⁴ ĝ(i/(6y))` it is taken in its direct form (`A1E_direct`, `Tint_eq`); this gives
   sixteen pairs `(e, f)` of divisors of six for each of the kernels `y⁻³`, `y⁻⁴`.
4. Each pair is carried from the `σ₃`-side to the `σ₁`-side by the interchange
   (`interchange_three`, `interchange_four`), and the coefficients recombine to `J₁`, `J₂`.

The four divisors are indexed by `Finset.range 4` through `dv`; the coefficient vectors of
`𝔉`, `𝔊` are `cF`, `cG`.  This file is written by `tools/gen_rungc1.py`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## The divisors of six and the coefficient vectors -/

/-- The divisors `1, 2, 3, 6` of six, indexed by `0, 1, 2, 3`. -/
noncomputable def dv (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 3 else if k = 3 then 6 else 1

/-- Coefficients of `𝔉 = 𝔈(τ) - 2𝔈(2τ) - 27𝔈(3τ) + 54𝔈(6τ)`. -/
noncomputable def cF (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then -2 else if k = 2 then -27 else if k = 3 then 54 else 0

/-- Coefficients of `𝔊 = 𝔈(τ) - 2𝔈(2τ) - (1/3)𝔈(3τ) + (2/3)𝔈(6τ)`. -/
noncomputable def cG (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then -2 else if k = 2 then -(1 / 3) else if k = 3 then 2 / 3
  else 0

theorem dv_pos (k : ℕ) : 0 < dv k := by
  unfold dv
  split_ifs <;> norm_num

theorem dv_zero : dv 0 = 1 := by norm_num [dv]
theorem dv_one : dv 1 = 2 := by norm_num [dv]
theorem dv_two : dv 2 = 3 := by norm_num [dv]
theorem dv_three : dv 3 = 6 := by norm_num [dv]
theorem cF_zero : cF 0 = 1 := by norm_num [cF]
theorem cF_one : cF 1 = -2 := by norm_num [cF]
theorem cF_two : cF 2 = -27 := by norm_num [cF]
theorem cF_three : cF 3 = 54 := by norm_num [cF]
theorem cG_zero : cG 0 = 1 := by norm_num [cG]
theorem cG_one : cG 1 = -2 := by norm_num [cG]
theorem cG_two : cG 2 = -(1 / 3) := by norm_num [cG]
theorem cG_three : cG 3 = 2 / 3 := by norm_num [cG]

theorem sum_range_four (F : ℕ → ℝ) : ∑ k ∈ Finset.range 4, F k = F 0 + F 1 + F 2 + F 3 := by
  simp [Finset.sum_range_succ]

/-! ## The objects of the paper as sums over the divisors -/

theorem ghatE_sum {x : ℝ} (hx : 0 < x) :
    ghatE x = 32 * ∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k * x) := by
  rw [ghatE_eq_qa hx, sum_range_four, dv_zero, dv_one, dv_two, dv_three, cG_zero, cG_one, cG_two,
    cG_three]
  simp only [one_mul]
  ring

theorem A1E_direct_sum {y : ℝ} (hy : 0 < y) :
    A1E y = 32 * (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * Tint (dv l * y)) := by
  rw [A1E_direct hy, sum_range_four, dv_zero, dv_one, dv_two, dv_three, cF_zero, cF_one, cF_two,
    cF_three]
  simp only [one_mul]
  ring

theorem A1E_fricke_sum {y : ℝ} (hy : 0 < y) :
    A1E y = 1 / (18 * y ^ 2) - 8 * (∑ k ∈ Finset.range 4, cG k * dv k * Tint (dv k / (6 * y))) := by
  rw [A1E_fricke hy, sum_range_four, dv_zero, dv_one, dv_two, dv_three, cG_zero, cG_one, cG_two,
    cG_three]
  ring

/-- `(q d/dq) 𝔈` in the notation of `QSeries.lean`. -/
theorem DEcal_eq_qa (y : ℝ) : DEcal y = qa (fun n : ℕ => (n : ℝ) * sig 1 n) y := by
  unfold DEcal qa
  refine tsum_congr (fun n => ?_)
  have h1 : (sigma1 n : ℝ) = sig 1 n := by simp [sigma1, sig]
  have he : (-2 * π * (n : ℝ) * y) = -(2 * π * (n : ℝ) * y) := by ring
  show (n : ℝ) * (sigma1 n : ℝ) * Real.exp (-2 * π * (n : ℝ) * y)
    = (n : ℝ) * sig 1 n * Real.exp (-(2 * π * (n : ℝ) * y))
  rw [h1, he]

theorem Fcal_sum (x : ℝ) : Fcal x = ∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k * x) := by
  unfold Fcal
  rw [sum_range_four, dv_zero, dv_one, dv_two, dv_three, cF_zero, cF_one, cF_two, cF_three]
  simp only [one_mul, Ecal_eq_qa]
  ring

theorem Gcal_sum (y : ℝ) : Gcal y = (∑ l ∈ Finset.range 4, cG l * qa (sig 1) (dv l * y)) := by
  unfold Gcal
  rw [sum_range_four, dv_zero, dv_one, dv_two, dv_three, cG_zero, cG_one, cG_two, cG_three]
  simp only [one_mul, Ecal_eq_qa]
  ring

theorem DGcal_sum (y : ℝ) : DGcal y = (∑ l ∈ Finset.range 4, cG l * dv l * qa (fun n : ℕ => (n : ℝ) * sig 1 n) (dv l * y)) := by
  unfold DGcal
  rw [sum_range_four, dv_zero, dv_one, dv_two, dv_three, cG_zero, cG_one, cG_two, cG_three]
  simp only [one_mul, DEcal_eq_qa]
  ring

/-- The direct form of `𝒜₁` through the `q`-expansion of the Eichler integral. -/
theorem sumT_eq {y : ℝ} (hy : 0 < y) :
    (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * Tint (dv l * y))
      = y / (2 * π) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 2 * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y))
        + 1 / (4 * π ^ 2) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Tint_eq (mul_pos (dv_pos l) hy)]
  have hDD : dv l * (dv l)⁻¹ = 1 := mul_inv_cancel₀ (dv_pos l).ne'
  linear_combination
    (cF l * y * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y) / (2 * π) * (dv l)⁻¹ ^ 2) * hDD

/-! ## The integrand -/

/-- The algebra of the split, for real numbers. -/
theorem c1_alg {G X y PS TC ST Q1 Q2 p : ℝ} (hy : y ≠ 0)
    (hg : G = 1 / (9 * y ^ 4) + 32 * PS / (6 * y) ^ 4)
    (hF : X = 1 / (18 * y ^ 2) - 8 * TC)
    (hD : X = 32 * ST)
    (hT : ST = y / (2 * p) * Q1 + 1 / (4 * p ^ 2) * Q2) :
    G * X - 1 / (162 * y ^ 6)
      = -(8 / 9) * (TC / y ^ 4) + 64 / 81 * (1 / (2 * p)) * (PS * Q1 / y ^ 3)
        + 64 / 81 * (1 / (4 * p ^ 2)) * (PS * Q2 / y ^ 4) := by
  have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy
  linear_combination X * hg + (1 / (9 * y ^ 4)) * hF + (32 * PS / (6 * y) ^ 4) * hD
    + (32 * PS / (6 * y) ^ 4 * 32) * hT + (64 / 81 * (1 / (2 * p)) * PS * Q1 * y⁻¹ ^ 3) * hyy

/-- The integrand of `D01E` for `y > 0`. -/
theorem D01E_integrand {y : ℝ} (hy : 0 < y) :
    g4E y * A1E y - 1 / (162 * y ^ 6)
      = (-(8 / 9) * (∑ k ∈ Finset.range 4, cG k * dv k * (Tint (dv k / (6 * y)) / y ^ 4)) + 64 / 81 * (1 / (2 * π)) * ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 2 * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y)) / y ^ 3) + 64 / 81 * (1 / (4 * π ^ 2)) * ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y)) / y ^ 4)) := by
  have hu : (0 : ℝ) < 1 / (6 * y) := by positivity
  have hsum : ∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k * (1 / (6 * y)))
      = (∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) :=
    Finset.sum_congr rfl (fun k _ => by rw [mul_one_div])
  have hPS : ghatE (1 / (6 * y)) = 32 * (∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) := by
    rw [ghatE_sum hu, hsum]
  have hg : g4E y = 1 / (9 * y ^ 4) + 32 * (∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) / (6 * y) ^ 4 := by
    rw [g4E_fricke hy, hPS]
  have hTC : (∑ k ∈ Finset.range 4, cG k * dv k * Tint (dv k / (6 * y))) / y ^ 4
      = (∑ k ∈ Finset.range 4, cG k * dv k * (Tint (dv k / (6 * y)) / y ^ 4)) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [← hTC]
  exact c1_alg hy.ne' hg (A1E_fricke_sum hy) (A1E_direct_sum hy) (sumT_eq hy)

/-! ## The three pieces: integrability and value -/

theorem lin_TC :
    Integrable (fun y : ℝ => (∑ k ∈ Finset.range 4, cG k * dv k * (Tint (dv k / (6 * y)) / y ^ 4))) (volume.restrict (Set.Ioi (0 : ℝ)))
      ∧ ∫ y in Set.Ioi (0 : ℝ), (∑ k ∈ Finset.range 4, cG k * dv k * (Tint (dv k / (6 * y)) / y ^ 4))
        = ∑ k ∈ Finset.range 4, cG k * dv k * (∫ y in Set.Ioi (0 : ℝ), Tint (dv k / (6 * y)) / y ^ 4) :=
  integral_lin_gen (Finset.range 4) (fun k y => Tint (dv k / (6 * y)) / y ^ 4) (fun k => cG k * dv k)
    (fun k _ => integrable_Tint_fricke (dv_pos k))

theorem const_sum :
    ∑ k ∈ Finset.range 4, cG k * dv k * (∫ y in Set.Ioi (0 : ℝ), Tint (dv k / (6 * y)) / y ^ 4)
      = 104 * (zeta5 / (24 * π ^ 3)) := by
  have h : ∀ k ∈ Finset.range 4,
      cG k * dv k * (∫ y in Set.Ioi (0 : ℝ), Tint (dv k / (6 * y)) / y ^ 4)
        = cG k * dv k * (216 / dv k ^ 3 * (zeta5 / (24 * π ^ 3))) :=
    fun k _ => by rw [integral_Tint_fricke (dv_pos k)]
  rw [Finset.sum_congr rfl h, sum_range_four, dv_zero, dv_one, dv_two, dv_three, cG_zero, cG_one,
    cG_two, cG_three]
  ring

theorem bilin_S3 :
    Integrable (fun y : ℝ => ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 2 * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y)) / y ^ 3)) (volume.restrict (Set.Ioi (0 : ℝ)))
      ∧ ∫ y in Set.Ioi (0 : ℝ), ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 2 * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y)) / y ^ 3)
        = ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * (cF l / dv l ^ 2) * (∫ y in Set.Ioi (0 : ℝ), qa (sig 3) (dv k / (6 * y)) * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y) / y ^ 3) :=
  integral_bilin_gen (Finset.range 4) (Finset.range 4)
    (fun k y => qa (sig 3) (dv k / (6 * y))) (fun l y => qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y))
    (fun y => y ^ 3) (fun k => 9 * cG k * dv k ^ 3) (fun l => cF l / dv l ^ 2)
    (fun k _ l _ => integrable_qa_mul (sig_zero 3) (by simp [sig_zero]) (sig_abs_le 3) bound_sig3_div
      (dv_pos k) (dv_pos l) 2 (sig_nonneg 3) sig3_div_nonneg (sig_one_pos 3) (by simp [sig]))

theorem bilin_S4 :
    Integrable (fun y : ℝ => ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y)) / y ^ 4)) (volume.restrict (Set.Ioi (0 : ℝ)))
      ∧ ∫ y in Set.Ioi (0 : ℝ), ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y)) / y ^ 4)
        = ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * (cF l / dv l ^ 3) * (∫ y in Set.Ioi (0 : ℝ), qa (sig 3) (dv k / (6 * y)) * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y) / y ^ 4) :=
  integral_bilin_gen (Finset.range 4) (Finset.range 4)
    (fun k y => qa (sig 3) (dv k / (6 * y))) (fun l y => qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y))
    (fun y => y ^ 4) (fun k => 9 * cG k * dv k ^ 3) (fun l => cF l / dv l ^ 3)
    (fun k _ l _ => integrable_qa_mul (sig_zero 3) (by simp [sig_zero]) (sig_abs_le 3) bound_sig3_div_sq
      (dv_pos k) (dv_pos l) 3 (sig_nonneg 3) sig3_div_sq_nonneg (sig_one_pos 3) (by simp [sig]))

theorem bilin_J1 :
    Integrable (fun y : ℝ => ((∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cG l * dv l * qa (fun n : ℕ => (n : ℝ) * sig 1 n) (dv l * y)) / y ^ 3)) (volume.restrict (Set.Ioi (0 : ℝ)))
      ∧ ∫ y in Set.Ioi (0 : ℝ), ((∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cG l * dv l * qa (fun n : ℕ => (n : ℝ) * sig 1 n) (dv l * y)) / y ^ 3)
        = ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, cF k * (cG l * dv l) * (∫ y in Set.Ioi (0 : ℝ), qa (sig 1) (dv k / (6 * y)) * qa (fun n : ℕ => (n : ℝ) * sig 1 n) (dv l * y) / y ^ 3) :=
  integral_bilin_gen (Finset.range 4) (Finset.range 4)
    (fun k y => qa (sig 1) (dv k / (6 * y))) (fun l y => qa (fun n : ℕ => (n : ℝ) * sig 1 n) (dv l * y))
    (fun y => y ^ 3) (fun k => cF k) (fun l => cG l * dv l)
    (fun k _ l _ => integrable_qa_mul (sig_zero 1) (by simp [sig_zero]) (sig_abs_le 1) bound_mul_sig1
      (dv_pos k) (dv_pos l) 2 (sig_nonneg 1)
      (fun n => mul_nonneg (Nat.cast_nonneg n) (sig_nonneg 1 n)) (sig_one_pos 1) (by simp [sig]))

theorem bilin_J2 :
    Integrable (fun y : ℝ => ((∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cG l * qa (sig 1) (dv l * y)) / y ^ 4)) (volume.restrict (Set.Ioi (0 : ℝ)))
      ∧ ∫ y in Set.Ioi (0 : ℝ), ((∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cG l * qa (sig 1) (dv l * y)) / y ^ 4)
        = ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, cF k * cG l * (∫ y in Set.Ioi (0 : ℝ), qa (sig 1) (dv k / (6 * y)) * qa (sig 1) (dv l * y) / y ^ 4) :=
  integral_bilin_gen (Finset.range 4) (Finset.range 4)
    (fun k y => qa (sig 1) (dv k / (6 * y))) (fun l y => qa (sig 1) (dv l * y))
    (fun y => y ^ 4) (fun k => cF k) (fun l => cG l)
    (fun k _ l _ => integrable_qa_mul (sig_zero 1) (sig_zero 1) (sig_abs_le 1) (sig_abs_le 1)
      (dv_pos k) (dv_pos l) 3 (sig_nonneg 1) (sig_nonneg 1) (sig_one_pos 1) (sig_one_pos 1))

/-! ## `J₁`, `J₂` as double sums -/

theorem J1_eq : J1 = ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, cF k * (cG l * dv l) * (∫ y in Set.Ioi (0 : ℝ), qa (sig 1) (dv k / (6 * y)) * qa (fun n : ℕ => (n : ℝ) * sig 1 n) (dv l * y) / y ^ 3) := by
  unfold J1
  refine Eq.trans ?_ bilin_J1.2
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  show Fcal (1 / (6 * y)) * DGcal y / y ^ 3 = ((∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cG l * dv l * qa (fun n : ℕ => (n : ℝ) * sig 1 n) (dv l * y)) / y ^ 3)
  have hF : ∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k * (1 / (6 * y))) = (∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k / (6 * y))) :=
    Finset.sum_congr rfl (fun k _ => by rw [mul_one_div])
  rw [Fcal_sum, DGcal_sum, hF]

theorem J2_eq : J2 = ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, cF k * cG l * (∫ y in Set.Ioi (0 : ℝ), qa (sig 1) (dv k / (6 * y)) * qa (sig 1) (dv l * y) / y ^ 4) := by
  unfold J2
  refine Eq.trans ?_ bilin_J2.2
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  show Fcal (1 / (6 * y)) * Gcal y / y ^ 4 = ((∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cG l * qa (sig 1) (dv l * y)) / y ^ 4)
  have hF : ∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k * (1 / (6 * y))) = (∑ k ∈ Finset.range 4, cF k * qa (sig 1) (dv k / (6 * y))) :=
    Finset.sum_congr rfl (fun k _ => by rw [mul_one_div])
  rw [Fcal_sum, Gcal_sum, hF]

/-! ## The sixteen pairs -/

theorem pair3_alg {cg cf dk dl IS JE : ℝ} (hdl : dl ≠ 0) (h : dk ^ 2 * IS = dl ^ 2 * JE) :
    9 * cg * dk ^ 3 * (cf / dl ^ 2) * IS = 9 * (cf * (cg * dk) * JE) := by
  have h2 : dl * dl⁻¹ = 1 := mul_inv_cancel₀ hdl
  linear_combination (9 * cg * dk * cf * dl⁻¹ ^ 2) * h
    + (9 * cf * cg * dk * JE * (dl * dl⁻¹ + 1)) * h2

theorem pair4_alg {cg cf dk dl IS JE : ℝ} (hdl : dl ≠ 0) (h : dk ^ 3 * IS = dl ^ 3 * JE) :
    9 * cg * dk ^ 3 * (cf / dl ^ 3) * IS = 9 * (cf * cg * JE) := by
  have h2 : dl * dl⁻¹ = 1 := mul_inv_cancel₀ hdl
  linear_combination (9 * cg * cf * dl⁻¹ ^ 3) * h
    + (9 * cf * cg * JE * ((dl * dl⁻¹) ^ 2 + dl * dl⁻¹ + 1)) * h2

/-- The `σ₃`-side double sum with kernel `y⁻³` is nine times the double sum of `J₁`. -/
theorem swap3 :
    ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * (cF l / dv l ^ 2) * (∫ y in Set.Ioi (0 : ℝ), qa (sig 3) (dv k / (6 * y)) * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y) / y ^ 3)
      = 9 * ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, cF k * (cG l * dv l) * (∫ y in Set.Ioi (0 : ℝ), qa (sig 1) (dv k / (6 * y)) * qa (fun n : ℕ => (n : ℝ) * sig 1 n) (dv l * y) / y ^ 3) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact pair3_alg (dv_pos l).ne' (interchange_three (dv_pos k) (dv_pos l))

/-- The `σ₃`-side double sum with kernel `y⁻⁴` is nine times the double sum of `J₂`. -/
theorem swap4 :
    ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * (cF l / dv l ^ 3) * (∫ y in Set.Ioi (0 : ℝ), qa (sig 3) (dv k / (6 * y)) * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y) / y ^ 4)
      = 9 * ∑ k ∈ Finset.range 4, ∑ l ∈ Finset.range 4, cF k * cG l * (∫ y in Set.Ioi (0 : ℝ), qa (sig 1) (dv k / (6 * y)) * qa (sig 1) (dv l * y) / y ^ 4) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact pair4_alg (dv_pos l).ne' (interchange_four (dv_pos k) (dv_pos l))

/-! ## The Fricke split -/

/-- The regularised double Eisenstein integral, for the Eisenstein combination `g4E`. -/
noncomputable def D01E : ℝ := ∫ y in Set.Ioi (0 : ℝ), (g4E y * A1E y - 1 / (162 * y ^ 6))

/-- **The Fricke split (rung C1, Eisenstein form).** -/
theorem D01E_eq : D01E = -(104 / (27 * π ^ 3)) * zeta5 + crossTerm := by
  have hcongr : D01E = ∫ y in Set.Ioi (0 : ℝ), (-(8 / 9) * (∑ k ∈ Finset.range 4, cG k * dv k * (Tint (dv k / (6 * y)) / y ^ 4)) + 64 / 81 * (1 / (2 * π)) * ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 2 * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y)) / y ^ 3) + 64 / 81 * (1 / (4 * π ^ 2)) * ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y)) / y ^ 4)) := by
    unfold D01E
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    exact D01E_integrand hy0
  have hlin : ∫ y in Set.Ioi (0 : ℝ), (-(8 / 9) * (∑ k ∈ Finset.range 4, cG k * dv k * (Tint (dv k / (6 * y)) / y ^ 4)) + 64 / 81 * (1 / (2 * π)) * ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 2 * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y)) / y ^ 3) + 64 / 81 * (1 / (4 * π ^ 2)) * ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y)) / y ^ 4))
      = -(8 / 9) * (∫ y in Set.Ioi (0 : ℝ), (∑ k ∈ Finset.range 4, cG k * dv k * (Tint (dv k / (6 * y)) / y ^ 4)))
        + 64 / 81 * (1 / (2 * π)) * (∫ y in Set.Ioi (0 : ℝ), ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 2 * qa (fun n : ℕ => sig 3 n / (n : ℝ)) (dv l * y)) / y ^ 3))
        + 64 / 81 * (1 / (4 * π ^ 2)) * (∫ y in Set.Ioi (0 : ℝ), ((∑ k ∈ Finset.range 4, 9 * cG k * dv k ^ 3 * qa (sig 3) (dv k / (6 * y))) * (∑ l ∈ Finset.range 4, cF l / dv l ^ 3 * qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (dv l * y)) / y ^ 4)) :=
    integral_lin3 lin_TC.1 bilin_S3.1 bilin_S4.1 (-(8 / 9)) (64 / 81 * (1 / (2 * π))) (64 / 81 * (1 / (4 * π ^ 2)))
  rw [hcongr, hlin, lin_TC.2, bilin_S3.2, bilin_S4.2, const_sum, swap3, swap4]
  unfold crossTerm
  rw [J1_eq, J2_eq]
  ring

end Tower.RV6
