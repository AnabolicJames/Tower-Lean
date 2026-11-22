import Mathlib
import Tower.RV6.MellinSeries

/-!
# The Eisenstein form `Ψ` and rung D′

`Ψ = (5/144) (Σ_d e_d E₄(dτ) - F̂²)` with `F̂ = (3/2)E₂(τ) - 3E₂(2τ) - (1/2)E₂(3τ) + E₂(6τ)` is the
weight-four form that the modular side of the six-step theorem produces; by equation (6.8) of
the paper it is the eta product `(η(τ)η(2τ)η(3τ)η(6τ))²`.  Its coefficients are finite divisor
sums (`psiCoeff`).

Main result: **`lambdaPsi5_eq`** (rung D′, no hypotheses):
`∫₀^∞ Ψ(iy) y⁴ dy = (3/(4π⁵)) Σ psiCoeff(n)/n⁵`.
The proof is the termwise Mellin transform of `MellinSeries.lean` together with the bound
`|psiCoeff n| ≤ 23200 n^{7/2}`, which comes from `σ₁(n) ≤ n (1 + log n) ≤ 4 n^{5/4}`.
-/

namespace Tower.RV6

open Real MeasureTheory Set

/-- `σ_k(n)` as a real number. -/
noncomputable def sig (k n : ℕ) : ℝ := ∑ d ∈ n.divisors, (d : ℝ) ^ k

/-- `σ_k(n/m)` if `m ∣ n`, and `0` otherwise. -/
noncomputable def sigDiv (k m n : ℕ) : ℝ := if m ∣ n then sig k (n / m) else 0

/-- Coefficients of `𝔊 = 𝔈(τ) - 2𝔈(2τ) - (1/3)𝔈(3τ) + (2/3)𝔈(6τ)`; `F̂ = -1 - 36 𝔊`. -/
noncomputable def gCoeff (n : ℕ) : ℝ :=
  sig 1 n - 2 * sigDiv 1 2 n - 1 / 3 * sigDiv 1 3 n + 2 / 3 * sigDiv 1 6 n

/-- Coefficients of `Ψ`. -/
noncomputable def psiCoeff (n : ℕ) : ℝ :=
  7 / 2 * sig 3 n + 14 * sigDiv 3 2 n - 11 / 6 * sigDiv 3 3 n - 22 / 3 * sigDiv 3 6 n
    - 5 / 2 * gCoeff n - 45 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, gCoeff p.1 * gCoeff p.2

/-- `Ψ(iy) = ∑_{n ≥ 1} psiCoeff(n) e^{-2πny}`. -/
noncomputable def PsiIm (y : ℝ) : ℝ :=
  ∑' n : ℕ, psiCoeff (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y))

/-- `Λ(Ψ, 5) = ∫₀^∞ Ψ(iy) y⁴ dy`. -/
noncomputable def LambdaPsi5 : ℝ := ∫ y in Ioi (0 : ℝ), PsiIm y * y ^ 4

/-- `L(Ψ, 5) = ∑ psiCoeff(n)/n⁵`. -/
noncomputable def LPsi5 : ℝ := ∑' n : ℕ, psiCoeff n / (n : ℝ) ^ 5

/-! ## Bounds -/

theorem sig_nonneg (k n : ℕ) : 0 ≤ sig k n :=
  Finset.sum_nonneg (fun d _ => pow_nonneg (Nat.cast_nonneg d) k)

theorem sigDiv_nonneg (k m n : ℕ) : 0 ≤ sigDiv k m n := by
  unfold sigDiv
  split_ifs
  · exact sig_nonneg _ _
  · exact le_refl 0

theorem sigDiv_le (k m n : ℕ) : sigDiv k m n ≤ sig k n := by
  unfold sigDiv
  split_ifs with h
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · unfold sig
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Nat.divisors_subset_of_dvd hn.ne' (Nat.div_dvd_of_dvd h))
        (fun d _ _ => pow_nonneg (Nat.cast_nonneg d) k)
  · exact sig_nonneg _ _

/-- `∑_{d ∣ n} 1/d ≤ H_n ≤ 1 + log n ≤ 4 n^{1/4}`. -/
theorem sum_inv_divisors_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, (1 : ℝ) / d ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hsub : n.divisors ⊆ Finset.Icc 1 n := fun d hd =>
    Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  have h1 : ∑ d ∈ n.divisors, (1 : ℝ) / d ≤ ∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
  have h2 : ∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / d = (harmonic n : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  have h3 : (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hn0 _
  have h4 : Real.log ((n : ℝ) ^ ((1 : ℝ) / 4)) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) - 1 :=
    Real.log_le_sub_one_of_pos hx
  rw [Real.log_rpow hn0] at h4
  linarith

/-- `σ₁(n) ≤ 4 n^{5/4}`. -/
theorem sig_one_le (n : ℕ) (hn : 1 ≤ n) :
    sig 1 n ≤ (n : ℝ) * (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
  unfold sig
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ∑ d ∈ n.divisors, (d : ℝ) ^ 1 = ∑ d ∈ n.divisors, (n : ℝ) * ((1 : ℝ) / d) := by
    rw [← Nat.sum_div_divisors n (fun d => (d : ℝ) ^ 1)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    rw [pow_one, Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
    ring
  rw [h1, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_inv_divisors_le n hn) hn0.le

theorem sig_one_le_of_le {i n : ℕ} (h : i ≤ n) :
    sig 1 i ≤ (n : ℝ) * (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h0 : sig 1 0 = 0 := by simp [sig]
    rw [h0]
    exact mul_nonneg (Nat.cast_nonneg n)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · have hin : (i : ℝ) ≤ n := by exact_mod_cast h
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    calc sig 1 i ≤ (i : ℝ) * (4 * (i : ℝ) ^ ((1 : ℝ) / 4)) := sig_one_le i hi
      _ ≤ (n : ℝ) * (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul hin
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hi0 hin (by norm_num)) (by norm_num))
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hi0 _)) (Nat.cast_nonneg n)

/-- `σ₃(n) ≤ n² σ₁(n)`. -/
theorem sig_three_le (n : ℕ) : sig 3 n ≤ (n : ℝ) ^ 2 * sig 1 n := by
  unfold sig
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun d hd => ?_)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdn : (d : ℝ) ≤ n := by exact_mod_cast Nat.divisor_le hd
  have h : (d : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by gcongr
  calc (d : ℝ) ^ 3 = (d : ℝ) ^ 2 * (d : ℝ) ^ 1 := by ring
    _ ≤ (n : ℝ) ^ 2 * (d : ℝ) ^ 1 := mul_le_mul_of_nonneg_right h (by positivity)

theorem gCoeff_abs_le (n : ℕ) : |gCoeff n| ≤ 4 * sig 1 n := by
  have h2 := sigDiv_le 1 2 n
  have h3 := sigDiv_le 1 3 n
  have h6 := sigDiv_le 1 6 n
  have p2 := sigDiv_nonneg 1 2 n
  have p3 := sigDiv_nonneg 1 3 n
  have p6 := sigDiv_nonneg 1 6 n
  have p1 := sig_nonneg 1 n
  unfold gCoeff
  rw [abs_le]
  constructor <;> linarith

theorem conv_abs_le (n : ℕ) (B : ℝ) (hB : ∀ i ≤ n, |gCoeff i| ≤ B) :
    |∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, gCoeff p.1 * gCoeff p.2| ≤ ((n : ℝ) + 1) * (B * B) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (Nat.zero_le n))
  calc |∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, gCoeff p.1 * gCoeff p.2|
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, |gCoeff p.1 * gCoeff p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal n, B * B := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rw [abs_mul]
        exact mul_le_mul (hB p.1 (by omega)) (hB p.2 (by omega)) (abs_nonneg _) hB0
    _ = ((n : ℝ) + 1) * (B * B) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul, Nat.cast_add_one]

/-- A fourth root: `x = n^{1/4}` with the two identities that are used. -/
theorem exists_root (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : ℝ, 1 ≤ x ∧ (n : ℝ) = x ^ 4 ∧ (n : ℝ) ^ ((3 : ℝ) / 2) = x ^ 6 ∧
      (n : ℝ) ^ ((1 : ℝ) / 4) = x := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  refine ⟨(n : ℝ) ^ ((1 : ℝ) / 4), Real.one_le_rpow hn1 (by norm_num), ?_, ?_, rfl⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num

theorem psiCoeff_abs_le (n : ℕ) (x : ℝ) (hx1 : 1 ≤ x) (hxn : (n : ℝ) = x ^ 4)
    (hxr : (n : ℝ) ^ ((1 : ℝ) / 4) = x) : |psiCoeff n| ≤ 23200 * x ^ 14 := by
  have hx0 : 0 ≤ x := by linarith
  have hM : ∀ i ≤ n, sig 1 i ≤ 4 * x ^ 5 := by
    intro i hi
    have h := sig_one_le_of_le hi
    rw [hxr, hxn] at h
    calc sig 1 i ≤ x ^ 4 * (4 * x) := h
      _ = 4 * x ^ 5 := by ring
  have hs1 : sig 1 n ≤ 4 * x ^ 5 := hM n le_rfl
  have hs3 : sig 3 n ≤ 4 * x ^ 13 := by
    have h := sig_three_le n
    rw [hxn] at h
    calc sig 3 n ≤ (x ^ 4) ^ 2 * sig 1 n := h
      _ ≤ (x ^ 4) ^ 2 * (4 * x ^ 5) := mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = 4 * x ^ 13 := by ring
  have hg : ∀ i ≤ n, |gCoeff i| ≤ 16 * x ^ 5 := by
    intro i hi
    calc |gCoeff i| ≤ 4 * sig 1 i := gCoeff_abs_le i
      _ ≤ 4 * (4 * x ^ 5) := by linarith [hM i hi]
      _ = 16 * x ^ 5 := by ring
  have hS := conv_abs_le n (16 * x ^ 5) hg
  have hn4 : (n : ℝ) + 1 ≤ 2 * x ^ 4 := by
    have h1 : (1 : ℝ) ≤ x ^ 4 := one_le_pow₀ hx1
    linarith
  have hS' : |∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, gCoeff p.1 * gCoeff p.2| ≤ 512 * x ^ 14 := by
    calc |∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, gCoeff p.1 * gCoeff p.2|
        ≤ ((n : ℝ) + 1) * (16 * x ^ 5 * (16 * x ^ 5)) := hS
      _ ≤ 2 * x ^ 4 * (16 * x ^ 5 * (16 * x ^ 5)) :=
          mul_le_mul_of_nonneg_right hn4 (by positivity)
      _ = 512 * x ^ 14 := by ring
  have hx13 : x ^ 13 ≤ x ^ 14 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx5 : x ^ 5 ≤ x ^ 14 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx14 : 0 ≤ x ^ 14 := by positivity
  have hg' := abs_le.mp (hg n le_rfl)
  have hS'' := abs_le.mp hS'
  have a1 := sig_nonneg 3 n
  have a2 := sigDiv_nonneg 3 2 n
  have a3 := sigDiv_nonneg 3 3 n
  have a6 := sigDiv_nonneg 3 6 n
  have b2 := sigDiv_le 3 2 n
  have b3 := sigDiv_le 3 3 n
  have b6 := sigDiv_le 3 6 n
  unfold psiCoeff
  rw [abs_le]
  constructor <;> linarith [hg'.1, hg'.2, hS''.1, hS''.2]

theorem psiCoeff_div_le (n : ℕ) (hn : 1 ≤ n) :
    |psiCoeff n| / (n : ℝ) ^ 5 ≤ 23200 * ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
  obtain ⟨x, hx1, hxn, hx6, hxr⟩ := exists_root n hn
  have hb := psiCoeff_abs_le n x hx1 hxn hxr
  have hx0 : 0 < x := by linarith
  rw [hx6, hxn, div_le_iff₀ (by positivity)]
  have e : (x ^ 6)⁻¹ * (x ^ 4) ^ 5 = x ^ 14 := by
    have h20 : (x ^ 4) ^ 5 = x ^ 6 * x ^ 14 := by ring
    rw [h20, inv_mul_cancel_left₀ (pow_ne_zero 6 hx0.ne')]
  calc |psiCoeff n| ≤ 23200 * x ^ 14 := hb
    _ = 23200 * (x ^ 6)⁻¹ * (x ^ 4) ^ 5 := by rw [mul_assoc, e]

theorem summable_psiCoeff :
    Summable fun n : ℕ => |psiCoeff (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ 5 := by
  have hp : Summable fun n : ℕ => (23200 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
    ((summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2))).mul_left 23200
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hp
  exact psiCoeff_div_le (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-! ## Rung D′ -/

theorem lPsi5_eq_shift : LPsi5 = ∑' n : ℕ, psiCoeff (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 := by
  unfold LPsi5
  have hsh : Summable fun n : ℕ => psiCoeff (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 := by
    refine Summable.of_norm_bounded summable_psiCoeff (fun n => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 5)]
  have hs : Summable fun n : ℕ => psiCoeff n / (n : ℝ) ^ 5 := (summable_nat_add_iff 1).mp hsh
  rw [hs.tsum_eq_zero_add]
  simp

/-- **Rung D′.**  `Λ(Ψ, 5) = (3/(4π⁵)) L(Ψ, 5)`. -/
theorem lambdaPsi5_eq : LambdaPsi5 = 3 / (4 * π ^ 5) * LPsi5 := by
  have h : ∫ y in Ioi (0 : ℝ),
        (∑' n : ℕ, psiCoeff (n + 1) * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y))) * y ^ 4
      = (Nat.factorial 4 : ℝ) / (2 * π) ^ 5
        * ∑' n : ℕ, psiCoeff (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 :=
    integral_qseries (fun n => psiCoeff (n + 1)) 4 summable_psiCoeff
  have h4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  unfold LambdaPsi5 PsiIm
  rw [h, lPsi5_eq_shift, h4]
  ring

end Tower.RV6
