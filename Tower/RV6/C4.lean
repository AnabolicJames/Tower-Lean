import Mathlib
import Tower.RV6.Defs
import Tower.RV6.QSeries
import Tower.RV6.Eichler2

/-!
# The Fourier coefficients of `g₄`

`Defs.lean` defines `g₄` by its Fourier coefficients `c4 n = 32 ∑_{d ∣ n} w(d) (n/d)³`,
`w(d) = 1 - [2 ∣ d] - 9 [3 ∣ d] + 9 [6 ∣ d]`.  This file shows that this is the Eisenstein
combination `g4E` of `Fricke6.lean`:

* `sum_antidiag_dvd`: `∑_{ab = n, m ∣ a} b³ = σ₃(n/m)` if `m ∣ n`, and `0` otherwise.
* `c4_eq`: `c₄(n) = 32 (σ₃(n) - σ₃(n/2) - 9 σ₃(n/3) + 9 σ₃(n/6))`.
* `g4_eq_g4E`: `g4 y = g4E y` for `y > 0`;  `A1_eq_A1E`: `A1 y = A1E y` for `y > 0`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `∑_{ab = n, m ∣ a} b³ = σ₃(n/m)` if `m ∣ n`, and `0` otherwise. -/
theorem sum_antidiag_dvd (m n : ℕ) (hm : 0 < m) :
    ∑ x ∈ n.divisorsAntidiagonal, (if m ∣ x.1 then (x.2 : ℝ) ^ 3 else 0)
      = if m ∣ n then sig 3 (n / m) else 0 := by
  by_cases hmn : m ∣ n
  · rw [if_pos hmn]
    obtain ⟨q, rfl⟩ := hmn
    rw [Nat.mul_div_cancel_left q hm]
    have hsig : sig 3 q = ∑ x ∈ q.divisorsAntidiagonal, (x.2 : ℝ) ^ 3 := by
      unfold sig
      exact (Nat.sum_divisorsAntidiagonal' (fun _ b => (b : ℝ) ^ 3)).symm
    rw [hsig, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun x => (x.1 / m, x.2)) (fun x => (m * x.1, x.2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨⟨h1, h2⟩, c, hc⟩ := hx
      rw [Nat.mem_divisorsAntidiagonal]
      refine ⟨?_, ?_⟩
      · show x.1 / m * x.2 = q
        rw [hc, mul_assoc] at h1
        rw [hc, Nat.mul_div_cancel_left c hm]
        exact Nat.eq_of_mul_eq_mul_left hm h1
      · intro hq
        exact h2 (by rw [hq, mul_zero])
    · intro x hx
      rw [Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨h1, h2⟩ := hx
      rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show m * x.1 * x.2 = m * q
        rw [mul_assoc, h1]
      · exact mul_ne_zero hm.ne' h2
      · show m ∣ m * x.1
        exact dvd_mul_right m x.1
    · intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨_, hd⟩ := hx
      exact Prod.ext (Nat.mul_div_cancel' hd) rfl
    · intro x _
      exact Prod.ext (Nat.mul_div_cancel_left x.1 hm) rfl
    · intro x _
      rfl
  · rw [if_neg hmn]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    obtain ⟨h1, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hnd : ¬ m ∣ x.1 := fun hd => hmn (by rw [← h1]; exact Dvd.dvd.mul_right hd x.2)
    rw [if_neg hnd]

theorem sum_lin4 {ι : Type*} (s : Finset ι) (f₁ f₂ f₃ f₄ : ι → ℝ) (c₁ c₂ c₃ c₄ : ℝ) :
    ∑ x ∈ s, (c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x + c₄ * f₄ x)
      = c₁ * (∑ x ∈ s, f₁ x) + c₂ * (∑ x ∈ s, f₂ x) + c₃ * (∑ x ∈ s, f₃ x)
        + c₄ * (∑ x ∈ s, f₄ x) := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- `w` as a real number. -/
theorem w_cast (d : ℕ) : ((w d : ℤ) : ℝ)
    = 1 - (if 2 ∣ d then 1 else 0) - (if 3 ∣ d then 9 else 0) + (if 6 ∣ d then 9 else 0) := by
  unfold w
  split_ifs <;> norm_num

/-- `c₄(n) = 32 (σ₃(n) - σ₃(n/2) - 9 σ₃(n/3) + 9 σ₃(n/6))`. -/
theorem c4_eq (n : ℕ) :
    (c4 n : ℝ) = 32 * sig 3 n + (-32) * (if 2 ∣ n then sig 3 (n / 2) else 0)
      + (-288) * (if 3 ∣ n then sig 3 (n / 3) else 0)
      + 288 * (if 6 ∣ n then sig 3 (n / 6) else 0) := by
  have h1 : sig 3 n = ∑ x ∈ n.divisorsAntidiagonal, (x.2 : ℝ) ^ 3 := by
    unfold sig
    exact (Nat.sum_divisorsAntidiagonal' (fun _ b => (b : ℝ) ^ 3)).symm
  have h2 := sum_antidiag_dvd 2 n (by norm_num)
  have h3 := sum_antidiag_dvd 3 n (by norm_num)
  have h6 := sum_antidiag_dvd 6 n (by norm_num)
  have hc : (c4 n : ℝ) = 32 * ∑ d ∈ n.divisors, ((w d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ) ^ 3 := by
    unfold c4
    first
      | (push_cast; done)
      | (push_cast; ring)
  have hA : ∑ d ∈ n.divisors, ((w d : ℤ) : ℝ) * ((n / d : ℕ) : ℝ) ^ 3
      = ∑ x ∈ n.divisorsAntidiagonal, ((w x.1 : ℤ) : ℝ) * (x.2 : ℝ) ^ 3 :=
    (Nat.sum_divisorsAntidiagonal (fun a b => ((w a : ℤ) : ℝ) * (b : ℝ) ^ 3)).symm
  have hB : ∑ x ∈ n.divisorsAntidiagonal, ((w x.1 : ℤ) : ℝ) * (x.2 : ℝ) ^ 3
      = ∑ x ∈ n.divisorsAntidiagonal, (1 * (x.2 : ℝ) ^ 3
          + (-1) * (if 2 ∣ x.1 then (x.2 : ℝ) ^ 3 else 0)
          + (-9) * (if 3 ∣ x.1 then (x.2 : ℝ) ^ 3 else 0)
          + 9 * (if 6 ∣ x.1 then (x.2 : ℝ) ^ 3 else 0)) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [w_cast]
    split_ifs <;> ring
  rw [hc, hA, hB, sum_lin4, ← h1, h2, h3, h6]
  ring

/-- `g₄(iy)` of `Defs.lean` is the Eisenstein combination `g4E` for `y > 0`. -/
theorem g4_eq_g4E {y : ℝ} (hy : 0 < y) : g4 y = g4E y := by
  have hq : g4 y = qa (fun n => 32 * sig 3 n + (-32) * (if 2 ∣ n then sig 3 (n / 2) else 0)
      + (-288) * (if 3 ∣ n then sig 3 (n / 3) else 0)
      + 288 * (if 6 ∣ n then sig 3 (n / 6) else 0)) y := by
    unfold g4 qa
    refine tsum_congr (fun n => ?_)
    have he : (-2 * π * (n : ℝ) * y) = -(2 * π * (n : ℝ) * y) := by ring
    show (c4 n : ℝ) * Real.exp (-2 * π * (n : ℝ) * y)
      = (32 * sig 3 n + (-32) * (if 2 ∣ n then sig 3 (n / 2) else 0)
        + (-288) * (if 3 ∣ n then sig 3 (n / 3) else 0)
        + 288 * (if 6 ∣ n then sig 3 (n / 6) else 0)) * Real.exp (-(2 * π * (n : ℝ) * y))
    rw [c4_eq n, he]
  have hcomb := qa_comb4 (A := sig 3) zero_le_one (sig_abs_le 3) 32 (-32) (-288) 288 hy
  rw [hq, hcomb, g4E_eq_qa hy]
  ring

/-- `𝒜₁` of `Defs.lean` is `A1E` for `y > 0`. -/
theorem A1_eq_A1E {y : ℝ} (hy : 0 < y) : A1 y = A1E y := by
  unfold A1 A1E
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := lt_trans hy ht
  show t * g4 t = t * g4E t
  rw [g4_eq_g4E ht0]

end Tower.RV6
