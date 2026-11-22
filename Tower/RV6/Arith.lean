import Mathlib
import Tower.RV6.Psi

/-!
# The arithmetic identity behind the interchange of Lemma 5.1

`∑_{mn = N} σ₃(m) σ₃(n) n = ∑_{mn = N} σ₁(m) σ₁(n) n³`.

In the ring of arithmetic functions under Dirichlet convolution both sides are
`ζ * id * id³ * id⁴`: `σ_k = ζ * id^k`, and multiplying pointwise by `id^j` distributes over the
convolution.
-/

namespace Tower.RV6

/-- Pointwise multiplication by `n^k` distributes over Dirichlet convolution. -/
theorem pmul_pow_mul (k : ℕ) (f g : ArithmeticFunction ℕ) :
    (ArithmeticFunction.pow k).pmul (f * g)
      = (ArithmeticFunction.pow k).pmul f * (ArithmeticFunction.pow k).pmul g := by
  ext n
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  obtain ⟨hx1, hx2⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have h1 : x.1 ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hx1
    exact hx2 hx1.symm
  have h2 : x.2 ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hx1
    exact hx2 hx1.symm
  have e0 : ArithmeticFunction.pow k n = n ^ k := by
    simp [ArithmeticFunction.pow_apply, hx2]
  have e1 : ArithmeticFunction.pow k x.1 = x.1 ^ k := by
    simp [ArithmeticFunction.pow_apply, h1]
  have e2 : ArithmeticFunction.pow k x.2 = x.2 ^ k := by
    simp [ArithmeticFunction.pow_apply, h2]
  rw [e0, e1, e2, ← hx1]
  ring

theorem pmul_pow_zeta (k : ℕ) :
    (ArithmeticFunction.pow k).pmul ArithmeticFunction.zeta = ArithmeticFunction.pow k := by
  ext n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · simp [ArithmeticFunction.pmul_apply, ArithmeticFunction.zeta_apply, h.ne']

theorem pmul_pow_pow (j k : ℕ) :
    (ArithmeticFunction.pow j).pmul (ArithmeticFunction.pow k) = ArithmeticFunction.pow (j + k) := by
  ext n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · simp [ArithmeticFunction.pmul_apply, ArithmeticFunction.pow_apply, h.ne', pow_add]

/-- `σ₃ * (id · σ₃) = σ₁ * (id³ · σ₁)` as arithmetic functions. -/
theorem sigma_conv_identity :
    ArithmeticFunction.sigma 3 * (ArithmeticFunction.pow 1).pmul (ArithmeticFunction.sigma 3)
      = ArithmeticFunction.sigma 1
        * (ArithmeticFunction.pow 3).pmul (ArithmeticFunction.sigma 1) := by
  have h3 : (ArithmeticFunction.pow 1).pmul (ArithmeticFunction.sigma 3)
      = ArithmeticFunction.pow 1 * ArithmeticFunction.pow 4 := by
    have e : ArithmeticFunction.pow (1 + 3) = ArithmeticFunction.pow 4 := rfl
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, pmul_pow_mul, pmul_pow_zeta, pmul_pow_pow, e]
  have h1 : (ArithmeticFunction.pow 3).pmul (ArithmeticFunction.sigma 1)
      = ArithmeticFunction.pow 3 * ArithmeticFunction.pow 4 := by
    have e : ArithmeticFunction.pow (3 + 1) = ArithmeticFunction.pow 4 := rfl
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, pmul_pow_mul, pmul_pow_zeta, pmul_pow_pow, e]
  rw [h3, h1, ← ArithmeticFunction.zeta_mul_pow_eq_sigma (k := 3),
    ← ArithmeticFunction.zeta_mul_pow_eq_sigma (k := 1)]
  exact mul_mul_mul_comm _ _ _ _

theorem sig_eq_sigma (k n : ℕ) : sig k n = ((ArithmeticFunction.sigma k n : ℕ) : ℝ) := by
  simp [sig, ArithmeticFunction.sigma_apply]

theorem pmul_pow_apply (k : ℕ) (f : ArithmeticFunction ℕ) {n : ℕ} (hn : n ≠ 0) :
    ((ArithmeticFunction.pow k).pmul f) n = n ^ k * f n := by
  simp [ArithmeticFunction.pmul_apply, ArithmeticFunction.pow_apply, hn]

/-- **The arithmetic identity of the interchange.** -/
theorem conv_sig_identity (N : ℕ) :
    ∑ x ∈ N.divisorsAntidiagonal, sig 3 x.1 * sig 3 x.2 * (x.2 : ℝ)
      = ∑ x ∈ N.divisorsAntidiagonal, sig 1 x.1 * sig 1 x.2 * (x.2 : ℝ) ^ 3 := by
  have h : (ArithmeticFunction.sigma 3
        * (ArithmeticFunction.pow 1).pmul (ArithmeticFunction.sigma 3)) N
      = (ArithmeticFunction.sigma 1
        * (ArithmeticFunction.pow 3).pmul (ArithmeticFunction.sigma 1)) N := by
    rw [sigma_conv_identity]
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply] at h
  have hx2 : ∀ x ∈ N.divisorsAntidiagonal, x.2 ≠ 0 := by
    intro x hx
    obtain ⟨hx1, hxN⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    rintro h0
    rw [h0, mul_zero] at hx1
    exact hxN hx1.symm
  have hL : ∑ x ∈ N.divisorsAntidiagonal, sig 3 x.1 * sig 3 x.2 * (x.2 : ℝ)
      = ((∑ x ∈ N.divisorsAntidiagonal, ArithmeticFunction.sigma 3 x.1
          * ((ArithmeticFunction.pow 1).pmul (ArithmeticFunction.sigma 3)) x.2 : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [pmul_pow_apply 1 _ (hx2 x hx), sig_eq_sigma, sig_eq_sigma]
    push_cast
    ring
  have hR : ∑ x ∈ N.divisorsAntidiagonal, sig 1 x.1 * sig 1 x.2 * (x.2 : ℝ) ^ 3
      = ((∑ x ∈ N.divisorsAntidiagonal, ArithmeticFunction.sigma 1 x.1
          * ((ArithmeticFunction.pow 3).pmul (ArithmeticFunction.sigma 1)) x.2 : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [pmul_pow_apply 3 _ (hx2 x hx), sig_eq_sigma, sig_eq_sigma]
    push_cast
    ring
  rw [hL, hR, h]

end Tower.RV6
