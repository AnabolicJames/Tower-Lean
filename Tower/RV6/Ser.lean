import Mathlib
import Tower.RV6.Psi

/-!
# Formal power series: the operator `θ = X d/dX`, dilation, truncation

The tools for rung E″, which is proved in the ring `ℝ⟦X⟧`.

* `theta`: `θ(∑ cₙ Xⁿ) = ∑ n cₙ Xⁿ`; it is a derivation (`theta_mul`) that kills constants.
* `theta_expand`: `θ` after `X ↦ X^d` is `d` times `X ↦ X^d` after `θ`.
* `coeff_mul_of_lower_zero`: if the coefficients of `ψ` below `n` vanish, the coefficient of `Xⁿ`
  in `φ ψ` is `φ(0)` times that of `ψ`.
* `P7`, `dvd7_sub_P7`: a series minus its first seven terms is divisible by `X⁷`;
  `pi7`: the quotient map modulo `X⁷`, through which polynomial expressions are compared.
-/

namespace Tower.RV6

open PowerSeries

/-- `θ = X d/dX`. -/
noncomputable def theta (φ : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => (n : ℝ) * PowerSeries.coeff n φ)

theorem coeff_theta (φ : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (theta φ) = (n : ℝ) * PowerSeries.coeff n φ :=
  PowerSeries.coeff_mk n _

theorem theta_add (φ ψ : PowerSeries ℝ) : theta (φ + ψ) = theta φ + theta ψ := by
  ext n
  simp only [coeff_theta, map_add, mul_add]

theorem theta_sub (φ ψ : PowerSeries ℝ) : theta (φ - ψ) = theta φ - theta ψ := by
  ext n
  simp only [coeff_theta, map_sub, mul_sub]

theorem theta_neg (φ : PowerSeries ℝ) : theta (-φ) = -theta φ := by
  ext n
  simp only [coeff_theta, map_neg, mul_neg]

/-- The Leibniz rule. -/
theorem theta_mul (φ ψ : PowerSeries ℝ) : theta (φ * ψ) = theta φ * ψ + φ * theta ψ := by
  ext n
  simp only [coeff_theta, map_add, PowerSeries.coeff_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hc : (n : ℝ) = (p.1 : ℝ) + (p.2 : ℝ) := by rw [← hp', Nat.cast_add]
  rw [hc]
  ring

theorem theta_C (a : ℝ) : theta ((PowerSeries.C : ℝ →+* PowerSeries ℝ) a) = 0 := by
  ext n
  rw [coeff_theta, PowerSeries.coeff_C, map_zero]
  split_ifs with h
  · subst h
    rw [Nat.cast_zero, zero_mul]
  · rw [mul_zero]

theorem theta_natCast (m : ℕ) : theta (m : PowerSeries ℝ) = 0 := by
  rw [← map_natCast (PowerSeries.C : ℝ →+* PowerSeries ℝ) m]
  exact theta_C _

theorem theta_ofNat (m : ℕ) [m.AtLeastTwo] : theta (OfNat.ofNat m : PowerSeries ℝ) = 0 := by
  rw [← Nat.cast_ofNat (R := PowerSeries ℝ)]
  exact theta_natCast _

theorem theta_one : theta (1 : PowerSeries ℝ) = 0 := by
  rw [← map_one (PowerSeries.C : ℝ →+* PowerSeries ℝ)]
  exact theta_C _

theorem theta_zero : theta (0 : PowerSeries ℝ) = 0 := by
  ext n
  rw [coeff_theta, map_zero, mul_zero]

/-- The coefficient of a natural number times a series. -/
theorem coeff_natCast_mul (m : ℕ) (φ : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n ((m : PowerSeries ℝ) * φ) = (m : ℝ) * PowerSeries.coeff n φ := by
  rw [← map_natCast (PowerSeries.C : ℝ →+* PowerSeries ℝ) m, PowerSeries.coeff_C_mul]

theorem coeff_ofNat_mul (m : ℕ) [m.AtLeastTwo] (φ : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n ((OfNat.ofNat m : PowerSeries ℝ) * φ)
      = (OfNat.ofNat m : ℝ) * PowerSeries.coeff n φ := by
  have h := coeff_natCast_mul (OfNat.ofNat m) φ n
  rw [Nat.cast_ofNat, Nat.cast_ofNat] at h
  exact h

/-- `θ` after `X ↦ X^d` is `d` times `X ↦ X^d` after `θ`. -/
theorem theta_expand (d : ℕ) (hd : d ≠ 0) (φ : PowerSeries ℝ) :
    theta (PowerSeries.expand d hd φ)
      = (d : PowerSeries ℝ) * PowerSeries.expand d hd (theta φ) := by
  ext n
  rw [coeff_theta, coeff_natCast_mul, PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs with h
  · rw [coeff_theta]
    obtain ⟨k, rfl⟩ := h
    rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hd), Nat.cast_mul]
    ring
  · rw [mul_zero, mul_zero]

/-- If the coefficients of `ψ` below `n` vanish, the coefficient of `Xⁿ` in `φ ψ` is `φ(0) ψₙ`. -/
theorem coeff_mul_of_lower_zero (φ ψ : PowerSeries ℝ) (n : ℕ)
    (h : ∀ m < n, PowerSeries.coeff m ψ = 0) :
    PowerSeries.coeff n (φ * ψ) = PowerSeries.constantCoeff φ * PowerSeries.coeff n ψ := by
  rw [PowerSeries.coeff_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine Finset.sum_eq_single (0, n) ?_ ?_
  · intro p hp hne
    have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hlt : p.2 < n := by
      rcases Nat.lt_or_ge p.2 n with h1 | h1
      · exact h1
      · exfalso
        apply hne
        have h2 : p.2 = n := by omega
        have h3 : p.1 = 0 := by omega
        exact Prod.ext h3 h2
    rw [h p.2 hlt, mul_zero]
  · intro hnot
    exfalso
    exact hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp))

/-! ## Truncation at `X⁷` -/

/-- The polynomial `c₀ + c₁ X + ⋯ + c₆ X⁶` as a power series. -/
noncomputable def P7 (c0 c1 c2 c3 c4 c5 c6 : ℝ) : PowerSeries ℝ :=
  PowerSeries.C c0 + PowerSeries.C c1 * PowerSeries.X ^ 1 + PowerSeries.C c2 * PowerSeries.X ^ 2
    + PowerSeries.C c3 * PowerSeries.X ^ 3 + PowerSeries.C c4 * PowerSeries.X ^ 4
    + PowerSeries.C c5 * PowerSeries.X ^ 5 + PowerSeries.C c6 * PowerSeries.X ^ 6

theorem coeff_P7 (c0 c1 c2 c3 c4 c5 c6 : ℝ) :
    PowerSeries.coeff 0 (P7 c0 c1 c2 c3 c4 c5 c6) = c0
      ∧ PowerSeries.coeff 1 (P7 c0 c1 c2 c3 c4 c5 c6) = c1
      ∧ PowerSeries.coeff 2 (P7 c0 c1 c2 c3 c4 c5 c6) = c2
      ∧ PowerSeries.coeff 3 (P7 c0 c1 c2 c3 c4 c5 c6) = c3
      ∧ PowerSeries.coeff 4 (P7 c0 c1 c2 c3 c4 c5 c6) = c4
      ∧ PowerSeries.coeff 5 (P7 c0 c1 c2 c3 c4 c5 c6) = c5
      ∧ PowerSeries.coeff 6 (P7 c0 c1 c2 c3 c4 c5 c6) = c6 := by
  unfold P7
  simp [PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C]

/-- A series whose first seven coefficients are `c₀, …, c₆` differs from `P7 c₀ … c₆` by a
multiple of `X⁷`. -/
theorem dvd7_sub_P7 (φ : PowerSeries ℝ) (c0 c1 c2 c3 c4 c5 c6 : ℝ)
    (h0 : PowerSeries.coeff 0 φ = c0) (h1 : PowerSeries.coeff 1 φ = c1)
    (h2 : PowerSeries.coeff 2 φ = c2) (h3 : PowerSeries.coeff 3 φ = c3)
    (h4 : PowerSeries.coeff 4 φ = c4) (h5 : PowerSeries.coeff 5 φ = c5)
    (h6 : PowerSeries.coeff 6 φ = c6) :
    (PowerSeries.X : PowerSeries ℝ) ^ 7 ∣ φ - P7 c0 c1 c2 c3 c4 c5 c6 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := coeff_P7 c0 c1 c2 c3 c4 c5 c6
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub]
  interval_cases m
  · rw [h0, e0, sub_self]
  · rw [h1, e1, sub_self]
  · rw [h2, e2, sub_self]
  · rw [h3, e3, sub_self]
  · rw [h4, e4, sub_self]
  · rw [h5, e5, sub_self]
  · rw [h6, e6, sub_self]

theorem coeff_eq_zero_of_dvd7 {φ : PowerSeries ℝ} (h : (PowerSeries.X : PowerSeries ℝ) ^ 7 ∣ φ)
    {m : ℕ} (hm : m < 7) : PowerSeries.coeff m φ = 0 :=
  PowerSeries.X_pow_dvd_iff.mp h m hm

/-- The ideal `(X⁷)`. -/
noncomputable def I7 : Ideal (PowerSeries ℝ) := Ideal.span {(PowerSeries.X : PowerSeries ℝ) ^ 7}

/-- Reduction modulo `X⁷`. -/
noncomputable def pi7 : PowerSeries ℝ →+* (PowerSeries ℝ ⧸ I7) := Ideal.Quotient.mk I7

theorem pi7_eq_of_dvd {a b : PowerSeries ℝ}
    (h : (PowerSeries.X : PowerSeries ℝ) ^ 7 ∣ a - b) : pi7 a = pi7 b :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

theorem dvd7_of_pi7_eq_zero {a : PowerSeries ℝ} (h : pi7 a = 0) :
    (PowerSeries.X : PowerSeries ℝ) ^ 7 ∣ a :=
  Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)

theorem pi7_X_pow_mul (S : PowerSeries ℝ) : pi7 ((PowerSeries.X : PowerSeries ℝ) ^ 7 * S) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mul_mem_right S I7 (Ideal.mem_span_singleton_self _))

/-- Divisibility by `X⁷` survives `X ↦ X^d`. -/
theorem dvd7_expand (d : ℕ) (hd : d ≠ 0) {a b : PowerSeries ℝ}
    (h : (PowerSeries.X : PowerSeries ℝ) ^ 7 ∣ a - b) :
    (PowerSeries.X : PowerSeries ℝ) ^ 7
      ∣ PowerSeries.expand d hd a - PowerSeries.expand d hd b := by
  obtain ⟨t, ht⟩ := h
  have h1 : PowerSeries.expand d hd a - PowerSeries.expand d hd b
      = ((PowerSeries.X : PowerSeries ℝ) ^ d) ^ 7 * PowerSeries.expand d hd t := by
    rw [← map_sub, ht, map_mul, map_pow, PowerSeries.expand_X]
  rw [h1]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_pow_self _ hd) 7) _

/-! ## Values of the divisor sums up to six -/

theorem divisors_1 : Nat.divisors 1 = {1} := by decide
theorem divisors_2 : Nat.divisors 2 = {1, 2} := by decide
theorem divisors_3 : Nat.divisors 3 = {1, 3} := by decide
theorem divisors_4 : Nat.divisors 4 = {1, 2, 4} := by decide
theorem divisors_5 : Nat.divisors 5 = {1, 5} := by decide
theorem divisors_6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide

theorem sig1_vals : sig 1 0 = 0 ∧ sig 1 1 = 1 ∧ sig 1 2 = 3 ∧ sig 1 3 = 4 ∧ sig 1 4 = 7
    ∧ sig 1 5 = 6 ∧ sig 1 6 = 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sig]
  · rw [sig, divisors_1]; norm_num
  · rw [sig, divisors_2]; norm_num
  · rw [sig, divisors_3]; norm_num
  · rw [sig, divisors_4]; norm_num
  · rw [sig, divisors_5]; norm_num
  · rw [sig, divisors_6]; norm_num

theorem sig3_vals : sig 3 0 = 0 ∧ sig 3 1 = 1 ∧ sig 3 2 = 9 ∧ sig 3 3 = 28 ∧ sig 3 4 = 73
    ∧ sig 3 5 = 126 ∧ sig 3 6 = 252 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sig]
  · rw [sig, divisors_1]; norm_num
  · rw [sig, divisors_2]; norm_num
  · rw [sig, divisors_3]; norm_num
  · rw [sig, divisors_4]; norm_num
  · rw [sig, divisors_5]; norm_num
  · rw [sig, divisors_6]; norm_num

end Tower.RV6
