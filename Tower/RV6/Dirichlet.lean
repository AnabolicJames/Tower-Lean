import Mathlib
import Tower.RV6.Defs
import Tower.RV6.Psi
import Tower.RV6.Regroup

/-!
# Two Dirichlet series

`∑_{n ≥ 1} σ₃(n)/n⁵ = ζ(2) ζ(5) = (π²/6) ζ(5)` and `∑_{n ≥ 1} σ₁(n)/n⁵ = ζ(4) ζ(5) = (π⁴/90) ζ(5)`,
with `ζ(5)` the real number `zeta5 = (riemannZeta 5).re` of `Defs.lean`.

The general statement is `tsum_sig_div_pow`: for `s = k + t`, `t ≥ 2`,
`∑ σ_k(n)/n^s = (∑ 1/a^s)(∑ 1/b^t)`, by regrouping the double series over `(a, b)` by `ab`.
-/

namespace Tower.RV6

open Real

/-- `∑_{n ≥ 1} 1/n^p` written from `n = 0` with the shift, equals the sum over all `n`
(the term at `0` is `1/0 = 0`). -/
theorem tsum_shift_one_div_pow (p : ℕ) (hp : 1 < p) :
    ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ p = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ p := by
  have hs : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p := Real.summable_one_div_nat_pow.mpr hp
  have h := hs.tsum_eq_zero_add
  have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ p = 0 := by
    rw [Nat.cast_zero, zero_pow (by omega), div_zero]
  rw [h0, zero_add] at h
  exact h.symm

theorem tsum_inv_pow_two_shift : ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 = π ^ 2 / 6 := by
  rw [tsum_shift_one_div_pow 2 (by norm_num)]
  exact hasSum_zeta_two.tsum_eq

theorem tsum_inv_pow_four_shift : ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4 = π ^ 4 / 90 := by
  rw [tsum_shift_one_div_pow 4 (by norm_num)]
  exact hasSum_zeta_four.tsum_eq

/-- `ζ(5)` as a real series. -/
theorem zeta5_eq_tsum : zeta5 = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 5 := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 5) (by norm_num)
  have h2 : (∑' n : ℕ, 1 / (n : ℂ) ^ 5) = ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 5 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    first
      | norm_num
      | simp
      | (push_cast; ring)
  have h3 : riemannZeta 5 = ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 5 : ℝ) : ℂ) := by
    have h' : riemannZeta ((5 : ℕ) : ℂ) = riemannZeta 5 := by norm_num
    rw [← h', h, h2]
  unfold zeta5
  rw [h3, Complex.ofReal_re]

theorem tsum_inv_pow_five_shift : ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 5 = zeta5 := by
  rw [tsum_shift_one_div_pow 5 (by norm_num)]
  exact zeta5_eq_tsum.symm

/-- `σ_k(N)/N^{k+t} = ∑_{ab = N} a^{-(k+t)} b^{-t}`. -/
theorem sum_divisorsAntidiagonal_inv (k t N : ℕ) :
    sig k N / (N : ℝ) ^ (k + t)
      = ∑ x ∈ N.divisorsAntidiagonal,
          (1 : ℝ) / (x.1 : ℝ) ^ (k + t) * ((1 : ℝ) / (x.2 : ℝ) ^ t) := by
  have h1 : ∀ x ∈ N.divisorsAntidiagonal,
      (1 : ℝ) / (x.1 : ℝ) ^ (k + t) * ((1 : ℝ) / (x.2 : ℝ) ^ t)
        = (x.2 : ℝ) ^ k / (N : ℝ) ^ (k + t) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have ha : (x.1 : ℝ) ≠ 0 := by
      have h : x.1 ≠ 0 := by
        rintro h
        rw [h, zero_mul] at hx1
        exact hx2 hx1.symm
      exact_mod_cast h
    have hb : (x.2 : ℝ) ≠ 0 := by
      have h : x.2 ≠ 0 := by
        rintro h
        rw [h, mul_zero] at hx1
        exact hx2 hx1.symm
      exact_mod_cast h
    have hNx : (N : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by exact_mod_cast hx1.symm
    rw [hNx, div_mul_div_comm, one_mul,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
        (pow_ne_zero _ (mul_ne_zero ha hb))]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div]
  congr 1
  unfold sig
  exact (Nat.sum_divisorsAntidiagonal' (fun _ b => (b : ℝ) ^ k)).symm

theorem summable_shift_one_div_pow {p : ℕ} (hp : 1 < p) :
    Summable fun a : ℕ => (1 : ℝ) / ((a + 1 : ℕ) : ℝ) ^ p :=
  (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := p)).mpr hp)

theorem summable_shift_one_div_pow_norm {p : ℕ} (hp : 1 < p) :
    Summable fun a : ℕ => ‖(1 : ℝ) / ((a + 1 : ℕ) : ℝ) ^ p‖ := by
  refine (summable_shift_one_div_pow hp).congr (fun a => ?_)
  show (1 : ℝ) / ((a + 1 : ℕ) : ℝ) ^ p = ‖(1 : ℝ) / ((a + 1 : ℕ) : ℝ) ^ p‖
  rw [Real.norm_of_nonneg (div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg _) _))]

theorem tsum_shift_mul (s t : ℕ) (hs : 1 < s) (ht : 1 < t) :
    (∑' a : ℕ, (1 : ℝ) / ((a + 1 : ℕ) : ℝ) ^ s) * (∑' b : ℕ, (1 : ℝ) / ((b + 1 : ℕ) : ℝ) ^ t)
      = ∑' p : ℕ × ℕ,
        (1 : ℝ) / ((p.1 + 1 : ℕ) : ℝ) ^ s * ((1 : ℝ) / ((p.2 + 1 : ℕ) : ℝ) ^ t) :=
  tsum_mul_tsum_of_summable_norm (summable_shift_one_div_pow_norm hs)
    (summable_shift_one_div_pow_norm ht)

theorem summable_shift_prod (s t : ℕ) (hs : 1 < s) (ht : 1 < t) :
    Summable fun p : ℕ × ℕ =>
      (1 : ℝ) / ((p.1 + 1 : ℕ) : ℝ) ^ s * ((1 : ℝ) / ((p.2 + 1 : ℕ) : ℝ) ^ t) :=
  summable_mul_of_summable_norm (summable_shift_one_div_pow_norm hs)
    (summable_shift_one_div_pow_norm ht)

theorem tsum_shift_prod_regroup (s t : ℕ) (hs : 1 < s) (ht : 1 < t) :
    ∑' p : ℕ × ℕ, (1 : ℝ) / ((p.1 + 1 : ℕ) : ℝ) ^ s * ((1 : ℝ) / ((p.2 + 1 : ℕ) : ℝ) ^ t)
      = ∑' N : ℕ, ∑ x ∈ (N + 1).divisorsAntidiagonal,
          (1 : ℝ) / (x.1 : ℝ) ^ s * ((1 : ℝ) / (x.2 : ℝ) ^ t) :=
  tsum_prod_eq_tsum_divisorsAntidiagonal
    (fun a b : ℕ => (1 : ℝ) / (a : ℝ) ^ s * ((1 : ℝ) / (b : ℝ) ^ t)) (summable_shift_prod s t hs ht)

/-- `∑ σ_k(n)/n^s = (∑ 1/a^s)(∑ 1/b^t)` for `s = k + t`, `t ≥ 2`. -/
theorem tsum_sig_div_pow (k t s : ℕ) (hs : s = k + t) (ht : 2 ≤ t) :
    ∑' n : ℕ, sig k (n + 1) / ((n + 1 : ℕ) : ℝ) ^ s
      = (∑' a : ℕ, (1 : ℝ) / ((a + 1 : ℕ) : ℝ) ^ s) * (∑' b : ℕ, (1 : ℝ) / ((b + 1 : ℕ) : ℝ) ^ t) := by
  subst hs
  have h1 : 1 < k + t := by omega
  have h2 : 1 < t := by omega
  rw [tsum_shift_mul (k + t) t h1 h2, tsum_shift_prod_regroup (k + t) t h1 h2]
  exact tsum_congr (fun N => sum_divisorsAntidiagonal_inv k t (N + 1))

/-- `∑_{n ≥ 1} σ₃(n)/n⁵ = (π²/6) ζ(5)`. -/
theorem tsum_sig3_div_pow5 :
    ∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 = π ^ 2 / 6 * zeta5 := by
  rw [tsum_sig_div_pow 3 2 5 rfl le_rfl, tsum_inv_pow_five_shift, tsum_inv_pow_two_shift]
  ring

/-- `∑_{n ≥ 1} σ₁(n)/n⁵ = (π⁴/90) ζ(5)`. -/
theorem tsum_sig1_div_pow5 :
    ∑' n : ℕ, sig 1 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 = π ^ 4 / 90 * zeta5 := by
  rw [tsum_sig_div_pow 1 4 5 rfl (by norm_num), tsum_inv_pow_five_shift, tsum_inv_pow_four_shift]
  ring

end Tower.RV6
