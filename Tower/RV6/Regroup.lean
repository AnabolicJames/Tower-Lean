import Mathlib

/-!
# Regrouping a double series by the product of the indices

For an absolutely summable family `G` on pairs of positive integers,

`∑_{(m,n)} G(m,n) = ∑_N ∑_{mn = N} G(m,n)`.

The inner sum is over `Nat.divisorsAntidiagonal N`.  The bijection between pairs and the
disjoint union of the divisor antidiagonals is Mathlib's `sigmaAntidiagonalEquivProd`.
-/

namespace Tower.RV6

/-- Regrouping over pairs of positive integers. -/
theorem tsum_pnat_prod_eq_tsum_divisorsAntidiagonal (G : ℕ → ℕ → ℝ)
    (hG : Summable fun c : ℕ+ × ℕ+ => G c.1 c.2) :
    ∑' c : ℕ+ × ℕ+, G c.1 c.2
      = ∑' n : ℕ+, ∑ x ∈ (n : ℕ).divisorsAntidiagonal, G x.1 x.2 := by
  have hs : Summable fun x : (Σ n : ℕ+, (n : ℕ).divisorsAntidiagonal) =>
      G (sigmaAntidiagonalEquivProd x).1 (sigmaAntidiagonalEquivProd x).2 :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hG
  rw [← sigmaAntidiagonalEquivProd.tsum_eq (fun c : ℕ+ × ℕ+ => G c.1 c.2),
    Summable.tsum_sigma hs]
  refine tsum_congr (fun n => ?_)
  try simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe,
    Equiv.coe_fn_mk]
  exact Finset.tsum_subtype ((n : ℕ).divisorsAntidiagonal) (fun x => G x.1 x.2)

/-- Regrouping over pairs of natural numbers, each shifted by one. -/
theorem tsum_prod_eq_tsum_divisorsAntidiagonal (G : ℕ → ℕ → ℝ)
    (hG : Summable fun p : ℕ × ℕ => G (p.1 + 1) (p.2 + 1)) :
    ∑' p : ℕ × ℕ, G (p.1 + 1) (p.2 + 1)
      = ∑' N : ℕ, ∑ x ∈ (N + 1).divisorsAntidiagonal, G x.1 x.2 := by
  have he : ∀ c : ℕ+ × ℕ+,
      G ((Equiv.prodCongr Equiv.pnatEquivNat Equiv.pnatEquivNat c).1 + 1)
        ((Equiv.prodCongr Equiv.pnatEquivNat Equiv.pnatEquivNat c).2 + 1) = G c.1 c.2 := by
    intro c
    simp [PNat.natPred_add_one]
  have hs : Summable fun c : ℕ+ × ℕ+ => G c.1 c.2 :=
    ((Equiv.prodCongr Equiv.pnatEquivNat Equiv.pnatEquivNat).summable_iff.mpr hG).congr he
  have h1 : ∑' p : ℕ × ℕ, G (p.1 + 1) (p.2 + 1) = ∑' c : ℕ+ × ℕ+, G c.1 c.2 := by
    rw [← (Equiv.prodCongr Equiv.pnatEquivNat Equiv.pnatEquivNat).tsum_eq
      (fun p : ℕ × ℕ => G (p.1 + 1) (p.2 + 1))]
    exact tsum_congr he
  rw [h1, tsum_pnat_prod_eq_tsum_divisorsAntidiagonal G hs]
  exact tsum_pnat_eq_tsum_succ (f := fun n => ∑ x ∈ n.divisorsAntidiagonal, G x.1 x.2)

end Tower.RV6
