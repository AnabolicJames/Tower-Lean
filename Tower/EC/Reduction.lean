import Mathlib

/-!
# Reduction maps: a group lemma and a hypothesis package

`addOrderOf_eq_zero_of_two_reductions` is pure group theory and is proved here: if a point `P`
of an additive group has images of orders `m₁` and `m₂` under two homomorphisms whose kernels
contain only `p₁`-power, respectively `p₂`-power, torsion, with `p₁ ≠ p₂`, `p₁ ∤ m₂`, `p₂ ∤ m₁`
and `m₁ ≠ m₂`, then `P` has infinite order.

`Reduction` is a **hypothesis package**, not a construction.  It lists the properties of
reduction modulo a prime of good reduction that are used downstream:

* `red` is a group homomorphism `W(K) → W'(𝔽_p)` (Silverman, *The Arithmetic of Elliptic
  Curves*, VII.2.1, with `E₀ = E` for good reduction);
* `red_some`: on a point with coordinates in the ring `A`, it reduces the coordinates;
* `ker_torsion`: a point of finite order in the kernel has `p`-power order (VII.3.1(a)).

Mathlib (v4.36.0) has the reduction of the curve but not the reduction map on points, so these
properties are assumed wherever a `Reduction` appears as an argument.
-/

namespace Tower.EC

open WeierstrassCurve.Affine

/-- If torsion in the kernel of `r` is `p`-primary, then the order of a torsion point is the
order of its image times a power of `p`. -/
theorem addOrderOf_eq_mul_pow_of_reduction {A B : Type*} [AddMonoid A] [AddMonoid B]
    (r : A →+ B) {p : ℕ}
    (hk : ∀ Q : A, r Q = 0 → addOrderOf Q ≠ 0 → ∃ k : ℕ, addOrderOf Q = p ^ k)
    (P : A) (hn : addOrderOf P ≠ 0) :
    ∃ k : ℕ, addOrderOf P = addOrderOf (r P) * p ^ k := by
  have hdvd : addOrderOf (r P) ∣ addOrderOf P := addOrderOf_map_dvd r P
  have hm0 : addOrderOf (r P) ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hdvd
    exact hn hdvd
  have hQ : r (addOrderOf (r P) • P) = 0 := by
    rw [map_nsmul]
    exact addOrderOf_nsmul_eq_zero (r P)
  have hord : addOrderOf (addOrderOf (r P) • P) = addOrderOf P / addOrderOf (r P) :=
    addOrderOf_nsmul_of_dvd hm0 hdvd
  have hpos : 0 < addOrderOf P / addOrderOf (r P) :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hm0)
  have hne : addOrderOf (addOrderOf (r P) • P) ≠ 0 := by
    rw [hord]
    exact hpos.ne'
  obtain ⟨k, hk'⟩ := hk _ hQ hne
  refine ⟨k, ?_⟩
  rw [← hk', hord, Nat.mul_div_cancel' hdvd]

/-- Two reductions that disagree on the order of the image force infinite order. -/
theorem addOrderOf_eq_zero_of_two_reductions {A B₁ B₂ : Type*}
    [AddMonoid A] [AddMonoid B₁] [AddMonoid B₂]
    (r₁ : A →+ B₁) (r₂ : A →+ B₂) {p₁ p₂ : ℕ}
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂)
    (hk₁ : ∀ Q : A, r₁ Q = 0 → addOrderOf Q ≠ 0 → ∃ k : ℕ, addOrderOf Q = p₁ ^ k)
    (hk₂ : ∀ Q : A, r₂ Q = 0 → addOrderOf Q ≠ 0 → ∃ k : ℕ, addOrderOf Q = p₂ ^ k)
    (P : A) {m₁ m₂ : ℕ}
    (h₁ : addOrderOf (r₁ P) = m₁) (h₂ : addOrderOf (r₂ P) = m₂)
    (hc₁ : ¬ p₁ ∣ m₂) (hc₂ : ¬ p₂ ∣ m₁) (hm : m₁ ≠ m₂) :
    addOrderOf P = 0 := by
  by_contra hn
  obtain ⟨a, ha⟩ := addOrderOf_eq_mul_pow_of_reduction r₁ hk₁ P hn
  obtain ⟨b, hb⟩ := addOrderOf_eq_mul_pow_of_reduction r₂ hk₂ P hn
  rw [h₁] at ha
  rw [h₂] at hb
  have ha0 : a = 0 := by
    by_contra h
    have hdvd : p₁ ∣ m₂ * p₂ ^ b := by
      rw [← hb, ha]
      exact Dvd.dvd.mul_left (dvd_pow_self p₁ h) m₁
    rcases (Nat.Prime.dvd_mul hp₁).mp hdvd with h' | h'
    · exact hc₁ h'
    · exact hne ((Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp (hp₁.dvd_of_dvd_pow h'))
  have hb0 : b = 0 := by
    by_contra h
    have hdvd : p₂ ∣ m₁ * p₁ ^ a := by
      rw [← ha, hb]
      exact Dvd.dvd.mul_left (dvd_pow_self p₂ h) m₂
    rcases (Nat.Prime.dvd_mul hp₂).mp hdvd with h' | h'
    · exact hc₂ h'
    · exact hne ((Nat.prime_dvd_prime_iff_eq hp₂ hp₁).mp (hp₂.dvd_of_dvd_pow h')).symm
  rw [ha0, pow_zero, mul_one] at ha
  rw [hb0, pow_zero, mul_one] at hb
  exact hm (ha.symm.trans hb)

/-- **Hypothesis package** for reduction modulo a prime of good reduction.  `K` is the field of
definition, `A` a ring of elements that are integral at the prime (with `ι : A → K`), `W` the
curve over `K` and `W'` the reduced curve over `𝔽_p`.  Nothing here is constructed: a term of
this type is an assumption that such a reduction map exists. -/
structure Reduction {K A : Type*} [Field K] [DecidableEq K] [CommRing A] (ι : A →+* K)
    (W : WeierstrassCurve.Affine K) (p : ℕ) [Fact p.Prime]
    (W' : WeierstrassCurve.Affine (ZMod p)) where
  /-- the residue map on integral elements -/
  res : A →+* ZMod p
  /-- reduction of points -/
  red : W.Point →+ W'.Point
  /-- on a point with integral coordinates, reduction reduces the coordinates -/
  red_some : ∀ (x y : A) (h : W.Nonsingular (ι x) (ι y)) (x' y' : ZMod p)
      (h' : W'.Nonsingular x' y'), res x = x' → res y = y' →
      red (Point.some (ι x) (ι y) h) = Point.some x' y' h'
  /-- a point of finite order in the kernel of reduction has `p`-power order -/
  ker_torsion : ∀ Q : W.Point, red Q = 0 → addOrderOf Q ≠ 0 → ∃ k : ℕ, addOrderOf Q = p ^ k

end Tower.EC
