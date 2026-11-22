import Mathlib

/-!
# Two algebraic pieces of the Bessel side

* `sixteen_mul_pow_six`: the identity `J⁶ = (3/16) J c₅ - (15/16) J² c₄ + (5/4) J³ c₃` with
  `c_j = (H⁺)^j + (H⁻)^j` and `H⁺ + H⁻ = 2J`, cleared of denominators.  With `J = J₀`,
  `H^± = J₀ ± i Y₀` it is the starting point of the rotation of `∫ J₀⁶ t^{s-1} dt` to
  integrals of products of `I₀` and `K₀`.
* `hasDerivAt_pow_mul_pow_of_wronskian`: with `u' = u₁`, `v' = -k₁` and the Wronskian relation
  `u k₁ + u₁ v = 1/t` (for `u = I₀`, `u₁ = I₁`, `v = K₀`, `k₁ = K₁`),
  `(u^{a+1} v^{p+1})' = (a + p + 2) u^a u₁ v^{p+1} - (p + 1) u^a v^p / t`.
  Integrated, this turns the regularised moment `FP ∫ I₀^a K₀^p dt/t` into the convergent
  integral `((a + p + 2)/(p + 1)) ∫ I₀^a I₁ K₀^{p+1} dt`.
-/

namespace Tower.RV6

theorem sixteen_mul_pow_six {R : Type*} [CommRing R] {J Hp Hm : R} (h : Hp + Hm = 2 * J) :
    16 * J ^ 6 = 3 * J * (Hp ^ 5 + Hm ^ 5) - 15 * J ^ 2 * (Hp ^ 4 + Hm ^ 4)
      + 20 * J ^ 3 * (Hp ^ 3 + Hm ^ 3) := by
  have hm : Hm = 2 * J - Hp := by linear_combination h
  subst hm
  ring

theorem hasDerivAt_pow_mul_pow_of_wronskian {u v : ℝ → ℝ} {u1 k1 t : ℝ} (a p : ℕ)
    (hu : HasDerivAt u u1 t) (hv : HasDerivAt v (-k1) t)
    (hW : u t * k1 + u1 * v t = 1 / t) :
    HasDerivAt (fun s => u s ^ (a + 1) * v s ^ (p + 1))
      (((a : ℝ) + p + 2) * u t ^ a * u1 * v t ^ (p + 1)
        - ((p : ℝ) + 1) * u t ^ a * v t ^ p / t) t := by
  have h3 := (hu.pow (a + 1)).mul (hv.pow (p + 1))
  refine h3.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have e : ((p : ℝ) + 1) * u t ^ a * v t ^ p / t
      = ((p : ℝ) + 1) * u t ^ a * v t ^ p * (1 / t) := by ring
  rw [e, ← hW]
  ring

end Tower.RV6
