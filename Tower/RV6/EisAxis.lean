import Mathlib
import Tower.RV6.Psi

/-!
# Eisenstein series on the imaginary axis

Mathlib's level-one Eisenstein series enter the real-variable arguments through two facts:

* `E4im_inv`: `E₄(i/y) = y⁴ E₄(iy)`, as an identity between real series;
* (to follow) `E₂(i/y) = -y² E₂(iy) + 6y/π`.

`E4im y = 1 + 240 ∑ σ₃(n) e^{-2πny}` is shown to be the value of Mathlib's `E₄` at `iy`
(`E4_axis`), and the inversion formula is the modularity of `E₄` under `z ↦ -1/z`.
-/

namespace Tower.RV6

open scoped MatrixGroups
open UpperHalfPlane hiding I

/-- `f(S z) = z^k f(z)` for a slash-invariant form on the full modular group. -/
theorem slash_S {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} [SlashInvariantFormClass F 𝒮ℒ k] (f : F)
    (z : ℍ) : f (ModularGroup.S • z) = (z : ℂ) ^ k * f z := by
  have : SlashInvariantFormClass F (CongruenceSubgroup.Gamma 1) k :=
    CongruenceSubgroup.Gamma_one_coe_eq_SL ▸ ‹_›
  have h := SlashInvariantForm.slash_action_eqn_SL'' f
    (CongruenceSubgroup.mem_Gamma_one ModularGroup.S) z
  rwa [ModularGroup.denom_S] at h

/-- `E₄(iy) = 1 + 240 ∑ σ₃(n) e^{-2πny}`. -/
noncomputable def E4im (y : ℝ) : ℝ :=
  1 + 240 * ∑' n : ℕ, sig 3 (n + 1) * Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y))

theorem cexp_axis (z : ℍ) {y : ℝ} (hz : (z : ℂ) = Complex.I * y) :
    Complex.exp (2 * Real.pi * Complex.I * z) = ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ) := by
  rw [hz, Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * (y : ℂ)) * Complex.I_mul_I

theorem tsum_pnat_sigma_axis (k : ℕ) (q : ℝ) :
    ∑' n : ℕ+, ((ArithmeticFunction.sigma k n : ℕ) : ℂ) * ((q : ℝ) : ℂ) ^ ((n : ℕ) : ℤ)
      = ((∑' n : ℕ, sig k (n + 1) * q ^ (n + 1) : ℝ) : ℂ) := by
  rw [tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => ((ArithmeticFunction.sigma k n : ℕ) : ℂ) * ((q : ℝ) : ℂ) ^ ((n : ℕ) : ℤ)),
    Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [zpow_natCast]
  simp [sig, ArithmeticFunction.sigma_apply]

theorem exp_pow_axis (y : ℝ) (n : ℕ) :
    Real.exp (-(2 * Real.pi * y)) ^ (n + 1)
      = Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Mathlib's `E₄` at `z = iy` is `E4im y`. -/
theorem E4_axis (z : ℍ) {y : ℝ} (hz : (z : ℂ) = Complex.I * y) :
    ModularForm.E₄ z = ((E4im y : ℝ) : ℂ) := by
  have h := EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) (by decide) z
  have hb : bernoulli 4 = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
  rw [cexp_axis z hz, hb] at h
  erw [tsum_pnat_sigma_axis 3 (Real.exp (-(2 * Real.pi * y)))] at h
  simp only [exp_pow_axis] at h
  refine h.trans ?_
  unfold E4im
  push_cast
  ring

/-- `E₄(i/y) = y⁴ E₄(iy)`. -/
theorem E4im_inv {y : ℝ} (hy : 0 < y) : E4im (1 / y) = y ^ 4 * E4im y := by
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have him : 0 < (Complex.I * (y : ℂ)).im := by simpa using hy
  have hz : ((UpperHalfPlane.mk (Complex.I * y) him : ℍ) : ℂ) = Complex.I * y :=
    UpperHalfPlane.coe_mk _ _
  have hS : ((ModularGroup.S • UpperHalfPlane.mk (Complex.I * y) him : ℍ) : ℂ)
      = Complex.I * ((1 / y : ℝ) : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, hz]
    have hyy : (y : ℂ) * (1 / (y : ℂ)) = 1 := mul_one_div_cancel hyc
    have e : -(Complex.I * (y : ℂ)) * (Complex.I * (1 / (y : ℂ))) = 1 := by
      linear_combination (-((y : ℂ) * (1 / (y : ℂ)))) * Complex.I_mul_I + hyy
    rw [inv_eq_of_mul_eq_one_right e, Complex.ofReal_div, Complex.ofReal_one]
  have h := slash_S ModularForm.E₄ (UpperHalfPlane.mk (Complex.I * y) him)
  rw [E4_axis _ hS, E4_axis _ hz, hz] at h
  have h4 : (Complex.I * (y : ℂ)) ^ (4 : ℤ) = ((y ^ 4 : ℝ) : ℂ) := by
    rw [zpow_ofNat, mul_pow, Complex.I_pow_four, one_mul, Complex.ofReal_pow]
  rw [h4, ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

/-! ## `E₂` -/

/-- A point `z = iy` of the upper half plane together with `S z = i/y`. -/
theorem axis_point {y : ℝ} (hy : 0 < y) :
    ∃ z : ℍ, (z : ℂ) = Complex.I * y ∧
      ((ModularGroup.S • z : ℍ) : ℂ) = Complex.I * ((1 / y : ℝ) : ℂ) := by
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have him : 0 < (Complex.I * (y : ℂ)).im := by simpa using hy
  have hz : ((UpperHalfPlane.mk (Complex.I * y) him : ℍ) : ℂ) = Complex.I * y :=
    UpperHalfPlane.coe_mk _ _
  have hS : ((ModularGroup.S • UpperHalfPlane.mk (Complex.I * y) him : ℍ) : ℂ)
      = Complex.I * ((1 / y : ℝ) : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, hz]
    have hyy : (y : ℂ) * (1 / (y : ℂ)) = 1 := mul_one_div_cancel hyc
    have e : -(Complex.I * (y : ℂ)) * (Complex.I * (1 / (y : ℂ))) = 1 := by
      linear_combination (-((y : ℂ) * (1 / (y : ℂ)))) * Complex.I_mul_I + hyy
    rw [inv_eq_of_mul_eq_one_right e, Complex.ofReal_div, Complex.ofReal_one]
  exact ⟨UpperHalfPlane.mk (Complex.I * y) him, hz, hS⟩

/-- `E₂(iy) = 1 - 24 ∑ σ₁(n) e^{-2πny}`. -/
noncomputable def E2im (y : ℝ) : ℝ :=
  1 - 24 * ∑' n : ℕ, sig 1 (n + 1) * Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y))

theorem tsum_pnat_sigma_axis' (k : ℕ) (q : ℝ) :
    ∑' n : ℕ+, ((ArithmeticFunction.sigma k n : ℕ) : ℂ) * ((q : ℝ) : ℂ) ^ (n : ℕ)
      = ((∑' n : ℕ, sig k (n + 1) * q ^ (n + 1) : ℝ) : ℂ) := by
  rw [tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => ((ArithmeticFunction.sigma k n : ℕ) : ℂ) * ((q : ℝ) : ℂ) ^ n),
    Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  simp [sig, ArithmeticFunction.sigma_apply]

/-- Mathlib's `E₂` at `z = iy` is `E2im y`. -/
theorem E2_axis (z : ℍ) {y : ℝ} (hz : (z : ℂ) = Complex.I * y) :
    EisensteinSeries.E2 z = ((E2im y : ℝ) : ℂ) := by
  have h := EisensteinSeries.E2_eq_tsum_cexp z
  rw [cexp_axis z hz] at h
  erw [tsum_pnat_sigma_axis' 1 (Real.exp (-(2 * Real.pi * y)))] at h
  simp only [exp_pow_axis] at h
  rw [h]
  unfold E2im
  rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]

/-- `E₂(-1/z) = z² E₂(z) - 6iz/π`. -/
theorem E2_S (z : ℍ) : EisensteinSeries.E2 (ModularGroup.S • z)
    = (z : ℂ) ^ 2 * EisensteinSeries.E2 z - 6 * Complex.I * z / Real.pi := by
  have h := EisensteinSeries.G2_S_transform z
  have hu : (z : ℂ) * (z : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (UpperHalfPlane.ne_zero z)
  have hp : (Real.pi : ℂ) * (Real.pi : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast Real.pi_ne_zero)
  have h' : EisensteinSeries.G2 (ModularGroup.S • z)
      = (z : ℂ) ^ 2 * EisensteinSeries.G2 z - 2 * Real.pi * Complex.I * z := by
    linear_combination (-((z : ℂ) ^ 2)) * h
      + (-(EisensteinSeries.G2 (ModularGroup.S • z) * ((z : ℂ) * (z : ℂ)⁻¹ + 1))
          - 2 * Real.pi * Complex.I * z) * hu
  show (1 / (2 * riemannZeta 2)) * EisensteinSeries.G2 (ModularGroup.S • z)
    = (z : ℂ) ^ 2 * ((1 / (2 * riemannZeta 2)) * EisensteinSeries.G2 z)
      - 6 * Complex.I * z / Real.pi
  rw [riemannZeta_two]
  linear_combination (1 / (2 * ((Real.pi : ℂ) ^ 2 / 6))) * h'
    + (-(6 * Complex.I * z * (Real.pi : ℂ)⁻¹)) * hp

/-- `E₂(i/y) = -y² E₂(iy) + 6y/π`. -/
theorem E2im_inv {y : ℝ} (hy : 0 < y) :
    E2im (1 / y) = -(y ^ 2) * E2im y + 6 * y / Real.pi := by
  obtain ⟨z, hz, hS⟩ := axis_point hy
  have h := E2_S z
  rw [E2_axis _ hS, E2_axis _ hz, hz] at h
  have e : (Complex.I * (y : ℂ)) ^ 2 * ((E2im y : ℝ) : ℂ)
        - 6 * Complex.I * (Complex.I * (y : ℂ)) / (Real.pi : ℂ)
      = ((-(y ^ 2) * E2im y + 6 * y / Real.pi : ℝ) : ℂ) := by
    push_cast
    linear_combination ((y : ℂ) ^ 2 * ((E2im y : ℝ) : ℂ) - 6 * (y : ℂ) / (Real.pi : ℂ))
      * Complex.I_mul_I
  rw [e] at h
  exact Complex.ofReal_injective h

end Tower.RV6
