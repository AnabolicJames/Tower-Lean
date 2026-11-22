import Mathlib
import Tower.RV6.Ladder
import Tower.RV6.Psi

/-!
# The ladder with the Eisenstein form `Ψ`

The rungs `RungC2` and `RungD` of `Ladder.lean` are replaced by

* `RungC2'`: the same evaluation with `Λ(Ψ, 5)` in place of `Λ(f, 5)`;
* rung D′, which is **proved** (`lambdaPsi5_eq` in `Psi.lean`);
* `RungE`: `aCoeff n = psiCoeff n` for all `n`, i.e. `Ψ` is the eta product.

`rv6_psi_of_rungs` is the six-step theorem with the explicit coefficients `psiCoeff`, from five
hypotheses; `rv6_of_rungs'` adds `RungE` and gives the statement with the eta product.
-/

namespace Tower.RV6

open Real

/-- The evaluation of the non-constant Fricke part, with the Eisenstein form `Ψ`. -/
def RungC2' : Prop :=
  crossTerm = 104 / (27 * π ^ 3) * zeta5 + 12 / (5 * π ^ 5) * zeta5
    + 1152 / (5 * π ^ 2) * LambdaPsi5

/-- `Ψ` is the eta product: equality of all coefficients (equation (6.8) of the paper). -/
def RungE : Prop := ∀ n : ℕ, (aCoeff n : ℝ) = psiCoeff n

theorem mu6_eq_of_modular (hA : RungA) (hB : RungB) {Λ : ℝ}
    (hC : D01 = 12 / (5 * π ^ 5) * zeta5 + 1152 / (5 * π ^ 2) * Λ) : mu6 = 864 / π * Λ := by
  unfold RungA at hA
  unfold RungB at hB
  have hp : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  linear_combination hA + (30 * π / 8) * (hC - hB)
    + (864 * Λ * π⁻¹ - 30 * R62 * π⁻¹ ^ 4) * hp

/-- The six-step theorem with the explicit Eisenstein coefficients, from five rungs. -/
theorem rv6_psi_of_rungs (hA1 : RungA1) (hA2 : RungA2) (hB : RungB) (hC1 : RungC1)
    (hC2 : RungC2') : mu6 = 648 / π ^ 6 * LPsi5 := by
  unfold RungC1 at hC1
  unfold RungC2' at hC2
  have hC : D01 = 12 / (5 * π ^ 5) * zeta5 + 1152 / (5 * π ^ 2) * LambdaPsi5 := by
    linear_combination hC1 + hC2
  rw [mu6_eq_of_modular (rungA_of hA1 hA2) hB hC, lambdaPsi5_eq]
  ring

/-- The six-step theorem with the eta product, from the five rungs and `RungE`. -/
theorem rv6_of_rungs' (hA1 : RungA1) (hA2 : RungA2) (hB : RungB) (hC1 : RungC1)
    (hC2 : RungC2') (hE : RungE) : mu6 = 648 / π ^ 6 * Lf5 := by
  have h := rv6_psi_of_rungs hA1 hA2 hB hC1 hC2
  have hL : Lf5 = LPsi5 := by
    unfold Lf5 LPsi5
    exact tsum_congr (fun n => by rw [hE n])
  rw [hL]
  exact h

end Tower.RV6
