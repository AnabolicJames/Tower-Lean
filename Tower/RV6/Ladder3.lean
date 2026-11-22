import Mathlib
import Tower.RV6.Ladder
import Tower.RV6.Ladder2
import Tower.RV6.RungC1
import Tower.RV6.PsiW
import Tower.RV6.RungC2

/-!
# The six-step theorem from the Bessel side and one identity of coefficients

With rungs C1, C2″ and D″ proved, the modular side of the six-step theorem carries no hypotheses:

* **`D01_eq_modular`**: `D₀₁ = (12/(5π⁵)) ζ(5) + (1152/(5π²)) Λ(Ψ^W, 5)`.
* **`rv6_psiW_of_bessel`**: from the three Bessel-side rungs `RungA1`, `RungA2`, `RungB`,
  `μ₆ = (648/π⁶) ∑ psiW(n)/n⁵`, with `psiW` the explicit divisor-sum coefficients of `PsiW.lean`.
* `rv6_of_bessel_and_E`: with `RungEW` (`aCoeff n = psiW n` for all `n`, i.e. `Ψ^W` is the eta
  product) this is `μ₆ = (648/π⁶) L(f, 5)`.
-/

namespace Tower.RV6

open Real

/-- `Ψ^W` is the eta product `(η(τ) η(2τ) η(3τ) η(6τ))²`: equality of all coefficients. -/
def RungEW : Prop := ∀ n : ℕ, (aCoeff n : ℝ) = psiW n

/-- The modular-side evaluation of the double Eisenstein integral, with no hypotheses. -/
theorem D01_eq_modular :
    D01 = 12 / (5 * π ^ 5) * zeta5 + 1152 / (5 * π ^ 2) * LambdaPsiW5 := by
  have h1 := rungC1
  unfold RungC1 at h1
  have h2 := rungC2W
  linear_combination h1 + h2

/-- The six-step Mahler measure with the explicit divisor-sum coefficients, from the three
Bessel-side rungs. -/
theorem rv6_psiW_of_bessel (hA1 : RungA1) (hA2 : RungA2) (hB : RungB) :
    mu6 = 648 / π ^ 6 * LPsiW5 := by
  rw [mu6_eq_of_modular (rungA_of hA1 hA2) hB D01_eq_modular, lambdaPsiW5_eq]
  ring

/-- The six-step theorem with the eta product, from the three Bessel-side rungs and `RungEW`. -/
theorem rv6_of_bessel_and_E (hA1 : RungA1) (hA2 : RungA2) (hB : RungB) (hE : RungEW) :
    mu6 = 648 / π ^ 6 * Lf5 := by
  have h := rv6_psiW_of_bessel hA1 hA2 hB
  have hL : Lf5 = LPsiW5 := by
    unfold Lf5 LPsiW5
    exact tsum_congr (fun n => by rw [hE n])
  rw [hL]
  exact h

end Tower.RV6
