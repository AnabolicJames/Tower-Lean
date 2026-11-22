import Mathlib
import Tower.RV6.Defs

/-!
# The six-step Mahler measure: the proof as a ladder of rungs

`rv6_of_rungs` derives

`m(1 + x₁ + ⋯ + x₅) = (648 / π⁶) · L(f, 5)`

from six named propositions, the *rungs*.  **A rung is a hypothesis.**  Nothing in this file
proves a rung; what is proved is that the rungs imply the theorem.  Each rung equates quantities
that are defined in `Tower/RV6/Defs.lean` as convergent integrals or series.  Before being stated
here each rung was checked numerically from those definitions: `RungA2`, `RungB`, `RungC1`,
`RungC2`, `RungD` by two independent programs to `10⁻¹²` or better, `RungA1` (a classical
representation) by Monte Carlo to four digits.

| rung | statement | where in the paper |
|---|---|---|
| `RungA1` | `μ₆ = log 2 + ∫₀^∞ (e^{-t} - J₀⁶) dt/t` | random-walk representation |
| `RungA2` | that integral side equals `(30/π⁴) R₆,₂` | Lemmas 2.1, 2.2 |
| `RungB`  | `D₀₁ = (8/π⁵) R₆,₂ + (12/(5π⁵)) ζ(5)` | (1.4), Bessel side |
| `RungC1` | `D₀₁ = -(104/(27π³)) ζ(5) + (64/9)(J₁/(2π) + J₂/(4π²))` | (5.4), Lemma 5.1 |
| `RungC2` | `(64/9)(J₁/(2π) + J₂/(4π²)) = (104/(27π³)) ζ(5) + (12/(5π⁵)) ζ(5) + (1152/(5π²)) Λ(f,5)` | Lemmas 6.1, 6.2 |
| `RungD`  | `Λ(f,5) = (3/(4π⁵)) L(f,5)` | Mellin transform of the cusp form |
-/

namespace Tower.RV6

open Real

/-- The random-walk representation of `μ₆`. -/
def RungA1 : Prop := mu6 = walkSide

/-- Rotation of the contour: the random-walk side is `(30/π⁴) R₆,₂`. -/
def RungA2 : Prop := walkSide = 30 / π ^ 4 * R62

/-- `μ₆ = (30/π⁴) R₆,₂`. -/
def RungA : Prop := mu6 = 30 / π ^ 4 * R62

/-- The Bessel-side evaluation of the double Eisenstein integral. -/
def RungB : Prop := D01 = 8 / π ^ 5 * R62 + 12 / (5 * π ^ 5) * zeta5

/-- The Fricke split of the double Eisenstein integral. -/
def RungC1 : Prop := D01 = -(104 / (27 * π ^ 3)) * zeta5 + crossTerm

/-- The evaluation of the non-constant Fricke part. -/
def RungC2 : Prop :=
  crossTerm = 104 / (27 * π ^ 3) * zeta5 + 12 / (5 * π ^ 5) * zeta5 + 1152 / (5 * π ^ 2) * Lambda5

/-- The modular-side evaluation of the double Eisenstein integral. -/
def RungC : Prop := D01 = 12 / (5 * π ^ 5) * zeta5 + 1152 / (5 * π ^ 2) * Lambda5

/-- The Mellin transform of the cusp form is its completed `L`-value:
`Λ(f, 5) = Γ(5) (2π)⁻⁵ L(f, 5)`. -/
def RungD : Prop := Lambda5 = 3 / (4 * π ^ 5) * Lf5

theorem rungA_of (h1 : RungA1) (h2 : RungA2) : RungA := by
  unfold RungA1 at h1
  unfold RungA2 at h2
  unfold RungA
  exact h1.trans h2

theorem rungC_of (h1 : RungC1) (h2 : RungC2) : RungC := by
  unfold RungC1 at h1
  unfold RungC2 at h2
  unfold RungC
  linear_combination h1 + h2

/-- The two evaluations of `D₀₁` cancel their `ζ(5)` terms: `μ₆ = (864/π) Λ(f, 5)`. -/
theorem mu6_eq_Lambda5 (hA : RungA) (hB : RungB) (hC : RungC) : mu6 = 864 / π * Lambda5 := by
  unfold RungA at hA
  unfold RungB at hB
  unfold RungC at hC
  have hp : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  linear_combination hA + (30 * π / 8) * (hC - hB)
    + (864 * Lambda5 * π⁻¹ - 30 * R62 * π⁻¹ ^ 4) * hp

/-- **The six-step Mahler measure, conditional on the rungs.**
`m(1 + x₁ + x₂ + x₃ + x₄ + x₅) = (648 / π⁶) L(f, 5)` follows from `RungA1`, `RungA2`, `RungB`,
`RungC1`, `RungC2`, `RungD`. -/
theorem rv6_of_rungs (hA1 : RungA1) (hA2 : RungA2) (hB : RungB) (hC1 : RungC1) (hC2 : RungC2)
    (hD : RungD) : mu6 = 648 / π ^ 6 * Lf5 := by
  have h := mu6_eq_Lambda5 (rungA_of hA1 hA2) hB (rungC_of hC1 hC2)
  unfold RungD at hD
  rw [h, hD]
  ring

end Tower.RV6
