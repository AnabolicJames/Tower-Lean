import Mathlib
import Tower.RV6.RungA2R

/-!
# Rung B, the first cut: one pairing, two evaluations

After `RungA2R.lean` the six-step theorem has one hypothesis left,

`RungB : D₀₁ = (8/π⁵) R₆,₂ + (12/(5π⁵)) ζ(5)`.

This file cuts it into two statements about **one** function of a real variable `s > 0`.  With the
paper's `f = I₀ K₀³` and `g = I₀² K₀²` put

* `hjF x = ∫₀^∞ J₀(xt) f(t) t dt`   (the Hankel transform of `f`),
* `ajG x = x ∫₀^∞ J₁(xt) g(t) dt`   (the cumulative of the Hankel transform of `g`),
* `pairS s = ∫₀^∞ hjF(x) ajG(x) x^{1-s} dx`   (the pairing, with the power `x^{-s}` as regulator).

Both transforms are absolutely convergent integrals.  At infinity `hjF x · ajG x · x = 3 log⁴x / x`
up to `O(x⁻³ log⁴ x)`, so `pairS s` has the pole `72/s⁵ = 3 · 4!/s⁵` at `s = 0` and nothing else:

| sub-rung | statement | content |
|---|---|---|
| `RungBP` | `pairS s - 72/s⁵ → R₆,₂/2 + (3/20) ζ(5)` as `s → 0+` | the logarithmic Hankel pairing (paper: Lemma 3.1, Proposition 3.2) |
| `RungBM` | `pairS s - 72/s⁵ → (π⁵/16) D₀₁` as `s → 0+` | Zhou's parametrisations and the change of variable `x = x(y)` (paper: Section 4) |

A function has at most one limit, so the two together are `RungB` (`rungB_of_PM`), and with the
rest of the ladder the theorem (`rv6_of_PM`).  **`RungBP` and `RungBM` are hypotheses here.**

The same regulator on both sides is what makes the cut clean: on the modular side
`x(y)^{-s} = e^{-πs/(6y)} (1 + O(e^{-π/(3y)}))` and `∫₀^∞ y⁻⁶ e^{-πs/(6y)} dy / 162 = (16/π⁵) · 72/s⁵`
exactly, so no constant is lost in a change of cutoff.

Before being stated, both sub-rungs and every step of the plan for proving them were checked
numerically from these definitions (ledger: PREREG2 Addendum 130, 24 criteria, all met at the
first run; second producer Wolfram): at `s = 0` the pairing computed from the Bessel integrals
alone equals `R₆,₂/2 + (3/20) ζ(5) = (π⁵/16) D₀₁` to ten digits, and
`hjF(x(y)) = (π²/16) Z(iy)`, `ajG(x(y)) = (π²/2) 𝒜₁(y)` hold to twenty digits.

An integral of a non-integrable function is `0` in Lean.  If `pairS s` were not integrable for
small `s`, then `pairS s - 72/s⁵ = -72/s⁵` would have no finite limit: each sub-rung carries the
integrability of the pairing with it.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `f(t) = I₀(t) K₀(t)³`. -/
noncomputable def fB (t : ℝ) : ℝ := besselI0 t * besselK0 t ^ 3

/-- `g(t) = I₀(t)² K₀(t)²`. -/
noncomputable def gB (t : ℝ) : ℝ := besselI0 t ^ 2 * besselK0 t ^ 2

/-- `HJ[f](x) = ∫₀^∞ J₀(xt) f(t) t dt`. -/
noncomputable def hjF (x : ℝ) : ℝ := ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * fB t * t

/-- `AJ[g](x) = ∫₀^x HJ[g](ξ) ξ dξ = x ∫₀^∞ J₁(xt) g(t) dt`. -/
noncomputable def ajG (x : ℝ) : ℝ := x * ∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * gB t

/-- The pairing `∫₀^∞ HJ[f](x) AJ[g](x) x^{1-s} dx` (real power). -/
noncomputable def pairS (s : ℝ) : ℝ := ∫ x in Set.Ioi (0 : ℝ), hjF x * ajG x * x ^ (1 - s)

/-- **Sub-rung BP** (the logarithmic Hankel pairing):
`pairS s - 72/s⁵ → R₆,₂/2 + (3/20) ζ(5)` as `s → 0+`. -/
def RungBP : Prop :=
  Filter.Tendsto (fun s : ℝ => pairS s - 72 / s ^ 5) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds (R62 / 2 + 3 / 20 * zeta5))

/-- **Sub-rung BM** (the modular side of the same pairing):
`pairS s - 72/s⁵ → (π⁵/16) D₀₁` as `s → 0+`. -/
def RungBM : Prop :=
  Filter.Tendsto (fun s : ℝ => pairS s - 72 / s ^ 5) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds (π ^ 5 / 16 * D01))

/-- The two evaluations of the pairing give Rung B: a function has at most one limit. -/
theorem rungB_of_PM (hP : RungBP) (hM : RungBM) : RungB := by
  unfold RungBP at hP
  unfold RungBM at hM
  unfold RungB
  have h : π ^ 5 / 16 * D01 = R62 / 2 + 3 / 20 * zeta5 := tendsto_nhds_unique hM hP
  have hp5 : π ^ 5 * (π ^ 5)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 5 Real.pi_ne_zero)
  linear_combination (16 * (π ^ 5)⁻¹) * h - D01 * hp5

/-- **The six-step theorem from the two sub-rungs of Rung B.** -/
theorem rv6_of_PM (hP : RungBP) (hM : RungBM) : mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_B (rungB_of_PM hP hM)

end Tower.RV6
