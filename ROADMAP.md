# Roadmap: a complete Lean proof of the six-step theorem

Target: `Tower.RV6.rv6 : mu6 = 648 / π ^ 6 * Lf5` with no hypotheses.

Today: the modular side is proved, including the identification with the eta product.
`Tower.RV6.rv6_of_bessel` takes the three Bessel-side rungs (`RungA1`, `RungA2`, `RungB`) and
gives `μ₆ = (648/π⁶) L(f, 5)`.  This file is the plan for removing the three hypotheses that
are left and is updated with every wave.  "Proved" means: in this repository,
kernel-checked, no hypotheses.

## Architecture

The modular side is done with a weight-four form given by divisor sums, not with the eta product,
and every integral is taken at the cusp where it converges absolutely.  Nothing is regularised
and nothing is continued analytically.

`𝔈 = Σ σ₁(n) qⁿ`,  `𝔉 = 𝔈(τ) - 2𝔈(2τ) - 27𝔈(3τ) + 54𝔈(6τ) = Σ F_n qⁿ`,

`psiW(n) = -(11/54) σ₃(n) - (22/27) σ₃(n/2) + (63/2) σ₃(n/3) + 126 σ₃(n/6) + (65/54) F_n - (5/9) Σ_{i+j=n} F_i F_j`

(`σ_k(n/m) = 0` unless `m ∣ n`).  The identity `psiW(n) = a(n)`, the coefficients of
`(η(τ) η(2τ) η(3τ) η(6τ))²`, is one statement about sequences, rung `E″`, proved in `ℝ⟦X⟧`.

| rung | statement | status |
|---|---|---|
| A1 | `μ₆ = log 2 + ∫ (e^{-t} - J₀⁶) dt/t` | open |
| A2 | that side `= (30/π⁴) R₆,₂` | open; two algebraic steps (`BesselAlgebra.lean`) and the Wronskian (`BesselW.lean`) proved; `R₆,₂` is a convergent positive integral (`BesselR.lean`) |
| B  | `D₀₁ = (8/π⁵) R₆,₂ + (12/(5π⁵)) ζ(5)` | open |
| C1 | `D₀₁ = -(104/(27π³)) ζ(5) + (64/9)(J₁/(2π) + J₂/(4π²))` | **proved** (`rungC1`, wave 5) |
| C2″ | `(64/9)(J₁/(2π) + J₂/(4π²)) = (104/(27π³) + 12/(5π⁵)) ζ(5) + (1152/(5π²)) Λ(Ψ^W, 5)` | **proved** (`rungC2W`, wave 6) |
| D″ | `Λ(Ψ^W, 5) = (3/(4π⁵)) Σ psiW(n)/n⁵` | **proved** (`lambdaPsiW5_eq`, wave 6) |
| E″ | `a(n) = psiW(n)` for all `n` | **proved** (`rungEW`, wave 7) |

C1 and C2″ together are `D01_eq_modular`:
`D₀₁ = (12/(5π⁵)) ζ(5) + (1152/(5π²)) ∫₀^∞ Ψ^W(iy) y⁴ dy`, with no hypotheses.

## Proved so far

| wave | files | content |
|---|---|---|
| 1 | `MellinSeries`, `Psi` | termwise Mellin transform of a `q`-series; `σ₁(n) ≤ 4 n^{5/4}`; rung D′ |
| 2 | `EisAxis` | `E₄(i/y) = y⁴ E₄(iy)`, `E₂(i/y) = -y² E₂(iy) + 6y/π` from Mathlib's Eisenstein series |
| 3 | `QSeries`, `Regroup`, `Arith`, `Dirichlet`, `Fricke6` | `q`-series calculus on the imaginary axis; regrouping a double series by the product of its indices; `Σ_{mn=N} σ₃(m)σ₃(n) n = Σ_{mn=N} σ₁(m)σ₁(n) n³`; `Σ σ₃(n)/n⁵ = (π²/6) ζ(5)`, `Σ σ₁(n)/n⁵ = (π⁴/90) ζ(5)`; the Fricke relations of `g₄` and `𝔊` |
| 4 | `PhiKernel`, `Interchange` | the interchange of Lemma 5.1 of the paper (Tonelli, regrouping, the arithmetic identity) |
| 5 | `Eichler`, `Eichler2`, `Bilin`, `RungC1`, `C4` | the partial Eichler integral `T(a) = ∫_a^∞ t S₃(t) dt` and its inversion formula; the two forms of `𝒜₁`; `∫ x² T = ζ(5)/(24π³)`; the Fricke split; `c₄(n)` as divisor sums; **rung C1** |
| 6 | `QCalc`, `DEInv`, `PsiW`, `RungC2`, `Ladder3` | termwise differentiation of a `q`-series, integrability of `qa C y · y^k`, the Cauchy product; the inversion formula of `D E₂`; the Fricke substitution in an integral; the moments of `𝔉` (`∫ 𝔉 y² = 0`, `∫ 𝔉 y⁴ = ζ(5)/(144π)`, `∫ 𝔉 D𝔉 y⁵ = (5/(4π)) ∫ 𝔉² y⁴`); **rungs C2″ and D″**; the ladder from the Bessel side |
| 7 | `Ser`, `Ramanujan`, `Level6`, `EtaRec` | `θ = X d/dX` on `ℝ⟦X⟧`; uniqueness of the coefficients of a `q`-series; `(2πi)⁻¹ d/dz` on the imaginary axis; Ramanujan's identities for `E₂, E₄, E₆` in `ℝ⟦X⟧` from Mathlib's; the nine relations at level 6 by a closed linear system under `θ`; the logarithmic derivative of the truncated eta product; **rung E″**; `rv6_of_bessel` |
| 8 | `BesselI`, `BesselK`, `BesselW`, `BesselR` | `I₀' = I₁`, `(t I₁)' = t I₀`; `K₁`, `K₀' = -K₁`, `(t K₁)' = -t K₀`; `e^{-t} ≤ t K₁ ≤ 1`; the Wronskian `I₀K₁ + I₁K₀ = 1/t`; `I₀ ≤ cosh`, `I₁ ≤ sinh`, `K₀ > 0`; `I₀ ≤ e^t` and `I₁K₀ ≤ 1/t` (from the Wronskian); `K₀(t) ≤ e^{-t}√(π/(2t))`, `K₀(t) ≤ log(1 + 2/t)`; **`I₀² I₁ K₀⁵` is integrable on `(0, ∞)` and `R₆,₂ > 0`** |

## Plan by rung

**E″.**  Done (wave 7), by power series and without the valence formula at level six:
Ramanujan's three identities at level one (Mathlib) restricted to the imaginary axis and read as
identities of coefficients; `X ↦ X^d`; nine relations among `E₂, E₄, E₆` at `X, X², X³, X⁶`, whose
differences satisfy `θR = M R` with `M(0)` having eigenvalues `0, 2, 3, 6` only; the first-order
equation `12 θG = (Σ_{d ∣ 6} d E₂(X^d)) G` for `G = Σ psiW(n) Xⁿ`; the same equation for the eta
product from its logarithmic derivative.

**Bessel calculus.**  Done (wave 8): the derivative formulas and the Wronskian for the functions
of `Defs.lean`; the bounds `I₀ ≤ e^t`, `I₁K₀ ≤ 1/t`, `K₀(t) ≤ e^{1-t} K₀(1)` (`t ≥ 1`),
`K₀(t) ≤ log(1 + 2/t)`; the integrability of `I₀² I₁ K₀⁵` on `(0, ∞)`.  `R₆,₂` of `Defs.lean` is a
convergent positive integral (a Bochner integral of a non-integrable function would be `0`).

**A1.**  In this order.  (1) `J₀' = -J₁` and `(t J₁)' = t J₀` from the series;
`J₀² + J₁² ≤ 1` on `t ≥ 0` (its derivative is `-2J₁²/t`); the energy
`E = t J₀² + t J₁² - J₀J₁ + J₀²/(2t)` of `√t J₀` has `E' = -J₀²/(2t²)`, so `J₀(t)² ≤ E(1)/t` for
`t ≥ 1`; the integrand of the walk side is integrable.  (2) `∫₀^∞ e^{-δt} J₀(at) dt = (δ² + a²)^{-1/2}`
from the two derivative formulas, hence `∫₀^∞ (e^{-t} - J₀(at)) dt/t = log a - log 2`.
(3) Bessel's integral `J₀(t) = ∫₀¹ cos(t cos 2πθ) dθ` (both sides solve the same first-order
system and the difference has non-increasing energy); the characteristic function of the
six-step walk; exchange with the expectation over the torus.  Real analysis only; several waves.

**A2.**  Lemma 2.1 (with the Wronskian, now available); Hankel functions `J₀ ± iY₀` in a half
plane and the rotation of `∫ J₀⁶ t^{s-1} dt`; the Mellin expansions (2.6).  Needs conditionally
convergent integrals handled by a damping factor; large.

**B.**  Lemma 3.1 (Mellin–Parseval and one contour shift), Proposition 3.2 (the Wronskian
identity), Lemma 4.1, and Zhou's parametrisations (4.4) of the Hankel transforms of `I₀K₀³` and
`(I₀K₀)²`, which the paper quotes and which would have to be proved here.  The largest item by
far; to be split into sub-rungs with convergent integrals when reached.

## Notes on compiling without a local Lean

Every compile is a CI run.  What has cost a run so far, so that it does not cost another:

* The body of `∫ x, …` and `∫ x in a..b, …` extends over `+` and `-`.  An integral that is followed
  by an operator is written in parentheses.  `∑` and `∑'` stop at `+`.
* A lemma whose conclusion contains a function variable applied to a non-variable (`C (n + 1)`,
  `f p.1 * g p.2`) is not given against an expected type: `have h := lemma …; exact h`.
* `|x|` and `‖x‖` on `ℝ` are rewritten into each other (`Real.norm_eq_abs`), never unfolded.
* `push_cast` pushes a cast `ℕ → ℤ` through a natural-number division; casts of such terms are
  pushed with an explicit list of lemmas.
* Algebraic steps are `linear_combination` with cofactors checked beforehand in exact rational
  arithmetic, with `x⁻¹` treated as an independent variable and `x * x⁻¹ = 1` as a hypothesis.
* An explicit lambda given as an argument leaves `(fun n => …) k` in the type of the result.
  A typed `have` absorbs it (the check is up to beta); `rw` finds the instance through it.
* Integrability of an integrand whose integral is known and non-zero is
  `Integrable.of_integral_ne_zero`; for an integrand that agrees with an integrable one on the
  domain, `IntegrableOn.congr_fun`.
* A lemma about a numeral that `simp` is to use is stated with `ofNat(n)` (Mathlib's
  `no_index (OfNat.ofNat n)`); stated with `OfNat.ofNat n` it is found by `rw` but not by `simp`.
* `exact_mod_cast` does not move a cast `ℝ → ℂ` across `12⁻¹ * ·`.  The cast equation is stated
  and proved by `push_cast`, then `Complex.ofReal_injective`.
* `unfold` reduces closed natural-number arithmetic (`0 / 2`); a following `rw [Nat.zero_div]`
  finds nothing.
* When a tactic may or may not close the goal (`push_cast`), the next one goes under `first`.
* `ring` does not identify `(1/2)^(2k)` with `(1/4)^k`: a numeral under a variable exponent is
  rewritten by `pow_mul` first.
* `IntegrableOn` is not unfolded by dot notation: `Integrable.const_mul h c`, not `h.const_mul c`.
* `rw` rewrites the first match in pre-order (the left-hand side of a relation before the right,
  a term before its subterms) and then every instance of that match; before a `rw [mul_one]` or
  `rw [neg_pow]` the first match is worked out by hand, or the lemma is given its arguments.
* `Continuous.mul`, `HasDerivAt.mul`, `Continuous.pow`, `HasDerivAt.div` are stated for `f * g`,
  `f ^ n`, `f / g` as functions; a typed `have` written with `fun x => f x * g x` accepts them.
