# Roadmap: a complete Lean proof of the six-step theorem

Target: `Tower.RV6.rv6 : mu6 = 648 / π ^ 6 * Lf5` with no hypotheses.
Today: `rv6_of_rungs` (six hypotheses).  This file is the plan for removing them, and is
updated with every wave.  "Proved" means: in this repository, kernel-checked, no hypotheses.

## Architecture

The modular side is done with an explicit Eisenstein form instead of the eta product:

`Ψ = (5/144) (Σ_d e_d E₄(dτ) - F̂²)`,  `F̂ = (3/2)E₂(τ) - 3E₂(2τ) - (1/2)E₂(3τ) + E₂(6τ)`,
`(e₁, e₂, e₃, e₆) = (21/50, 42/25, -11/50, -22/25)`,

whose coefficients `psiCoeff n` are finite divisor sums.  The identity `Ψ = (η η₂ η₃ η₆)²`
(equation (6.8) of the paper) is isolated as one arithmetic statement, rung `E`.

| rung | statement | status |
|---|---|---|
| A1 | `μ₆ = log 2 + ∫ (e^{-t} - J₀⁶) dt/t` | open |
| A2 | that side `= (30/π⁴) R₆,₂` | open; two algebraic steps proved (`BesselAlgebra.lean`) |
| B  | `D₀₁ = (8/π⁵) R₆,₂ + (12/(5π⁵)) ζ(5)` | open |
| C1 | `D₀₁ = -(104/(27π³)) ζ(5) + crossTerm` | open; substitution identity and convergence proved (`Swap.lean`, `Lambert.lean`) |
| C2′ | `crossTerm = (104/(27π³) + 12/(5π⁵)) ζ(5) + (1152/(5π²)) Λ(Ψ, 5)` | open |
| D′ | `Λ(Ψ, 5) = (3/(4π⁵)) Σ psiCoeff(n)/n⁵` | wave 1 |
| E  | `aCoeff n = psiCoeff n` for all `n` | open |

## Plan by rung (everything on the imaginary axis; no analytic continuation is needed)

**D′.** `MellinSeries.lean`: `∫₀^∞ (Σ c(n) e^{-2πny}) y^k dy = k!/(2π)^{k+1} Σ c(n)/n^{k+1}` when
`Σ |c(n)|/n^{k+1}` converges.  `Psi.lean`: `σ₁(n) ≤ 4 n^{5/4}`, `|psiCoeff n| ≤ C n^{7/2}`.

**C1.** (a) Fricke formula `g₄(iy) = (6y)⁻⁴ ĝ₄(i/(6y))` from `E₄(i/y) = y⁴ E₄(iy)` (Mathlib:
level-one Eisenstein series and their q-expansions).  (b) `𝒜₁(y) - 1/(18y²)` is exponentially
small at `0`: the constant vanishes because `Σ α_d/d² = Σ α_d/d⁴ = 0` for the coefficients of
`ĝ₄`; real-variable proof by folding `(0, 1)` onto `(1, ∞)`.  (c) The constant part:
`∫ (9y⁴)⁻¹ (𝒜₁ - 1/(18y²)) dy = -(2/9) Λ(ĝ₄ - 144, 5) = -(104/(27π³)) ζ(5)`, a convergent
Dirichlet series with `ζ(2) = π²/6`.  (d) Lemma 5.1: Tonelli on the product of two Lambert series,
`Phi_swap`, and Mathlib's `tsum_prod_pow_eq_tsum_sigma` for the regrouping.

**C2′.** (a) `E₂(i/y) = y² E₂(iy)`-type formula with its extra term (Mathlib: `G2_S_transform`),
giving `𝔉(i/(6y)) = 13/12 - (3/2)y² - 54 y² 𝔊(iy)`.  (b) Regularised Mellin values as honest
integrals of `h - (polar part)`; `Λ(H, -3) = 36 ζ(5)/π` by Fricke duality and a convergent
Dirichlet series with `ζ(4)`; `Λ(H, -1) = 0`.  (c) `J₁`, `J₂` in terms of the regularised value
of `H²` at `-1` (finite-part integration by parts).  (d) `H² = (F̂² - 1) + 2H`, the Eisenstein part
at `-1` by duality, and the Fricke symmetry `Ψ(i/(6y)) = 36 y⁴ Ψ(iy)` for the cusp part.

**E.** Both sides are in `M₄(Γ₀(6))`; agreement through `q⁴` plus a Sturm bound.  Mathlib has the
norm to level one and the level-one valence results; the eta quotient needs exact invariance
under `Γ₀(6)` (via `Δ = η²⁴` and fixed points of the Atkin–Lehner involutions).  Alternatively
through the pentagonal number theorem (in Mathlib) and theta-series identities.

**A1.** `J₀` as the characteristic function of a uniform step; `log r = ∫ (J₀(t) - J₀(rt)) dt/t`;
exchange with the expectation; `|J₀(t)| ≤ C t^{-1/2}`.

**A2.** `I₀' = I₁`, `K₀' = -K₁`, the Wronskian; Lemma 2.1; Hankel functions and the rotation of
`∫ J₀⁶ t^{s-1} dt`; the Mellin expansions (2.6).

**B.** Lemma 3.1 (Mellin–Parseval and one contour shift) and Zhou's parametrisations (4.4) of
the Hankel transforms of `I₀K₀³` and `(I₀K₀)²`.  The largest item by far; to be split when reached.
