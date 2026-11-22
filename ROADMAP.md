# Roadmap: a complete Lean proof of the six-step theorem

Target: `Tower.RV6.rv6 : mu6 = 648 / π ^ 6 * Lf5` with no hypotheses.

Today: `rv6_of_rungs` takes six hypotheses (the rungs of `Tower/RV6/Ladder.lean`).  One of them,
`RungC1`, is now a theorem (`Tower.RV6.rungC1`).  This file is the plan for removing the others
and is updated with every wave.  "Proved" means: in this repository, kernel-checked, no
hypotheses.

## Architecture

The modular side is done with a weight-four form given by divisor sums, not with the eta product,
and every integral is taken at the cusp where it converges absolutely.  Nothing is regularised
and nothing is continued analytically.

`𝔈 = Σ σ₁(n) qⁿ`,  `𝔉 = 𝔈(τ) - 2𝔈(2τ) - 27𝔈(3τ) + 54𝔈(6τ) = Σ F_n qⁿ`,

`psiW(n) = -(11/54) σ₃(n) - (22/27) σ₃(n/2) + (63/2) σ₃(n/3) + 126 σ₃(n/6) + (65/54) F_n - (5/9) Σ_{i+j=n} F_i F_j`

(`σ_k(n/m) = 0` unless `m ∣ n`).  The identity `psiW(n) = a(n)`, the coefficients of
`(η(τ) η(2τ) η(3τ) η(6τ))²`, is isolated as one statement about integer sequences, rung `E″`.

| rung | statement | status |
|---|---|---|
| A1 | `μ₆ = log 2 + ∫ (e^{-t} - J₀⁶) dt/t` | open |
| A2 | that side `= (30/π⁴) R₆,₂` | open; two algebraic steps proved (`BesselAlgebra.lean`) |
| B  | `D₀₁ = (8/π⁵) R₆,₂ + (12/(5π⁵)) ζ(5)` | open |
| C1 | `D₀₁ = -(104/(27π³)) ζ(5) + (64/9)(J₁/(2π) + J₂/(4π²))` | **proved** (`rungC1`, wave 5) |
| C2″ | `(64/9)(J₁/(2π) + J₂/(4π²)) = (104/(27π³) + 12/(5π⁵)) ζ(5) + (1152/(5π²)) Λ(Ψ^W, 5)` | open (next) |
| D″ | `Λ(Ψ^W, 5) = (3/(4π⁵)) Σ psiW(n)/n⁵` | open (next); the same statement for an earlier form is proved (`lambdaPsi5_eq`) |
| E″ | `a(n) = psiW(n)` for all `n` | open |

## Proved so far

| wave | files | content |
|---|---|---|
| 1 | `MellinSeries`, `Psi` | termwise Mellin transform of a `q`-series; `σ₁(n) ≤ 4 n^{5/4}`; rung D′ |
| 2 | `EisAxis` | `E₄(i/y) = y⁴ E₄(iy)`, `E₂(i/y) = -y² E₂(iy) + 6y/π` from Mathlib's Eisenstein series |
| 3 | `QSeries`, `Regroup`, `Arith`, `Dirichlet`, `Fricke6` | `q`-series calculus on the imaginary axis; regrouping a double series by the product of its indices; `Σ_{mn=N} σ₃(m)σ₃(n) n = Σ_{mn=N} σ₁(m)σ₁(n) n³`; `Σ σ₃(n)/n⁵ = (π²/6) ζ(5)`, `Σ σ₁(n)/n⁵ = (π⁴/90) ζ(5)`; the Fricke relations of `g₄` and `𝔊` |
| 4 | `PhiKernel`, `Interchange` | the interchange of Lemma 5.1 of the paper (Tonelli, regrouping, the arithmetic identity) |
| 5 | `Eichler`, `Eichler2`, `Bilin`, `RungC1`, `C4` | the partial Eichler integral `T(a) = ∫_a^∞ t S₃(t) dt` and its inversion formula; the two forms of `𝒜₁`; `∫ x² T = ζ(5)/(24π³)`; the Fricke split; `c₄(n)` as divisor sums; **rung C1** |

## Plan by rung

**C2″.**  Substitute `y → 1/(6y)` in `J₁`, `J₂`; with `𝔊(i/(6y)) = -(1 - 26y² + 24y² 𝔉(iy))/36`
(`Gcal_fricke`) and its derivative,
`(D𝔊)(i/(6y)) = (13/(3π)) y³ - (4/π) y³ 𝔉(iy) + 4 y⁴ (D𝔉)(iy)`,
both become integrals at the cusp `∞`:
`J₂ = 156 L₅(𝔉) - 144 L₅(𝔉²)`, `J₁ = (156/π) L₅(𝔉) + (36/π) L₅(𝔉²)`, `L₅(h) = ∫₀^∞ h(iy) y⁴ dy`,
using `∫ y² 𝔉 = 0`, `L₅(𝔉) = ζ(5)/(144π)` and `∫ y⁵ 𝔉 D𝔉 = (5/(4π)) L₅(𝔉²)` (coefficients of
`𝔉 · D𝔉` are `(n/2)(F∗F)_n`).  By definition of `psiW`,
`Λ(Ψ^W, 5) = -ζ(5)/(96π³) + (65/54) L₅(𝔉) - (5/9) L₅(𝔉²)`, and `L₅(𝔉²)` cancels.
Needed: termwise differentiation of a `q`-series (Mathlib: `hasDerivAt_tsum_of_isPreconnected`),
integrability of `qa C y · y^k` from the summability of `Σ |C(n)|/n^{k+1}`, the Cauchy product
(`qa_mul`).

**D″.**  `integral_qa` with `|psiW(n)| ≤ C n^{7/2}`; the bound is the one of `Psi.lean` with `F` in
place of `g`.

**E″.**  Both sides are in `M₄(Γ₀(6))`; agreement through `q⁴` plus a Sturm bound.  Mathlib has
the norm to level one and the level-one valence results; the eta quotient needs exact invariance
under `Γ₀(6)`.  Alternatively through the pentagonal number theorem (in Mathlib) and theta-series
identities.

**A1.**  `J₀` as the characteristic function of a uniform step; `log r = ∫ (J₀(t) - J₀(rt)) dt/t`;
exchange with the expectation; `|J₀(t)| ≤ C t^{-1/2}`.

**A2.**  `I₀' = I₁`, `K₀' = -K₁`, the Wronskian; Lemma 2.1; Hankel functions and the rotation of
`∫ J₀⁶ t^{s-1} dt`; the Mellin expansions (2.6).

**B.**  Lemma 3.1 (Mellin–Parseval and one contour shift) and Zhou's parametrisations (4.4) of
the Hankel transforms of `I₀K₀³` and `(I₀K₀)²`.  The largest item by far; to be split when reached.

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
