# Roadmap: a complete Lean proof of the six-step theorem

Target: `Tower.RV6.rv6 : mu6 = 648 / π ^ 6 * Lf5` with no hypotheses.

Today: the modular side is proved.  `Tower.RV6.rv6_psiW_of_bessel` takes the three Bessel-side
rungs (`RungA1`, `RungA2`, `RungB`) and gives `μ₆ = (648/π⁶) Σ psiW(n)/n⁵` with explicit
divisor-sum coefficients; `rv6_of_bessel_and_E` adds the identity of coefficients `RungEW` and
gives the statement with the eta product.  This file is the plan for removing the four
hypotheses that are left and is updated with every wave.  "Proved" means: in this repository,
kernel-checked, no hypotheses.

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
| C2″ | `(64/9)(J₁/(2π) + J₂/(4π²)) = (104/(27π³) + 12/(5π⁵)) ζ(5) + (1152/(5π²)) Λ(Ψ^W, 5)` | **proved** (`rungC2W`, wave 6) |
| D″ | `Λ(Ψ^W, 5) = (3/(4π⁵)) Σ psiW(n)/n⁵` | **proved** (`lambdaPsiW5_eq`, wave 6) |
| E″ | `a(n) = psiW(n)` for all `n` | open (next); true for `n ≤ 60` in exact arithmetic |

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

## Plan by rung

**E″.**  By power series, without the valence formula at level six.  Write
`x_d = E₂(q^d)`, `u_d = E₄(q^d)`, `v_d = E₆(q^d)` (`d ∣ 6`) as formal power series with their
divisor-sum coefficients, and `θ = q d/dq`.

1. Ramanujan's identities `12 θx = x² - u`, `3 θu = xu - v`, `2 θv = xv - u²` are in Mathlib as
   identities of functions on the upper half plane (`RamanujanFormula.lean`).  Restricted to the
   imaginary axis they are identities between the real `q`-series of `QSeries.lean`, hence between
   coefficients; applying `X ↦ X^d` (`PowerSeries.expand`) gives them for `x_d, u_d, v_d`.
2. Nine relations hold among the twelve series: `ρ(x) = 0` (one quadratic relation among the
   `x_d`), `u_d = U_d(x)` (four), `v_d = V_d(x)` (four).  The vector `R` of the nine differences
   satisfies `θR = M R` with a matrix `M` of polynomials (nine polynomial identities, checked by
   `ring`).  At `q = 0` the matrix has eigenvalues `0, 2, 3, 6`, so `R = 0` as soon as its
   coefficients vanish through `q⁶`: for `n ≥ 7`, `n - M(0)` is invertible.
3. With the nine relations, `θG = P G` for `G = Σ psiW(n) qⁿ`, `P = (1/12) Σ_{d ∣ 6} d x_d`: one more
   polynomial identity.  The eta product satisfies the same equation (logarithmic derivative of
   the product, in `ℤ⟦X⟧`), and the equation determines the coefficients from the first one.

**A1.****A1.**  `J₀` as the characteristic function of a uniform step; `log r = ∫ (J₀(t) - J₀(rt)) dt/t`;
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
* An explicit lambda given as an argument leaves `(fun n => …) k` in the type of the result.
  A typed `have` absorbs it (the check is up to beta); `rw` finds the instance through it.
* Integrability of an integrand whose integral is known and non-zero is
  `Integrable.of_integral_ne_zero`; for an integrand that agrees with an integrable one on the
  domain, `IntegrableOn.congr_fun`.
