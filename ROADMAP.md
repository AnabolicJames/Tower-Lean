# Roadmap: a complete Lean proof of the six-step theorem

Target: `Tower.RV6.rv6 : mu6 = 648 / π ^ 6 * Lf5` with no hypotheses.

Today: the modular side is proved, including the identification with the eta product, and so is
the first rung of the Bessel side, the random-walk representation of `μ₆` (`rungA1`, wave 13).
`Tower.RV6.rv6_of_A2_B` takes the two rungs that are left (`RungA2`, `RungB`) and gives
`μ₆ = (648/π⁶) L(f, 5)`.  `RungA2` is cut into five sub-rungs about a real parameter `s > 0`
(wave 15), and four of the five are proved (waves 16 to 20).  **`Tower.RV6.rv6_of_A2R_B` takes
the two hypotheses that are left, `RungA2R` (the rotation of the contour) and `RungB`.**  This file is the plan for
removing these hypotheses and is updated with every wave.  "Proved" means: in this repository,
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
| A1 | `μ₆ = log 2 + ∫ (e^{-t} - J₀⁶) dt/t` | **proved** (`rungA1`, wave 13) |
| A2 | that side `= (30/π⁴) R₆,₂` | open; **reduced to five sub-rungs** (`rungA2_of_subrungs`, wave 15), four of them proved, table below |
| B  | `D₀₁ = (8/π⁵) R₆,₂ + (12/(5π⁵)) ζ(5)` | open |
| C1 | `D₀₁ = -(104/(27π³)) ζ(5) + (64/9)(J₁/(2π) + J₂/(4π²))` | **proved** (`rungC1`, wave 5) |
| C2″ | `(64/9)(J₁/(2π) + J₂/(4π²)) = (104/(27π³) + 12/(5π⁵)) ζ(5) + (1152/(5π²)) Λ(Ψ^W, 5)` | **proved** (`rungC2W`, wave 6) |
| D″ | `Λ(Ψ^W, 5) = (3/(4π⁵)) Σ psiW(n)/n⁵` | **proved** (`lambdaPsiW5_eq`, wave 6) |
| E″ | `a(n) = psiW(n)` for all `n` | **proved** (`rungEW`, wave 7) |

The sub-rungs of A2 (`LadderA2.lean`).  `mellU h s = ∫ h(e^u) e^{su} du` is the Mellin transform
`∫₀^∞ h(t) t^{s-1} dt` in the variable `u = log t`; `N = mellU J₀⁶`, `M_{a,b} = mellU (I₀^a K₀^b)`,
`P(s) = mellU (I₀² I₁ K₀⁵) (s + 1)`, `a₀ = log 2 + eulerW`, where `eulerW` is the constant of
`K₀(t) = -log(t/2) + eulerW + O(t)` (`KZero.lean`).

| sub-rung | statement | status |
|---|---|---|
| A2R | for `0 < s < 1`: `N(s) = (12/π⁵) sin(πs/2) M₁,₅(s) - (30/π⁴) cos(πs/2) M₂,₄(s) - (20/π³) sin(πs/2) M₃,₃(s)` | **open** (rotation of the contour; plan below) |
| A2N | `N(s) - 1/s → eulerW - (walkSide - log 2)` as `s → 0+` | **proved** (`rungA2N`, wave 20) |
| A2M | `e^{-a₀ s} M_{a,b}(s) - b!/s^{b+1}` bounded on `0 < s ≤ 1` for `(a,b) = (1,5), (3,3), (3,5)` | **proved** (`rungA2M`, wave 19) |
| A2P | for `0 < s ≤ 1`: `M₂,₄(s) = (8/5) P(s) + (s/5) M₃,₅(s)`; `(8/5) P(s) → R₆,₂` as `s → 0+` | **proved** (`rungA2P`, wave 18) |
| A2T | `(1440/π⁵) sin(πs/2)/s⁶ - (720/π⁴) cos(πs/2)/s⁵ - (120/π³) sin(πs/2)/s⁴ - 1/s → 0` as `s → 0+` | **proved** (`rungA2T`, wave 16) |

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
| 9 | `BesselJ` | `J₀' = -J₁`, `(t J₁)' = t J₀`, `J₁' = J₀ - J₁/t`; `J₀² + J₁² ≤ 1` on `t ≥ 0`; the energy `E = tJ₀² + tJ₁² - J₀J₁ + J₀²/(2t)` with `E' = -J₀²/(2t²)` and `J₀(t)² ≤ E(1)/t` for `t ≥ 1`; **the integrand of the walk side is integrable on `(0, ∞)`** |
| 10 | `Laplace`, `LogInt` | `lapl φ δ = ∫₀^∞ e^{-δt} φ(t) dt`: integrability, differentiation in `δ`, integration by parts; **`∫₀^∞ e^{-δt} J₀(at) dt = 1/√(a² + δ²)`** (from the two derivative formulas: `(a² + δ²) L' = -δ L`, so `(a² + δ²) L²` is constant); **`∫₀^∞ (e^{-t} - e^{-δt} J₀(at)) dt/t = log(δ + √(a² + δ²)) - log 2`** for `a ≥ 0`, `δ > 0` |
| 11 | `BesselInt` | **Bessel's integral** `J₀(x) = ∫₀¹ cos(x cos 2πθ) dθ`, `J₁(x) = ∫₀¹ sin(x cos 2πθ) cos 2πθ dθ` (`x ≥ 0`): both pairs solve `A' = -B`, `(xB)' = xA`, and a solution with zero data at `0` vanishes on `[0, ∞)` |
| 12 | `CharFun` | invariance of a period integral under shifts; `J₀(t‖z‖) = ∫₀¹ cos(t (Re z cos 2πθ - Im z sin 2πθ)) dθ`; Lebesgue measure on `[0,1]⁵` as a product measure; **the characteristic function of the walk**, `∫_{[0,1]⁵} J₀(t ‖1 + Σ e(τ_j)‖) dτ = J₀(t)⁶` |
| 13 | `CubeLog`, `RungA1` | the exchange `∫_{[0,1]⁵} log(δ + √(‖X‖² + δ²)) = log 2 + ∫₀^∞ (e^{-t} - e^{-δt} J₀⁶) dt/t` (Fubini on `cube × (0, ∞)`); the damping removed on the walk side (dominated convergence); `X ≠ 0` almost everywhere on the cube; a limit of an antitone sequence of integrable functions with integrals bounded below is integrable; **rung A1**; `rv6_of_A2_B` |

| 14 | `KZero` | `E(x) = ∫₀^∞ exp(-x e^u) du` with `E' = -e^{-x}/x`; `0 ≤ E(t/2) - K₀(t) ≤ t/2`; the constant `eulerW = E(1) - ∫₀¹ (1 - e^{-w}) dw/w`; **`|K₀(t) + log(t/2) - eulerW| ≤ t/2`** for `t > 0` |
| 15 | `LadderA2` | the five sub-rungs of A2 stated (each checked numerically from the definitions first); **`rungA2_of_subrungs`**: they imply `RungA2` (multiply the rotation formula by `e^{-a₀ s}`, subtract `1/s`, let `s → 0+`; limits along the right neighbourhoods of `0` and their uniqueness); `rv6_of_A2sub_B` |
| 16 | `TrigA2` | **sub-rung A2T**: with `x = πs/2` the expression is `(π/2) N(x)/x⁶`, `N = 45 sin x - 45 x cos x - 15 x² sin x - x⁵`; `-x⁷/14 ≤ N(x) ≤ 0` on `x ≥ 0` from `N' = 5x N₁`, `N₁' = 3x (sin x - x)` and `x - x³/6 ≤ sin x ≤ x`; so the expression is `O(s)` |
| 17 | `MellinU` | `integrable_mul_exp_of_bounds`: `g(u) e^{σu}` is integrable on `ℝ` if `|g| ≤ A (2 - u)^b` on `u ≤ 0` and `|g| ≤ B e^{-αu}` on `u > 0`, `0 < σ < α`; the bounds for `I₀^a K₀^b`, `I₀² I₁ K₀⁵`, `J₀⁶` at `e^u`; hence every Mellin integrand of the ladder is integrable for `0 < σ < 3` |
| 18 | `RungA2P` | **sub-rung A2P**: `φ(u) = I₀(e^u)³ K₀(e^u)⁵ e^{su}` has `φ' = 8 P-integrand - 5 M₂,₄-integrand + s M₃,₅-integrand` (the Wronskian) and `φ → 0` at `±∞`, so `∫ φ' = 0`; `(8/5) P(s) → R₆,₂` by dominated convergence |
| 19 | `PoleM`, `RungA2M` | **sub-rung A2M**: reflection `u = a₀ - y`; `∫₀^∞ y^b e^{-sy} dy = b!/s^{b+1}` (Mathlib's Gamma integral); `|I₀^a K₀^b (e^{a₀-y}) - y^b| ≤ D e^{-y/2}` for `y ≥ 0` from `|K₀(t) - (a₀ - log t)| ≤ t/2`; `I₀^a K₀^b ≤ t^{-b}` on the other half-line |
| 20 | `RungA2N` | **sub-rung A2N**: `N(s) - 1/s = ∫_{u ≤ 0} (j - 1) e^{su} + ∫_{u > 0} j e^{su}` (`j(u) = J₀(e^u)⁶`), dominated convergence on each half-line, and `∫_{u ≤ 0} (j - 1) + ∫_{u > 0} j = eulerW - (walkSide - log 2)` by the substitutions `t = e^u` on `ℝ` and `w = e^u` on `u ≤ 0` (Mathlib's change of variables); `rv6_of_A2R_B` |

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

**A1.**  Done (waves 9 to 13).  The calculus and decay of `J₀`; the Laplace transform of `J₀` and
the logarithm formula with the damping factor `e^{-δt}`; Bessel's integral; the characteristic
function of the walk on the cube; then, for every `δ > 0`, the identity
`∫_{[0,1]⁵} log(δ + √(‖X‖² + δ²)) = log 2 + ∫₀^∞ (e^{-t} - e^{-δt} J₀⁶) dt/t` between bounded
continuous integrands.  The right side stays bounded as `δ → 0`; the integrand on the left is
`≤ log 8` and equals `log 2δ` where `X = 0`; so `{X = 0}` is a null set, `log ‖X‖` is integrable
on the cube (monotone convergence), and the two limits agree.  No change of variables on the cube
and no circle average was needed.

**A2.**  `walkSide = (30/π⁴) R₆,₂`.  The proof keeps `s` real and small and never continues a
Mellin transform analytically.  Done: the constant `eulerW` and `K₀(t) = a₀ - log t + O(t)` at `0`
(wave 14; the constant is never identified with Euler's, it cancels); the reduction to the five
sub-rungs (wave 15); A2T, A2P, A2M, A2N (waves 16 to 20, table above).

**A2R, the one sub-rung left.**  For `0 < s < 1`:
`N(s) = (12/π⁵) sin(πs/2) M₁,₅(s) - (30/π⁴) cos(πs/2) M₂,₄(s) - (20/π³) sin(πs/2) M₃,₃(s)`.
Plan, fixed after wave 20 (it replaces the earlier sketch; every item is a convergent integral):

1. *Kernels.*  `cJ0 z = (1/π) ∫₀^π cos(z sin θ) dθ`, entire, `|cJ0 z| ≤ e^{|Im z|}`; termwise
   integration with Mathlib's `∫₀^π sin^{2k}` gives `cJ0 z = Σ (-1)^k (z/2)^{2k}/(k!)²`, hence
   `cJ0 x = J₀(x)` and `cJ0 (iy) = I₀(y)`.  `cK0 w = ∫₀^∞ exp(-w cosh u) du` on `Re w > 0`:
   holomorphic, `|cK0 w| ≤ K₀(Re w)`, `cK0 t = K₀(t)`.
2. *Two forms of `H⁺ = J₀ + iY₀`.*  `hK z = (2/(πi)) cK0(-iz)` on `Im z > 0`, and
   `hE z = (1/π) ∫₀^π e^{iz sin θ} dθ - (2i/π) ∫₀^∞ e^{-z sinh u} du` on `Re z > 0`; both
   holomorphic.  On the real axis `hE x = J₀(x) + i·(real)`; on the imaginary axis
   `hK (iy) = (2/(πi)) K₀(y)`.
3. *Agreement* `hE = hK` on the open quadrant: Cauchy's theorem for `w ↦ e^{z sinh w}` on the
   rectangle `[-R, 0] × [0, π/2]`, the side `Re w = -R` tends to `0`
   (`Re(z sinh(-R + iθ)) ≤ -min(Re z, Im z) sinh R`), and `θ ↦ π - θ`.
4. *The rotation at finite `R`*, in `w = log z`: with
   `G(J, H) = (3/8) J H⁵ - (15/8) J² H⁴ + (5/2) J³ H³`, Cauchy on `[-R, R] × [0, π/4]` for
   `G(cJ0, hE)(e^w) e^{sw}` and on `[-R, R] × [π/4, π/2]` for `G(cJ0, hK)(e^w) e^{sw}`; the
   common side cancels by 3.  Take real parts *before* letting `R → ∞`: the bottom side is
   `∫_{-R}^R J₀(e^u)⁶ e^{su} du` (`Re G(J, J + iY) = J⁶`, `sixteen_mul_pow_six`), the top side is
   the combination of `I₀^a K₀^b`; both converge absolutely (`MellinU.lean`).  The decay of `Y₀`
   on the real axis is never needed.
5. *The two vertical sides vanish.*  `|G| ≤ Φ(Im z)`,
   `Φ(y) = Σ c_k e^{ky} ((2/π) K₀(y))^{6-k}` (`k = 1, 2, 3`); for every `δ ∈ (0, 1)`,
   `Φ(y) ≤ C_δ y^{-δ}` on `y > 0` (`K₀(y) ≤ 2 - log y` for `y ≤ 1`; `e^y K₀(y) ≤ √(π/(2y))` from
   `cosh u - 1 = 2 sinh²(u/2) ≥ u²/2` and the Gaussian integral); `sin θ ≥ 2θ/π`; so the side at
   `|z| = r` is `≤ C r^{s-δ}`: take `δ > s` for `r → ∞` and `δ < s` for `r → 0`.

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
* What the five files of waves 8 (second session) to 10 had in common, all green at the first
  compile: every combinator result (`.mul`, `.comp`, `.sub`, `.fun_div`, …) is restated by a typed
  `have` before it is used; no `field_simp` (cancellations are `linear_combination` with
  `x * x⁻¹ = 1` or `a / b * b = a` as a hypothesis); no `positivity` on a goal that needs a
  hypothesis; a `by` block is never left inside a `rw [...]` term without a type ascription;
  nonlinear steps are given to `linarith` as explicit products (`mul_le_mul …`), not left to
  `nlinarith`.
* Waves 11 to 13 (five more files, all green at the first compile) added: every Mathlib name is
  read off the local copy of the pinned version before it is used (`continuous_finsetSum`,
  `Set.indicator_of_notMem`, `abs_add_le` are this version's names); a goal produced by
  `refine … (fun n => ?_)` is restated by `show` before a `rw`; an inequality between functions
  (`0 ≤ f`, `f ≤ g`) is given as a typed `have` before it is passed to `integral_mono` or
  `integral_nonneg`; an instance that Mathlib does not provide (`IsFiniteMeasure` of Lebesgue
  measure restricted to a box in `Fin 5 → ℝ`) is declared once, after rewriting the measure as a
  product; a constant is integrated as `c * 1` with the integral of `1` proved once.
* Waves 14 and 15: a new top-level name is counted across `Tower/` before the first push (a clash
  with an older file fails the build of `Audit` although the new file compiles); lemmas produced
  by `@[to_dual]` or `@[to_additive]` (`Ioo_mem_nhdsGT`, `Filter.Tendsto.abs`,
  `squeeze_zero_norm'`) have no `theorem` line of their own, so they are found through the dual
  or multiplicative name; limits at `0+` are stated with `nhdsWithin 0 (Set.Ioi 0)` written out
  and combined by `.mul`, `.add`, `.sub`, `.const_mul`, each result restated by a typed `have`;
  two functions that must be the same lambda in two hypotheses are compared as text by a script
  before the push.
* Waves 16 to 20 (seven files, six green at the first compile): `congr 1` can close a goal by
  `rfl`, and a tactic after it then fails with "no goals" (the one failed run): an exponential is
  split with a lemma `e^a e^b = e^c` given `a + b = c` (`exp_mul_exp_of_add_eq (by ring)`), stated
  as a typed `have`; the name checker's regular expression reads a primed name as its unprimed
  stem, so no declaration name carries a prime; factorial values are `by decide` on the natural
  number, then `rw` and `norm_num` for the cast; closed natural-number arithmetic in exponents and
  indices (`2 + 1` for `3`) is accepted by `exact` up to definitional equality; unused binders are
  written `_`; a constant that would be a long expression is a `noncomputable def`, unfolded once
  at the end; long repeated integrands are substituted by a generator in `tools/`; a dominated
  convergence along `s → 0+` is `tendsto_integral_filter_of_dominated_convergence` on the
  restricted measure, with the bound stated through `ae_restrict_of_forall_mem` and the result
  taken by `have hD := …; exact hD`; Mathlib's one-dimensional change of variables
  (`integral_image_eq_integral_abs_deriv_smul`, `integral_comp_exp`) is given as a typed `have`
  whose two sides are written out, and the pointwise simplification is a separate function
  equality (`funext`, `show`, `rw`).
