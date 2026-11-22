# Tower-Lean

Lean 4 / Mathlib formalisation of results from the random-walk Mahler-measure programme
(James Anderson-Joyce).  Every statement in this repository is checked by the Lean kernel on
each push; the build status of the latest commit is the status of the mathematics.

No `sorry`, no `native_decide`, no added axioms.  `Tower/Audit.lean` prints the axioms behind
each headline theorem in the build log; they are `propext`, `Classical.choice`, `Quot.sound`.

## The tangent-line family (complete, conditional on reduction maps)

`E : 1 + x + 1/x + y + 1/y = 0`, written `G(x, y) = 0`; Weierstrass model
`Y² = X³ - (7/4) X² + X`.  `F(x, y, w) = 0` is the condition studied (tangency of the branch
curve through a node; `w` a primitive cube root of unity).

| File | Content |
|---|---|
| `Tower/TangentLine/Resultant.lean` | `G = F = 0` and `x ≠ 0` force `x² + 1 = 0`, `x + 1 = 0` or `Q₄(x) = 0`, with `Q₄(t) = t⁴ + (2 + 3w) t³ - t² + (2 + w) t + (1 + w)`; the resultant factorises as `(1 + w) x³ (x² + 1)² (x + 1) Q₄(x)` |
| `Tower/TangentLine/Maps.lean` | the polynomials commute with ring homomorphisms; distinct roots of `Q₄` and its divided difference; `equation_of_link`: the point `(t, y)` of `G = 0` goes to a point of the Weierstrass model |
| `Tower/EC/Cert.lean` | slope certificates for Mathlib's group law on `WeierstrassCurve.Affine.Point` |
| `Tower/TangentLine/Orders103.lean`, `Orders373.lean`, `Orders499.lean` (generated) | `Q₄` splits completely over `𝔽₁₀₃`, `𝔽₃₇₃`, `𝔽₄₉₉`; the point over each root is unique; its exact order (`addOrderOf`) is `120, 40, 24, 6`, resp. `400, 400, 400, 80`, resp. `248, 124, 62, 124`; exact orders of the six differences modulo `103` and `499` |
| `Tower/EC/Reduction.lean` | group lemma: two homomorphisms with `p₁`-, `p₂`-primary torsion kernels and different orders of the image force infinite order; the hypothesis package `Reduction` |
| `Tower/TangentLine/Red103.lean`, `Red373.lean`, `Red499.lean` (generated) | under a `Reduction` package, the reduction of the point over a root of `Q₄` is one of the four listed points |
| `Tower/TangentLine/NonTorsion.lean` (generated) | **`addOrderOf_eq_zero_of_reductions`**: the point over a root of `Q₄` has infinite order; **`sub_addOrderOf_eq_zero_of_reductions`**: so does the difference of the points over two distinct roots |
| `tools/gen_orders.py` | the generator of the generated files (it computes slopes and orders; Lean checks them) |

### What is assumed

The two theorems of `NonTorsion.lean` take `Tower.EC.Reduction` packages as arguments.  A
package asserts that a reduction map `W(K) → W'(𝔽_p)` exists with the textbook properties
(homomorphism; reduces integral coordinates; torsion in the kernel is `p`-primary: Silverman,
*The Arithmetic of Elliptic Curves*, VII.2.1 and VII.3.1).  Mathlib does not yet have the
reduction map on points, so this is an explicit hypothesis, not a proof.  Everything else in the
chain is proved.

Not formalised: that `F = 0` is the tangency condition; the passage from non-torsion differences
to "not a congruence modular surface" (Manin–Drinfeld).

## The six-step Mahler measure (the modular side and the random-walk representation proved; two rungs open)

`m(1 + x₁ + x₂ + x₃ + x₄ + x₅) = (648 / π⁶) L(f, 5)`, `f = (η(τ) η(2τ) η(3τ) η(6τ))²`
(the six-step conjecture of Rodriguez-Villegas; proof: J. Anderson-Joyce, *Logarithmic Hankel
pairings, the six-step Mahler measure, and sunset endpoint periods*, 2026).

| File | Content |
|---|---|
| `Tower/RV6/Defs.lean` | the objects, each a convergent integral or series: the Mahler measure as a torus integral; `I₀`, `I₁`, `J₀`, `K₀`; the Bessel moment `R₆,₂ = (8/5) ∫ I₀² I₁ K₀⁵`; `Λ(f, 5)` from Mathlib's eta function; `L(f, 5)` from the coefficients of the eta product; the regularised double Eisenstein integral `D₀₁` on `Γ₀(6)`; the integrals `J₁`, `J₂` |
| `Tower/RV6/Ladder.lean` | the proof cut into six named propositions (`RungA1`, `RungA2`, `RungB`, `RungC1`, `RungC2`, `RungD`) and **`rv6_of_rungs`**: the rungs imply the theorem |
| `Tower/RV6/Ladder2.lean`, `Psi.lean`, `MellinSeries.lean` | the modular side re-cut with an explicit Eisenstein form; termwise Mellin transform of a `q`-series; **`lambdaPsi5_eq`** (rung D′) |
| `Tower/RV6/EisAxis.lean` | **`E4im_inv`**, **`E2im_inv`**: `E₄(i/y) = y⁴ E₄(iy)` and `E₂(i/y) = -y² E₂(iy) + 6y/π`, from Mathlib's Eisenstein series |
| `Tower/RV6/QSeries.lean`, `Regroup.lean`, `Arith.lean`, `Dirichlet.lean`, `Fricke6.lean` | `q`-series on the imaginary axis (dilation, Cauchy product, Mellin transform); regrouping of double series by the product of the indices; `Σ_{mn=N} σ₃(m)σ₃(n) n = Σ_{mn=N} σ₁(m)σ₁(n) n³`; `Σ σ₃(n)/n⁵ = (π²/6) ζ(5)`, `Σ σ₁(n)/n⁵ = (π⁴/90) ζ(5)`; the Fricke relations at level six |
| `Tower/RV6/PhiKernel.lean`, `Interchange.lean` | **`interchange_three`**, **`interchange_four`**: Lemma 5.1 of the paper (the interchange of the two Eisenstein series under the integral), by Tonelli and one identity of arithmetic functions |
| `Tower/RV6/Eichler.lean`, `Eichler2.lean` | the partial Eichler integral `T(a) = ∫_a^∞ t S₃(t) dt`; **`Tint_inv`**: `T(a) + T(1/a) = (a² + a⁻²)/480 + 2T(1) - 1/240`; the two forms of `𝒜₁`; `∫₀^∞ x² T(x) dx = ζ(5)/(24π³)` |
| `Tower/RV6/Bilin.lean` | linearity of the integral for finite combinations and for products of two finite combinations |
| `Tower/RV6/C4.lean` | the Fourier coefficients `c₄(n)` of `Defs.lean` are `32 (σ₃(n) - σ₃(n/2) - 9σ₃(n/3) + 9σ₃(n/6))` |
| `Tower/RV6/RungC1.lean` (generated) | **`rungC1 : RungC1`**: `D₀₁ = -(104/(27π³)) ζ(5) + (64/9)(J₁/(2π) + J₂/(4π²))`, with no hypotheses |
| `Tower/RV6/QCalc.lean`, `DEInv.lean` | termwise differentiation and integrability of a `q`-series on the imaginary axis, the Cauchy product; **`DEq_inv`**: the inversion formula of `D E₂`; `fricke_subst`: `∫₀^∞ g(1/(6y)) y⁻² dy = 6 ∫₀^∞ g` |
| `Tower/RV6/PsiW.lean` | the weight-four form `Ψ^W` by its coefficients `psiW` (divisor sums); the moments of `𝔉`; **`lambdaPsiW5_eq`** (rung D″): `∫₀^∞ Ψ^W(iy) y⁴ dy = (3/(4π⁵)) Σ psiW(n)/n⁵` |
| `Tower/RV6/RungC2.lean` | **`rungC2W`** (rung C2″): `(64/9)(J₁/(2π) + J₂/(4π²)) = (104/(27π³) + 12/(5π⁵)) ζ(5) + (1152/(5π²)) ∫₀^∞ Ψ^W(iy) y⁴ dy` |
| `Tower/RV6/Ladder3.lean` | **`D01_eq_modular`** (no hypotheses); **`rv6_psiW_of_bessel`**: `RungA1`, `RungA2`, `RungB` imply `μ₆ = (648/π⁶) Σ psiW(n)/n⁵`; `rv6_of_bessel_and_E` |
| `Tower/RV6/Ser.lean` | formal power series over `ℝ`: `θ = X d/dX` (a derivation), its commutation with `X ↦ X^d`, truncation at `X⁷` |
| `Tower/RV6/Ramanujan.lean` | **`qa_coeff_unique`**: a `q`-series of polynomial growth that vanishes for all `y > 0` has zero coefficients; **`D_axis`**: `(2πi)⁻¹ d/dz` on the imaginary axis; **`ram6`**: Ramanujan's identities for `E₂, E₄, E₆` at `X, X², X³, X⁶` in `ℝ⟦X⟧`, from Mathlib's identities on the upper half plane |
| `Tower/RV6/Level6.lean` (generated) | the nine polynomial relations among `E₂, E₄, E₆` at `X, X², X³, X⁶` (**`Rf1_eq_zero`** … **`Rf9_eq_zero`**): the differences satisfy a closed linear system under `θ`, whose matrix at `X = 0` has no eigenvalue `≥ 7`; **`thetaGam_scaled`** |
| `Tower/RV6/EtaRec.lean` | **`rungEW`** (rung E″): `psiW(n)` is the `n`-th coefficient of `X ∏ ((1-X^k)(1-X^{2k})(1-X^{3k})(1-X^{6k}))²`, by the logarithmic derivative of the product and uniqueness of the recurrence; **`rv6_of_bessel`**: `RungA1`, `RungA2`, `RungB` imply `μ₆ = (648/π⁶) L(f, 5)` |
| `Tower/RV6/BesselI.lean`, `BesselK.lean`, `BesselW.lean` | the Bessel functions of `Defs.lean`: `I₀' = I₁`, `(t I₁)' = t I₀` (termwise differentiation of the series); `K₁(t) = ∫₀^∞ e^{-t cosh u} cosh u du`, `K₀' = -K₁`, `(t K₁)' = -t K₀` (differentiation under the integral sign, integration by parts); `e^{-t} ≤ t K₁(t) ≤ 1`; **`wronskian`**: `I₀ K₁ + I₁ K₀ = 1/t` |
| `Tower/RV6/BesselR.lean` | bounds: `I₀ ≤ cosh`, `I₁ ≤ sinh`, `K₀ > 0`, `I₀(t) ≤ e^t`, `I₁K₀ ≤ 1/t`, `K₀(t) ≤ e^{-t}√(π/(2t))`, `K₀(t) ≤ log(1 + 2/t)`; **`integrableOn_R62_integrand`**, **`R62_pos`**: `R₆,₂ = (8/5) ∫₀^∞ I₀² I₁ K₀⁵ dt` is a convergent positive integral |
| `Tower/RV6/BesselJ.lean` | `J₀' = -J₁`, `(t J₁)' = t J₀`; `J₀² + J₁² ≤ 1`; **`besselJ0_sq_le`**: `J₀(t)² ≤ E(1)/t` for `t ≥ 1` (the energy of `√t J₀` decreases); **`integrableOn_walk_integrand`**: the integral in `walkSide` converges |
| `Tower/RV6/Laplace.lean`, `LogInt.lean` | **`lapl_besselJ0`**: `∫₀^∞ e^{-δt} J₀(at) dt = 1/√(a² + δ²)`; **`logInt_eq`**: `∫₀^∞ (e^{-t} - e^{-δt} J₀(at)) dt/t = log(δ + √(a² + δ²)) - log 2` (`a ≥ 0`, `δ > 0`) |
| `Tower/RV6/BesselInt.lean` | **`besselJ0_eq_besG`**: Bessel's integral `J₀(x) = ∫₀¹ cos(x cos 2πθ) dθ` for the series `J₀` of `Defs.lean` (uniqueness for the system `A' = -B`, `(xB)' = xA`) |
| `Tower/RV6/CharFun.lean` | **`integral_cube_besselJ0`**: `∫_{[0,1]⁵} J₀(t ‖1 + Σ e(τ_j)‖) dτ = J₀(t)⁶`, the characteristic function of the six-step walk; `cube_restrict`: Lebesgue measure on the cube is a product measure |
| `Tower/RV6/CubeLog.lean` | **`integral_cube_logG`**: `∫_{[0,1]⁵} log(δ + √(‖X‖² + δ²)) dτ = log 2 + ∫₀^∞ (e^{-t} - e^{-δt} J₀(t)⁶) dt/t` for `δ > 0` |
| `Tower/RV6/RungA1.lean` | **`rungA1 : RungA1`**: `m(1 + x₁ + ⋯ + x₅) = log 2 + ∫₀^∞ (e^{-t} - J₀(t)⁶) dt/t`, with no hypotheses; `ae_cubeX_ne_zero`; `integrable_of_antitone_of_tendsto`; **`rv6_of_A2_B`**: `RungA2`, `RungB` imply `μ₆ = (648/π⁶) L(f, 5)` |
| `Tower/RV6/KZero.lean` | **`abs_besselK0_add_log_le`**: `|K₀(t) + log(t/2) - eulerW| ≤ t/2` for `t > 0`, with `eulerW = E(1) - ∫₀¹ (1 - e^{-w}) dw/w`, `E(x) = ∫₀^∞ exp(-x e^u) du` |
| `Tower/RV6/LadderA2.lean` | `RungA2` cut into five named sub-rungs about a real `s > 0` (`RungA2R`, `RungA2N`, `RungA2M`, `RungA2P`, `RungA2T`) and **`rungA2_of_subrungs`**: they imply `RungA2`; **`rv6_of_A2sub_B`** |
| `Tower/RV6/BesselAlgebra.lean`, `Swap.lean`, `Lambert.lean` | pieces proved on the way: the sixth-power identity and the Wronskian derivative identity of the Bessel side; a substitution identity; convergence of the Lambert series of the definitions |
| `tools/gen_interchange.py`, `tools/gen_rungc1.py`, `tools/gen_level6.py` | generators of the generated files (the first two only substitute repeated expressions; the third writes the relations, the matrix and the cofactors, which were computed in exact arithmetic; Lean checks them) |

**Status: this is not yet a Lean proof of the theorem.**  The modular side is proved with no
hypotheses: the double Eisenstein integral `D₀₁` of `Defs.lean` equals
`(12/(5π⁵)) ζ(5) + (1152/(5π²)) ∫₀^∞ Ψ^W(iy) y⁴ dy`, that integral is
`(3/(4π⁵)) Σ psiW(n)/n⁵`, and `psiW(n)` is the `n`-th coefficient of the eta product
(Sections 5 and 6 of the paper; nothing is regularised and no convergence is assumed).
The first rung of the Bessel side is proved as well: **`rungA1`**, the random-walk representation
`μ₆ = log 2 + ∫₀^∞ (e^{-t} - J₀(t)⁶) dt/t`, for the Mahler measure defined in `Defs.lean` as an
integral over `[0,1]⁵` (the integrability of `log ‖1 + Σ e(τ_j)‖` on the cube is part of the proof).
**`rv6_of_A2_B`** therefore derives the theorem from two statements, which are still hypotheses:
`RungA2` (`walkSide = (30/π⁴) R₆,₂`, the rotation of the contour) and `RungB` (the Bessel-side
evaluation of the double Eisenstein integral).  Each was checked numerically from the Lean
definitions before it was stated.  `RungA2` is in turn derived (**`rungA2_of_subrungs`**) from five
sub-rungs about Mellin transforms at a real `s > 0`, also hypotheses and also checked numerically
first; **`rv6_of_A2sub_B`** takes those five and `RungB`.  Towards them, the calculus of
`I₀, I₁, K₀, K₁`, the Wronskian, the convergence and positivity of the integral defining `R₆,₂`,
and the expansion of `K₀` at `0` are proved.  `ROADMAP.md` has the plan and the state by rung.

## Not here yet

* proofs of the five sub-rungs of `RungA2` and of `RungB` (`ROADMAP.md`);
* the finite census of genus-0 subgroups of `PSL₂(ℤ/15)` and `PSL₂(ℤ/30)`.

## Building

```
lake update
lake exe cache get
lake build
```

Toolchain: Lean `v4.36.0`, Mathlib `v4.36.0`.
