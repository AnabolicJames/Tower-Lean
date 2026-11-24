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

## The six-step Mahler measure (proved, no hypotheses: `Tower.RV6.rv6`)

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
| `Tower/RV6/TrigA2.lean` | **`rungA2T : RungA2T`**: the trigonometric poles cancel (`-x⁷/14 ≤ 45 sin x - 45 x cos x - 15 x² sin x - x⁵ ≤ 0` on `x ≥ 0`) |
| `Tower/RV6/MellinU.lean` | `integrable_mul_exp_of_bounds` and the bounds that make every Mellin integrand of the ladder (`I₀^a K₀^b`, `I₀² I₁ K₀⁵`, `J₀⁶` at `e^u`, times `e^{σu}`) integrable on `ℝ` for `0 < σ < 3` |
| `Tower/RV6/RungA2P.lean` (generated) | **`rungA2P : RungA2P`**: `M₂,₄(s) = (8/5) P(s) + (s/5) M₃,₅(s)` (the Wronskian, integrated in `u = log t`) and `(8/5) P(s) → R₆,₂` |
| `Tower/RV6/PoleM.lean`, `RungA2M.lean` (generated) | **`rungA2M : RungA2M`**: `e^{-a₀ s} M_{a,b}(s) - b!/s^{b+1}` is bounded on `0 < s ≤ 1`; `∫₀^∞ y^b e^{-sy} dy = b!/s^{b+1}`; `I₀^a K₀^{a+d} ≤ t^{-(a+d)}` |
| `Tower/RV6/RungA2N.lean` (generated) | **`rungA2N : RungA2N`**: `N(s) - 1/s → eulerW - (walkSide - log 2)` as `s → 0+`; **`rv6_of_A2R_B`**: `RungA2R` and `RungB` imply `μ₆ = (648/π⁶) L(f, 5)` |
| `Tower/RV6/CKernel.lean`, `CJSeries.lean` (generated) | `J₀` on `ℂ`: `cJ0 z = (2/π) ∫₀^{π/2} cos(z sin t) dt`, entire, `‖cJ0 z‖ ≤ e^{|Im z|}`; its power series by termwise integration; **`cJ0_ofReal`**, **`cJ0_I_mul`**: `cJ0 x = J₀(x)`, `cJ0 (iy) = I₀(y)` for the series of `Defs.lean`; differentiation under the integral sign for `exp(w g)` |
| `Tower/RV6/CKZero.lean`, `HAgree.lean` | `K₀` on the right half-plane (`cK0`); the two forms `hE` and `hK` of `H₀⁽¹⁾ = J₀ + iY₀`, differentiable on `Re z > 0` resp. `Im z > 0`; `Re hE(x) = J₀(x)`, `hK(iy) = -(2i/π) K₀(y)`, `‖hK z‖ ≤ (2/π) K₀(Im z)`; **`hE_eq_hK`**: they agree on the open first quadrant (Cauchy's theorem on a rectangle for `exp(z sinh w)`) |
| `Tower/RV6/GPoly.lean` (generated) | `G(J, H) = (3/8) J H⁵ - (15/8) J² H⁴ + (5/2) J³ H³`: **`gpoly_re`** (`Re G(J, H) = J⁶` for real `J = Re H`), **`gpoly_I_axis_mul_re`** (its real part on the imaginary axis); **`norm_cJ0_le_besselI0`**: `‖J₀(z)‖ ≤ I₀(Im z)`; the majorant `sidePhi` of the vertical sides and its decay |
| `Tower/RV6/RotRect.lean`, `RotSides.lean` (generated) | the rotated integrands `rotE`, `rotK` in `w = log z`; Cauchy's theorem on `[-R, R] × [0, π/4]` and `[-R, R] × [π/4, π/2]`; **`rect_rot`**: the rotated contour at finite `R`; `‖sideInt s U‖ ≤ K e^{(s-δ)U}` for `0 < δ < 1`, so both vertical sides tend to `0` |
| `Tower/RV6/RungA2R.lean` (generated) | **`rungA2R : RungA2R`**; **`rungA2`**, **`rungA`**: `μ₆ = (30/π⁴) R₆,₂`; **`mu6_eq_bessel`**: `m(1 + x₁ + ⋯ + x₅) = (48/π⁴) ∫₀^∞ I₀(t)² I₁(t) K₀(t)⁵ dt`, with no hypotheses; **`rv6_of_B`**: `RungB` implies `μ₆ = (648/π⁶) L(f, 5)` |
| `Tower/RV6/AxisEv.lean`, `ModAxis.lean` | power series on the imaginary axis; the five relations of level six among `E₂`, `E₄` there; `Zax`, `Uax`, `Pax`, `Eax` and their differential system; `P² = 16Z² + 320ZU + 1024U²`; `g₄ = 8UP` |
| `Tower/RV6/QTail.lean`, `EtaForm.lean` | a tail bound for `q`-series; `Zax`, `Uax` as exponentials of explicit `q`-series (the eta quotients); `Zax > 0`, `Uax > 0` |
| `Tower/RV6/FrickeAx.lean`, `XMod.lean` | the Fricke relations; `Pax > 0`; the Hauptmodul `xm = 8 √(Uax/Zax)` with `xm' = -(π/4) Pax xm`, `xm(y) xm(1/(6y)) = 8`, both cusps, and `xm` a decreasing bijection of `(0, ∞)` |
| `Tower/RV6/BMReduce.lean` | **`pairS_eq_JS`**: Zhou's parametrisations turn the pairing into `(π⁵/16) ∫₀^∞ g₄ 𝒜₁ xm^{-s} dy` (exact, every `s`); the pole `72/s⁵` as a Gamma integral; **`rungBM_of_zhou`**, **`rv6_of_zhou`** |
| `Tower/RV6/BMBounds.lean`, `LimBM.lean` | explicit bounds for `g₄`, `𝒜₁`, `xm` at both cusps; **`limBM`**: `∫ g₄ 𝒜₁ xm^{-s} - ∫ e^{-πs/(6y)}/(162y⁶) → D₀₁` as `s → 0+` (dominated convergence); **`rungBM_of_zhou2`**, **`rv6_of_zhou2`** |
| `Tower/RV6/BesselL5.lean` (generated) | the fifth-order equation of `f = I₀K₀³` and `g = I₀²K₀²`: with `θ = t d/dt`, `p = tI₁`, `q = tK₁`, the ladder `eₖ` of a product of four Bessel factors satisfies `θeₖ = (k+1)eₖ₊₁ + (5-k)t²eₖ₋₁` (`hasDerivAt_ldFk`, `hasDerivAt_ldGk`; no Wronskian); the θ-chains `thFk`, `thGk` with `HasDerivAt thₖ (thₖ₊₁ t / t) t` on `t > 0`; **`l5_fB`**, **`l5_gB`**: `θ⁵ - 4t²(5θ³ + 15θ² + 18θ + 8) + 64t⁴(θ + 2)` annihilates `f` and `g` |
| `Tower/RV6/HankelDom.lean`, `HankelDomF.lean` (generated) | the class `HDom` of the Hankel transform (explicit bounds at `0` and at `∞`, closure rules, integrability, vanishing boundary terms); **`hdom_thF0 … hdom_thF5`**: `θᵏ f` is in it |
| `Tower/RV6/HankelIBP.lean`, `HankelRelF.lean` (generated) | the Hankel transform `hk ψ x = ∫₀^∞ J₀(xt) ψ(t) t dt` (`hjF = hk fB`); two integrations by parts; **`hk_theta2`**: `hk((θ + 2)² φ) = -x² hk(t² φ)`; **`hk_relation_F`**: the linear relation among `hk(θᵏ f)(x)`, `k ≤ 5`, with coefficients in `x²` (leading coefficient `(x² + 4)(x² + 16)`) |
| `Tower/RV6/HankelDeriv.lean` | **`hasDerivAt_hk`**: `ϑ hk(ψ) = -hk((θ + 2)ψ)` (`x > 0`), so `hk(θᵏ⁺¹ f) = -(ϑ + 2) hk(θᵏ f)` |
| `Tower/RV6/HankelODEF.lean` | **`uF_eq`**: `L₃′ hjF = x² (c₁ + c₂ log x)` on `(0, ∞)` (two first-order equations in `ϑ`; generated by `tools/gen_hankelodef.py`) |
| `Tower/RV6/HankelTaylor.lean` | `hk_taylor` (`hk ψ x = hk ψ 0 - (x²/4) hk(t²ψ) 0 + O(x³)`), the moment shifts at `x = 0`, two limits at `0+` |
| `Tower/RV6/HankelZeroF.lean` | **`uF_zero`**: `L₃′ hjF = 0` on `(0, ∞)` (the `s = 0` relation of `L₅`; generated by `tools/gen_hankelzerof.py`) |
| `Tower/RV6/PullbackF.lean` | **`hjF_xm_quad`**: `hjF(xm y) = (a + by + cy²) Zax y` (the third `y`-derivative of `hjF(xm y)/Zax y` is a multiple of `L₃′ hjF`; generated by `tools/gen_pullbackf.py`) |
| `Tower/RV6/ZhouFa0.lean` | **`zhouF_a0`**: `hjF(xm y) = a₀ Zax y` (`a₀ = ∫ t I₀K₀³`); `zhouF_of_const`; **`rv6_of_a0`**: the six-step theorem from `RungBP`, `a₀ = π²/16` and `ZhouG` |
| `Tower/RV6/CuspBesselF.lean` | **`tendsto_x2_hk_thF2`**: `x² hk(θ²f)(x) → 6` as `x → ∞` (the Bessel side of the cusp that fixes `a₀`) |
| `Tower/RV6/CuspModF.lean` | **`zhouF`**, **`a0_pi_sq`** (`∫ t I₀K₀³ = π²/16`), **`rv6_of_zhou3`**: the six-step theorem from `RungBP` and `ZhouG` (generated by `tools/gen_cuspmodf.py`) |
| `Tower/RV6/LaplaceIK.lean`, `LaplaceP.lean`, `LaplaceDecay.lean` | **`laplace_P`**: `I₀K₀ = ∫₀^∞ e^{-tw} ν(w) dw`; the decay of `θʲ(I₀K₀)` at infinity, uniform in `t > 0` |
| `Tower/RV6/AJ.lean` | the `J₁` transform `AJ` (`ajG = AJ g`) on `PDom` and its two transport rules **`hasDerivAt_AJ`** (R1) and **`AJ_theta2`** (R2) |
| `Tower/RV6/DomG.lean`, `AJODEG.lean` | the chain of `g` in `PDom`; **`AJ_rel`** and **`uG_eq`**: the dual equation of `ajG` up to one constant (generated by `tools/gen_domg.py`, `tools/gen_ajodeg.py`) |
| `Tower/RV6/ZeroG.lean` | **`uG_zero`**: the dual equation of `ajG` holds with constant `0` (`AJ(θ⁴g) = ∫ J₀(xt) θ⁵g/t → 0`) |
| `Tower/RV6/PullbackG.lean` | **`vG0_xm_quad`**: `ajG′(x)/x` pulled back along `xm` is `(a + by + cy²) Zax y` (generated by `tools/gen_pullbackg.py`) |
| `Tower/RV6/SmallG.lean` | **`vG0_c_zero`**: `|ajG′(x)/x| ≤ 2K(-log x)` near `0`, so the `y²` coefficient of the pull-back is `0` |
| `Tower/RV6/CuspG.lean` | **`cusp_ab`**, **`vG0_eq`**: the cusp `x → ∞`, `ajG′(x)/x` along `xm` is `(π/4) y Zax y` |
| `Tower/RV6/ZhouG.lean` | **`zhouG`**: `ajG(xm y) = (π²/2) 𝒜₁(y)`; **`rv6_of_rungBP`**: the six-step theorem from `RungBP` alone |
| `Tower/RV6/LadderB.lean` | the last rung cut into two evaluations of one pairing: `hjF x = ∫₀^∞ J₀(xt) I₀K₀³ t dt`, `ajG x = x ∫₀^∞ J₁(xt) I₀²K₀² dt`, `pairS s = ∫₀^∞ hjF · ajG · x^{1-s} dx`; the sub-rungs `RungBP` (`pairS s - 72/s⁵ → R₆,₂/2 + (3/20) ζ(5)`) and `RungBM` (`pairS s - 72/s⁵ → (π⁵/16) D₀₁`); **`rungB_of_PM`**, **`rv6_of_PM`**: the two sub-rungs imply `RungB` and `μ₆ = (648/π⁶) L(f, 5)` |
| `Tower/RV6/BPIbp.lean`, `BPProd.lean` | `x² hjF x = ∫ F₂(t)(1 - J₀(xt)) dt`, `ajG x = ∫ G(t)(1 - J₀(xt)) dt` (`F₂ = θ²f/t`, `G = -θg/t`); the product formula `J₀(a)J₀(b) = ∫₀¹ J₀(\|a + b e(θ)\|) dθ` |
| `Tower/RV6/BPKernel.lean`, `BPHs.lean` | `j(s) = ∫₀^∞ (1 - J₀(y)) y^{-1-s} dy`; `k_s(τ,t) = ∫₀^∞ (1 - J₀(xτ))(1 - J₀(xt)) x^{-1-s} dx = j(s)(τ^s + t^s - M_s(τ,t))`; `h_s(w) = Σ b_k² w^k`, `b_k = binom(s/2, k)`, `0 ≤ h_s(w) ≤ (s²/2) w` |
| `Tower/RV6/BPGauss.lean`, `BPRclosed.lean`, `BPEuler.lean`, `BPGammaRatio.lean`, `BPQexp.lean` | `s j(s) = 2^{-s} Γ(1 - s/2)/Γ(1 + s/2)`; `Q(s) = e^{a₀ s} s j(s) = exp(ℓ(s))` and `\|Q - 1 - ζ(3)s³/12 - ζ(5)s⁵/80\| ≤ s⁶` (`a₀ = log 2 - γ`) |
| `Tower/RV6/BPPhi.lean`, `BPLam.lean`, `BPMellin.lean`, `BPLamPhi.lean` | `ℓ′ = Φ` and its expansion; `Λ(v) = Σ b_k²/(2k + v)`, `T₁`, `E(s) = Λ(-s) - Λ(0) - sT₁` with `E/s⁴ → ζ(5)/32`; the Mellin identity `j(u)j(s-u) = j(s)[s/(u(s-u)) - Λ(-u) - Λ(u-s)]`, hence `Λ(0) + Λ(-s) = Φ(s)` |
| `Tower/RV6/BPModel.lean`, `BPFubini.lean`, `BPMin.lean`, `BPH.lean` | the model `\|θ²f - 6 log(c/t)\| ≤ C t E³`, `\|θg + 2 log(c/t)\| ≤ C t E²` near `0`; Fubini: `pairS(s) = j(s)(s B(s) - H(s))`, `B = (4/5) P + (3/5) s M₃₅`, `H = ∫∫ F₂ G k_H` |
| `Tower/RV6/BPHm.lean`, `BPD.lean` | the model integral `H_m(s) = 24[Λ(0)(a₀²/s + 2a₀/s² + 2/s³) + T₁(a₀/s + 1/s²)]` in closed form; `\|H(s) - H_m(s)\| ≤ K s²` |
| `Tower/RV6/BPAsm.lean` | **`rungBP : RungBP`**: `pairS s - 72/s⁵ → R₆,₂/2 + (3/20) ζ(5)`; **`rv6 : mu6 = 648 / π ^ 6 * Lf5`**, with no hypotheses |
| `Tower/RV6/BesselAlgebra.lean`, `Swap.lean`, `Lambert.lean` | pieces proved on the way: the sixth-power identity and the Wronskian derivative identity of the Bessel side; a substitution identity; convergence of the Lambert series of the definitions |
| `tools/gen_modaxis.py`, `tools/gen_interchange.py`, `tools/gen_rungc1.py`, `tools/gen_level6.py`, `tools/gen_runga2p.py`, `tools/gen_runga2m.py`, `tools/gen_runga2n.py`, `tools/gen_cjseries.py`, `tools/gen_gpoly.py`, `tools/gen_rotrect.py`, `tools/gen_rotsides.py`, `tools/gen_runga2r.py`, `tools/gen_besselL5.py`, `tools/gen_hankeldomf.py`, `tools/gen_hankelrelf.py`, `tools/gen_domg.py`, `tools/gen_ajodeg.py`, `tools/gen_pullbackg.py` | generators of the generated files (most only substitute repeated expressions; `gen_level6.py` writes the relations, the matrix and the cofactors, `gen_gpoly.py` the two cofactors modulo `i² + 1`, and `gen_besselL5.py` the ladder, the θ-chain and its `linear_combination` cofactors, all computed in exact arithmetic; Lean checks them) |

**Status: proved.**  **`Tower.RV6.rv6 : mu6 = 648 / π ^ 6 * Lf5`** holds with no hypotheses (wave 65,
`BPAsm.lean`); its line in the axiom audit is `[propext, Classical.choice, Quot.sound]`.  The rest of
this section is the history of how the last rung was cut down and closed.

Proved with no hypotheses:

* the modular side: the double Eisenstein integral `D₀₁` of `Defs.lean` equals
  `(12/(5π⁵)) ζ(5) + (1152/(5π²)) ∫₀^∞ Ψ^W(iy) y⁴ dy`, that integral is `(3/(4π⁵)) Σ psiW(n)/n⁵`,
  and `psiW(n)` is the `n`-th coefficient of the eta product (Sections 5 and 6 of the paper;
  nothing is regularised and no convergence is assumed);
* the Bessel side of the Mahler measure (Section 2 of the paper): **`rungA1`**, the random-walk
  representation `μ₆ = log 2 + ∫₀^∞ (e^{-t} - J₀(t)⁶) dt/t` for the Mahler measure defined in
  `Defs.lean` as an integral over `[0,1]⁵` (the integrability of `log ‖1 + Σ e(τ_j)‖` on the cube
  is part of the proof), and **`rungA2`**, the rotation of the contour to the imaginary axis,
  `log 2 + ∫₀^∞ (e^{-t} - J₀(t)⁶) dt/t = (30/π⁴) R₆,₂`.  Together:
  **`mu6_eq_bessel : m(1 + x₁ + ⋯ + x₅) = (48/π⁴) ∫₀^∞ I₀(t)² I₁(t) K₀(t)⁵ dt`**.

**`rv6_of_B`** derives the theorem from the one statement that is still a hypothesis: `RungB`,
`D₀₁ = (8/π⁵) R₆,₂ + (12/(5π⁵)) ζ(5)`, the Bessel-side evaluation of the double Eisenstein integral
(Sections 3 and 4 of the paper: the logarithmic Hankel pairing and Zhou's modular parametrisations
of two Hankel transforms).  It was checked numerically from the Lean definitions before it was
stated.

**`rv6_of_PM`** cuts that rung in two (`LadderB.lean`): with `hjF`, `ajG` the two Hankel
transforms above and `pairS s = ∫₀^∞ hjF(x) ajG(x) x^{1-s} dx`, the hypotheses are
`RungBP : pairS s - 72/s⁵ → R₆,₂/2 + (3/20) ζ(5)` and `RungBM : pairS s - 72/s⁵ → (π⁵/16) D₀₁`
as `s → 0+`; `RungB` is the uniqueness of the limit.  Both sub-rungs, and every step of the plan
for proving them, were checked numerically from the Lean definitions before they were stated (the
pairing at `s = 0` computed from the Bessel integrals alone agrees with both limits to ten
digits).  Since wave 27, `RungBM` is derived (`rungBM_of_zhou`, `BMReduce.lean`) from three sharper
statements: Zhou's two parametrisations `ZhouF : hjF (xm y) = (π²/16) Zax y`,
`ZhouG : ajG (xm y) = (π²/2) 𝒜₁(y)` for the Hauptmodul `xm` of `XMod.lean`, and the limit `LimBM`
of a modular integral; **`rv6_of_zhou`** takes `RungBP`, `ZhouF`, `ZhouG`, `LimBM`.  Since wave 28
`LimBM` is proved (`limBM`), and **`rv6_of_zhou2`** takes `RungBP`, `ZhouF`, `ZhouG`.  Everything
modular that this needs (the level-six differential system on the axis, the eta forms and
positivity of `Zax`, `Uax`, `Pax`, the Fricke relations, `xm` and its cusps) is proved with no
hypotheses.  On the Bessel side of the two parametrisations, the first step is proved (wave 29):
`f` and `g` satisfy the fifth-order equation (`l5_fB`, `l5_gB`), and for `f` its Hankel dual holds
at fixed `x` (`hk_relation_F`, waves 30 and 31).  **Waves 32 to 38 proved `ZhouF`** (`zhouF`),
with `∫₀^∞ t I₀(t)K₀(t)³ dt = π²/16` (`integral_t_I0_K0_cube`) on the way, so **`rv6_of_zhou3`**
takes `RungBP` and `ZhouG` only.  Waves 39 to 43 put `ZhouG` on the same road: `uG_eq` (`AJODEG.lean`)
is the dual equation of `ajG` up to one constant, and `uG_zero` (`ZeroG.lean`) sets it to `0`; `vG0_xm_quad` (`PullbackG.lean`) pulls it back to `y`.  **Waves 46 and 47 fixed
the three constants at the two cusps and proved `ZhouG`** (`zhouG`, `ZhouG.lean`), so **`rv6_of_rungBP`**
takes `RungBP` and nothing else.  **Waves 48 to 65 proved `RungBP`** (`rungBP`, `BPAsm.lean`), on the
Bessel side and with real variables only: two integrations by parts and the product formula of `J₀`
turn `pairS` into `j(s) ∫∫ F₂(τ) G(t) (min^s - k_H)`; the `min^s` part is `s B(s)` with
`B = (4/5) P + (3/5) s M₃₅`; the remainder `H(s)` equals the closed-form model `H_m(s)` up to `K s²`;
and `ζ(5)` enters through `s j(s) = 2^{-s} Γ(1 - s/2)/Γ(1 + s/2)` and the identity
`Λ(0) + Λ(-s) = Φ(s)`.  So **`rv6`** has no hypotheses.  `ROADMAP.md` has the plan and the history by rung.

## Not here yet

* the finite census of genus-0 subgroups of `PSL₂(ℤ/15)` and `PSL₂(ℤ/30)`.

## Building

```
lake update
lake exe cache get
lake build
```

Toolchain: Lean `v4.36.0`, Mathlib `v4.36.0`.
