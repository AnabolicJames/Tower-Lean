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

## The six-step Mahler measure (stated; proof reduced to six rungs)

`m(1 + x₁ + x₂ + x₃ + x₄ + x₅) = (648 / π⁶) L(f, 5)`, `f = (η(τ) η(2τ) η(3τ) η(6τ))²`
(the six-step conjecture of Rodriguez-Villegas; proof: J. Anderson-Joyce, *Logarithmic Hankel
pairings, the six-step Mahler measure, and sunset endpoint periods*, 2026).

| File | Content |
|---|---|
| `Tower/RV6/Defs.lean` | the objects, each a convergent integral or series: the Mahler measure as a torus integral; `I₀`, `I₁`, `J₀`, `K₀`; the Bessel moment `R₆,₂ = (8/5) ∫ I₀² I₁ K₀⁵`; `Λ(f, 5)` from Mathlib's eta function; `L(f, 5)` from the coefficients of the eta product; the regularised double Eisenstein integral `D₀₁` on `Γ₀(6)`; the integrals `J₁`, `J₂` |
| `Tower/RV6/Ladder.lean` | the proof cut into six named propositions (`RungA1`, `RungA2`, `RungB`, `RungC1`, `RungC2`, `RungD`) and **`rv6_of_rungs`**: the rungs imply the theorem |
| `Tower/RV6/BesselAlgebra.lean` | two pieces of the Bessel side that are already proved: the sixth-power identity behind the rotation of `∫ J₀⁶`, and the Wronskian derivative identity behind `R₆,₂ = (8/5) ∫ I₀² I₁ K₀⁵` |

**Status: this is not yet a Lean proof of the theorem.**  A rung is a hypothesis.  What the
kernel has checked is that the six rungs imply the theorem.  Each rung was checked numerically
from the Lean definitions before it was stated (five of them by two independent programs to
`10⁻¹²` or better, the classical random-walk representation by Monte Carlo).  The work ahead is
to discharge the rungs one by one.

## Not here yet

* proofs of the six rungs of `Tower/RV6/Ladder.lean`;
* the finite census of genus-0 subgroups of `PSL₂(ℤ/15)` and `PSL₂(ℤ/30)`.

## Building

```
lake update
lake exe cache get
lake build
```

Toolchain: Lean `v4.36.0`, Mathlib `v4.36.0`.
