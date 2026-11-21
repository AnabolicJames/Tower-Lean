# Tower-Lean

Lean 4 / Mathlib formalisation of results from the random-walk Mahler-measure programme
(James Anderson-Joyce).  Every statement in this repository is checked by the Lean kernel on
each push; the build status of the latest commit is the status of the mathematics.

## What is here

| File | Content | Status |
|---|---|---|
| `Tower/TangentLine/Resultant.lean` | Elimination and factorisation for the tangent lines of the level-15 branch sextic through a node: `Res = (1 + w) x³ (x² + 1)² (x + 1) Q₄(x)` | checked |
| `Tower/TangentLine/ModP.lean` | `Q₄` splits completely over `𝔽₁₀₃` (cube root of unity `56`, roots `2, 41, 99, 100`) | checked |
| `Tower/EC/Cert.lean` | Slope certificates for Mathlib's group law on a Weierstrass curve | |
| `Tower/TangentLine/Orders103.lean`, `Orders373.lean` | The four points over the roots of `Q₄` in `E(𝔽₁₀₃)` and `E(𝔽₃₇₃)`: `n • P = 0` and `(n/q) • P ≠ 0` for every prime `q ∣ n`, with `n = 120, 40, 24, 6` and `400, 400, 400, 80` | |

## What is not here yet

* the conclusion that the points over the roots of `Q₄` have infinite order (this needs
  injectivity of reduction on torsion, which will enter as a stated hypothesis until it is
  available in Mathlib);
* the finite census of genus-0 subgroups of `PSL₂(ℤ/15)` and `PSL₂(ℤ/30)`;
* the six-step evaluation `m(1 + x₁ + ⋯ + x₅) = 648 L(f, 5)/π⁶`.

## Building

```
lake update
lake exe cache get
lake build
```

Toolchain: Lean `v4.36.0`, Mathlib `v4.36.0`.
