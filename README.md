# Tower-Lean

Lean 4 / Mathlib formalisation of results from the random-walk Mahler-measure programme
(James Anderson-Joyce).  Every statement in this repository is checked by the Lean kernel on
each push; the build status of the latest commit is the status of the mathematics.

## What is here

| File | Content | Status |
|---|---|---|
| `Tower/TangentLine/Resultant.lean` | Elimination and factorisation for the tangent lines of the level-15 branch sextic through a node: `Res = (1 + w) x³ (x² + 1)² (x + 1) Q₄(x)` | first push |

## What is not here yet

* the orders of the points over the roots of `Q₄` modulo primes, and the conclusion that they
  have infinite order (this needs injectivity of reduction on torsion, which will enter as a
  stated hypothesis until it is available in Mathlib);
* the finite census of genus-0 subgroups of `PSL₂(ℤ/15)` and `PSL₂(ℤ/30)`;
* the six-step evaluation `m(1 + x₁ + ⋯ + x₅) = 648 L(f, 5)/π⁶`.

## Building

```
lake update
lake exe cache get
lake build
```

Toolchain: Lean `v4.36.0`, Mathlib `v4.36.0`.
