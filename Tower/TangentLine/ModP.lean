import Mathlib
import Tower.TangentLine.Resultant

/-!
# The quartic `Q₄` modulo primes

Data for the reduction argument: at a prime `p ≡ 1 (mod 3)` with a primitive cube root of
unity `z ∈ 𝔽_p`, the quartic `Q₄(t) = t⁴ + (2 + 3z) t³ - t² + (2 + z) t + (1 + z)` may split
completely.  This file records, checked by the kernel, the first such prime.
-/

namespace Tower.TangentLine

/-- `56` is a primitive cube root of unity in `𝔽₁₀₃`. -/
theorem cubeRoot_103 : (56 : ZMod 103) ^ 2 + 56 + 1 = 0 := by decide

set_option maxRecDepth 100000 in
/-- Over `𝔽₁₀₃` with `w = 56`, the quartic `Q₄` has exactly the four roots `2, 41, 99, 100`. -/
theorem Q4_roots_103 :
    ∀ t : ZMod 103, Q4 t 56 = 0 ↔ (t = 2 ∨ t = 41 ∨ t = 99 ∨ t = 100) := by
  decide

end Tower.TangentLine
