import Mathlib

/-!
# The six-step Mahler measure: objects

Everything needed to state

`m(1 + x₁ + x₂ + x₃ + x₄ + x₅) = (648 / π⁶) · L(f, 5)`,  `f = (η(τ) η(2τ) η(3τ) η(6τ))²`,

and to cut its proof (J. Anderson-Joyce, *Logarithmic Hankel pairings, the six-step Mahler
measure, and sunset endpoint periods*, 2026) at quantities that are convergent integrals or series.

All integrals are Bochner integrals: an integral of a non-integrable function is `0` in Lean.
A statement that equates one of the integrals below with a non-zero number therefore carries
the integrability of its integrand with it.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## The Mahler measure -/

/-- `μ₆ = m(1 + x₁ + ⋯ + x₅)`: the average of `log |1 + e(t₁) + ⋯ + e(t₅)|` over the torus
`[0, 1]⁵`, `e(t) = exp(2πit)`. -/
noncomputable def mu6 : ℝ :=
  ∫ t in Set.Icc (0 : Fin 5 → ℝ) 1,
    Real.log ‖(1 : ℂ) + ∑ j, Complex.exp (2 * π * Complex.I * (t j))‖

/-! ## Bessel functions -/

/-- `I₀(t) = ∑ (t/2)^{2k} / (k!)²`. -/
noncomputable def besselI0 (t : ℝ) : ℝ :=
  ∑' k : ℕ, (t / 2) ^ (2 * k) / ((Nat.factorial k : ℝ) ^ 2)

/-- `I₁(t) = ∑ (t/2)^{2k+1} / (k! (k+1)!)`. -/
noncomputable def besselI1 (t : ℝ) : ℝ :=
  ∑' k : ℕ, (t / 2) ^ (2 * k + 1) / ((Nat.factorial k : ℝ) * (Nat.factorial (k + 1) : ℝ))

/-- `J₀(t) = ∑ (-1)^k (t/2)^{2k} / (k!)²`. -/
noncomputable def besselJ0 (t : ℝ) : ℝ :=
  ∑' k : ℕ, (-1) ^ k * (t / 2) ^ (2 * k) / ((Nat.factorial k : ℝ) ^ 2)

/-- `K₀(t) = ∫₀^∞ exp(-t cosh u) du`. -/
noncomputable def besselK0 (t : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), Real.exp (-t * Real.cosh u)

/-- The regularised Bessel moment `R₆,₂ = FP ∫ I₀² K₀⁴ dt/t`, in its convergent form
`(8/5) ∫₀^∞ I₀² I₁ K₀⁵ dt`. -/
noncomputable def R62 : ℝ :=
  8 / 5 * ∫ t in Set.Ioi (0 : ℝ), besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5

/-- The random-walk side: `log 2 + ∫₀^∞ (e^{-t} - J₀(t)⁶) dt/t`. -/
noncomputable def walkSide : ℝ :=
  Real.log 2 + ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t) - besselJ0 t ^ 6) / t

/-! ## The cusp form and its `L`-value -/

/-- `ζ(5)`, from Mathlib's Riemann zeta function. -/
noncomputable def zeta5 : ℝ := (riemannZeta 5).re

/-- `f(iy)` for `f = (η(τ) η(2τ) η(3τ) η(6τ))²`, with Mathlib's Dedekind eta function.  On the
imaginary axis the product of the four eta values is a positive real number, so `f(iy)` is the
square of its norm. -/
noncomputable def f46 (y : ℝ) : ℝ :=
  ‖ModularForm.eta (y * Complex.I) * ModularForm.eta (2 * y * Complex.I) *
    ModularForm.eta (3 * y * Complex.I) * ModularForm.eta (6 * y * Complex.I)‖ ^ 2

/-- The completed value `Λ(f, 5) = ∫₀^∞ f(iy) y⁴ dy`. -/
noncomputable def Lambda5 : ℝ := ∫ y in Set.Ioi (0 : ℝ), f46 y * y ^ 4

/-- `a(n)`: the coefficient of `qⁿ` in `q ∏_{k ≥ 1} ((1 - q^k)(1 - q^{2k})(1 - q^{3k})(1 - q^{6k}))²`.
Factors with `k > n` do not change it, so the product is cut at `k = n`. -/
noncomputable def aCoeff (n : ℕ) : ℤ :=
  ((Polynomial.X : Polynomial ℤ) * ∏ k ∈ Finset.Icc 1 n,
    ((1 - Polynomial.X ^ k) * (1 - Polynomial.X ^ (2 * k)) * (1 - Polynomial.X ^ (3 * k)) *
      (1 - Polynomial.X ^ (6 * k))) ^ 2).coeff n

/-- `L(f, 5) = ∑ a(n) / n⁵`. -/
noncomputable def Lf5 : ℝ := ∑' n : ℕ, (aCoeff n : ℝ) / (n : ℝ) ^ 5

/-! ## The double Eisenstein integral on `Γ₀(6)` -/

/-- `w(n) = 1 - [2 ∣ n] - 9 [3 ∣ n] + 9 [6 ∣ n]`. -/
def w (n : ℕ) : ℤ :=
  1 - (if 2 ∣ n then 1 else 0) - (if 3 ∣ n then 9 else 0) + (if 6 ∣ n then 9 else 0)

/-- Fourier coefficients of `g₄ = (2/15)(E₄(τ) - E₄(2τ) - 9 E₄(3τ) + 9 E₄(6τ))
= 32 ∑ w(a) b³ q^{ab}`. -/
def c4 (n : ℕ) : ℤ := 32 * ∑ d ∈ n.divisors, w d * ((n / d : ℕ) : ℤ) ^ 3

/-- `g₄(iy)`. -/
noncomputable def g4 (y : ℝ) : ℝ := ∑' n : ℕ, (c4 n : ℝ) * Real.exp (-2 * π * n * y)

/-- `𝒜₁(y) = ∫_y^∞ t g₄(it) dt`. -/
noncomputable def A1 (y : ℝ) : ℝ := ∫ t in Set.Ioi y, t * g4 t

/-- The regularised double Eisenstein integral
`D₀₁ = lim_{ε → 0} (∫_ε^∞ g₄(iy) 𝒜₁(y) dy - 1/(810 ε⁵))`, written as the convergent integral of
`g₄(iy) 𝒜₁(y) - 1/(162 y⁶)`. -/
noncomputable def D01 : ℝ := ∫ y in Set.Ioi (0 : ℝ), (g4 y * A1 y - 1 / (162 * y ^ 6))

/-- `σ₁(n)`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `𝔈(iy) = ∑ σ₁(n) e^{-2πny}`, i.e. `(1 - E₂)/24`. -/
noncomputable def Ecal (y : ℝ) : ℝ := ∑' n : ℕ, (sigma1 n : ℝ) * Real.exp (-2 * π * n * y)

/-- `(q d/dq) 𝔈` at `τ = iy`. -/
noncomputable def DEcal (y : ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * (sigma1 n : ℝ) * Real.exp (-2 * π * n * y)

/-- `𝔉(iy)`, `𝔉 = 𝔈(τ) - 2 𝔈(2τ) - 27 𝔈(3τ) + 54 𝔈(6τ)`. -/
noncomputable def Fcal (y : ℝ) : ℝ :=
  Ecal y - 2 * Ecal (2 * y) - 27 * Ecal (3 * y) + 54 * Ecal (6 * y)

/-- `𝔊(iy)`, `𝔊 = 𝔈(τ) - 2 𝔈(2τ) - (1/3) 𝔈(3τ) + (2/3) 𝔈(6τ)`. -/
noncomputable def Gcal (y : ℝ) : ℝ :=
  Ecal y - 2 * Ecal (2 * y) - 1 / 3 * Ecal (3 * y) + 2 / 3 * Ecal (6 * y)

/-- `((q d/dq) 𝔊)(iy)`. -/
noncomputable def DGcal (y : ℝ) : ℝ :=
  DEcal y - 4 * DEcal (2 * y) - DEcal (3 * y) + 4 * DEcal (6 * y)

/-- `J₁ = ∫₀^∞ y⁻³ 𝔉(i/(6y)) (D𝔊)(iy) dy`. -/
noncomputable def J1 : ℝ := ∫ y in Set.Ioi (0 : ℝ), Fcal (1 / (6 * y)) * DGcal y / y ^ 3

/-- `J₂ = ∫₀^∞ y⁻⁴ 𝔉(i/(6y)) 𝔊(iy) dy`. -/
noncomputable def J2 : ℝ := ∫ y in Set.Ioi (0 : ℝ), Fcal (1 / (6 * y)) * Gcal y / y ^ 4

/-- The non-constant Fricke part of `D₀₁`: `(64/9)(J₁/(2π) + J₂/(4π²))`. -/
noncomputable def crossTerm : ℝ := 64 / 9 * (J1 / (2 * π) + J2 / (4 * π ^ 2))

end Tower.RV6
