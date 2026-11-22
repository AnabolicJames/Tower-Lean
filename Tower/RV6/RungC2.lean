import Mathlib
import Tower.RV6.Defs
import Tower.RV6.Ladder
import Tower.RV6.Fricke6
import Tower.RV6.DEInv
import Tower.RV6.PsiW

/-!
# Rung C2″: the non-constant Fricke part as a Mellin transform at the cusp

`J₁ = ∫₀^∞ y⁻³ 𝔉(i/(6y)) (D𝔊)(iy) dy` and `J₂ = ∫₀^∞ y⁻⁴ 𝔉(i/(6y)) 𝔊(iy) dy` are carried to the
cusp `∞` by `y ↦ 1/(6y)` (`fricke_subst`), where `𝔊(i/(6x))` and `(D𝔊)(i/(6x))` are polynomials in
`x`, `𝔉(ix)`, `(D𝔉)(ix)` (`Gcal_fricke`, `DGcal_fricke`):

* `J2_eq_moments`: `J₂ = 6 (-M₂ + 26 L₅(𝔉) - 24 L₅(𝔉²))`;
* `J1_eq_moments`: `J₁ = 6 ((26/π) L₅(𝔉) - (24/π) L₅(𝔉²) + 24 M₅)`.

With `M₂ = 0`, `L₅(𝔉) = ζ(5)/(144π)`, `M₅ = (5/(4π)) L₅(𝔉²)` and the split of `Λ(Ψ^W, 5)`
(`PsiW.lean`) the unknown `L₅(𝔉²)` cancels:

**`rungC2W`:  `(64/9)(J₁/(2π) + J₂/(4π²)) = (104/(27π³) + 12/(5π⁵)) ζ(5) + (1152/(5π²)) Λ(Ψ^W, 5)`.**
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `J₂ = 6 (-M₂ + 26 L₅(𝔉) - 24 L₅(𝔉²))`. -/
theorem J2_eq_moments : J2 = 6 * (-M2F + 26 * L5F - 24 * L5F2) := by
  have h1 : J2 = ∫ y in Set.Ioi (0 : ℝ),
      (Fcal (1 / (6 * y)) * Gcal (1 / (6 * (1 / (6 * y)))) * (6 * (1 / (6 * y))) ^ 2) / y ^ 2 := by
    unfold J2
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    show Fcal (1 / (6 * y)) * Gcal y / y ^ 4
      = (Fcal (1 / (6 * y)) * Gcal (1 / (6 * (1 / (6 * y)))) * (6 * (1 / (6 * y))) ^ 2) / y ^ 2
    have e1 : 1 / (6 * (1 / (6 * y))) = y := by
      rw [mul_one_div, one_div_div]
      ring
    have e2 : 6 * (1 / (6 * y)) = 1 / y := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [e1, e2]
    ring
  have h2 : ∫ y in Set.Ioi (0 : ℝ),
        (Fcal (1 / (6 * y)) * Gcal (1 / (6 * (1 / (6 * y)))) * (6 * (1 / (6 * y))) ^ 2) / y ^ 2
      = 6 * ∫ x in Set.Ioi (0 : ℝ), Fcal x * Gcal (1 / (6 * x)) * (6 * x) ^ 2 :=
    fricke_subst (fun x : ℝ => Fcal x * Gcal (1 / (6 * x)) * (6 * x) ^ 2)
  have h3 : ∫ x in Set.Ioi (0 : ℝ), Fcal x * Gcal (1 / (6 * x)) * (6 * x) ^ 2
      = ∫ x in Set.Ioi (0 : ℝ), ((-1) * (Fcal x * x ^ 2) + 26 * (Fcal x * x ^ 4)
          + (-24) * (Fcal x ^ 2 * x ^ 4)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    show Fcal x * Gcal (1 / (6 * x)) * (6 * x) ^ 2
      = (-1) * (Fcal x * x ^ 2) + 26 * (Fcal x * x ^ 4) + (-24) * (Fcal x ^ 2 * x ^ 4)
    rw [Gcal_fricke hx0]
    ring
  have h4 := integral_lin3 integrable_F_pow2 integrable_F_pow4 integrable_Fsq (-1 : ℝ) 26 (-24)
  rw [h1, h2, h3, h4]
  unfold M2F L5F L5F2
  ring

/-- `J₁ = 6 ((26/π) L₅(𝔉) - (24/π) L₅(𝔉²) + 24 M₅)`. -/
theorem J1_eq_moments : J1 = 6 * (26 / π * L5F - 24 / π * L5F2 + 24 * M5F) := by
  have h1 : J1 = ∫ y in Set.Ioi (0 : ℝ),
      (Fcal (1 / (6 * y)) * DGcal (1 / (6 * (1 / (6 * y)))) * (6 * (1 / (6 * y)))) / y ^ 2 := by
    unfold J1
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    show Fcal (1 / (6 * y)) * DGcal y / y ^ 3
      = (Fcal (1 / (6 * y)) * DGcal (1 / (6 * (1 / (6 * y)))) * (6 * (1 / (6 * y)))) / y ^ 2
    have e1 : 1 / (6 * (1 / (6 * y))) = y := by
      rw [mul_one_div, one_div_div]
      ring
    have e2 : 6 * (1 / (6 * y)) = 1 / y := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [e1, e2]
    ring
  have h2 : ∫ y in Set.Ioi (0 : ℝ),
        (Fcal (1 / (6 * y)) * DGcal (1 / (6 * (1 / (6 * y)))) * (6 * (1 / (6 * y)))) / y ^ 2
      = 6 * ∫ x in Set.Ioi (0 : ℝ), Fcal x * DGcal (1 / (6 * x)) * (6 * x) :=
    fricke_subst (fun x : ℝ => Fcal x * DGcal (1 / (6 * x)) * (6 * x))
  have h3 : ∫ x in Set.Ioi (0 : ℝ), Fcal x * DGcal (1 / (6 * x)) * (6 * x)
      = ∫ x in Set.Ioi (0 : ℝ), (26 / π * (Fcal x * x ^ 4) + (-(24 / π)) * (Fcal x ^ 2 * x ^ 4)
          + 24 * (Fcal x * DFcal x * x ^ 5)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    show Fcal x * DGcal (1 / (6 * x)) * (6 * x)
      = 26 / π * (Fcal x * x ^ 4) + (-(24 / π)) * (Fcal x ^ 2 * x ^ 4)
        + 24 * (Fcal x * DFcal x * x ^ 5)
    rw [DGcal_fricke hx0]
    ring
  have h4 := integral_lin3 integrable_F_pow4 integrable_Fsq integrable_FDF (26 / π) (-(24 / π)) 24
  rw [h1, h2, h3, h4]
  unfold M5F L5F L5F2
  ring

/-- **Rung C2″.**  The non-constant Fricke part of the double Eisenstein integral. -/
theorem rungC2W :
    crossTerm = 104 / (27 * π ^ 3) * zeta5 + 12 / (5 * π ^ 5) * zeta5
      + 1152 / (5 * π ^ 2) * LambdaPsiW5 := by
  have hJ1 := J1_eq_moments
  have hJ2 := J2_eq_moments
  have hM2 := M2F_eq
  have hM5 := M5F_eq
  have hL := L5F_eq
  have hS := lambdaPsiW5_split
  unfold crossTerm
  linear_combination (32 / 9 * π⁻¹) * hJ1 + (16 / 9 * π⁻¹ ^ 2) * hJ2
    + (-(32 / 3) * π⁻¹ ^ 2) * hM2 + (512 * π⁻¹) * hM5 + (1664 / 3 * π⁻¹ ^ 2) * hL
    + (-(1152 / 5) * π⁻¹ ^ 2) * hS

end Tower.RV6
