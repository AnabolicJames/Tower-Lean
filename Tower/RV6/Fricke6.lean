import Mathlib
import Tower.RV6.Defs
import Tower.RV6.QSeries

/-!
# The Fricke involution `y ↦ 1/(6y)` on the Eisenstein combinations of level six

Everything here is algebra on top of the two inversion formulas of `EisAxis.lean`.

* `g4E_fricke`: `g₄(iy) = 1/(9y⁴) + (6y)⁻⁴ ĝ*(i/(6y))` for the weight-four combination
  `g4E = (2/15)(E₄(y) - E₄(2y) - 9E₄(3y) + 9E₄(6y))`.
* `Gcal_fricke`: `𝔊(i/(6y)) = -(1 - 26y² + 24y² 𝔉(iy))/36` for the `Fcal`, `Gcal` of `Defs.lean`.
-/

namespace Tower.RV6

open Real

/-- `g₄(iy)` as a combination of Eisenstein series. -/
noncomputable def g4E (y : ℝ) : ℝ :=
  2 / 15 * (E4im y - E4im (2 * y) - 9 * E4im (3 * y) + 9 * E4im (6 * y))

/-- The Fricke image of `g₄` without its constant term `144`. -/
noncomputable def ghatE (x : ℝ) : ℝ :=
  2 / 15 * (9 * E4im x - 144 * E4im (2 * x) - 81 * E4im (3 * x) + 1296 * E4im (6 * x)) - 144

theorem g4E_fricke {y : ℝ} (hy : 0 < y) :
    g4E y = 1 / (9 * y ^ 4) + ghatE (1 / (6 * y)) / (6 * y) ^ 4 := by
  have h1 := E4im_inv (y := 6 * (1 / (6 * y))) (by positivity)
  have h2 := E4im_inv (y := 3 * (1 / (6 * y))) (by positivity)
  have h3 := E4im_inv (y := 2 * (1 / (6 * y))) (by positivity)
  have h6 := E4im_inv (y := 1 / (6 * y)) (by positivity)
  have e1 : 1 / (6 * (1 / (6 * y))) = y := by
    rw [mul_one_div, one_div_div]
    ring
  have e2 : 1 / (3 * (1 / (6 * y))) = 2 * y := by
    rw [mul_one_div, one_div_div]
    ring
  have e3 : 1 / (2 * (1 / (6 * y))) = 3 * y := by
    rw [mul_one_div, one_div_div]
    ring
  have e6 : 1 / (1 / (6 * y)) = 6 * y := one_div_one_div _
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e6] at h6
  unfold g4E ghatE
  rw [h1, h2, h3, h6]
  ring

/-- The series `𝔈` of `Defs.lean` in the notation of `QSeries.lean`. -/
theorem Ecal_eq_qa (y : ℝ) : Ecal y = qa (sig 1) y := by
  unfold Ecal qa
  refine tsum_congr (fun n => ?_)
  have h1 : (sigma1 n : ℝ) = sig 1 n := by simp [sigma1, sig]
  rw [h1]
  congr 2
  ring

theorem E2im_eq_Ecal {y : ℝ} (hy : 0 < y) : E2im y = 1 - 24 * Ecal y := by
  rw [Ecal_eq_qa]
  exact E2im_eq_qa hy

/-- `𝔊(i/(6y)) = -(1 - 26y² + 24y² 𝔉(iy))/36`. -/
theorem Gcal_fricke {y : ℝ} (hy : 0 < y) :
    Gcal (1 / (6 * y)) = -(1 - 26 * y ^ 2 + 24 * y ^ 2 * Fcal y) / 36 := by
  have k1 : 1 - 24 * Ecal (1 / (6 * y))
      = -((6 * y) ^ 2) * (1 - 24 * Ecal (6 * y)) + 6 * (6 * y) / π := by
    have h := E2im_inv (y := 6 * y) (by positivity)
    rw [E2im_eq_Ecal (by positivity : (0 : ℝ) < 1 / (6 * y)),
      E2im_eq_Ecal (by positivity : (0 : ℝ) < 6 * y)] at h
    exact h
  have k2 : 1 - 24 * Ecal (2 * (1 / (6 * y)))
      = -((3 * y) ^ 2) * (1 - 24 * Ecal (3 * y)) + 6 * (3 * y) / π := by
    have h := E2im_inv (y := 3 * y) (by positivity)
    rw [E2im_eq_Ecal (by positivity : (0 : ℝ) < 1 / (3 * y)),
      E2im_eq_Ecal (by positivity : (0 : ℝ) < 3 * y)] at h
    have a : 2 * (1 / (6 * y)) = 1 / (3 * y) := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [a]
    exact h
  have k3 : 1 - 24 * Ecal (3 * (1 / (6 * y)))
      = -((2 * y) ^ 2) * (1 - 24 * Ecal (2 * y)) + 6 * (2 * y) / π := by
    have h := E2im_inv (y := 2 * y) (by positivity)
    rw [E2im_eq_Ecal (by positivity : (0 : ℝ) < 1 / (2 * y)),
      E2im_eq_Ecal (by positivity : (0 : ℝ) < 2 * y)] at h
    have a : 3 * (1 / (6 * y)) = 1 / (2 * y) := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [a]
    exact h
  have k6 : 1 - 24 * Ecal (6 * (1 / (6 * y)))
      = -(y ^ 2) * (1 - 24 * Ecal y) + 6 * y / π := by
    have h := E2im_inv hy
    rw [E2im_eq_Ecal (by positivity : (0 : ℝ) < 1 / y), E2im_eq_Ecal hy] at h
    have a : 6 * (1 / (6 * y)) = 1 / y := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [a]
    exact h
  unfold Gcal Fcal
  linear_combination (-1 / 24 : ℝ) * k1 + (1 / 12 : ℝ) * k2 + (1 / 72 : ℝ) * k3
    + (-1 / 36 : ℝ) * k6

end Tower.RV6
