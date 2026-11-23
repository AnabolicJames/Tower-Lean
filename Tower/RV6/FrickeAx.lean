import Mathlib
import Tower.RV6.EtaForm

/-!
# The Fricke involution `y ↦ 1/(6y)` on `Zax`, `Uax`, `Pax`, and the sign of `Pax`

From `E₂(i/t) = -t² E₂(it) + 6t/π` (`E2im_inv` of `EisAxis.lean`) at `t = 6w, 3w, 2w, w`:

* `Zax_fricke : Zax (1/(6w)) = 48 w² Uax w`, and `Uax_fricke : Zax w = 48 (1/(6w))² Uax (1/(6w))`;
* `Pax_fricke : Pax (1/(6w)) = 6 w² Pax w`.

`Pax` has no zero (`Pax_ne_zero`, from `Pax² = 16 Z² + 320 Z U + 1024 U²` and `Z, U > 0`), is
continuous on `(0, ∞)` and tends to `4` at `+∞` (`tendsto_Pax_atTop`); so `Pax_pos`.
-/

namespace Tower.RV6

open Real

/-- `Zax (1/(6w)) = 48 w² Uax w`. -/
theorem Zax_fricke {w : ℝ} (hw : 0 < w) : Zax (1 / (6 * w)) = 48 * w ^ 2 * Uax w := by
  have h1 := E2im_inv (y := 6 * w) (mul_pos (by norm_num) hw)
  have h2 := E2im_inv (y := 3 * w) (mul_pos (by norm_num) hw)
  have h3 := E2im_inv (y := 2 * w) (mul_pos (by norm_num) hw)
  have h6 := E2im_inv (y := w) hw
  have a2 : 2 * (1 / (6 * w)) = 1 / (3 * w) := by ring
  have a3 : 3 * (1 / (6 * w)) = 1 / (2 * w) := by ring
  have a6 : 6 * (1 / (6 * w)) = 1 / w := by ring
  unfold Zax Uax
  rw [a2, a3, a6, h1, h2, h3, h6]
  ring

/-- `Zax w = 48 (1/(6w))² Uax (1/(6w))`. -/
theorem Uax_fricke {w : ℝ} (hw : 0 < w) :
    Zax w = 48 * (1 / (6 * w)) ^ 2 * Uax (1 / (6 * w)) := by
  have hw' : 0 < 1 / (6 * w) := one_div_pos.mpr (mul_pos (by norm_num) hw)
  have h := Zax_fricke hw'
  have e : 1 / (6 * (1 / (6 * w))) = w := by
    rw [mul_one_div, one_div_div]
    ring
  rw [e] at h
  exact h

/-- `Pax (1/(6w)) = 6 w² Pax w`. -/
theorem Pax_fricke {w : ℝ} (hw : 0 < w) : Pax (1 / (6 * w)) = 6 * w ^ 2 * Pax w := by
  have h1 := E2im_inv (y := 6 * w) (mul_pos (by norm_num) hw)
  have h2 := E2im_inv (y := 3 * w) (mul_pos (by norm_num) hw)
  have h3 := E2im_inv (y := 2 * w) (mul_pos (by norm_num) hw)
  have h6 := E2im_inv (y := w) hw
  have a2 : 2 * (1 / (6 * w)) = 1 / (3 * w) := by ring
  have a3 : 3 * (1 / (6 * w)) = 1 / (2 * w) := by ring
  have a6 : 6 * (1 / (6 * w)) = 1 / w := by ring
  unfold Pax
  rw [a2, a3, a6, h1, h2, h3, h6]
  ring

/-! ## The sign of `Pax` -/

theorem Pax_eq_lin (y : ℝ) :
    Pax y = -1 * E2im y + 2 * E2im (2 * y) + -3 * E2im (3 * y) + 6 * E2im (6 * y) := by
  unfold Pax
  ring

theorem continuousAt_Pax {y : ℝ} (hy : 0 < y) : ContinuousAt Pax y := by
  have h1 := hasDerivAt_E2im hy
  have h2 := hasDerivAt_E2im_mul 2 (by norm_num) hy
  have h3 := hasDerivAt_E2im_mul 3 (by norm_num) hy
  have h6 := hasDerivAt_E2im_mul 6 (by norm_num) hy
  have k := hasDerivAt_lin4 (-1) 2 (-3) 6 h1 h2 h3 h6
  have hf : Pax = fun t : ℝ =>
      -1 * E2im t + 2 * E2im (2 * t) + -3 * E2im (3 * t) + 6 * E2im (6 * t) :=
    funext Pax_eq_lin
  rw [hf]
  exact k.continuousAt

/-- `Pax → 4` at the cusp. -/
theorem tendsto_Pax_atTop : Filter.Tendsto Pax Filter.atTop (nhds 4) := by
  have h1 := tendsto_E2im_atTop
  have h2 := tendsto_comp_mul_atTop tendsto_E2im_atTop 2 (by norm_num)
  have h3 := tendsto_comp_mul_atTop tendsto_E2im_atTop 3 (by norm_num)
  have h6 := tendsto_comp_mul_atTop tendsto_E2im_atTop 6 (by norm_num)
  have k1 : Filter.Tendsto (fun y : ℝ => -E2im y) Filter.atTop (nhds (-1)) := h1.neg
  have k2 : Filter.Tendsto (fun y : ℝ => -E2im y + 2 * E2im (2 * y)) Filter.atTop
      (nhds (-1 + 2 * 1)) := k1.add (h2.const_mul 2)
  have k3 : Filter.Tendsto (fun y : ℝ => -E2im y + 2 * E2im (2 * y) - 3 * E2im (3 * y))
      Filter.atTop (nhds (-1 + 2 * 1 - 3 * 1)) := k2.sub (h3.const_mul 3)
  have k4 : Filter.Tendsto
      (fun y : ℝ => -E2im y + 2 * E2im (2 * y) - 3 * E2im (3 * y) + 6 * E2im (6 * y))
      Filter.atTop (nhds (-1 + 2 * 1 - 3 * 1 + 6 * 1)) := k3.add (h6.const_mul 6)
  have e : (-1 : ℝ) + 2 * 1 - 3 * 1 + 6 * 1 = 4 := by norm_num
  rw [e] at k4
  exact k4

theorem Pax_ne_zero {y : ℝ} (hy : 0 < y) : Pax y ≠ 0 := by
  intro h0
  have hs := Pax_sq hy
  have hZ := Zax_pos hy
  have hU := Uax_pos hy
  rw [h0] at hs
  nlinarith [mul_pos hZ hZ, mul_pos hZ hU, mul_pos hU hU]

/-- **`Pax > 0` on `(0, ∞)`.** -/
theorem Pax_pos {y : ℝ} (hy : 0 < y) : 0 < Pax y := by
  have hev : ∀ᶠ t in Filter.atTop, (0 : ℝ) < Pax t :=
    tendsto_Pax_atTop.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 4))
  obtain ⟨b, hb0, hby⟩ := (hev.and (Filter.eventually_ge_atTop y)).exists
  rcases lt_or_gt_of_ne (Pax_ne_zero hy) with hneg | hpos
  · exfalso
    have hcont : ContinuousOn Pax (Set.Icc y b) := fun t ht =>
      (continuousAt_Pax (lt_of_lt_of_le hy ht.1)).continuousWithinAt
    have hivt := intermediate_value_Icc hby hcont
    have h0 : (0 : ℝ) ∈ Set.Icc (Pax y) (Pax b) := ⟨hneg.le, hb0.le⟩
    obtain ⟨c, hc, hPc⟩ := hivt h0
    exact Pax_ne_zero (lt_of_lt_of_le hy hc.1) hPc
  · exact hpos

end Tower.RV6
