import Mathlib
import Tower.RV6.FrickeAx

/-!
# The function `x(y)` of the change of variable in Rung B

`xm y = 8 exp((lgU y - lgZ y)/2)`, which is `8 √(Uax/Zax)` (`xm_sq`) and whose logarithm is the
explicit series `log 8 - πy + 3 (qb(y) - qb(2y) + qb(3y) - qb(6y))` (`log_xm`).

* `hasDerivAt_xm : xm' = -(π/4) Pax xm`, so `xm` is strictly decreasing (`strictAntiOn_xm`);
* `xm_mul_fricke : xm y · xm (1/(6y)) = 8`;
* the cusps: `e^{πy} xm y → 8` and `xm → 0` as `y → +∞`; `xm → +∞` as `y → 0+`;
* `image_xm : xm '' (0, ∞) = (0, ∞)`.
-/

namespace Tower.RV6

open Real

/-- `x(y) = 8 √(U(iy)/Z(iy))`, written with the exponential forms of `EtaForm.lean`. -/
noncomputable def xm (y : ℝ) : ℝ := 8 * Real.exp ((lgU y - lgZ y) / 2)

theorem xm_pos (y : ℝ) : 0 < xm y := mul_pos (by norm_num) (Real.exp_pos _)

theorem xm_sq {y : ℝ} (hy : 0 < y) : xm y ^ 2 = 64 * Uax y / Zax y := by
  have hX : Real.exp ((lgU y - lgZ y) / 2) * Real.exp ((lgU y - lgZ y) / 2)
      = Real.exp (lgU y) * Real.exp (-lgZ y) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hinv : Real.exp (-lgZ y) = (Real.exp (lgZ y))⁻¹ := Real.exp_neg _
  unfold xm
  rw [Uax_eq_exp hy, Zax_eq_exp hy]
  linear_combination 64 * hX + 64 * Real.exp (lgU y) * hinv

theorem log_xm (y : ℝ) :
    Real.log (xm y)
      = Real.log 8 - π * y + 3 * (qb y - qb (2 * y) + qb (3 * y) - qb (6 * y)) := by
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  unfold xm
  rw [Real.log_mul h8 (Real.exp_pos _).ne', Real.log_exp]
  unfold lgU lgUr lgZ
  ring

/-- `x' = -(π/4) P x`. -/
theorem hasDerivAt_xm {y : ℝ} (hy : 0 < y) : HasDerivAt xm (-(π / 4) * Pax y * xm y) y := by
  have h1 := (hasDerivAt_lgU hy).sub (hasDerivAt_lgZ hy)
  have h2 := h1.div_const 2
  have h3 := h2.exp
  have h4 := h3.const_mul 8
  have h5 : HasDerivAt xm
      (8 * (Real.exp ((lgU y - lgZ y) / 2)
        * ((-(2 * π) * (Eax y + Pax y / 4) - -(2 * π) * Eax y) / 2))) y := h4
  have e : 8 * (Real.exp ((lgU y - lgZ y) / 2)
        * ((-(2 * π) * (Eax y + Pax y / 4) - -(2 * π) * Eax y) / 2))
      = -(π / 4) * Pax y * xm y := by
    unfold xm
    ring
  exact h5.congr_deriv e

/-- **The Fricke symmetry of `x`:** `x(y) x(1/(6y)) = 8`. -/
theorem xm_mul_fricke {y : ℝ} (hy : 0 < y) : xm y * xm (1 / (6 * y)) = 8 := by
  have hw : 0 < 1 / (6 * y) := one_div_pos.mpr (mul_pos (by norm_num) hy)
  have hZy := Zax_pos hy
  have hZw := Zax_pos hw
  have hUy := Uax_pos hy
  have hUw := Uax_pos hw
  have A : xm y ^ 2 * Zax y = 64 * Uax y := by
    rw [xm_sq hy]
    exact div_mul_cancel₀ _ hZy.ne'
  have B : xm (1 / (6 * y)) ^ 2 * Zax (1 / (6 * y)) = 64 * Uax (1 / (6 * y)) := by
    rw [xm_sq hw]
    exact div_mul_cancel₀ _ hZw.ne'
  have F1 := Zax_fricke hy
  have F2 := Uax_fricke hy
  have h6 : (6 * y) * (6 * y)⁻¹ = 1 := mul_inv_cancel₀ (mul_pos (by norm_num) hy).ne'
  have H : 1 / (6 * y) * y = 1 / 6 := by linear_combination (1 / 6 : ℝ) * h6
  have hT : 64 * Uax y * Uax (1 / (6 * y)) * ((xm y * xm (1 / (6 * y))) ^ 2 - 64) = 0 := by
    linear_combination
      (-(xm y ^ 2 * xm (1 / (6 * y)) ^ 2 * Zax (1 / (6 * y)))) * F2
      + (-(48 * xm y ^ 2 * xm (1 / (6 * y)) ^ 2 * (1 / (6 * y)) ^ 2 * Uax (1 / (6 * y)))) * F1
      + (-(2304 * xm y ^ 2 * xm (1 / (6 * y)) ^ 2 * Uax (1 / (6 * y)) * Uax y
          * (1 / (6 * y) * y + 1 / 6))) * H
      + (xm (1 / (6 * y)) ^ 2 * Zax (1 / (6 * y))) * A + (64 * Uax y) * B
  have hne : 64 * Uax y * Uax (1 / (6 * y)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hUy.ne') hUw.ne'
  have hsq : (xm y * xm (1 / (6 * y))) ^ 2 - 64 = 0 := (mul_eq_zero.mp hT).resolve_left hne
  have hp : 0 < xm y * xm (1 / (6 * y)) := mul_pos (xm_pos _) (xm_pos _)
  have hfac : (xm y * xm (1 / (6 * y)) - 8) * (xm y * xm (1 / (6 * y)) + 8) = 0 := by
    linear_combination hsq
  have hpos8 : xm y * xm (1 / (6 * y)) + 8 ≠ 0 :=
    (by linarith : (0 : ℝ) < xm y * xm (1 / (6 * y)) + 8).ne'
  have h0 := (mul_eq_zero.mp hfac).resolve_right hpos8
  linarith

/-- `x` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_xm : StrictAntiOn xm (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun t ht => (hasDerivAt_xm (Set.mem_Ioi.mp ht)).continuousAt.continuousWithinAt)
    (fun t ht => ?_)
  rw [interior_Ioi] at ht
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  rw [(hasDerivAt_xm ht0).deriv]
  have hP := Pax_pos ht0
  have hx := xm_pos t
  nlinarith [mul_pos (mul_pos Real.pi_pos hP) hx]

/-! ## The two cusps -/

/-- `e^{πy} x(y) → 8` as `y → +∞`. -/
theorem tendsto_exp_mul_xm :
    Filter.Tendsto (fun y : ℝ => Real.exp (π * y) * xm y) Filter.atTop (nhds 8) := by
  have hr : Filter.Tendsto (fun y : ℝ => (lgUr y - lgZ y) / 2) Filter.atTop
      (nhds ((0 - 0) / 2)) := (tendsto_lgUr_atTop.sub tendsto_lgZ_atTop).div_const 2
  have he0 := (Real.continuous_exp.tendsto ((0 - 0) / 2)).comp hr
  have he : Filter.Tendsto (fun y : ℝ => Real.exp ((lgUr y - lgZ y) / 2)) Filter.atTop
      (nhds (Real.exp ((0 - 0) / 2))) := he0
  have hm : Filter.Tendsto (fun y : ℝ => 8 * Real.exp ((lgUr y - lgZ y) / 2)) Filter.atTop
      (nhds (8 * Real.exp ((0 - 0) / 2))) := he.const_mul 8
  have e : (8 : ℝ) * Real.exp ((0 - 0) / 2) = 8 := by
    rw [sub_self, zero_div, Real.exp_zero, mul_one]
  rw [e] at hm
  refine hm.congr (fun y => ?_)
  show 8 * Real.exp ((lgUr y - lgZ y) / 2) = Real.exp (π * y) * xm y
  have hk : Real.exp (π * y) * Real.exp ((lgU y - lgZ y) / 2)
      = Real.exp ((lgUr y - lgZ y) / 2) := by
    rw [← Real.exp_add]
    congr 1
    unfold lgU
    ring
  unfold xm
  linear_combination (-8 : ℝ) * hk

/-- `x(y) → 0` as `y → +∞`. -/
theorem tendsto_xm_atTop : Filter.Tendsto xm Filter.atTop (nhds 0) := by
  have hlin : Filter.Tendsto (fun y : ℝ => π * y) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop Real.pi_pos Filter.tendsto_id
  have h1' := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have h1 : Filter.Tendsto (fun y : ℝ => Real.exp (-(π * y))) Filter.atTop (nhds 0) := h1'
  have h2 := h1.mul tendsto_exp_mul_xm
  have h3 : Filter.Tendsto (fun y : ℝ => Real.exp (-(π * y)) * (Real.exp (π * y) * xm y))
      Filter.atTop (nhds (0 * 8)) := h2
  rw [zero_mul] at h3
  refine h3.congr (fun y => ?_)
  show Real.exp (-(π * y)) * (Real.exp (π * y) * xm y) = xm y
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- `x(y) → +∞` as `y → 0+`. -/
theorem tendsto_xm_zero : Filter.Tendsto xm (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have hinv : Filter.Tendsto (fun y : ℝ => y⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have hw0 : Filter.Tendsto (fun y : ℝ => 6⁻¹ * y⁻¹) (nhdsWithin 0 (Set.Ioi 0))
      Filter.atTop := Filter.Tendsto.const_mul_atTop (by norm_num) hinv
  have hw : Filter.Tendsto (fun y : ℝ => 1 / (6 * y)) (nhdsWithin 0 (Set.Ioi 0))
      Filter.atTop := by
    refine hw0.congr (fun y => ?_)
    show 6⁻¹ * y⁻¹ = 1 / (6 * y)
    ring
  have hx0 : Filter.Tendsto (fun y : ℝ => xm (1 / (6 * y))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := tendsto_xm_atTop.comp hw
  have hx : Filter.Tendsto (fun y : ℝ => xm (1 / (6 * y))) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hx0, Filter.Eventually.of_forall (fun y => Set.mem_Ioi.mpr (xm_pos _))⟩
  have hi := hx.inv_tendsto_nhdsGT_zero
  have h8 := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 8) hi
  refine Filter.Tendsto.congr' ?_ h8
  filter_upwards [eventually_mem_nhdsWithin] with y hy
  have hy0 : 0 < y := Set.mem_Ioi.mp hy
  show 8 * (xm (1 / (6 * y)))⁻¹ = xm y
  have hf := xm_mul_fricke hy0
  have hI : xm (1 / (6 * y)) * (xm (1 / (6 * y)))⁻¹ = 1 :=
    mul_inv_cancel₀ (xm_pos (1 / (6 * y))).ne'
  linear_combination (xm y) * hI - (xm (1 / (6 * y)))⁻¹ * hf

/-- **`x` maps `(0, ∞)` onto `(0, ∞)`.** -/
theorem image_xm : xm '' Set.Ioi 0 = Set.Ioi 0 := by
  ext v
  constructor
  · rintro ⟨y, -, rfl⟩
    exact Set.mem_Ioi.mpr (xm_pos y)
  · intro hv
    have hv0 : 0 < v := Set.mem_Ioi.mp hv
    have ev1 : ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioi 0), v < xm y ∧ y ∈ Set.Ioi 0 :=
      (tendsto_xm_zero.eventually (Filter.eventually_gt_atTop v)).and eventually_mem_nhdsWithin
    obtain ⟨a, hav, ha⟩ := ev1.exists
    have ha0 : 0 < a := Set.mem_Ioi.mp ha
    have ev2 : ∀ᶠ y in Filter.atTop, xm y < v ∧ a ≤ y :=
      (tendsto_xm_atTop.eventually (gt_mem_nhds hv0)).and (Filter.eventually_ge_atTop a)
    obtain ⟨b, hbv, hab⟩ := ev2.exists
    have hcont : ContinuousOn xm (Set.Icc a b) := fun t ht =>
      (hasDerivAt_xm (lt_of_lt_of_le ha0 ht.1)).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hxc⟩ := intermediate_value_Icc' hab hcont ⟨hbv.le, hav.le⟩
    exact ⟨c, Set.mem_Ioi.mpr (lt_of_lt_of_le ha0 hc.1), hxc⟩

end Tower.RV6
