import Mathlib
import Tower.RV6.CuspG
import Tower.RV6.C4
import Tower.RV6.ModAxis

/-!
# `ZhouG`, and the six-step theorem from `RungBP` alone

* `hasDerivAt_ajG_xm`: `d/dy ajG(xm y) = -(π²/2) y g₄(y)` (R1, `v₀(xm y) = (π/4) y Zax y`, `xm² Zax = 64 Uax`,
  `g₄ = 8 Uax Pax`);
* `integrableOn_mul_g4`: `t g₄(t)` is integrable on `(y, ∞)`; `tendsto_ajG_xm`: `ajG(xm y) → 0`;
* **`zhouG`**: `ajG(xm y) = (π²/2) 𝒜₁(y)` for `y > 0`;
* **`rv6_of_rungBP`**: `μ₆ = (648/π⁶) L(f, 5)` from `RungBP` alone.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

theorem hasDerivAt_ajG_xm {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => ajG (xm y)) (-(π ^ 2 / 2) * (y * g4 y)) y := by
  have hX := xm_pos y
  have h1 := hasDerivAt_AJ_thG0 hX
  have h := h1.comp y (hasDerivAt_xm hy)
  have h' : HasDerivAt (fun y : ℝ => AJ thG0 (xm y))
      (-(AJ thG1 (xm y)) / xm y * (-(π / 4) * Pax y * xm y)) y := h
  have hfun : (fun y : ℝ => ajG (xm y)) = fun y : ℝ => AJ thG0 (xm y) := by
    rw [ajG_eq_AJ, thG0_eq_gB]
  rw [hfun]
  refine h'.congr_deriv ?_
  have hv := vG0_eq hy
  have hZ := Zax_pos hy
  have hg := g4_eq_UP hy
  have hxi : xm y * (xm y)⁻¹ = 1 := mul_inv_cancel₀ hX.ne'
  have hv' : -(AJ thG1 (xm y)) = π / 4 * y * Zax y * xm y ^ 2 := by
    unfold vG0 at hv
    rw [div_eq_iff (pow_ne_zero 2 hX.ne')] at hv
    exact hv
  have hx2' : xm y ^ 2 * Zax y = 64 * Uax y := by
    rw [xm_sq hy, div_mul_cancel₀ _ hZ.ne']
  linear_combination (π / 4 * Pax y * AJ thG1 (xm y)) * hxi + (-(π / 4 * Pax y)) * hv'
    + (-(π ^ 2 / 16 * Pax y * y)) * hx2' + (π ^ 2 / 2 * y) * hg

theorem integrableOn_mul_g4 {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => t * g4 t) (Set.Ioi y) := by
  have h : IntegrableOn (fun t : ℝ => 32 * (t * qa (sig 3) t) + (-32) * (t * qa (sig 3) (2 * t))
      + (-288) * (t * qa (sig 3) (3 * t)) + 288 * (t * qa (sig 3) (6 * t))) (Set.Ioi y) := by
    have h3 := integrable_lin3 (integrableOn_Tint hy)
      (integrableOn_mul_qa_scale (by norm_num : (0 : ℝ) < 2) hy)
      (integrableOn_mul_qa_scale (by norm_num : (0 : ℝ) < 3) hy) 32 (-32) (-288)
    exact h3.add (Integrable.const_mul (integrableOn_mul_qa_scale (by norm_num : (0 : ℝ) < 6) hy) 288)
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := lt_trans hy ht
  show 32 * (t * qa (sig 3) t) + (-32) * (t * qa (sig 3) (2 * t))
      + (-288) * (t * qa (sig 3) (3 * t)) + 288 * (t * qa (sig 3) (6 * t)) = t * g4 t
  rw [g4_eq_g4E ht0, g4E_eq_qa ht0]
  ring

theorem tendsto_ajG_xm : Tendsto (fun y : ℝ => ajG (xm y)) atTop (nhds 0) := by
  have hb : Tendsto (fun y : ℝ => xm y * ∫ t in Set.Ioi (0 : ℝ), |thG0 t|) atTop (nhds 0) := by
    have h := tendsto_xm_atTop.mul_const (∫ t in Set.Ioi (0 : ℝ), |thG0 t|)
    rw [zero_mul] at h
    exact h
  refine squeeze_zero_norm' ?_ hb
  filter_upwards with y
  have h := abs_AJ_le pdom_thG0 (xm_pos y)
  have e : ajG (xm y) = AJ thG0 (xm y) := by rw [ajG_eq_AJ, thG0_eq_gB]
  rw [Real.norm_eq_abs, e]
  exact h

/-- **`ZhouG`**: `ajG(xm y) = (π²/2) 𝒜₁(y)` for `y > 0`. -/
theorem zhouG : ZhouG := by
  intro y hy
  have hint : IntegrableOn (fun s : ℝ => -(π ^ 2 / 2) * (s * g4 s)) (Set.Ioi y) :=
    Integrable.const_mul (integrableOn_mul_g4 hy) _
  have hc : ContinuousWithinAt (fun y : ℝ => ajG (xm y)) (Set.Ici y) y :=
    (hasDerivAt_ajG_xm hy).continuousAt.continuousWithinAt
  have hd : ∀ s ∈ Set.Ioi y, HasDerivAt (fun y : ℝ => ajG (xm y)) (-(π ^ 2 / 2) * (s * g4 s)) s :=
    fun s hs => hasDerivAt_ajG_xm (lt_trans hy hs)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc hd hint tendsto_ajG_xm
  rw [integral_const_mul] at h
  show ajG (xm y) = π ^ 2 / 2 * ∫ t in Set.Ioi y, t * g4 t
  linarith

/-- **The six-step theorem from `RungBP` alone**: `μ₆ = (648/π⁶) L(f, 5)`. -/
theorem rv6_of_rungBP (hP : RungBP) : mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_zhou3 hP zhouG

end Tower.RV6
