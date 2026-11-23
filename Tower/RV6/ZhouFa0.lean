import Mathlib
import Tower.RV6.PullbackF
import Tower.RV6.LimBM

/-!
# The cusp `y → ∞`: `hjF(xm y) = a₀ Zax y`

With `hjF_xm_quad` (`hjF(xm y) = (a + b y + c y²) Zax y`):

* `tendsto_hjF_xm`: `hjF(xm y) → a₀ = hk thF0 0` as `y → ∞` (`hk_taylor` and `xm → 0`);
* `quad_tendsto`: a quadratic with a finite limit at `∞` is that constant;
* **`zhouF_a0`**: `hjF(xm y) = a₀ Zax y` for `y > 0`, with `a₀ = ∫₀^∞ t I₀K₀³ dt` (`hk_thF0_zero`);
* `zhouF_of_const`: `a₀ = π²/16 → ZhouF`, and `rv6_of_a0`: the six-step theorem from `RungBP`,
  `a₀ = π²/16` and `ZhouG`.
-/

namespace Tower.RV6

open Real Filter

/-- `hjF(xm y) → a₀` as `y → ∞`. -/
theorem tendsto_hjF_xm : Tendsto (fun y : ℝ => hk thF0 (xm y)) atTop (nhds (hk thF0 0)) := by
  have hb : ∀ x : ℝ, 0 ≤ x → |hk thF0 x - hk thF0 0|
      ≤ x ^ 2 / 4 * |hk (fun t => t ^ 2 * thF0 t) 0|
        + x ^ 3 * ∫ t in Set.Ioi (0 : ℝ), |t ^ 4 * thF0 t| := by
    intro x hx
    have h := hk_taylor hdom_thF0 hx
    have h4 : 0 ≤ x ^ 2 / 4 := by positivity
    have u1 := mul_le_mul_of_nonneg_left (le_abs_self (hk (fun t => t ^ 2 * thF0 t) 0)) h4
    have u2 := mul_le_mul_of_nonneg_left (neg_abs_le (hk (fun t => t ^ 2 * thF0 t) 0)) h4
    obtain ⟨h1, h2⟩ := abs_le.mp h
    rw [abs_le]
    constructor <;> linarith
  have hg : Tendsto (fun y : ℝ => xm y ^ 2 / 4 * |hk (fun t => t ^ 2 * thF0 t) 0|
      + xm y ^ 3 * ∫ t in Set.Ioi (0 : ℝ), |t ^ 4 * thF0 t|) atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℝ => xm y ^ 2 / 4 * |hk (fun t => t ^ 2 * thF0 t) 0|
        + xm y ^ 3 * ∫ t in Set.Ioi (0 : ℝ), |t ^ 4 * thF0 t|) atTop
        (nhds ((0 : ℝ) ^ 2 / 4 * |hk (fun t => t ^ 2 * thF0 t) 0|
          + (0 : ℝ) ^ 3 * ∫ t in Set.Ioi (0 : ℝ), |t ^ 4 * thF0 t|)) :=
      (((tendsto_xm_atTop.pow 2).div_const 4).mul_const _).add
        ((tendsto_xm_atTop.pow 3).mul_const _)
    have e : (0 : ℝ) ^ 2 / 4 * |hk (fun t => t ^ 2 * thF0 t) 0|
        + (0 : ℝ) ^ 3 * ∫ t in Set.Ioi (0 : ℝ), |t ^ 4 * thF0 t| = 0 := by ring
    rw [e] at h1
    exact h1
  have hd : Tendsto (fun y : ℝ => hk thF0 (xm y) - hk thF0 0) atTop (nhds 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall (fun y => ?_)) hg
    rw [Real.norm_eq_abs]
    exact hb (xm y) (xm_pos y).le
  exact tendsto_sub_nhds_zero_iff.mp hd

/-- A quadratic `a + b y + c y²` with a finite limit `L` at `∞` has `c = 0`, `b = 0`, `a = L`. -/
theorem quad_tendsto {a b c L : ℝ}
    (h : Tendsto (fun y : ℝ => a + b * y + c * y ^ 2) atTop (nhds L)) : c = 0 ∧ b = 0 ∧ a = L := by
  have hc : c = 0 := by
    have h1 : Tendsto (fun y : ℝ => (a + b * y + c * y ^ 2) / y ^ 2) atTop (nhds 0) :=
      h.div_atTop (tendsto_pow_atTop two_ne_zero)
    have h2 : Tendsto (fun y : ℝ => a * (y ^ 2)⁻¹ + b * y⁻¹ + c) atTop
        (nhds (a * 0 + b * 0 + c)) :=
      (((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)).const_mul a).add
        (tendsto_inv_atTop_zero.const_mul b)).add tendsto_const_nhds
    have h3 : (fun y : ℝ => (a + b * y + c * y ^ 2) / y ^ 2)
        =ᶠ[atTop] (fun y : ℝ => a * (y ^ 2)⁻¹ + b * y⁻¹ + c) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hy1 : y * y⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
      rw [div_eq_mul_inv]
      linear_combination (b * y⁻¹ + c * (y * y⁻¹ + 1)) * hy1
    have h4 := tendsto_nhds_unique (h1.congr' h3) h2
    linarith
  have hb : b = 0 := by
    have h' : Tendsto (fun y : ℝ => a + b * y) atTop (nhds L) :=
      h.congr (fun y => by
        show a + b * y + c * y ^ 2 = a + b * y
        rw [hc]
        ring)
    have h1 : Tendsto (fun y : ℝ => (a + b * y) / y) atTop (nhds 0) := h'.div_atTop tendsto_id
    have h2 : Tendsto (fun y : ℝ => a * y⁻¹ + b) atTop (nhds (a * 0 + b)) :=
      (tendsto_inv_atTop_zero.const_mul a).add tendsto_const_nhds
    have h3 : (fun y : ℝ => (a + b * y) / y) =ᶠ[atTop] (fun y : ℝ => a * y⁻¹ + b) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hy1 : y * y⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
      rw [div_eq_mul_inv]
      linear_combination b * hy1
    have h4 := tendsto_nhds_unique (h1.congr' h3) h2
    linarith
  have ha : a = L := by
    have h' : Tendsto (fun _ : ℝ => a) atTop (nhds L) :=
      h.congr (fun y => by
        show a + b * y + c * y ^ 2 = a
        rw [hc, hb]
        ring)
    exact tendsto_nhds_unique tendsto_const_nhds h'
  exact ⟨hc, hb, ha⟩

/-- **`hjF(xm y) = a₀ Zax y`** for `y > 0`, `a₀ = hk thF0 0`. -/
theorem zhouF_a0 : ∀ y : ℝ, 0 < y → hjF (xm y) = hk thF0 0 * Zax y := by
  obtain ⟨a, b, c, hq⟩ := hjF_xm_quad
  have hj : ∀ y : ℝ, hjF (xm y) = hk thF0 (xm y) := fun y => by
    rw [hjF_eq_hk, ← thF0_eq_fB]
  have hlim : Tendsto (fun y : ℝ => hk thF0 (xm y) / Zax y) atTop (nhds (hk thF0 0 / 1)) :=
    tendsto_hjF_xm.div tendsto_Zax_atTop one_ne_zero
  have hev : (fun y : ℝ => hk thF0 (xm y) / Zax y)
      =ᶠ[atTop] (fun y : ℝ => a + b * y + c * y ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hz : Zax y ≠ 0 := (Zax_pos hy).ne'
    rw [← hj y, hq y hy, mul_div_assoc, div_self hz, mul_one]
  obtain ⟨hc, hb, ha⟩ := quad_tendsto (hlim.congr' hev)
  intro y hy
  rw [hq y hy, hc, hb, ha, div_one]
  ring

/-- `a₀ = ∫₀^∞ t I₀(t) K₀(t)³ dt`. -/
theorem hk_thF0_zero :
    hk thF0 0 = ∫ t in Set.Ioi (0 : ℝ), t * (besselI0 t * besselK0 t ^ 3) := by
  unfold hk
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  show besselJ0 (0 * t) * thF0 t * t = t * (besselI0 t * besselK0 t ^ 3)
  rw [zero_mul, besselJ0_zero]
  unfold thF0 ldF0
  ring

/-- `ZhouF` is the single equation `a₀ = π²/16`. -/
theorem zhouF_of_const (h : hk thF0 0 = π ^ 2 / 16) : ZhouF := by
  unfold ZhouF
  intro y hy
  rw [zhouF_a0 y hy, h]

/-- The six-step theorem from `RungBP`, `a₀ = π²/16` and `ZhouG`. -/
theorem rv6_of_a0 (hP : RungBP) (h0 : hk thF0 0 = π ^ 2 / 16) (hG : ZhouG) :
    mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_zhou2 hP (zhouF_of_const h0) hG

end Tower.RV6
