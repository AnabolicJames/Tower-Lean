import Mathlib
import Tower.RV6.PullbackG
import Tower.RV6.ZhouFa0

/-!
# The cusp `y → ∞` for `g`: `c = 0`

* `abs_besselJ1_le_half`: `|J₁(u)| ≤ u/2` for `u ≥ 0` (`(uJ₁)' = uJ₀`, `|J₀| ≤ 1`);
* `abs_F_le`: for `0 < x ≤ 1/2`, `s > 0`: `|J₁(s) θg(s/x)| ≤ K x² / ((s + x)(s + 1))`, `K = kS = 8 kG0 + 64`;
* `integral_inv_mul_inv`: `∫₀^∞ ds/((s + x)(s + 1)) = -log x/(1 - x)`;
* `abs_vG0_small`: `|v₀(x)| ≤ 2K (-log x)` on `(0, 1/2]`;
* **`vG0_c_zero`**: with `-log xm(y) ≤ πy + 1` for large `y`, `v₀(xm y)/y² → 0`, so the `c` of `vG0_xm_quad` is `0`:
  `v₀(xm y) = (a + b y) Zax y`.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

/-! ## `|J₁(u)| ≤ u/2` -/

theorem abs_besselJ1_le_half {u : ℝ} (hu : 0 ≤ u) : |besselJ1 u| ≤ u / 2 := by
  have hc1 : ContinuousOn (fun t : ℝ => t * besselJ1 t - t ^ 2 / 2) (Set.Ici 0) :=
    ((continuous_id.mul continuous_besselJ1).sub
      ((continuous_pow 2 : Continuous fun t : ℝ => t ^ 2).div_const 2)).continuousOn
  have hc2 : ContinuousOn (fun t : ℝ => -(t * besselJ1 t) - t ^ 2 / 2) (Set.Ici 0) :=
    (((continuous_id.mul continuous_besselJ1).neg).sub
      ((continuous_pow 2 : Continuous fun t : ℝ => t ^ 2).div_const 2)).continuousOn
  have hd1 : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => t * besselJ1 t - t ^ 2 / 2)
      (t * besselJ0 t - t) t := by
    intro t _
    have h := (hasDerivAt_mul_besselJ1 t).sub ((hasDerivAt_sqx t).div_const 2)
    exact h.congr_deriv (by ring)
  have hd2 : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => -(t * besselJ1 t) - t ^ 2 / 2)
      (-(t * besselJ0 t) - t) t := by
    intro t _
    have h := (hasDerivAt_mul_besselJ1 t).neg.sub ((hasDerivAt_sqx t).div_const 2)
    exact h.congr_deriv (by ring)
  have hn1 : ∀ t : ℝ, 0 < t → t * besselJ0 t - t ≤ 0 := by
    intro t ht
    have j := (abs_le.mp (abs_besselJ0_le_one ht.le)).2
    nlinarith
  have hn2 : ∀ t : ℝ, 0 < t → -(t * besselJ0 t) - t ≤ 0 := by
    intro t ht
    have j := (abs_le.mp (abs_besselJ0_le_one ht.le)).1
    nlinarith
  have a1 : u * besselJ1 u - u ^ 2 / 2 ≤ 0 * besselJ1 0 - 0 ^ 2 / 2 :=
    antitone_of_hasDerivAt_nonpos hc1 hd1 hn1 (le_refl 0) hu
  have a2 : -(u * besselJ1 u) - u ^ 2 / 2 ≤ -(0 * besselJ1 0) - 0 ^ 2 / 2 :=
    antitone_of_hasDerivAt_nonpos hc2 hd2 hn2 (le_refl 0) hu
  rcases eq_or_lt_of_le hu with h0 | hpos
  · rw [← h0, besselJ1_zero, abs_zero]
    norm_num
  · have b1 : u * besselJ1 u ≤ u ^ 2 / 2 := by linarith
    have b2 : -(u ^ 2 / 2) ≤ u * besselJ1 u := by linarith
    have hb : |u * besselJ1 u| ≤ u ^ 2 / 2 := abs_le.mpr ⟨b2, b1⟩
    rw [abs_mul, abs_of_pos hpos] at hb
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h3 : u * (|besselJ1 u| * 2) ≤ u * u := by linarith
    exact le_of_mul_le_mul_left h3 hpos

/-! ## The majorant -/

theorem mul_abs_thG1_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : t * |thG1 t| ≤ 4 * kG0 := by
  obtain ⟨p0, p1, -, -, -, -⟩ := abs_pB_small ht ht1
  have h : |thG1 t| ≤ 2 * (bG t ^ 2 * (2 * bG t ^ 2)) := by
    rw [thG1_eq_P]
    exact abs_cmul_leG (by norm_num) (abs_mul_leG p0 p1)
  have k := mul_bG_pow4_le ht ht1
  have h2 := mul_le_mul_of_nonneg_left h ht.le
  linarith

theorem kG0_nonneg : 0 ≤ kG0 := by
  unfold kG0
  positivity

/-- `K = 8 kG0 + 64`. -/
noncomputable def kS : ℝ := 8 * kG0 + 64

theorem kS_nonneg : 0 ≤ kS := by
  unfold kS
  linarith [kG0_nonneg]

theorem abs_F_le {x s : ℝ} (hx : 0 < x) (hx2 : x ≤ 1 / 2) (hs : 0 < s) :
    |besselJ1 s * thG1 (s / x)| ≤ kS * x ^ 2 * ((s + x) * (s + 1))⁻¹ := by
  have hk := kG0_nonneg
  have hJ1 := abs_besselJ1_le_one hs.le
  have hJh := abs_besselJ1_le_half hs.le
  have hsx : 0 < s + x := by linarith
  have hs1 : 0 < s + 1 := by linarith
  have hP : 0 < (s + x) * (s + 1) := mul_pos hsx hs1
  have ht : 0 < s / x := div_pos hs hx
  have hth := abs_nonneg (thG1 (s / x))
  have hx2' : 0 ≤ 64 * x ^ 2 := by positivity
  have hkx : 0 ≤ kG0 * x ^ 2 := mul_nonneg hk (sq_nonneg x)
  have hkx1 : 0 ≤ 2 * kG0 * x := by have := mul_nonneg hk hx.le; linarith
  rw [abs_mul, ← div_eq_mul_inv, le_div_iff₀ hP]
  rcases le_or_gt s x with h1 | h1
  · have htl : s / x ≤ 1 := by
      rw [div_le_one hx]
      exact h1
    have hm := mul_abs_thG1_le ht htl
    have e : s / x * |thG1 (s / x)| = s * |thG1 (s / x)| / x := by ring
    rw [e, div_le_iff₀ hx] at hm
    have a := mul_le_mul_of_nonneg_right hJh hth
    have c1 : |besselJ1 s| * |thG1 (s / x)| ≤ 2 * kG0 * x := by linarith
    have hb : (s + x) * (s + 1) ≤ 2 * x * 2 :=
      mul_le_mul (by linarith) (by linarith) hs1.le (by linarith)
    have c2 := mul_le_mul c1 hb hP.le hkx1
    unfold kS
    linarith
  · have hq := abs_tsq_thG1_le ht
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), div_pow, div_mul_eq_mul_div,
      div_le_iff₀ (pow_pos hx 2)] at hq
    rcases le_or_gt s 1 with h2 | h2
    · have a := mul_le_mul_of_nonneg_right hJh hth
      have hb : (s + x) * (s + 1) ≤ 2 * s * 2 :=
        mul_le_mul (by linarith) (by linarith) hs1.le (by linarith)
      have c2 := mul_le_mul a hb hP.le (mul_nonneg (by linarith) hth)
      unfold kS
      linarith
    · have a : |besselJ1 s| * |thG1 (s / x)| ≤ 1 * |thG1 (s / x)| :=
        mul_le_mul_of_nonneg_right hJ1 hth
      have hb : (s + x) * (s + 1) ≤ 2 * s * (2 * s) :=
        mul_le_mul (by linarith) (by linarith) hs1.le (by linarith)
      have c2 := mul_le_mul a hb hP.le (by linarith)
      unfold kS
      linarith

/-! ## `∫₀^∞ ds/((s + x)(s + 1))` -/

theorem hasDerivAt_logq {x s : ℝ} (hx1 : x < 1) (hs : -x < s) (hs1' : -1 < s) :
    HasDerivAt (fun s : ℝ => (Real.log (s + x) - Real.log (s + 1)) / (1 - x))
      ((s + x) * (s + 1))⁻¹ s := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hsx : 0 < s + x := by linarith
  have hs1 : 0 < s + 1 := by linarith
  have l1 : HasDerivAt Real.log (s + x)⁻¹ (s + x) := Real.hasDerivAt_log hsx.ne'
  have l2 : HasDerivAt Real.log (s + 1)⁻¹ (s + 1) := Real.hasDerivAt_log hs1.ne'
  have a1 : HasDerivAt (fun y : ℝ => y + x) 1 s := (hasDerivAt_id' s).add_const x
  have a2 : HasDerivAt (fun y : ℝ => y + 1) 1 s := (hasDerivAt_id' s).add_const 1
  have d1' := l1.comp s a1
  have d2' := l2.comp s a2
  have d1 : HasDerivAt (fun s : ℝ => Real.log (s + x)) ((s + x)⁻¹ * 1) s := d1'
  have d2 : HasDerivAt (fun s : ℝ => Real.log (s + 1)) ((s + 1)⁻¹ * 1) s := d2'
  have h := (d1.sub d2).div_const (1 - x)
  refine h.congr_deriv ?_
  have hA : (s + x) * (s + x)⁻¹ = 1 := mul_inv_cancel₀ hsx.ne'
  have hB : (s + 1) * (s + 1)⁻¹ = 1 := mul_inv_cancel₀ hs1.ne'
  rw [mul_inv, div_eq_iff hpos.ne']
  linear_combination (-(s + x)⁻¹) * hB + (s + 1)⁻¹ * hA

theorem integrableOn_inv_mul_inv {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => ((s + x) * (s + 1))⁻¹) (Set.Ioi 0) := by
  have hc : ContinuousOn (fun s : ℝ => ((s + x) * (s + 1))⁻¹) (Set.Ioi 0) := by
    refine ContinuousOn.inv₀ ?_ (fun s hs => ?_)
    · exact (by fun_prop : Continuous (fun s : ℝ => (s + x) * (s + 1))).continuousOn
    · have hs0 : (0 : ℝ) < s := hs
      have hp : 0 < (s + x) * (s + 1) := mul_pos (by linarith) (by linarith)
      exact hp.ne'
  refine integrableOn_Ioi_of_bounds hc (A := x⁻¹) (B := 1) (fun t ht ht1 => ?_) (fun t ht => ?_)
  · have hP : x ≤ (t + x) * (t + 1) := by nlinarith
    have hpos : 0 < (t + x) * (t + 1) := mul_pos (by linarith) (by linarith)
    have hi : ((t + x) * (t + 1))⁻¹ ≤ x⁻¹ := inv_anti₀ hx hP
    have hs1 : Real.sqrt t ≤ 1 := by
      have h' := Real.sqrt_le_sqrt ht1
      rwa [Real.sqrt_one] at h'
    have hm : Real.sqrt t * |((t + x) * (t + 1))⁻¹| ≤ 1 * x⁻¹ := by
      rw [abs_of_pos (inv_pos.mpr hpos)]
      exact mul_le_mul hs1 hi (inv_pos.mpr hpos).le zero_le_one
    show |((t + x) * (t + 1))⁻¹| ≤ x⁻¹ * (Real.sqrt t)⁻¹
    exact abs_le_of_sqrt_mul_le ht (by linarith)
  · have ht0 : (0 : ℝ) < t := by linarith
    have hpos : 0 < (t + x) * (t + 1) := mul_pos (by linarith) (by linarith)
    have hm : t ^ 2 * |((t + x) * (t + 1))⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr hpos), ← div_eq_mul_inv, div_le_one hpos]
      nlinarith
    show |((t + x) * (t + 1))⁻¹| ≤ 1 * (t ^ 2)⁻¹
    exact abs_le_of_sq_mul_le ht0 hm

/-- `∫₀^∞ ds/((s + x)(s + 1)) = -log x/(1 - x)` for `0 < x < 1`. -/
theorem integral_inv_mul_inv {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ∫ s in Set.Ioi (0 : ℝ), ((s + x) * (s + 1))⁻¹ = -Real.log x / (1 - x) := by
  have hd : ∀ s : ℝ, 0 < s → HasDerivAt
      (fun s : ℝ => (Real.log (s + x) - Real.log (s + 1)) / (1 - x)) (((s + x) * (s + 1))⁻¹) s :=
    fun s hs => hasDerivAt_logq hx1 (by linarith) (by linarith)
  have h0 : Tendsto (fun s : ℝ => (Real.log (s + x) - Real.log (s + 1)) / (1 - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log x / (1 - x))) := by
    have hc := (hasDerivAt_logq hx1 (by linarith : -x < (0 : ℝ)) (by norm_num : (-1 : ℝ) < 0)).continuousAt
    have h := hc.tendsto
    have e : (Real.log (0 + x) - Real.log (0 + 1)) / (1 - x) = Real.log x / (1 - x) := by
      rw [zero_add, zero_add, Real.log_one, sub_zero]
    rw [e] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (fun s : ℝ => (Real.log (s + x) - Real.log (s + 1)) / (1 - x)) atTop
      (nhds 0) := by
    have hq : Tendsto (fun s : ℝ => (1 - x) / (s + 1)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.atTop_add tendsto_const_nhds)
    have hr : Tendsto (fun s : ℝ => 1 - (1 - x) / (s + 1)) atTop (nhds 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hq
      rw [sub_zero] at h
      exact h
    have hl : Tendsto (fun s : ℝ => Real.log (1 - (1 - x) / (s + 1))) atTop (nhds 0) := by
      have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hr
      rw [Real.log_one] at h
      exact h
    have hl2 := hl.div_const (1 - x)
    rw [zero_div] at hl2
    refine hl2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hsx : 0 < s + x := by linarith
    have hs1 : 0 < s + 1 := by linarith
    have e : 1 - (1 - x) / (s + 1) = (s + x) / (s + 1) := by
      rw [eq_div_iff hs1.ne', sub_mul, div_mul_cancel₀ _ hs1.ne']
      ring
    rw [e, Real.log_div hsx.ne' hs1.ne']
  have hz := integral_Ioi_deriv_eq_neg hd h0 hinf (integrableOn_inv_mul_inv hx)
  rw [hz]
  ring

/-! ## `v₀` near `0` -/

theorem abs_AJ_thG1_small {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 1 / 2) :
    |AJ thG1 x| ≤ kS * x ^ 2 * (-Real.log x / (1 - x)) := by
  have hx1 : x < 1 := by linarith
  have hmaj : Integrable (fun s : ℝ => kS * x ^ 2 * ((s + x) * (s + 1))⁻¹)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_inv_mul_inv hx) (kS * x ^ 2)
  have hb : ‖∫ s in Set.Ioi (0 : ℝ), besselJ1 s * thG1 (s / x)‖
      ≤ ∫ s in Set.Ioi (0 : ℝ), kS * x ^ 2 * ((s + x) * (s + 1))⁻¹ := by
    refine norm_integral_le_of_norm_le hmaj
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_))
    have hs0 : (0 : ℝ) < s := hs
    show ‖besselJ1 s * thG1 (s / x)‖ ≤ kS * x ^ 2 * ((s + x) * (s + 1))⁻¹
    rw [Real.norm_eq_abs]
    exact abs_F_le hx hx2 hs0
  rw [Real.norm_eq_abs, integral_const_mul, integral_inv_mul_inv hx hx1] at hb
  rw [AJ_eq_subst thG1 hx]
  exact hb

theorem abs_vG0_small {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 1 / 2) : |vG0 x| ≤ 2 * kS * (-Real.log x) := by
  have h := abs_AJ_thG1_small hx hx2
  have hl : 0 ≤ -Real.log x := by
    have : Real.log x ≤ 0 := Real.log_nonpos hx.le (by linarith)
    linarith
  have hk := kS_nonneg
  have hq : -Real.log x / (1 - x) ≤ 2 * (-Real.log x) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - x)]
    nlinarith
  have hx2' : 0 < x ^ 2 := pow_pos hx 2
  have hm := mul_le_mul_of_nonneg_left hq (mul_nonneg hk hx2'.le)
  unfold vG0
  rw [abs_div, abs_neg, abs_of_pos hx2', div_le_iff₀ hx2']
  linarith

/-! ## `c = 0` -/

theorem tendsto_vG0_div : Tendsto (fun y : ℝ => vG0 (xm y) / y ^ 2) atTop (nhds 0) := by
  have hk : 0 ≤ 2 * kS := by linarith [kS_nonneg]
  have h1 : ∀ᶠ y in atTop, xm y ≤ 1 / 2 :=
    tendsto_xm_atTop.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hS : Tendsto (fun y : ℝ => qb y - qb (2 * y) + qb (3 * y) - qb (6 * y)) atTop (nhds 0) := by
    have q1 := tendsto_qb_atTop
    have q2 := tendsto_qb_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id)
    have q3 := tendsto_qb_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) tendsto_id)
    have q6 := tendsto_qb_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 6) tendsto_id)
    have h := ((q1.sub q2).add q3).sub q6
    rw [show (0 : ℝ) - 0 + 0 - 0 = 0 by norm_num] at h
    exact h
  have h2 : ∀ᶠ y in atTop, -1 / 3 < qb y - qb (2 * y) + qb (3 * y) - qb (6 * y) :=
    hS.eventually (lt_mem_nhds (by norm_num : (-1 / 3 : ℝ) < 0))
  have hK : Tendsto (fun y : ℝ => 2 * kS * (π + 1) / y) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with y hx hq hy1
  have hy0 : (0 : ℝ) < y := by linarith
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hlog : -Real.log (xm y) ≤ π * y + 1 := by
    rw [log_xm y]
    linarith
  have hv := abs_vG0_small (xm_pos y) hx
  have hv2 : |vG0 (xm y)| ≤ 2 * kS * (π * y + 1) :=
    le_trans hv (mul_le_mul_of_nonneg_left hlog hk)
  have hyy : y ≤ y ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right hv2 hy0.le
  have h4 := mul_le_mul_of_nonneg_left hyy hk
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hy0 2), div_le_div_iff₀ (pow_pos hy0 2) hy0]
  linarith

/-- **`c = 0`**: `v₀(xm y) = (a + b y) Zax y` for `y > 0`. -/
theorem vG0_c_zero : ∃ a b : ℝ, ∀ y : ℝ, 0 < y → vG0 (xm y) = (a + b * y) * Zax y := by
  obtain ⟨a, b, c, h⟩ := vG0_xm_quad
  have hc : c = 0 := by
    have hi2 : Tendsto (fun y : ℝ => (y ^ 2)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
    have hi1 : Tendsto (fun y : ℝ => y⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have hQ : Tendsto (fun y : ℝ => (a * (y ^ 2)⁻¹ + b * y⁻¹ + c) * Zax y) atTop
        (nhds ((a * 0 + b * 0 + c) * 1)) :=
      (((hi2.const_mul a).add (hi1.const_mul b)).add tendsto_const_nhds).mul tendsto_Zax_atTop
    rw [mul_zero, mul_zero, zero_add, zero_add, mul_one] at hQ
    have hE : Tendsto (fun y : ℝ => vG0 (xm y) / y ^ 2) atTop (nhds c) := by
      refine hQ.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy0
      have hyi : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
      rw [h y hy0, div_eq_mul_inv]
      linear_combination (-(b * Zax y * y⁻¹) - c * Zax y * (y * y⁻¹ + 1)) * hyi
    exact tendsto_nhds_unique hE tendsto_vG0_div
  refine ⟨a, b, fun y hy => ?_⟩
  rw [h y hy, hc]
  ring

end Tower.RV6
