import Mathlib
import Tower.RV6.HankelIBP
import Tower.RV6.HankelRelF

/-!
# The `x`-derivative of the Hankel transform

**`hasDerivAt_hk`**: for a chain `ψ, ψ₁ = θψ` in `HDom` and `x > 0`,
`(hk ψ)'(x) = -(2 hk ψ x + hk ψ₁ x)/x`, that is `ϑ hk(ψ) = -hk((θ + 2) ψ)` with `ϑ = x d/dx`.

The derivative of `J₀(xt) ψ(t) t` in `x` is `-t J₁(xt) ψ(t) t`, bounded by `t² |ψ(t)|` for
`x > 0` (`|J₁| ≤ 1`), which is integrable (`integrableOn_hdom`); so Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` gives `(hk ψ)' = -∫ t² ψ J₁(xt) dt`, and the
first integration by parts (`hk_ibpA`) turns this into `-(hk ψ₁ + 2 hk ψ)/x`.

`hasDerivAt_hk_thF0 … hasDerivAt_hk_thF4`: with `A_k = hk(θᵏ f)`, `A_k' = -(2A_k + A_{k+1})/x`,
i.e. `A_{k+1} = -(ϑ + 2) A_k`.
-/

namespace Tower.RV6

open MeasureTheory

/-- **`ϑ hk(ψ) = -hk((θ + 2) ψ)`** for a chain `ψ, ψ₁` in `HDom` and `x > 0`. -/
theorem hasDerivAt_hk {ψ ψ1 : ℝ → ℝ} (hc : HChain ψ ψ1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (hk ψ) (-(2 * hk ψ x + hk ψ1 x) / x) x := by
  have hψ : HDom ψ := hc.1
  have hψ1 : HDom ψ1 := hc.2.1
  have hcψ : ContinuousOn ψ (Set.Ioi 0) := hψ.1
  have hs : Set.Ioi (x / 2) ∈ nhds x := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable (fun t : ℝ => besselJ0 (y * t) * ψ t * t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro y
    have h1 : ContinuousOn (fun t : ℝ => besselJ0 (y * t) * ψ t * t) (Set.Ioi 0) :=
      ((continuousOn_besselJ0_mul y).mul hcψ).mul continuousOn_id
    exact h1.aestronglyMeasurable measurableSet_Ioi
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => -(t * besselJ1 (x * t)) * ψ t * t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hm : Continuous (fun t : ℝ => x * t) := continuous_const.mul continuous_id
    have hj : Continuous (fun t : ℝ => besselJ1 (x * t)) := continuous_besselJ1.comp hm
    have hk1 : Continuous (fun t : ℝ => -(t * besselJ1 (x * t))) := (continuous_id.mul hj).neg
    have h1 : ContinuousOn (fun t : ℝ => -(t * besselJ1 (x * t)) * ψ t * t) (Set.Ioi 0) :=
      (hk1.continuousOn.mul hcψ).mul continuousOn_id
    exact h1.aestronglyMeasurable measurableSet_Ioi
  have hb1 : IntegrableOn (fun t : ℝ => t ^ 2 * ψ t * 1) (Set.Ioi 0) :=
    integrableOn_hdom (g := fun _ : ℝ => (1 : ℝ)) (G := 1) hψ continuousOn_const
      (fun _ _ => by norm_num) (by norm_num)
  have hbi : IntegrableOn (fun t : ℝ => t ^ 2 * |ψ t|) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.norm hb1) (fun t _ => ?_) measurableSet_Ioi
    show ‖t ^ 2 * ψ t * 1‖ = t ^ 2 * |ψ t|
    rw [Real.norm_eq_abs, mul_one, abs_mul, abs_of_nonneg (sq_nonneg t)]
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (x / 2),
      ‖-(t * besselJ1 (y * t)) * ψ t * t‖ ≤ t ^ 2 * |ψ t| := by
    intro t ht y hy
    have ht0 : (0 : ℝ) < t := ht
    have hy0 : (0 : ℝ) < y := lt_trans (by linarith) (Set.mem_Ioi.mp hy)
    have hJ := abs_besselJ1_le_one (mul_nonneg hy0.le ht0.le)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_mul, abs_of_pos ht0]
    have hp := abs_nonneg (ψ t)
    have h1 : t * |besselJ1 (y * t)| ≤ t * 1 := mul_le_mul_of_nonneg_left hJ ht0.le
    have h2 : t * |besselJ1 (y * t)| * |ψ t| ≤ t * 1 * |ψ t| :=
      mul_le_mul_of_nonneg_right h1 hp
    have h3 : t * |besselJ1 (y * t)| * |ψ t| * t ≤ t * 1 * |ψ t| * t :=
      mul_le_mul_of_nonneg_right h2 ht0.le
    have e : t * 1 * |ψ t| * t = t ^ 2 * |ψ t| := by ring
    linarith
  have hdiff : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (x / 2),
      HasDerivAt (fun y : ℝ => besselJ0 (y * t) * ψ t * t)
        (-(t * besselJ1 (y * t)) * ψ t * t) y := by
    intro t _ y _
    have h0 := (hasDerivAt_besselJ0 (y * t)).comp y ((hasDerivAt_id' y).mul_const t)
    have h1 : HasDerivAt (fun y : ℝ => besselJ0 (y * t)) (-besselJ1 (y * t) * (1 * t)) y := h0
    have h2 := (h1.mul_const (ψ t)).mul_const t
    have h3 : HasDerivAt (fun y : ℝ => besselJ0 (y * t) * ψ t * t)
        (-besselJ1 (y * t) * (1 * t) * ψ t * t) y := h2
    refine h3.congr_deriv ?_
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun y t => besselJ0 (y * t) * ψ t * t)
    (F' := fun y t => -(t * besselJ1 (y * t)) * ψ t * t)
    (bound := fun t => t ^ 2 * |ψ t|) hs
    (Filter.Eventually.of_forall hmeas) (integrableOn_hk hψ hx.le) hmeas'
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound) hbi
    (ae_restrict_of_forall_mem measurableSet_Ioi hdiff)
  have h3 : HasDerivAt (hk ψ)
      (∫ t in Set.Ioi (0 : ℝ), -(t * besselJ1 (x * t)) * ψ t * t) x := key.2
  have hA := hk_ibpA hc hx.le
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  have e2 : ∫ t in Set.Ioi (0 : ℝ), -(t * besselJ1 (x * t)) * ψ t * t
      = -x⁻¹ * ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * ψ t * (x * besselJ1 (x * t)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show -(t * besselJ1 (x * t)) * ψ t * t = -x⁻¹ * (t ^ 2 * ψ t * (x * besselJ1 (x * t)))
    linear_combination (t ^ 2 * ψ t * besselJ1 (x * t)) * hxinv
  have e3 : ∫ t in Set.Ioi (0 : ℝ), t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (x * t)
      = hk ψ1 x + 2 * hk ψ x := by
    rw [← hk_add_cmul hψ1 hψ 2 hx.le]
    unfold hk
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (x * t) = besselJ0 (x * t) * (ψ1 t + 2 * ψ t) * t
    ring
  refine h3.congr_deriv ?_
  rw [e2, ← hA, e3]
  ring

theorem hasDerivAt_hk_thF0 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (hk thF0) (-(2 * hk thF0 x + hk thF1 x) / x) x := hasDerivAt_hk hchain_thF0 hx

theorem hasDerivAt_hk_thF1 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (hk thF1) (-(2 * hk thF1 x + hk thF2 x) / x) x := hasDerivAt_hk hchain_thF1 hx

theorem hasDerivAt_hk_thF2 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (hk thF2) (-(2 * hk thF2 x + hk thF3 x) / x) x := hasDerivAt_hk hchain_thF2 hx

theorem hasDerivAt_hk_thF3 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (hk thF3) (-(2 * hk thF3 x + hk thF4 x) / x) x := hasDerivAt_hk hchain_thF3 hx

theorem hasDerivAt_hk_thF4 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (hk thF4) (-(2 * hk thF4 x + hk thF5 x) / x) x := hasDerivAt_hk hchain_thF4 hx

end Tower.RV6
