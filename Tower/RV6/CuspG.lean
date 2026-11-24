import Mathlib
import Tower.RV6.SmallG
import Tower.RV6.CuspModF

/-!
# The cusp `x → ∞` for `g`: `v₀(xm y) = (π/4) y Zax y`

* `tendsto_thG2_zero`: `θ²g → 2` at `0+` (`pB₁ → -1`, `pB₀ pB₂ → 0`); `θ³g/t` is integrable (`integrableOn_thG3_div`);
* **`AJ_thG2_eq`**: `AJ(θ²g)(x) = 2 + ∫₀^∞ J₀(xt) θ³g(t)/t dt`, so `AJ(θ²g) → 2` as `x → ∞` (`tendsto_AJ_thG2`);
* `Xc_sq_vG0`: along `X = Xc w = xm(1/(6w))`, `-AJ(θg)(X) = (48 a w² + 8 b w) Zax w`;
* `cusp_identity` (uniqueness of derivatives) and `cusp_ab`: `(96 a w + 8 b) Z → 2π`, so `a = 0`, `b = π/4`;
* **`vG0_eq`**: `v₀(xm y) = (π/4) y Zax y` for `y > 0`.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

/-! ## `θ³g/t` and `θ²g(0+) = 2` -/

theorem abs_thG3_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |thG3 t| ≤ 72 * (t ^ 2 * bG t ^ 4) := by
  obtain ⟨p0, p1, p2, p3, -, -⟩ := abs_pB_small ht ht1
  have q1 := abs_cmul_leG (c := (2 : ℝ)) (C := 2) (by norm_num) (abs_mul_leG p0 p3)
  have q2 := abs_cmul_leG (c := (6 : ℝ)) (C := 6) (by norm_num) (abs_mul_leG p1 p2)
  have a := abs_add_le ((2 : ℝ) * (pB0 t * pB3 t)) ((6 : ℝ) * (pB1 t * pB2 t))
  rw [thG3_eq_P]
  linarith

theorem abs_thG3_div_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : |thG3 t / t| ≤ 72 * kG0 := by
  have h := abs_thG3_small ht ht1
  have k := mul_le_mul_of_nonneg_left (mul_bG_pow4_le ht ht1) ht.le
  have h2 : |thG3 t| ≤ 72 * kG0 * t := by linarith
  rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
  exact h2

theorem continuousOn_thG3_div : ContinuousOn (fun t : ℝ => thG3 t / t) (Set.Ioi 0) :=
  continuousOn_thG3.div continuousOn_id (fun t ht => ne_of_gt ht)

theorem integrableOn_thG3_div : IntegrableOn (fun t : ℝ => thG3 t / t) (Set.Ioi 0) := by
  refine integrableOn_Ioi_of_bounds continuousOn_thG3_div (A := 72 * kG0) (B := 1072)
    (fun t ht ht1 => ?_) (fun t ht => ?_)
  · have h := abs_thG3_div_le ht ht1
    have hs1 : Real.sqrt t ≤ 1 := by
      have h' := Real.sqrt_le_sqrt ht1
      rwa [Real.sqrt_one] at h'
    have hm : Real.sqrt t * |thG3 t / t| ≤ 1 * (72 * kG0) :=
      mul_le_mul hs1 h (abs_nonneg _) zero_le_one
    exact abs_le_of_sqrt_mul_le ht (by linarith)
  · have ht0 : (0 : ℝ) < t := by linarith
    have h := abs_tsq_thG3_le ht0
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)] at h
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
    have e : t ^ 2 * |thG3 t / t| = t * |thG3 t| := by
      rw [abs_div, abs_of_pos ht0, div_eq_mul_inv]
      linear_combination (t * |thG3 t|) * hinv
    have a : t * |thG3 t| ≤ t ^ 2 * |thG3 t| :=
      mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
    exact abs_le_of_sq_mul_le ht0 (by linarith)

theorem tendsto_kG0_mul_zero (k : ℝ) :
    Tendsto (fun t : ℝ => k * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : Tendsto (fun t : ℝ => k * t) (nhds 0) (nhds (k * 0)) :=
    (by fun_prop : Continuous (fun t : ℝ => k * t)).tendsto 0
  rw [mul_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_pB1_zero : Tendsto pB1 (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
  have hq := tendsto_mul_besselK1_zero
  have hI0 : Tendsto besselI0 (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : Tendsto besselI0 (nhds 0) (nhds (besselI0 0)) := continuous_besselI0.tendsto 0
    rw [besselI0_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hX : Tendsto (fun t : ℝ => t * besselI1 t * besselK0 t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_kG0_mul_zero kG0)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (one_pos : (0 : ℝ) < 1))] with t ht ht1
    have ht0 : (0 : ℝ) < t := ht
    have ht1' : t < 1 := ht1
    obtain ⟨-, hI1, hK0, -⟩ := near0_prim ht0 ht1'.le
    have hu := one_le_bG ht0 ht1'.le
    have k := mul_bG_pow4_le ht0 ht1'.le
    have h := abs_mul_leG hI1 hK0
    have hb2 : bG t ^ 2 ≤ bG t ^ 4 := pow_le_pow_right₀ hu (by norm_num)
    have h3 : t ^ 2 * bG t ^ 2 ≤ t ^ 2 * bG t ^ 4 := mul_le_mul_of_nonneg_left hb2 (sq_nonneg t)
    have h4 := mul_le_mul_of_nonneg_left k ht0.le
    rw [Real.norm_eq_abs]
    linarith
  have hY := hI0.mul hq
  rw [one_mul] at hY
  have h := hX.sub hY
  rw [zero_sub] at h
  refine h.congr' ?_
  filter_upwards with t
  rfl

theorem tendsto_thG2_zero : Tendsto thG2 (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
  have hB := tendsto_pB1_zero
  have hX : Tendsto (fun t : ℝ => pB0 t * pB2 t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_kG0_mul_zero (4 * kG0))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (one_pos : (0 : ℝ) < 1))] with t ht ht1
    have ht0 : (0 : ℝ) < t := ht
    have ht1' : t < 1 := ht1
    obtain ⟨p0, -, p2, -, -, -⟩ := abs_pB_small ht0 ht1'.le
    have k := mul_bG_pow4_le ht0 ht1'.le
    have h := abs_mul_leG p0 p2
    have h4 := mul_le_mul_of_nonneg_left k ht0.le
    rw [Real.norm_eq_abs]
    linarith
  have h := (hX.const_mul 2).add ((hB.mul hB).const_mul 2)
  have hv : (2 : ℝ) * 0 + 2 * (-1 * -1) = 2 := by norm_num
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards with t
  exact (thG2_eq_P t).symm

theorem tendsto_thG2_atTop : Tendsto thG2 atTop (nhds 0) := by
  have hb : Tendsto (fun t : ℝ => (112 : ℝ) / t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have h := abs_tsq_thG2_le ht0
  rw [abs_mul, abs_of_nonneg (sq_nonneg t)] at h
  have a : |thG2 t| * t ≤ |thG2 t| * t ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
  rw [Real.norm_eq_abs, le_div_iff₀ ht0]
  linarith

/-! ## `AJ(θ²g) = 2 + ∫ J₀(xt) θ³g/t` and its limit -/

theorem AJ_thG2_eq {x : ℝ} (hx : 0 < x) :
    AJ thG2 x = 2 + ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * (thG3 t / t) := by
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => besselJ0 (x * t) * thG2 t)
      ((-x) * (besselJ1 (x * t) * thG2 t) + besselJ0 (x * t) * (thG3 t / t)) t := by
    intro t ht
    have d1 : HasDerivAt (fun t : ℝ => besselJ0 (x * t)) (-besselJ1 (x * t) * (x * 1)) t :=
      (hasDerivAt_besselJ0 (x * t)).comp t ((hasDerivAt_id' t).const_mul x)
    have h := d1.mul (hasDerivAt_thG2 ht)
    exact h.congr_deriv (by ring)
  have hJ : Tendsto (fun t : ℝ => besselJ0 (x * t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : Tendsto (fun t : ℝ => besselJ0 (x * t)) (nhds 0) (nhds (besselJ0 (x * 0))) :=
      (continuous_besselJ0_mul' x).tendsto 0
    rw [mul_zero, besselJ0_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h0 : Tendsto (fun t : ℝ => besselJ0 (x * t) * thG2 t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 2) := by
    have h := hJ.mul tendsto_thG2_zero
    rw [one_mul] at h
    exact h
  have hzi : Tendsto (fun t : ℝ => |thG2 t|) atTop (nhds 0) := by
    have h := tendsto_thG2_atTop.abs
    rw [abs_zero] at h
    exact h
  have hinf : Tendsto (fun t : ℝ => besselJ0 (x * t) * thG2 t) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hzi
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have j := abs_besselJ0_le_one (mul_nonneg hx.le ht.le)
    rw [Real.norm_eq_abs, abs_mul]
    calc |besselJ0 (x * t)| * |thG2 t| ≤ 1 * |thG2 t| :=
          mul_le_mul_of_nonneg_right j (abs_nonneg _)
      _ = |thG2 t| := one_mul _
  have i1 : Integrable (fun t : ℝ => (-x) * (besselJ1 (x * t) * thG2 t))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrable_J1_mul_of_pdom pdom_thG2 hx).const_mul (-x)
  have i2 : Integrable (fun t : ℝ => besselJ0 (x * t) * (thG3 t / t))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => besselJ0 (x * t) * (thG3 t / t))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      ((continuousOn_besselJ0_mul x).mul continuousOn_thG3_div).aestronglyMeasurable
        measurableSet_Ioi
    refine (Integrable.abs integrableOn_thG3_div).mono' hm
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := ht
    have j := abs_besselJ0_le_one (mul_nonneg hx.le ht0.le)
    show ‖besselJ0 (x * t) * (thG3 t / t)‖ ≤ |thG3 t / t|
    rw [Real.norm_eq_abs, abs_mul]
    calc |besselJ0 (x * t)| * |thG3 t / t| ≤ 1 * |thG3 t / t| :=
          mul_le_mul_of_nonneg_right j (abs_nonneg _)
      _ = |thG3 t / t| := one_mul _
  have hint : IntegrableOn
      (fun t : ℝ => (-x) * (besselJ1 (x * t) * thG2 t) + besselJ0 (x * t) * (thG3 t / t))
      (Set.Ioi 0) := i1.add i2
  have hz := integral_Ioi_deriv_eq_neg hd h0 hinf hint
  have a1 : (∫ t in Set.Ioi (0 : ℝ),
        ((-x) * (besselJ1 (x * t) * thG2 t) + besselJ0 (x * t) * (thG3 t / t)))
      = (∫ t in Set.Ioi (0 : ℝ), (-x) * (besselJ1 (x * t) * thG2 t))
        + ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * (thG3 t / t) := integral_add i1 i2
  have a2 : (∫ t in Set.Ioi (0 : ℝ), (-x) * (besselJ1 (x * t) * thG2 t))
      = (-x) * ∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * thG2 t := integral_const_mul _ _
  show x * (∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * thG2 t) = _
  linarith

/-- **`AJ(θ²g)(x) → 2`** as `x → ∞`. -/
theorem tendsto_AJ_thG2 : Tendsto (AJ thG2) atTop (nhds 2) := by
  have hD : Tendsto (fun x : ℝ => ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * (thG3 t / t)) atTop
      (nhds (∫ t in Set.Ioi (0 : ℝ), (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => |thG3 t / t|) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall (fun x => ?_)
      have hc : ContinuousOn (fun t : ℝ => besselJ0 (x * t) * (thG3 t / t)) (Set.Ioi 0) :=
        (continuousOn_besselJ0_mul x).mul continuousOn_thG3_div
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
      have ht0 : (0 : ℝ) < t := ht
      have j := abs_besselJ0_le_one (mul_nonneg hx ht0.le)
      show ‖besselJ0 (x * t) * (thG3 t / t)‖ ≤ |thG3 t / t|
      rw [Real.norm_eq_abs, abs_mul]
      calc |besselJ0 (x * t)| * |thG3 t / t| ≤ 1 * |thG3 t / t| :=
            mul_le_mul_of_nonneg_right j (abs_nonneg _)
        _ = |thG3 t / t| := one_mul _
    · exact Integrable.abs integrableOn_thG3_div
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
      have ht0 : (0 : ℝ) < t := ht
      have hJ : Tendsto (fun x : ℝ => besselJ0 (x * t)) atTop (nhds 0) :=
        tendsto_besselJ0_atTop.comp (tendsto_id.atTop_mul_const ht0)
      have h := hJ.mul_const (thG3 t / t)
      rw [zero_mul] at h
      exact h
  rw [integral_zero] at hD
  have h2 := (tendsto_const_nhds (x := (2 : ℝ))).add hD
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [AJ_thG2_eq hx]

/-! ## The modular side along `X(w) = xm(1/(6w))` -/

theorem Xc_sq_vG0 {a b : ℝ} (hab : ∀ y : ℝ, 0 < y → vG0 (xm y) = (a + b * y) * Zax y) {w : ℝ}
    (hw : 0 < w) : -(AJ thG1 (Xc w)) = (48 * a * w ^ 2 + 8 * b * w) * Zax w := by
  have hy : 0 < 1 / (6 * w) := one_div_pos.mpr (by linarith)
  have h1 := hab (1 / (6 * w)) hy
  have hX : 0 < xm (1 / (6 * w)) := xm_pos _
  have hZ := Zax_pos hy
  have hU := Uax_inv_six hw
  have hv : vG0 (xm (1 / (6 * w))) * xm (1 / (6 * w)) ^ 2 = -(AJ thG1 (xm (1 / (6 * w)))) := by
    unfold vG0
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hX.ne')]
  have hXZ : xm (1 / (6 * w)) ^ 2 * Zax (1 / (6 * w)) = 64 * Uax (1 / (6 * w)) := by
    rw [xm_sq hy, div_mul_cancel₀ _ hZ.ne']
  have hwi : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  show -(AJ thG1 (xm (1 / (6 * w)))) = (48 * a * w ^ 2 + 8 * b * w) * Zax w
  linear_combination (-1 : ℝ) * hv + xm (1 / (6 * w)) ^ 2 * h1
    + (a + b * (1 / (6 * w))) * hXZ + 64 * (a + b * (1 / (6 * w))) * hU + 8 * b * Zax w * w * hwi

theorem hasDerivAt_negAJ1_Xc {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun w : ℝ => -(AJ thG1 (Xc w))) (π / 4 * Pax w * AJ thG2 (Xc w)) w := by
  have hX := Xc_pos w
  have h1 := (hasDerivAt_AJ_thG1 hX).neg
  have h := h1.comp w (hasDerivAt_Xc hw)
  have h' : HasDerivAt (fun w : ℝ => -(AJ thG1 (Xc w)))
      (-(-(AJ thG2 (Xc w)) / Xc w) * (π / 4 * Pax w * Xc w)) w := h
  refine h'.congr_deriv ?_
  have hi : Xc w * (Xc w)⁻¹ = 1 := mul_inv_cancel₀ hX.ne'
  linear_combination (π / 4 * Pax w * AJ thG2 (Xc w)) * hi

theorem cusp_identity {a b : ℝ} (hab : ∀ y : ℝ, 0 < y → vG0 (xm y) = (a + b * y) * Zax y) {w : ℝ}
    (hw : 0 < w) :
    π / 4 * Pax w * AJ thG2 (Xc w) = (48 * a * (2 * w) + 8 * b * 1) * Zax w
      + (48 * a * w ^ 2 + 8 * b * w) * (-(2 * π) * (Zax w * Eax w)) := by
  have h1 := hasDerivAt_negAJ1_Xc hw
  have hq : HasDerivAt (fun w : ℝ => 48 * a * w ^ 2 + 8 * b * w) (48 * a * (2 * w) + 8 * b * 1) w :=
    ((hasDerivAt_sqx w).const_mul (48 * a)).add ((hasDerivAt_id' w).const_mul (8 * b))
  have h2 : HasDerivAt (fun w : ℝ => (48 * a * w ^ 2 + 8 * b * w) * Zax w)
      ((48 * a * (2 * w) + 8 * b * 1) * Zax w
        + (48 * a * w ^ 2 + 8 * b * w) * (-(2 * π) * (Zax w * Eax w))) w :=
    hq.mul (hasDerivAt_Zax hw)
  have hev : (fun w : ℝ => -(AJ thG1 (Xc w))) =ᶠ[nhds w]
      (fun w : ℝ => (48 * a * w ^ 2 + 8 * b * w) * Zax w) := by
    filter_upwards [Ioi_mem_nhds hw] with v hv
    exact Xc_sq_vG0 hab hv
  exact h1.unique (h2.congr_of_eventuallyEq hev)

theorem cusp_ab {a b : ℝ} (hab : ∀ y : ℝ, 0 < y → vG0 (xm y) = (a + b * y) * Zax y) :
    a = 0 ∧ b = π / 4 := by
  have hAJ : Tendsto (fun w : ℝ => AJ thG2 (Xc w)) atTop (nhds 2) :=
    tendsto_AJ_thG2.comp tendsto_Xc_atTop
  have hG : Tendsto (fun w : ℝ => π / 4 * Pax w * AJ thG2 (Xc w)
      + 2 * π * (48 * a * (w ^ 2 * Eax w) + 8 * b * (w * Eax w)) * Zax w) atTop
      (nhds (π / 4 * 4 * 2 + 2 * π * (48 * a * 0 + 8 * b * 0) * 1)) :=
    (((tendsto_const_nhds.mul tendsto_Pax_atTop).mul hAJ).add
      ((tendsto_const_nhds.mul ((tendsto_const_nhds.mul tendsto_sq_Eax).add
        (tendsto_const_nhds.mul tendsto_mul_Eax))).mul tendsto_Zax_atTop))
  have hv : π / 4 * 4 * 2 + 2 * π * (48 * a * 0 + 8 * b * 0) * 1 = 2 * π := by ring
  rw [hv] at hG
  have hD := hG.div tendsto_Zax_atTop one_ne_zero
  rw [div_one] at hD
  have hQ : Tendsto (fun w : ℝ => 8 * b + 96 * a * w + 0 * w ^ 2) atTop (nhds (2 * π)) := by
    refine hD.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    have hi := cusp_identity hab hw
    have hZ := Zax_pos hw
    rw [div_eq_iff hZ.ne']
    linear_combination hi
  obtain ⟨-, h1, h2⟩ := quad_tendsto hQ
  constructor
  · linarith
  · linarith

/-- **`v₀(xm y) = (π/4) y Zax y`** for `y > 0`. -/
theorem vG0_eq {y : ℝ} (hy : 0 < y) : vG0 (xm y) = π / 4 * y * Zax y := by
  obtain ⟨a, b, hab⟩ := vG0_c_zero
  obtain ⟨ha, hb⟩ := cusp_ab hab
  rw [hab y hy, ha, hb]
  ring

end Tower.RV6
