import Mathlib
import Tower.RV6.BMBounds

/-!
# The limit `LimBM`, and `RungBM` from Zhou's two parametrisations alone

`JS s - poleS s = ∫₀^∞ FS s` for `0 < s ≤ 1`, split at `y = 1`; on `(0, 1]` the integrand is
dominated by `(1 + 1/xm(1)) |f0| + K` and on `(1, ∞)` by an explicit sum of exponentials and
`y⁻⁶` (`BMBounds.lean`).  Dominated convergence on each piece gives `limBM : LimBM`, and then

* `rungBM_of_zhou2 : ZhouF → ZhouG → RungBM`,
* `rv6_of_zhou2 : RungBP → ZhouF → ZhouG → μ₆ = (648/π⁶) L(f, 5)`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## The two dominating functions are integrable -/

theorem boundIoc_integrable (Kb : ℝ) :
    Integrable (fun y : ℝ => (1 + (xm 1)⁻¹) * |f0 y| + Kb)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have h1 : IntegrableOn f0 (Set.Ioc (0 : ℝ) 1) :=
    integrableOn_f0.mono_set Set.Ioc_subset_Ioi_self
  have h2 : Integrable (fun y : ℝ => (1 + (xm 1)⁻¹) * |f0 y|)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    Integrable.const_mul (Integrable.abs h1) (1 + (xm 1)⁻¹)
  have h3 : IntegrableOn (fun _ : ℝ => Kb) (Set.Ioc (0 : ℝ) 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have h4 := Integrable.add h2 h3
  exact h4

theorem boundIoi_integrable :
    Integrable (fun y : ℝ => 640 * S3c * (80 * Tint 1) * (Real.exp (-(2 * π * 1 * (y - 1)))
      + Real.exp (-(2 * π * 1 * (y - 1))) * Real.exp (π * y + 12 * qb 1)) + 1 / (162 * y ^ 6))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have i1 : IntegrableOn (fun x : ℝ => Real.exp (-(2 * π) * x)) (Set.Ioi 1) :=
    exp_neg_integrableOn_Ioi 1 (mul_pos (by norm_num) Real.pi_pos)
  have i2 : IntegrableOn (fun x : ℝ => Real.exp (-π * x)) (Set.Ioi 1) :=
    exp_neg_integrableOn_Ioi 1 Real.pi_pos
  have i3 : IntegrableOn (fun t : ℝ => t ^ (-6 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have j1 : IntegrableOn (fun x : ℝ =>
      640 * S3c * (80 * Tint 1) * Real.exp (2 * π) * Real.exp (-(2 * π) * x)) (Set.Ioi 1) :=
    Integrable.const_mul i1 (640 * S3c * (80 * Tint 1) * Real.exp (2 * π))
  have j2 : IntegrableOn (fun x : ℝ =>
      640 * S3c * (80 * Tint 1) * Real.exp (2 * π + 12 * qb 1) * Real.exp (-π * x))
      (Set.Ioi 1) :=
    Integrable.const_mul i2 (640 * S3c * (80 * Tint 1) * Real.exp (2 * π + 12 * qb 1))
  have j3 : IntegrableOn (fun x : ℝ => 1 / 162 * x ^ (-6 : ℝ)) (Set.Ioi 1) :=
    Integrable.const_mul i3 (1 / 162)
  have hsum : IntegrableOn (fun y : ℝ =>
      640 * S3c * (80 * Tint 1) * Real.exp (2 * π) * Real.exp (-(2 * π) * y)
      + 640 * S3c * (80 * Tint 1) * Real.exp (2 * π + 12 * qb 1) * Real.exp (-π * y)
      + 1 / 162 * y ^ (-6 : ℝ)) (Set.Ioi 1) :=
    Integrable.add (Integrable.add j1 j2) j3
  refine IntegrableOn.congr_fun hsum (fun y hy => ?_) measurableSet_Ioi
  have hy0 : 0 < y := lt_trans one_pos (Set.mem_Ioi.mp hy)
  show 640 * S3c * (80 * Tint 1) * Real.exp (2 * π) * Real.exp (-(2 * π) * y)
      + 640 * S3c * (80 * Tint 1) * Real.exp (2 * π + 12 * qb 1) * Real.exp (-π * y)
      + 1 / 162 * y ^ (-6 : ℝ)
    = 640 * S3c * (80 * Tint 1) * (Real.exp (-(2 * π * 1 * (y - 1)))
      + Real.exp (-(2 * π * 1 * (y - 1))) * Real.exp (π * y + 12 * qb 1)) + 1 / (162 * y ^ 6)
  have e2 : Real.exp (-(2 * π * 1 * (y - 1))) * Real.exp (π * y + 12 * qb 1)
      = Real.exp (2 * π + 12 * qb 1) * Real.exp (-π * y) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have e1 : Real.exp (-(2 * π * 1 * (y - 1))) = Real.exp (2 * π) * Real.exp (-(2 * π) * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e3 : y ^ (-6 : ℝ) = (y ^ 6)⁻¹ := by
    rw [Real.rpow_neg hy0.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e2, e1, e3]
  ring

/-! ## Integrability of `FS s` on the two pieces -/

theorem integrableOn_FS_Ioc {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IntegrableOn (FS s) (Set.Ioc (0 : ℝ) 1) := by
  obtain ⟨Kb, hKb⟩ := pole_part_le
  have hm : AEStronglyMeasurable (FS s) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ((continuousOn_FS s).mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  have hb : ∀ᵐ y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖FS s y‖ ≤ (1 + (xm 1)⁻¹) * |f0 y| + Kb := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_)
    rw [Real.norm_eq_abs]
    exact FS_bound_Ioc hKb hy hs0 hs1
  exact Integrable.mono' (boundIoc_integrable Kb) hm hb

theorem integrableOn_FS_Ioi {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IntegrableOn (FS s) (Set.Ioi (1 : ℝ)) := by
  have hm : AEStronglyMeasurable (FS s) (volume.restrict (Set.Ioi (1 : ℝ))) :=
    ((continuousOn_FS s).mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi
  have hb : ∀ᵐ y ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ‖FS s y‖ ≤ 640 * S3c * (80 * Tint 1) * (Real.exp (-(2 * π * 1 * (y - 1)))
        + Real.exp (-(2 * π * 1 * (y - 1))) * Real.exp (π * y + 12 * qb 1))
        + 1 / (162 * y ^ 6) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => ?_)
    rw [Real.norm_eq_abs]
    exact FS_bound_Ioi (Set.mem_Ioi.mp hy) hs0 hs1
  exact Integrable.mono' boundIoi_integrable hm hb

/-! ## Dominated convergence on each piece -/

theorem tendsto_int_Ioc :
    Filter.Tendsto (fun s : ℝ => ∫ y in Set.Ioc (0 : ℝ) 1, FS s y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ y in Set.Ioc (0 : ℝ) 1, f0 y)) := by
  obtain ⟨Kb, hKb⟩ := pole_part_le
  have hm : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (FS s) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall (fun s =>
      ((continuousOn_FS s).mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
  have hb : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ᵐ y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖FS s y‖ ≤ (1 + (xm 1)⁻¹) * |f0 y| + Kb := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_)
    rw [Real.norm_eq_abs]
    exact FS_bound_Ioc hKb hy hs.1.le hs.2.le
  have hl : ∀ᵐ y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      Filter.Tendsto (fun s : ℝ => FS s y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f0 y)) :=
    ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => tendsto_FS hy.1)
  have hD := tendsto_integral_filter_of_dominated_convergence (F := FS) (f := f0)
    (fun y : ℝ => (1 + (xm 1)⁻¹) * |f0 y| + Kb) hm hb (boundIoc_integrable Kb) hl
  exact hD

theorem tendsto_int_Ioi1 :
    Filter.Tendsto (fun s : ℝ => ∫ y in Set.Ioi (1 : ℝ), FS s y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ y in Set.Ioi (1 : ℝ), f0 y)) := by
  have hm : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (FS s) (volume.restrict (Set.Ioi (1 : ℝ))) :=
    Filter.Eventually.of_forall (fun s =>
      ((continuousOn_FS s).mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi)
  have hb : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ᵐ y ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ‖FS s y‖ ≤ 640 * S3c * (80 * Tint 1) * (Real.exp (-(2 * π * 1 * (y - 1)))
        + Real.exp (-(2 * π * 1 * (y - 1))) * Real.exp (π * y + 12 * qb 1))
        + 1 / (162 * y ^ 6) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => ?_)
    rw [Real.norm_eq_abs]
    exact FS_bound_Ioi (Set.mem_Ioi.mp hy) hs.1.le hs.2.le
  have hl : ∀ᵐ y ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      Filter.Tendsto (fun s : ℝ => FS s y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f0 y)) :=
    ae_restrict_of_forall_mem measurableSet_Ioi
      (fun y hy => tendsto_FS (lt_trans one_pos (Set.mem_Ioi.mp hy)))
  have hD := tendsto_integral_filter_of_dominated_convergence (F := FS) (f := f0)
    (fun y : ℝ => 640 * S3c * (80 * Tint 1) * (Real.exp (-(2 * π * 1 * (y - 1)))
      + Real.exp (-(2 * π * 1 * (y - 1))) * Real.exp (π * y + 12 * qb 1)) + 1 / (162 * y ^ 6))
    hm hb boundIoi_integrable hl
  exact hD

/-! ## Assembling the limit -/

theorem JS_sub_poleS {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    JS s - poleS s = (∫ y in Set.Ioc (0 : ℝ) 1, FS s y) + ∫ y in Set.Ioi (1 : ℝ), FS s y := by
  have hPne : poleS s ≠ 0 := by
    intro h0
    have h := pole_eq hs0
    rw [h0, mul_zero] at h
    have hpos : 0 < 72 / s ^ 5 := div_pos (by norm_num) (pow_pos hs0 5)
    linarith
  have hP : IntegrableOn (fun y : ℝ => Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6))
      (Set.Ioi 0) := Integrable.of_integral_ne_zero hPne
  have hFc := integrableOn_FS_Ioc hs0.le hs1
  have hFi := integrableOn_FS_Ioi hs0.le hs1
  have hF : IntegrableOn (FS s) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hFc.union hFi
  have hJ : IntegrableOn (fun y : ℝ => g4 y * A1 y * xm y ^ (-s)) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.add hF hP) (fun y _ => ?_) measurableSet_Ioi
    show FS s y + Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6) = g4 y * A1 y * xm y ^ (-s)
    unfold FS
    ring
  have hsub := integral_sub hJ hP
  have hu := setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hFc hFi
  rw [Set.Ioc_union_Ioi_eq_Ioi zero_le_one] at hu
  unfold JS poleS
  rw [← hsub]
  exact hu

theorem D01_split :
    D01 = (∫ y in Set.Ioc (0 : ℝ) 1, f0 y) + ∫ y in Set.Ioi (1 : ℝ), f0 y := by
  have hu := setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (integrableOn_f0.mono_set Set.Ioc_subset_Ioi_self)
    (integrableOn_f0.mono_set (Set.Ioi_subset_Ioi zero_le_one))
  rw [Set.Ioc_union_Ioi_eq_Ioi zero_le_one] at hu
  unfold D01
  exact hu

/-- **The limit `LimBM`, with no hypotheses.** -/
theorem limBM : LimBM := by
  unfold LimBM
  have h := tendsto_int_Ioc.add tendsto_int_Ioi1
  rw [← D01_split] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
  exact (JS_sub_poleS hs.1 hs.2.le).symm

/-- **`RungBM` from Zhou's two parametrisations alone.** -/
theorem rungBM_of_zhou2 (hF : ZhouF) (hG : ZhouG) : RungBM :=
  rungBM_of_zhou hF hG limBM

/-- **The six-step theorem from `RungBP` and Zhou's two parametrisations.** -/
theorem rv6_of_zhou2 (hP : RungBP) (hF : ZhouF) (hG : ZhouG) : mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_zhou hP hF hG limBM

end Tower.RV6
