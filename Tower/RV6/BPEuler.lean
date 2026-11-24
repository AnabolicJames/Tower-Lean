import Mathlib
import Tower.RV6.KZero
import Tower.RV6.LadderA2

/-!
# RungBP, step 5: `eulerW = -γ`, so `a₀ = log 2 - γ`

`eulerW = E₁(1) - ∫₀¹ (1 - e^{-w})/w dw` (`KZero`).  Mathlib has
`γ = -∫₀^∞ log t · e^{-t} dt`.  The integral is split at `1`:

* on `(0, 1]`, `G(t) = log t · (1 - e^{-t})` has `G' = psiE t + log t · e^{-t}` and
  `G(0+) = G(1) = 0`, so `∫₀¹ log t · e^{-t} = -∫₀¹ psiE`;
* on `(1, ∞)`, `F(t) = -log t · e^{-t}` has `F' = -e^{-t}/t + log t · e^{-t}` and
  `F(1) = F(∞) = 0`, so `∫₁^∞ log t · e^{-t} = ∫₁^∞ e^{-t}/t = E₁(1)` (`expE_one`).
-/

namespace Tower.RV6

open Real MeasureTheory Set Filter Topology

theorem integrableOn_mul_exp_neg :
    IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show Real.exp (-t) * t ^ ((2 : ℝ) - 1) = t * Real.exp (-t)
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm]

theorem log_mul_exp_neg_le {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ Real.log t * Real.exp (-t) ∧ Real.log t * Real.exp (-t) ≤ t * Real.exp (-t) := by
  have he := (Real.exp_pos (-t)).le
  refine ⟨mul_nonneg (Real.log_nonneg ht) he, mul_le_mul_of_nonneg_right ?_ he⟩
  have := Real.log_le_sub_one_of_pos (show 0 < t by linarith)
  linarith

theorem integrableOn_log_mul_exp_Ioi_one :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi 1) := by
  refine Integrable.mono' (integrableOn_mul_exp_neg.mono_set (Ioi_subset_Ioi zero_le_one)) ?_ ?_
  · exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have h := log_mul_exp_neg_le (le_of_lt (show (1 : ℝ) < t from ht))
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2

theorem integrableOn_exp_neg_div_Ioi_one :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi 1) := by
  refine Integrable.mono' (integrableOn_mul_exp_neg.mono_set (Ioi_subset_Ioi zero_le_one)) ?_ ?_
  · exact ((Real.measurable_exp.comp measurable_neg).div measurable_id).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have he := (Real.exp_pos (-t)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg he (by linarith))]
    calc Real.exp (-t) / t ≤ Real.exp (-t) := div_le_self he ht1.le
      _ ≤ t * Real.exp (-t) := le_mul_of_one_le_left he ht1.le

theorem integral_log_mul_exp_Ioi_one :
    ∫ t in Ioi (1 : ℝ), Real.log t * Real.exp (-t) = expE 1 := by
  rw [expE_one]
  have hF : ∀ x ∈ Ici (1 : ℝ), HasDerivAt (fun t : ℝ => -(Real.log t * Real.exp (-t)))
      (-(Real.exp (-x) / x) + Real.log x * Real.exp (-x)) x := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := hx
    have hx0 : x ≠ 0 := (show (0 : ℝ) < x by linarith).ne'
    have h1 := ((Real.hasDerivAt_log hx0).mul ((hasDerivAt_neg x).exp)).neg
    convert h1 using 1
    ring
  have hA : IntegrableOn (fun x : ℝ => -(Real.exp (-x) / x)) (Ioi 1) :=
    Integrable.neg integrableOn_exp_neg_div_Ioi_one
  have hint : IntegrableOn (fun x : ℝ => -(Real.exp (-x) / x) + Real.log x * Real.exp (-x))
      (Ioi 1) := Integrable.add hA integrableOn_log_mul_exp_Ioi_one
  have h0 : Tendsto (fun t : ℝ => t * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 : Tendsto (fun t : ℝ => Real.log t * Real.exp (-t)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact (log_mul_exp_neg_le ht).1
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact (log_mul_exp_neg_le ht).2
  have hlim : Tendsto (fun t : ℝ => -(Real.log t * Real.exp (-t))) atTop (𝓝 0) := by
    simpa using h2.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hF hint hlim
  rw [integral_add hA integrableOn_log_mul_exp_Ioi_one, integral_neg] at h
  simp only [Real.log_one, zero_mul, neg_zero, sub_zero] at h
  linarith

theorem abs_one_sub_exp_neg_le {t : ℝ} (ht : 0 ≤ t) : |1 - Real.exp (-t)| ≤ t := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 := Real.add_one_le_exp (-t)
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem integral_log_mul_exp_zero_one :
    ∫ t in (0 : ℝ)..1, Real.log t * Real.exp (-t) = -∫ t in (0 : ℝ)..1, psiE t := by
  set G : ℝ → ℝ := fun t => Real.log t * (1 - Real.exp (-t)) with hG
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt G (psiE t + Real.log t * Real.exp (-t)) t := by
    intro t ht
    have h1 := (Real.hasDerivAt_log ht.1.ne').mul (((hasDerivAt_neg t).exp).const_sub 1)
    convert h1 using 1
    simp only [psiE]
    ring
  have hlog : IntervalIntegrable (fun t : ℝ => Real.log t * Real.exp (-t)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.mul_continuousOn
      (Real.continuous_exp.comp continuous_neg).continuousOn
  have hpsi : IntervalIntegrable psiE volume 0 1 := intervalIntegrable_psiE le_rfl zero_le_one
  have hint : IntervalIntegrable (fun t => psiE t + Real.log t * Real.exp (-t)) volume 0 1 :=
    hpsi.add hlog
  have hb : Tendsto G (𝓝[<] 1) (𝓝 0) := by
    have hc : ContinuousAt G 1 :=
      (Real.continuousAt_log one_ne_zero).mul
        (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousAt
    have : G 1 = 0 := by simp [hG]
    rw [← this]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have ha : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    have hm : Tendsto (fun t : ℝ => |t * Real.log t|) (𝓝[>] 0) (𝓝 0) := by
      have h := (continuous_abs.comp Real.continuous_mul_log).tendsto 0
      simp only [Function.comp_def, zero_mul, abs_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hm
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) ≤ t := (show (0 : ℝ) < t from ht).le
    simp only [hG, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg ht0, mul_comm t]
    exact mul_le_mul_of_nonneg_left (abs_one_sub_exp_neg_le ht0) (abs_nonneg _)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hderiv hint ha hb
  rw [intervalIntegral.integral_add hpsi hlog] at h
  linarith

/-- `eulerW` is minus the Euler–Mascheroni constant. -/
theorem eulerW_eq : eulerW = -Real.eulerMascheroniConstant := by
  rw [Real.eulerMascheroniConstant_eq_neg_integral_log, neg_neg]
  have hI1 : IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).1
      (intervalIntegral.intervalIntegrable_log'.mul_continuousOn
        (Real.continuous_exp.comp continuous_neg).continuousOn)
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hI1
      integrableOn_log_mul_exp_Ioi_one,
    ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1), integral_log_mul_exp_zero_one,
    integral_log_mul_exp_Ioi_one, eulerW]
  ring

/-- `a₀ = log 2 - γ`. -/
theorem a0_eq_gamma : a0 = Real.log 2 - Real.eulerMascheroniConstant := by
  rw [a0, eulerW_eq]
  ring

end Tower.RV6
