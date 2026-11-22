import Mathlib
import Tower.RV6.Defs
import Tower.RV6.Ladder
import Tower.RV6.EtaRec
import Tower.RV6.BesselJ
import Tower.RV6.Laplace
import Tower.RV6.LogInt
import Tower.RV6.CharFun
import Tower.RV6.CubeLog

/-!
# Rung A1: the random-walk representation of the six-step Mahler measure

`m(1 + x₁ + ⋯ + x₅) = log 2 + ∫₀^∞ (e^{-t} - J₀(t)⁶) dt/t`  (`rungA1 : RungA1`).

For `δ > 0`, `integral_cube_logG` gives
`∫_{[0,1]⁵} log (δ + √(|X|² + δ²)) = log 2 + ∫₀^∞ (e^{-t} - e^{-δt} J₀(t)⁶) dt/t`.  Along
`δ_n = 1/(n+1)`:

* the right side tends to `walkSide` (`tendsto_walk_damped`, dominated convergence);
* the integrands on the left are `≤ log 8`, equal `log (2δ_n)` on `{X = 0}`, and their integrals
  are bounded below, so `{X = 0}` is a null set (`ae_cubeX_ne_zero`);
* they decrease to `log |X|` off that set; a limit of an antitone sequence of integrable functions
  with integrals bounded below is integrable (`integrable_of_antitone_of_tendsto`), and monotone
  convergence identifies the limit of the integrals with `mu6`.

Consequence: `rv6_of_A2_B : RungA2 → RungB → mu6 = 648 / π ^ 6 * Lf5`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## A monotone limit is integrable -/

/-- An almost-everywhere limit of an antitone sequence of integrable functions whose integrals are
bounded below is integrable. -/
theorem integrable_of_antitone_of_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hFm : AEStronglyMeasurable F μ)
    (hanti : ∀ᵐ x ∂μ, Antitone fun n => f n x)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (F x)))
    {c : ℝ} (hc : ∀ n, c ≤ ∫ x, f n x ∂μ) : Integrable F μ := by
  have hsub : ∀ n, Integrable (fun x => f 0 x - f n x) μ := fun n => (hf 0).sub (hf n)
  have hu_nn : ∀ n, 0 ≤ᵐ[μ] fun x => f 0 x - f n x := by
    intro n
    filter_upwards [hanti] with x hx
    show (0 : ℝ) ≤ f 0 x - f n x
    have h : f n x ≤ f 0 x := hx (Nat.zero_le n)
    linarith
  have hU_nn : 0 ≤ᵐ[μ] fun x => f 0 x - F x := by
    filter_upwards [hanti, hlim] with x hx hl
    show (0 : ℝ) ≤ f 0 x - F x
    have h : F x ≤ f 0 x := le_of_tendsto' hl (fun n => hx (Nat.zero_le n))
    linarith
  have hmono : ∀ᵐ x ∂μ, Monotone fun n => ENNReal.ofReal (f 0 x - f n x) := by
    filter_upwards [hanti] with x hx n m hnm
    show ENNReal.ofReal (f 0 x - f n x) ≤ ENNReal.ofReal (f 0 x - f m x)
    have h : f m x ≤ f n x := hx hnm
    have h' : f 0 x - f n x ≤ f 0 x - f m x := by linarith
    exact ENNReal.ofReal_le_ofReal h'
  have htend : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => ENNReal.ofReal (f 0 x - f n x)) Filter.atTop
      (nhds (ENNReal.ofReal (f 0 x - F x))) := by
    filter_upwards [hlim] with x hl
    have h1 : Filter.Tendsto (fun n => f 0 x - f n x) Filter.atTop (nhds (f 0 x - F x)) :=
      hl.const_sub (f 0 x)
    exact (ENNReal.continuous_ofReal.tendsto _).comp h1
  have hmeas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (f 0 x - f n x)) μ :=
    fun n => (hsub n).aemeasurable.ennreal_ofReal
  have hL : Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f 0 x - f n x) ∂μ) Filter.atTop
      (nhds (∫⁻ x, ENNReal.ofReal (f 0 x - F x) ∂μ)) :=
    lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htend
  have hle : ∫⁻ x, ENNReal.ofReal (f 0 x - F x) ∂μ ≤ ENNReal.ofReal (∫ x, f 0 x ∂μ - c) := by
    refine le_of_tendsto' hL (fun n => ?_)
    show ∫⁻ x, ENNReal.ofReal (f 0 x - f n x) ∂μ ≤ ENNReal.ofReal (∫ x, f 0 x ∂μ - c)
    have h1 : ∫⁻ x, ENNReal.ofReal (f 0 x - f n x) ∂μ
        = ENNReal.ofReal (∫ x, (f 0 x - f n x) ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hsub n) (hu_nn n)).symm
    have h2 : ∫ x, (f 0 x - f n x) ∂μ = ∫ x, f 0 x ∂μ - ∫ x, f n x ∂μ :=
      integral_sub (hf 0) (hf n)
    have h3 : ∫ x, f 0 x ∂μ - ∫ x, f n x ∂μ ≤ ∫ x, f 0 x ∂μ - c := by linarith [hc n]
    rw [h1, h2]
    exact ENNReal.ofReal_le_ofReal h3
  have hfin : HasFiniteIntegral (fun x => f 0 x - F x) μ :=
    (hasFiniteIntegral_iff_ofReal hU_nn).mpr (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have hdiff : Integrable (fun x => f 0 x - F x) μ :=
    ⟨(hf 0).aestronglyMeasurable.sub hFm, hfin⟩
  have h := (hf 0).sub hdiff
  refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
  show f 0 x - (f 0 x - F x) = F x
  ring

/-! ## The damping sequence -/

/-- `δ_n = 1/(n+1)`. -/
noncomputable def dampSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem dampSeq_pos (n : ℕ) : 0 < dampSeq n := by
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  exact one_div_pos.mpr hpos

theorem dampSeq_le_one (n : ℕ) : dampSeq n ≤ 1 := by
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  exact (div_le_one hpos).mpr h1

theorem dampSeq_anti {n m : ℕ} (h : n ≤ m) : dampSeq m ≤ dampSeq n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnm : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr h
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hle : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by linarith
  exact one_div_le_one_div_of_le hpos hle

theorem tendsto_dampSeq : Filter.Tendsto dampSeq Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact h

/-! ## The damping removed on the walk side -/

/-- `J₀(t)⁶ ∈ [0, 1]` for `t ≥ 0`. -/
theorem besselJ0_pow_six_mem {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ besselJ0 t ^ 6 ∧ besselJ0 t ^ 6 ≤ 1 := by
  have h := pow_six_bound (abs_besselJ0_le_one ht)
  have e : besselJ0 t ^ 6 = (besselJ0 t ^ 3) ^ 2 := by ring
  constructor
  · rw [e]
    exact sq_nonneg _
  · linarith [h.1]

/-- For `t ≥ 1`: `J₀(t)⁶ t ≤ E(1)`. -/
theorem besselJ0_pow_six_mul_le {t : ℝ} (ht : 1 ≤ t) : besselJ0 t ^ 6 * t ≤ besselJE 1 := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hsq := besselJ0_sq_le ht
  have hsq' : besselJ0 t * besselJ0 t * t ≤ besselJE 1 := (le_div_iff₀ ht0).mp hsq
  have hA2 : besselJ0 t * besselJ0 t ≤ 1 := by
    have h := besselJ_sq_le_one ht0.le
    have h1 := mul_self_nonneg (besselJ1 t)
    linarith
  have hA2n : 0 ≤ besselJ0 t * besselJ0 t := mul_self_nonneg _
  have h44 : (besselJ0 t * besselJ0 t) * (besselJ0 t * besselJ0 t) ≤ 1 := by
    calc (besselJ0 t * besselJ0 t) * (besselJ0 t * besselJ0 t)
        ≤ 1 * 1 := mul_le_mul hA2 hA2 hA2n zero_le_one
      _ = 1 := one_mul 1
  have e : besselJ0 t ^ 6 * t = (besselJ0 t * besselJ0 t * t)
      * ((besselJ0 t * besselJ0 t) * (besselJ0 t * besselJ0 t)) := by ring
  have hn : 0 ≤ besselJ0 t * besselJ0 t * t := mul_nonneg hA2n ht0.le
  rw [e]
  calc (besselJ0 t * besselJ0 t * t) * ((besselJ0 t * besselJ0 t) * (besselJ0 t * besselJ0 t))
      ≤ (besselJ0 t * besselJ0 t * t) * 1 := mul_le_mul_of_nonneg_left h44 hn
    _ = besselJ0 t * besselJ0 t * t := mul_one _
    _ ≤ besselJE 1 := hsq'

theorem exp_neg_damp_le_one {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) : Real.exp (-δ * t) ≤ 1 := by
  have hδt : 0 ≤ δ * t := mul_nonneg hδ ht.le
  have h := Real.exp_le_exp.mpr (by linarith : -δ * t ≤ 0)
  rw [Real.exp_zero] at h
  exact h

/-- The damping term `(1 - e^{-δt}) J₀(t)⁶ / t` is nonnegative. -/
theorem damping_term_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) {t : ℝ} (ht : 0 < t) :
    0 ≤ (1 - Real.exp (-δ * t)) * besselJ0 t ^ 6 / t := by
  have hq := (besselJ0_pow_six_mem ht.le).1
  have hd1 := exp_neg_damp_le_one hδ0 ht
  have hs : 0 ≤ 1 - Real.exp (-δ * t) := by linarith
  exact div_nonneg (mul_nonneg hs hq) ht.le

/-- The damping term is at most `(2 + 2 E(1)) / (1 + t²)` for `0 ≤ δ ≤ 1`. -/
theorem damping_term_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : 0 < t) :
    (1 - Real.exp (-δ * t)) * besselJ0 t ^ 6 / t
      ≤ (2 + 2 * besselJE 1) * (1 + t ^ 2)⁻¹ := by
  obtain ⟨hq0, hq1⟩ := besselJ0_pow_six_mem ht.le
  have hE := besselJE_one_nonneg
  have hδt : 0 ≤ δ * t := mul_nonneg hδ0 ht.le
  have hd1 := exp_neg_damp_le_one hδ0 ht
  have hd2 : -δ * t + 1 ≤ Real.exp (-δ * t) := Real.add_one_le_exp (-δ * t)
  have hd0 := Real.exp_pos (-δ * t)
  have hs0 : 0 ≤ 1 - Real.exp (-δ * t) := by linarith
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hw : 0 < (1 + t ^ 2)⁻¹ := inv_pos.mpr hpos
  have e1 : (1 + t ^ 2) * (1 + t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  rw [div_le_iff₀ ht]
  rcases le_total t 1 with h | h
  · have hδt1 : δ * t ≤ 1 * t := mul_le_mul_of_nonneg_right hδ1 ht.le
    have hs1 : 1 - Real.exp (-δ * t) ≤ t := by linarith
    have hsq : (1 - Real.exp (-δ * t)) * besselJ0 t ^ 6 ≤ t * 1 :=
      mul_le_mul hs1 hq1 hq0 ht.le
    have htt : t * t ≤ 1 * 1 := mul_le_mul h h ht.le zero_le_one
    have ht2 : 0 ≤ 1 - t ^ 2 := by
      rw [pow_two]
      linarith
    have h3 : 0 ≤ (1 + t ^ 2)⁻¹ * (1 - t ^ 2) := mul_nonneg hw.le ht2
    have e2 : (1 + t ^ 2)⁻¹ * (1 - t ^ 2)
        = 2 * (1 + t ^ 2)⁻¹ - (1 + t ^ 2) * (1 + t ^ 2)⁻¹ := by ring
    have h2w : 1 ≤ 2 * (1 + t ^ 2)⁻¹ := by linarith
    have h4 : t * 1 ≤ t * (2 * (1 + t ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h2w ht.le
    have h5 : 0 ≤ 2 * besselJE 1 * (1 + t ^ 2)⁻¹ * t :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hE) hw.le) ht.le
    have e3 : (2 + 2 * besselJE 1) * (1 + t ^ 2)⁻¹ * t
        = t * (2 * (1 + t ^ 2)⁻¹) + 2 * besselJE 1 * (1 + t ^ 2)⁻¹ * t := by ring
    rw [e3]
    linarith
  · have hs1 : 1 - Real.exp (-δ * t) ≤ 1 := by linarith
    have hqt := besselJ0_pow_six_mul_le h
    have hsq : (1 - Real.exp (-δ * t)) * besselJ0 t ^ 6 ≤ 1 * besselJ0 t ^ 6 :=
      mul_le_mul_of_nonneg_right hs1 hq0
    have htt : 1 * 1 ≤ t * t := mul_le_mul h h zero_le_one ht.le
    have ht2 : 0 ≤ t ^ 2 - 1 := by
      rw [pow_two]
      linarith
    have h3 : 0 ≤ (1 + t ^ 2)⁻¹ * (t ^ 2 - 1) := mul_nonneg hw.le ht2
    have e2 : (1 + t ^ 2)⁻¹ * (t ^ 2 - 1)
        = 2 * (1 + t ^ 2)⁻¹ * t ^ 2 - (1 + t ^ 2) * (1 + t ^ 2)⁻¹ := by ring
    have h2w : 1 ≤ 2 * (1 + t ^ 2)⁻¹ * t ^ 2 := by linarith
    have hii : besselJ0 t ^ 6 ≤ 2 * besselJE 1 * (1 + t ^ 2)⁻¹ * t := by
      calc besselJ0 t ^ 6
          ≤ besselJ0 t ^ 6 * (2 * (1 + t ^ 2)⁻¹ * t ^ 2) := le_mul_of_one_le_right hq0 h2w
        _ = besselJ0 t ^ 6 * t * (2 * (1 + t ^ 2)⁻¹ * t) := by ring
        _ ≤ besselJE 1 * (2 * (1 + t ^ 2)⁻¹ * t) :=
            mul_le_mul_of_nonneg_right hqt
              (mul_nonneg (mul_nonneg zero_le_two hw.le) ht.le)
        _ = 2 * besselJE 1 * (1 + t ^ 2)⁻¹ * t := by ring
    have h5 : 0 ≤ 2 * (1 + t ^ 2)⁻¹ * t := mul_nonneg (mul_nonneg zero_le_two hw.le) ht.le
    have e3 : (2 + 2 * besselJE 1) * (1 + t ^ 2)⁻¹ * t
        = 2 * (1 + t ^ 2)⁻¹ * t + 2 * besselJE 1 * (1 + t ^ 2)⁻¹ * t := by ring
    rw [e3]
    linarith

/-- The damped walk integrand is dominated, uniformly in `0 ≤ δ ≤ 1`. -/
theorem walk_damped_abs_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : 0 < t) :
    |(Real.exp (-t) - Real.exp (-δ * t) * besselJ0 t ^ 6) / t|
      ≤ |(Real.exp (-t) - besselJ0 t ^ 6) / t| + (2 + 2 * besselJE 1) * (1 + t ^ 2)⁻¹ := by
  have e : (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 t ^ 6) / t
      = (Real.exp (-t) - besselJ0 t ^ 6) / t
        + (1 - Real.exp (-δ * t)) * besselJ0 t ^ 6 / t := by ring
  have hD0 := damping_term_nonneg hδ0 ht
  have hD1 := damping_term_le hδ0 hδ1 ht
  rw [e]
  calc |(Real.exp (-t) - besselJ0 t ^ 6) / t + (1 - Real.exp (-δ * t)) * besselJ0 t ^ 6 / t|
      ≤ |(Real.exp (-t) - besselJ0 t ^ 6) / t|
        + |(1 - Real.exp (-δ * t)) * besselJ0 t ^ 6 / t| := abs_add_le _ _
    _ = |(Real.exp (-t) - besselJ0 t ^ 6) / t|
        + (1 - Real.exp (-δ * t)) * besselJ0 t ^ 6 / t := by rw [abs_of_nonneg hD0]
    _ ≤ |(Real.exp (-t) - besselJ0 t ^ 6) / t| + (2 + 2 * besselJE 1) * (1 + t ^ 2)⁻¹ := by
        linarith

theorem measurable_walk_damped (δ : ℝ) :
    Measurable fun t : ℝ => (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 t ^ 6) / t := by
  have h1 : Continuous fun t : ℝ => Real.exp (-t) - Real.exp (-δ * t) * besselJ0 t ^ 6 :=
    (Real.continuous_exp.comp continuous_neg).sub
      ((continuous_exp_neg_mul δ).mul (continuous_besselJ0.pow 6))
  exact h1.measurable.div measurable_id

/-- `∫₀^∞ (e^{-t} - e^{-δ_n t} J₀(t)⁶) dt/t → ∫₀^∞ (e^{-t} - J₀(t)⁶) dt/t`. -/
theorem tendsto_walk_damped :
    Filter.Tendsto (fun n : ℕ => ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-t) - Real.exp (-dampSeq n * t) * besselJ0 t ^ 6) / t)
      Filter.atTop
      (nhds (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t) - besselJ0 t ^ 6) / t)) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun t : ℝ => (Real.exp (-t) - Real.exp (-dampSeq n * t) * besselJ0 t ^ 6) / t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun n => (measurable_walk_damped (dampSeq n)).aestronglyMeasurable
  have h0 : Integrable (fun t : ℝ => (Real.exp (-t) - besselJ0 t ^ 6) / t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := integrableOn_walk_integrand
  have hb1 : Integrable (fun t : ℝ => |(Real.exp (-t) - besselJ0 t ^ 6) / t|)
      (volume.restrict (Set.Ioi (0 : ℝ))) := h0.abs
  have hb0 : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
    integrable_inv_one_add_sq.integrableOn
  have hb2 : Integrable (fun t : ℝ => (2 + 2 * besselJE 1) * (1 + t ^ 2)⁻¹)
      (volume.restrict (Set.Ioi (0 : ℝ))) := Integrable.const_mul hb0 (2 + 2 * besselJE 1)
  have hb : Integrable (fun t : ℝ => |(Real.exp (-t) - besselJ0 t ^ 6) / t|
      + (2 + 2 * besselJE 1) * (1 + t ^ 2)⁻¹) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hb1.add hb2
  have hbound : ∀ n : ℕ, ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(Real.exp (-t) - Real.exp (-dampSeq n * t) * besselJ0 t ^ 6) / t‖
        ≤ |(Real.exp (-t) - besselJ0 t ^ 6) / t| + (2 + 2 * besselJE 1) * (1 + t ^ 2)⁻¹ := by
    intro n
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs]
    exact walk_damped_abs_le (dampSeq_pos n).le (dampSeq_le_one n) ht0
  have hlim : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Filter.Tendsto
        (fun n : ℕ => (Real.exp (-t) - Real.exp (-dampSeq n * t) * besselJ0 t ^ 6) / t)
        Filter.atTop (nhds ((Real.exp (-t) - besselJ0 t ^ 6) / t)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h1 : Continuous fun d : ℝ => -d * t := continuous_neg.mul continuous_const
    have h2 : Continuous fun d : ℝ => Real.exp (-d * t) := Real.continuous_exp.comp h1
    have h3 : Continuous fun d : ℝ => Real.exp (-t) - Real.exp (-d * t) * besselJ0 t ^ 6 :=
      continuous_const.sub (h2.mul continuous_const)
    have h4 : Continuous fun d : ℝ =>
        (Real.exp (-t) - Real.exp (-d * t) * besselJ0 t ^ 6) / t := h3.div_const t
    have hT : Filter.Tendsto
        (fun n : ℕ => (Real.exp (-t) - Real.exp (-dampSeq n * t) * besselJ0 t ^ 6) / t)
        Filter.atTop (nhds ((Real.exp (-t) - Real.exp (-0 * t) * besselJ0 t ^ 6) / t)) :=
      (h4.tendsto 0).comp tendsto_dampSeq
    have e0 : (Real.exp (-t) - Real.exp (-0 * t) * besselJ0 t ^ 6) / t
        = (Real.exp (-t) - besselJ0 t ^ 6) / t := by
      rw [neg_zero, zero_mul, Real.exp_zero, one_mul]
    rw [e0] at hT
    exact hT
  exact tendsto_integral_of_dominated_convergence
    (fun t : ℝ => |(Real.exp (-t) - besselJ0 t ^ 6) / t|
      + (2 + 2 * besselJE 1) * (1 + t ^ 2)⁻¹)
    hmeas hb hbound hlim

/-! ## The functions `log (δ + √(|X|² + δ²))` on the cube -/

/-- `g_δ(τ) = log (δ + √(|X(τ)|² + δ²))`. -/
noncomputable def cubeG (δ : ℝ) (τ : Fin 5 → ℝ) : ℝ :=
  Real.log (δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ))

theorem cubeG_arg_pos {δ : ℝ} (hδ : 0 < δ) (τ : Fin 5 → ℝ) :
    0 < δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ) := by
  have h := Real.sqrt_nonneg (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ)
  linarith

theorem continuous_cubeG {δ : ℝ} (hδ : 0 < δ) : Continuous (cubeG δ) := by
  have h1 : Continuous fun τ : Fin 5 → ℝ => ‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ :=
    (continuous_norm_cubeX.mul continuous_norm_cubeX).add continuous_const
  have h2 : Continuous fun τ : Fin 5 → ℝ =>
      Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ) := h1.sqrt
  have h3 : Continuous fun τ : Fin 5 → ℝ =>
      δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ) := continuous_const.add h2
  have h4 : Continuous fun τ : Fin 5 → ℝ =>
      Real.log (δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ)) :=
    h3.log (fun τ => (cubeG_arg_pos hδ τ).ne')
  exact h4

theorem integrable_cubeG {δ : ℝ} (hδ : 0 < δ) :
    Integrable (cubeG δ) (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) :=
  (continuous_cubeG hδ).integrableOn_Icc

theorem integral_cubeG {δ : ℝ} (hδ : 0 < δ) :
    ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeG δ τ
      = Real.log 2 + ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-t) - Real.exp (-δ * t) * besselJ0 t ^ 6) / t :=
  integral_cube_logG hδ

/-- `g_δ ≤ log 8` for `0 < δ ≤ 1`. -/
theorem cubeG_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (τ : Fin 5 → ℝ) :
    cubeG δ τ ≤ Real.log 8 := by
  have ha : 0 ≤ ‖cubeX τ‖ := norm_nonneg _
  have ha6 := norm_cubeX_le τ
  have haa : ‖cubeX τ‖ * ‖cubeX τ‖ ≤ 6 * 6 := mul_le_mul ha6 ha6 ha (by norm_num)
  have hdd : δ * δ ≤ 1 * 1 := mul_le_mul hδ1 hδ1 hδ.le zero_le_one
  have e49 : (7 : ℝ) ^ 2 = 49 := by norm_num
  have h7 : (0 : ℝ) ≤ 7 := by norm_num
  have hs : Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ) ≤ 7 := by
    rw [Real.sqrt_le_left h7, e49]
    linarith
  have harg : δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ) ≤ 8 := by linarith
  show Real.log (δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ)) ≤ Real.log 8
  exact Real.log_le_log (cubeG_arg_pos hδ τ) harg

/-- `g_δ` is monotone in `δ > 0`. -/
theorem cubeG_mono {δ' δ : ℝ} (hδ' : 0 < δ') (h : δ' ≤ δ) (τ : Fin 5 → ℝ) :
    cubeG δ' τ ≤ cubeG δ τ := by
  have hdd : δ' * δ' ≤ δ * δ := mul_le_mul h h hδ'.le (le_trans hδ'.le h)
  have hle : ‖cubeX τ‖ * ‖cubeX τ‖ + δ' * δ' ≤ ‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ := by linarith
  have hs : Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ' * δ')
      ≤ Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ) := Real.sqrt_le_sqrt hle
  have harg : δ' + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ' * δ')
      ≤ δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ) := by linarith
  show Real.log (δ' + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ' * δ'))
    ≤ Real.log (δ + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + δ * δ))
  exact Real.log_le_log (cubeG_arg_pos hδ' τ) harg

/-- On the zero set of `X`, `g_δ = log (2δ)`. -/
theorem cubeG_of_eq_zero {δ : ℝ} (hδ : 0 ≤ δ) {τ : Fin 5 → ℝ} (hτ : cubeX τ = 0) :
    cubeG δ τ = Real.log (δ + δ) := by
  unfold cubeG
  rw [hτ, norm_zero, zero_mul, zero_add, Real.sqrt_mul_self hδ]

/-- Off the zero set of `X`, `g_{δ_n} → log |X|`. -/
theorem tendsto_cubeG {τ : Fin 5 → ℝ} (hτ : cubeX τ ≠ 0) :
    Filter.Tendsto (fun n : ℕ => cubeG (dampSeq n) τ) Filter.atTop
      (nhds (Real.log ‖cubeX τ‖)) := by
  have ha : 0 < ‖cubeX τ‖ := norm_pos_iff.mpr hτ
  have h1 : Continuous fun d : ℝ => ‖cubeX τ‖ * ‖cubeX τ‖ + d * d :=
    continuous_const.add (continuous_id'.mul continuous_id')
  have h2 : Continuous fun d : ℝ => d + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + d * d) :=
    continuous_id'.add h1.sqrt
  have hT : Filter.Tendsto
      (fun n : ℕ => dampSeq n + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + dampSeq n * dampSeq n))
      Filter.atTop (nhds ((0 : ℝ) + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + 0 * 0))) :=
    (h2.tendsto 0).comp tendsto_dampSeq
  have e0 : (0 : ℝ) + Real.sqrt (‖cubeX τ‖ * ‖cubeX τ‖ + 0 * 0) = ‖cubeX τ‖ := by
    rw [mul_zero, add_zero, zero_add, Real.sqrt_mul_self ha.le]
  rw [e0] at hT
  exact hT.log ha.ne'

/-- The integrals of `g_{δ_n}` over the cube tend to `walkSide`. -/
theorem tendsto_integral_cubeG :
    Filter.Tendsto (fun n : ℕ => ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeG (dampSeq n) τ)
      Filter.atTop (nhds walkSide) := by
  have hfun : (fun n : ℕ => ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeG (dampSeq n) τ)
      = fun n : ℕ => Real.log 2 + ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-t) - Real.exp (-dampSeq n * t) * besselJ0 t ^ 6) / t := by
    funext n
    exact integral_cubeG (dampSeq_pos n)
  have h : Filter.Tendsto (fun n : ℕ => Real.log 2 + ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-t) - Real.exp (-dampSeq n * t) * besselJ0 t ^ 6) / t) Filter.atTop
      (nhds (Real.log 2 + ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t) - besselJ0 t ^ 6) / t)) :=
    tendsto_const_nhds.add tendsto_walk_damped
  rw [hfun]
  exact h

/-! ## The zero set of `X` is a null set -/

/-- The zero set of `X`. -/
def cubeZ : Set (Fin 5 → ℝ) := {τ | cubeX τ = 0}

theorem measurableSet_cubeZ : MeasurableSet cubeZ := by
  have h : IsClosed {τ : Fin 5 → ℝ | cubeX τ = 0} :=
    isClosed_eq continuous_cubeX continuous_const
  exact h.measurableSet

/-- The indicator function of the zero set of `X`. -/
noncomputable def cubeInd (τ : Fin 5 → ℝ) : ℝ := cubeZ.indicator (fun _ => (1 : ℝ)) τ

theorem cubeInd_of_eq_zero {τ : Fin 5 → ℝ} (h : cubeX τ = 0) : cubeInd τ = 1 := by
  have hm : τ ∈ cubeZ := h
  show cubeZ.indicator (fun _ => (1 : ℝ)) τ = 1
  exact Set.indicator_of_mem hm _

theorem cubeInd_of_ne_zero {τ : Fin 5 → ℝ} (h : cubeX τ ≠ 0) : cubeInd τ = 0 := by
  have hm : τ ∉ cubeZ := h
  show cubeZ.indicator (fun _ => (1 : ℝ)) τ = 0
  exact Set.indicator_of_notMem hm _

theorem cubeInd_nonneg (τ : Fin 5 → ℝ) : 0 ≤ cubeInd τ := by
  show 0 ≤ cubeZ.indicator (fun _ => (1 : ℝ)) τ
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) τ

theorem integrable_cubeInd :
    Integrable cubeInd (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := by
  have h : Integrable (cubeZ.indicator fun _ : Fin 5 → ℝ => (1 : ℝ))
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) :=
    (integrable_const (1 : ℝ)).indicator measurableSet_cubeZ
  exact h

/-- `(log 8 - log (2δ_n)) · vol{X = 0} ≤ log 8 - c` whenever `c ≤ ∫ g_{δ_n}`. -/
theorem cube_zero_set_bound (n : ℕ) {c : ℝ}
    (hc : c ≤ ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeG (dampSeq n) τ) :
    (Real.log 8 - Real.log (dampSeq n + dampSeq n))
        * ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeInd τ ≤ Real.log 8 - c := by
  have hδ := dampSeq_pos n
  have hδ1 := dampSeq_le_one n
  have hpt : ∀ τ : Fin 5 → ℝ,
      (Real.log 8 - Real.log (dampSeq n + dampSeq n)) * cubeInd τ
        ≤ Real.log 8 * 1 - cubeG (dampSeq n) τ := by
    intro τ
    by_cases hτ : cubeX τ = 0
    · rw [cubeInd_of_eq_zero hτ, cubeG_of_eq_zero hδ.le hτ]
      linarith
    · rw [cubeInd_of_ne_zero hτ]
      have h := cubeG_le hδ hδ1 τ
      linarith
  have hi1 : Integrable
      (fun τ : Fin 5 → ℝ => (Real.log 8 - Real.log (dampSeq n + dampSeq n)) * cubeInd τ)
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := Integrable.const_mul integrable_cubeInd _
  have hi2 : Integrable (fun _ : Fin 5 → ℝ => Real.log 8 * 1)
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := integrable_const _
  have hi3 : Integrable (fun τ : Fin 5 → ℝ => Real.log 8 * 1 - cubeG (dampSeq n) τ)
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := hi2.sub (integrable_cubeG hδ)
  have hmono : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1,
        (Real.log 8 - Real.log (dampSeq n + dampSeq n)) * cubeInd τ
      ≤ ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, (Real.log 8 * 1 - cubeG (dampSeq n) τ) :=
    integral_mono hi1 hi3 hpt
  have e1 : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1,
        (Real.log 8 - Real.log (dampSeq n + dampSeq n)) * cubeInd τ
      = (Real.log 8 - Real.log (dampSeq n + dampSeq n))
        * ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeInd τ := integral_const_mul _ _
  have e2 : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, (Real.log 8 * 1 - cubeG (dampSeq n) τ)
      = Real.log 8 - ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeG (dampSeq n) τ := by
    rw [integral_sub hi2 (integrable_cubeG hδ), integral_const_mul, integral_cube_one, mul_one]
  rw [e1, e2] at hmono
  linarith

theorem log_dampSeq_le (n : ℕ) :
    Real.log (dampSeq n + dampSeq n) ≤ Real.log 8 - Real.log ((n : ℝ) + 1) := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hd := dampSeq_pos n
  have e8 : (8 : ℝ) / ((n : ℝ) + 1) = 8 * dampSeq n := div_eq_mul_one_div 8 _
  have hle : dampSeq n + dampSeq n ≤ 8 / ((n : ℝ) + 1) := by
    rw [e8]
    linarith
  have hpos2 : 0 < dampSeq n + dampSeq n := by linarith
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  calc Real.log (dampSeq n + dampSeq n) ≤ Real.log (8 / ((n : ℝ) + 1)) :=
        Real.log_le_log hpos2 hle
    _ = Real.log 8 - Real.log ((n : ℝ) + 1) := Real.log_div h8 hpos.ne'

/-- If `log (n+1) · v ≤ K` for every `n` and `v ≥ 0`, then `v = 0`. -/
theorem zero_of_unbounded_mul {v K : ℝ} (hv : 0 ≤ v)
    (h : ∀ n : ℕ, Real.log ((n : ℝ) + 1) * v ≤ K) : v = 0 := by
  by_contra hne
  have hv' : 0 < v := lt_of_le_of_ne hv (Ne.symm hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (K / v))
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hexp : Real.exp (K / v) < (n : ℝ) + 1 := by linarith
  have hlog : K / v < Real.log ((n : ℝ) + 1) := (Real.lt_log_iff_exp_lt hpos).mpr hexp
  have h3 : K / v * v = K := div_mul_cancel₀ K hv'.ne'
  have h4 : K / v * v < Real.log ((n : ℝ) + 1) * v := mul_lt_mul_of_pos_right hlog hv'
  have h5 := h n
  linarith

theorem integral_cubeInd_eq_zero : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeInd τ = 0 := by
  obtain ⟨c, hc⟩ := tendsto_integral_cubeG.bddBelow_range
  have hnn : (0 : (Fin 5 → ℝ) → ℝ) ≤ cubeInd := fun τ => cubeInd_nonneg τ
  have hv_nn : 0 ≤ ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeInd τ := integral_nonneg hnn
  refine zero_of_unbounded_mul (K := Real.log 8 - c) hv_nn (fun n => ?_)
  have hcn : c ≤ ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeG (dampSeq n) τ :=
    hc (Set.mem_range_self n)
  have h1 := log_dampSeq_le n
  have h2 := cube_zero_set_bound n hcn
  have h3 : Real.log ((n : ℝ) + 1) ≤ Real.log 8 - Real.log (dampSeq n + dampSeq n) := by
    linarith
  have h4 : Real.log ((n : ℝ) + 1) * ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeInd τ
      ≤ (Real.log 8 - Real.log (dampSeq n + dampSeq n))
        * ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeInd τ :=
    mul_le_mul_of_nonneg_right h3 hv_nn
  linarith

/-- `X(τ) ≠ 0` for almost every `τ` in the cube. -/
theorem ae_cubeX_ne_zero :
    ∀ᵐ τ ∂((volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)),
      cubeX τ ≠ 0 := by
  have hnn : (0 : (Fin 5 → ℝ) → ℝ) ≤ cubeInd := fun τ => cubeInd_nonneg τ
  have h0 : cubeInd =ᵐ[(volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn integrable_cubeInd).mp integral_cubeInd_eq_zero
  filter_upwards [h0] with τ hτ hX
  have h1 : cubeInd τ = 1 := cubeInd_of_eq_zero hX
  have h2 : cubeInd τ = 0 := hτ
  linarith

/-! ## Rung A1 -/

/-- **Rung A1.** `m(1 + x₁ + ⋯ + x₅) = log 2 + ∫₀^∞ (e^{-t} - J₀(t)⁶) dt/t`. -/
theorem rungA1 : RungA1 := by
  have hf : ∀ n : ℕ, Integrable (cubeG (dampSeq n))
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) := fun n => integrable_cubeG (dampSeq_pos n)
  have hFm : AEStronglyMeasurable (fun τ : Fin 5 → ℝ => Real.log ‖cubeX τ‖)
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) :=
    (Real.measurable_log.comp continuous_norm_cubeX.measurable).aestronglyMeasurable
  have hanti : ∀ᵐ τ ∂((volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)),
      Antitone fun n : ℕ => cubeG (dampSeq n) τ := by
    refine Filter.Eventually.of_forall (fun τ => ?_)
    intro n m hnm
    show cubeG (dampSeq m) τ ≤ cubeG (dampSeq n) τ
    exact cubeG_mono (dampSeq_pos m) (dampSeq_anti hnm) τ
  have hlim : ∀ᵐ τ ∂((volume : Measure (Fin 5 → ℝ)).restrict (Set.Icc (0 : Fin 5 → ℝ) 1)),
      Filter.Tendsto (fun n : ℕ => cubeG (dampSeq n) τ) Filter.atTop
        (nhds (Real.log ‖cubeX τ‖)) := by
    filter_upwards [ae_cubeX_ne_zero] with τ hτ
    exact tendsto_cubeG hτ
  obtain ⟨c, hc⟩ := tendsto_integral_cubeG.bddBelow_range
  have hcn : ∀ n : ℕ, c ≤ ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeG (dampSeq n) τ :=
    fun n => hc (Set.mem_range_self n)
  have hF : Integrable (fun τ : Fin 5 → ℝ => Real.log ‖cubeX τ‖)
      (volume.restrict (Set.Icc (0 : Fin 5 → ℝ) 1)) :=
    integrable_of_antitone_of_tendsto hf hFm hanti hlim hcn
  have hMCT : Filter.Tendsto
      (fun n : ℕ => ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, cubeG (dampSeq n) τ)
      Filter.atTop (nhds (∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, Real.log ‖cubeX τ‖)) :=
    integral_tendsto_of_tendsto_of_antitone hf hF hanti hlim
  have huniq : ∫ τ in Set.Icc (0 : Fin 5 → ℝ) 1, Real.log ‖cubeX τ‖ = walkSide :=
    tendsto_nhds_unique hMCT tendsto_integral_cubeG
  show mu6 = walkSide
  rw [mu6_eq_cubeX]
  exact huniq

/-- **The six-step theorem from the two remaining Bessel rungs.** -/
theorem rv6_of_A2_B (hA2 : RungA2) (hB : RungB) : mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_bessel rungA1 hA2 hB

end Tower.RV6
