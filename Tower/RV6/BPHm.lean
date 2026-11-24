import Mathlib
import Tower.RV6.BPH

/-!
# RungBP (b7): the model `H_m(s) = 24 [Λ(0)(a₀²/s + 2a₀/s² + 2/s³) + T₁ (a₀/s + 1/s²)]`

`g_L(y) = 2 L_c(y)/y`, `L_c = a₀ - log y`, and `H_m(s) = ∫_{(0,1]} ∫_{(0,1]} 3 g_L(τ) g_L(t) k_H(τ,t)` (`hM`).

* `∫₀¹ x^{c-1}(-log x) = 1/c²`, `∫₀¹ x^{c-1} log² x = 2/c³` (`integral_rpow_neg_log`, `integral_rpow_log_sq`).
* `∫₀¹ h_s(r²)(-log r) dr/r = T₁` (`integral_hS_log`).
* For `0 < x ≤ 1`: `∫₀^x g_L(y) k_H(x,y) dy = 2 x^s (L_c(x) Λ(0) + T₁)` (`region_integral`; `y = x r`).
* The region `τ < t` is moved by Fubini to the same closed form (`hM_eq`).
-/

namespace Tower.RV6

open Real MeasureTheory Set Filter Topology

/-! ## One-dimensional integrals with logarithms -/

theorem ftc_Ioc01 {F f : ℝ → ℝ} (hcont : ContinuousOn F (Icc 0 1))
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (f x) x) (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x) :
    IntegrableOn f (Ioc 0 1) ∧ ∫ x in Ioc (0 : ℝ) 1, f x = F 1 - F 0 := by
  have hi := intervalIntegral.integrableOn_deriv_of_nonneg hcont hd hpos
  refine ⟨hi, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hd
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hi)

theorem continuousOn_Icc01_of {F : ℝ → ℝ} (h0 : Tendsto F (𝓝[>] 0) (𝓝 (F 0)))
    (hpos : ∀ x : ℝ, 0 < x → ContinuousAt F x) : ContinuousOn F (Icc 0 1) := by
  intro x hx
  rcases hx.1.eq_or_lt with h | h
  · obtain rfl := h
    exact (continuousWithinAt_Ioi_iff_Ici.1 h0).mono Icc_subset_Ici_self
  · exact (hpos x h).continuousWithinAt

theorem rpow_tendsto_zero_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ c) (𝓝[>] 0) (𝓝 0) := by
  have h := ((Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rwa [Real.zero_rpow hc.ne'] at h

theorem rpow_neg_log_facts {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ (c - 1) * (-Real.log x)) (Ioc 0 1) ∧
      ∫ x in Ioc (0 : ℝ) 1, x ^ (c - 1) * (-Real.log x) = 1 / c ^ 2 := by
  have hc0 : c ≠ 0 := hc.ne'
  have h0 : Tendsto (fun x : ℝ => x ^ c * (-Real.log x / c + 1 / c ^ 2)) (𝓝[>] 0)
      (𝓝 ((fun x : ℝ => x ^ c * (-Real.log x / c + 1 / c ^ 2)) 0)) := by
    have e : (fun x : ℝ => x ^ c * (-Real.log x / c + 1 / c ^ 2))
        = fun x : ℝ => -(Real.log x * x ^ c) / c + x ^ c / c ^ 2 := by
      funext x
      ring
    have h := ((tendsto_log_mul_rpow_nhdsGT_zero hc).neg.div_const c).add
      ((rpow_tendsto_zero_nhdsGT hc).div_const (c ^ 2))
    rw [e]
    convert h using 2
    simp [Real.zero_rpow hc0]
  have hcont : ∀ x : ℝ, 0 < x → ContinuousAt (fun x : ℝ => x ^ c * (-Real.log x / c + 1 / c ^ 2)) x :=
    fun x hx => (Real.continuousAt_rpow_const x c (Or.inl hx.ne')).mul
      (((Real.continuousAt_log hx.ne').neg.div_const c).add continuousAt_const)
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ c * (-Real.log x / c + 1 / c ^ 2))
      (x ^ (c - 1) * (-Real.log x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h := (Real.hasDerivAt_rpow_const (p := c) (Or.inl hx0)).mul
      (((Real.hasDerivAt_log hx0).neg.div_const c).add_const (1 / c ^ 2))
    convert h using 1
    simp only [Pi.neg_apply]
    rw [Real.rpow_sub_one hx0]
    field_simp
    all_goals ring
  have hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ x ^ (c - 1) * (-Real.log x) := fun x hx =>
    mul_nonneg (Real.rpow_nonneg hx.1.le _) (neg_nonneg.2 (Real.log_nonpos hx.1.le hx.2.le))
  obtain ⟨hi, hv⟩ := ftc_Ioc01 (continuousOn_Icc01_of h0 hcont) hd hpos
  refine ⟨hi, ?_⟩
  rw [hv]
  simp [Real.zero_rpow hc0]

theorem integrableOn_rpow_neg_log {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ (c - 1) * (-Real.log x)) (Ioc 0 1) :=
  (rpow_neg_log_facts hc).1

theorem integral_rpow_neg_log {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioc (0 : ℝ) 1, x ^ (c - 1) * (-Real.log x) = 1 / c ^ 2 :=
  (rpow_neg_log_facts hc).2

theorem rpow_log_sq_facts {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ (c - 1) * (Real.log x * Real.log x)) (Ioc 0 1) ∧
      ∫ x in Ioc (0 : ℝ) 1, x ^ (c - 1) * (Real.log x * Real.log x) = 2 / c ^ 3 := by
  have hc0 : c ≠ 0 := hc.ne'
  have h0 : Tendsto (fun x : ℝ => x ^ c * (Real.log x * Real.log x / c - 2 * Real.log x / c ^ 2 + 2 / c ^ 3))
      (𝓝[>] 0)
      (𝓝 ((fun x : ℝ => x ^ c * (Real.log x * Real.log x / c - 2 * Real.log x / c ^ 2 + 2 / c ^ 3)) 0)) := by
    have h1 := tendsto_log_mul_rpow_nhdsGT_zero (half_pos hc)
    have h := (((h1.mul h1).div_const c).sub
      (((tendsto_log_mul_rpow_nhdsGT_zero hc).const_mul 2).div_const (c ^ 2))).add
      (((rpow_tendsto_zero_nhdsGT hc).const_mul 2).div_const (c ^ 3))
    have hev : (fun x : ℝ => (Real.log x * x ^ (c / 2)) * (Real.log x * x ^ (c / 2)) / c
          - 2 * (Real.log x * x ^ c) / c ^ 2 + 2 * x ^ c / c ^ 3)
        =ᶠ[𝓝[>] 0] fun x : ℝ => x ^ c * (Real.log x * Real.log x / c - 2 * Real.log x / c ^ 2 + 2 / c ^ 3) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : (0 : ℝ) < x := hx
      have e : x ^ (c / 2) * x ^ (c / 2) = x ^ c := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      rw [show (Real.log x * x ^ (c / 2)) * (Real.log x * x ^ (c / 2))
        = Real.log x * Real.log x * (x ^ (c / 2) * x ^ (c / 2)) by ring, e]
      ring
    have h' := h.congr' hev
    convert h' using 2
    simp [Real.zero_rpow hc0]
  have hcont : ∀ x : ℝ, 0 < x → ContinuousAt
      (fun x : ℝ => x ^ c * (Real.log x * Real.log x / c - 2 * Real.log x / c ^ 2 + 2 / c ^ 3)) x :=
    fun x hx => (Real.continuousAt_rpow_const x c (Or.inl hx.ne')).mul
      (((((Real.continuousAt_log hx.ne').mul (Real.continuousAt_log hx.ne')).div_const c).sub
        ((continuousAt_const.mul (Real.continuousAt_log hx.ne')).div_const (c ^ 2))).add continuousAt_const)
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun x : ℝ => x ^ c * (Real.log x * Real.log x / c - 2 * Real.log x / c ^ 2 + 2 / c ^ 3))
      (x ^ (c - 1) * (Real.log x * Real.log x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hl := Real.hasDerivAt_log hx0
    have h := (Real.hasDerivAt_rpow_const (p := c) (Or.inl hx0)).mul
      ((((hl.mul hl).div_const c).sub ((hl.const_mul 2).div_const (c ^ 2))).add_const (2 / c ^ 3))
    convert h using 1
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [Real.rpow_sub_one hx0]
    field_simp
    all_goals ring
  have hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ x ^ (c - 1) * (Real.log x * Real.log x) := fun x hx =>
    mul_nonneg (Real.rpow_nonneg hx.1.le _) (mul_self_nonneg _)
  obtain ⟨hi, hv⟩ := ftc_Ioc01 (continuousOn_Icc01_of h0 hcont) hd hpos
  refine ⟨hi, ?_⟩
  rw [hv]
  simp [Real.zero_rpow hc0]
  all_goals ring

theorem integrableOn_rpow_log_sq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ (c - 1) * (Real.log x * Real.log x)) (Ioc 0 1) :=
  (rpow_log_sq_facts hc).1

theorem integral_rpow_log_sq {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioc (0 : ℝ) 1, x ^ (c - 1) * (Real.log x * Real.log x) = 2 / c ^ 3 :=
  (rpow_log_sq_facts hc).2

/-! ## `T₁` as an integral -/

theorem integrableOn_hS_log {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IntegrableOn (fun r : ℝ => hS s (r ^ 2) * (-Real.log r / r)) (Ioc 0 1) := by
  have hs2 : s ≤ 2 := by linarith
  have hb := (integrableOn_rpow_neg_log (by norm_num : (0 : ℝ) < 2)).const_mul (s ^ 2 / 2)
  refine Integrable.mono' hb ?_ (ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact ((continuous_hS hs0).comp (continuous_pow 2)).continuousOn.mul
      ((Real.continuousOn_log.mono (fun r (hr : r ∈ Ioc (0 : ℝ) 1) => (show (0 : ℝ) < r from hr.1).ne')).neg.div
        continuousOn_id (fun r (hr : r ∈ Ioc (0 : ℝ) 1) => (show (0 : ℝ) < r from hr.1).ne'))
  · have hr0 : (0 : ℝ) < r := hr.1
    have hr0' : r ≠ 0 := hr0.ne'
    have hr1 : r ≤ 1 := hr.2
    have hw1 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
    have h0 := hS_nonneg_le_one hs0 hs2 (sq_nonneg r) hw1
    have h1 := hS_le_sq hs0 hs2 (sq_nonneg r) hw1
    have hl : 0 ≤ -Real.log r / r := div_nonneg (neg_nonneg.2 (Real.log_nonpos hr0.le hr1)) hr0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hl), show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one]
    calc hS s (r ^ 2) * (-Real.log r / r) ≤ s ^ 2 / 2 * r ^ 2 * (-Real.log r / r) :=
          mul_le_mul_of_nonneg_right h1 hl
      _ = s ^ 2 / 2 * (r * -Real.log r) := by
          field_simp
          all_goals ring

/-- **`∫₀¹ h_s(r²)(-log r) dr/r = T₁`** for `0 ≤ s ≤ 1`. -/
theorem integral_hS_log {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫ r in Ioc (0 : ℝ) 1, hS s (r ^ 2) * (-Real.log r / r) = t1S s := by
  have hs2 : s ≤ 2 := by linarith
  have hc : ∀ n : ℕ, (0 : ℝ) < 2 * (n : ℝ) + 2 := fun n => by positivity
  have hpt : ∀ r ∈ Ioo (0 : ℝ) 1, hS s (r ^ 2) * (-Real.log r / r)
      = ∑' n : ℕ, bk s (n + 1) ^ 2 * (r ^ ((2 * (n : ℝ) + 2) - 1) * (-Real.log r)) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr.1
    have hr1 : r < 1 := hr.2
    rw [hS_eq_tsum hs0 hs2 (sq_nonneg r) (by nlinarith), ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [Real.rpow_sub_one hr0.ne', show (2 * (n : ℝ) + 2) = ((2 * (n + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
    ring
  have hint : ∀ n : ℕ, Integrable (fun r : ℝ => bk s (n + 1) ^ 2 * (r ^ ((2 * (n : ℝ) + 2) - 1) * (-Real.log r)))
      (volume.restrict (Ioo (0 : ℝ) 1)) := fun n =>
    ((integrableOn_rpow_neg_log (hc n)).mono_set Ioo_subset_Ioc_self).const_mul _
  have hval : ∀ n : ℕ, ∫ r in Ioo (0 : ℝ) 1, bk s (n + 1) ^ 2 * (r ^ ((2 * (n : ℝ) + 2) - 1) * (-Real.log r))
      = bk s (n + 1) ^ 2 / (4 * ((n : ℝ) + 1) ^ 2) := fun n => by
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo, integral_rpow_neg_log (hc n)]
    field_simp
    all_goals ring
  have hnorm : ∀ n : ℕ, ∫ r in Ioo (0 : ℝ) 1, ‖bk s (n + 1) ^ 2 * (r ^ ((2 * (n : ℝ) + 2) - 1) * (-Real.log r))‖
      = ∫ r in Ioo (0 : ℝ) 1, bk s (n + 1) ^ 2 * (r ^ ((2 * (n : ℝ) + 2) - 1) * (-Real.log r)) := fun n =>
    setIntegral_congr_fun measurableSet_Ioo (fun r hr =>
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hr.1.le _)
        (neg_nonneg.2 (Real.log_nonpos hr.1.le hr.2.le)))))
  have hsum : Summable (fun n : ℕ =>
      ∫ r in Ioo (0 : ℝ) 1, ‖bk s (n + 1) ^ 2 * (r ^ ((2 * (n : ℝ) + 2) - 1) * (-Real.log r))‖) :=
    (summable_t1_term hs0 hs2).congr fun n => ((hnorm n).trans (hval n)).symm
  rw [integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hpt,
    ← integral_tsum_of_summable_integral_norm hint hsum, t1S]
  exact tsum_congr hval

/-! ## The region integral -/

/-- `g_L(y) = 2 L_c(y)/y`. -/
noncomputable def gL (y : ℝ) : ℝ := 2 * Lc y / y

theorem continuousOn_gL : ContinuousOn gL (Ioi 0) :=
  (continuousOn_const.mul (continuousOn_const.sub
    (Real.continuousOn_log.mono (fun y hy => (show (0 : ℝ) < y from hy).ne')))).div continuousOn_id
    (fun y hy => (show (0 : ℝ) < y from hy).ne')

theorem measurable_gL : Measurable gL :=
  (measurable_const.mul (measurable_const.sub Real.measurable_log)).div measurable_id

theorem gL_nonneg {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : 0 ≤ gL y :=
  div_nonneg (mul_nonneg zero_le_two (Lc_pos hy hy1).le) hy.le

theorem integrableOn_region {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    IntegrableOn (fun y : ℝ => gL y * kerH s x y) (Ioc 0 x) := by
  have hs2 : s ≤ 2 := by linarith
  have hb := ((integrableOn_Eb_pow_rpow (k := 1) (a := 1) (by norm_num)).mono_set
    (Ioc_subset_Ioc_right hx1)).const_mul (s ^ 2 * x ^ s / x ^ 2)
  refine Integrable.mono' hb ?_ (ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_))
  · exact ((continuousOn_mul_kerH hs0 continuousOn_gL).mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc
  · have hy0 : (0 : ℝ) < y := hy.1
    have hy0' : y ≠ 0 := hy0.ne'
    have hx0' : x ≠ 0 := hx0.ne'
    have hyx : y ≤ x := hy.2
    have hy1 : y ≤ 1 := hyx.trans hx1
    have hk0 := kerH_nonneg hs0 hs2 hx0 hy0
    have hk := kerH_le_left hs0 hs2 hy0 hyx
    have hg := gL_nonneg hy0 hy1
    have hL := Lc_le_Eb hy0 hy1
    have hLp := Lc_pos hy0 hy1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg hk0), pow_one, Real.rpow_one]
    calc gL y * kerH s x y ≤ gL y * (s ^ 2 / 2 * (y / x) ^ 2 * x ^ s) := mul_le_mul_of_nonneg_left hk hg
      _ = s ^ 2 * x ^ s / x ^ 2 * (Lc y * y) := by
          unfold gL
          field_simp
          all_goals ring
      _ ≤ s ^ 2 * x ^ s / x ^ 2 * (Eb y * y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL hy0.le)
            (div_nonneg (mul_nonneg (sq_nonneg s) (Real.rpow_nonneg hx0.le s)) (sq_nonneg x))

/-- **The region integral**: `∫₀^x g_L(y) k_H(x,y) dy = 2 x^s (L_c(x) Λ(0) + T₁)` for `0 < x ≤ 1`. -/
theorem region_integral {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ∫ y in Ioc (0 : ℝ) x, gL y * kerH s x y = 2 * x ^ s * (Lc x * lamS s 0 + t1S s) := by
  have hs2 : s ≤ 2 := by linarith
  have e2 := intervalIntegral.integral_comp_mul_left (fun y : ℝ => gL y * kerH s x y) (a := 0) (b := 1)
    hx0.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at e2
  have e3 : ∫ y in (0 : ℝ)..x, gL y * kerH s x y
      = x * ∫ r in (0 : ℝ)..1, gL (x * r) * kerH s x (x * r) := by
    rw [e2, ← mul_assoc, mul_inv_cancel₀ hx0.ne', one_mul]
  have hpt : EqOn (fun r : ℝ => x * (gL (x * r) * kerH s x (x * r)))
      (fun r : ℝ => 2 * x ^ s * Lc x * (hS s (r ^ 2) * r ^ ((0 : ℝ) - 1))
        + 2 * x ^ s * (hS s (r ^ 2) * (-Real.log r / r))) (Ioc 0 1) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr.1
    have hxr : 0 < x * r := mul_pos hx0 hr0
    have hxrx : x * r ≤ x := mul_le_of_le_one_right hx0.le hr.2
    show x * (gL (x * r) * kerH s x (x * r))
      = 2 * x ^ s * Lc x * (hS s (r ^ 2) * r ^ ((0 : ℝ) - 1)) + 2 * x ^ s * (hS s (r ^ 2) * (-Real.log r / r))
    rw [kerH_eq_le hxr hxrx, mul_div_cancel_left₀ r hx0.ne', gL, Lc, Lc,
      Real.log_mul hx0.ne' hr0.ne', Real.rpow_sub_one hr0.ne', Real.rpow_zero]
    field_simp
    all_goals ring
  have i1 : IntegrableOn (fun r : ℝ => hS s (r ^ 2) * r ^ ((0 : ℝ) - 1)) (Ioc 0 1) :=
    integrableOn_hS_sq hs0 hs1 (by norm_num)
  have i2 := integrableOn_hS_log hs0 hs1
  rw [← intervalIntegral.integral_of_le hx0.le, e3, intervalIntegral.integral_of_le zero_le_one,
    ← integral_const_mul, setIntegral_congr_fun measurableSet_Ioc hpt,
    integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_hS_rpow hs0 hs1 (by norm_num) (by norm_num), integral_hS_log hs0 hs1]
  ring

/-! ## The model -/

/-- `H_m(s) = ∫_{(0,1]} ∫_{(0,1]} 3 g_L(τ) g_L(t) k_H(τ,t)`. -/
noncomputable def hM (s : ℝ) : ℝ :=
  ∫ τ in Ioc (0 : ℝ) 1, ∫ t in Ioc (0 : ℝ) 1, 3 * gL τ * gL t * kerH s τ t

/-- `w(x) = 6 g_L(x) x^s (L_c(x) Λ(0) + T₁)`, written through the three powers. -/
theorem wM_eq {s x : ℝ} (hx0 : 0 < x) :
    6 * gL x * x ^ s * (Lc x * lamS s 0 + t1S s)
      = 12 * (lamS s 0 * a0 ^ 2 + t1S s * a0) * x ^ (s - 1)
        + 12 * (2 * lamS s 0 * a0 + t1S s) * (x ^ (s - 1) * (-Real.log x))
        + 12 * lamS s 0 * (x ^ (s - 1) * (Real.log x * Real.log x)) := by
  rw [gL, Lc, Real.rpow_sub_one hx0.ne']
  field_simp
  all_goals ring

theorem integral_wM {s : ℝ} (hs0 : 0 < s) :
    IntegrableOn (fun x : ℝ => 6 * gL x * x ^ s * (Lc x * lamS s 0 + t1S s)) (Ioc 0 1) ∧
      ∫ x in Ioc (0 : ℝ) 1, 6 * gL x * x ^ s * (Lc x * lamS s 0 + t1S s)
        = 12 * (lamS s 0 * (a0 ^ 2 / s + 2 * a0 / s ^ 2 + 2 / s ^ 3) + t1S s * (a0 / s + 1 / s ^ 2)) := by
  have j0 : IntegrableOn (fun x : ℝ => x ^ (s - 1)) (Ioc 0 1) := integrableOn_rpow_Ioc01 (by linarith)
  have j1 := integrableOn_rpow_neg_log hs0
  have j2 := integrableOn_rpow_log_sq hs0
  have k01 : IntegrableOn (fun x : ℝ => 12 * (lamS s 0 * a0 ^ 2 + t1S s * a0) * x ^ (s - 1)
      + 12 * (2 * lamS s 0 * a0 + t1S s) * (x ^ (s - 1) * (-Real.log x))) (Ioc 0 1) :=
    (j0.const_mul (12 * (lamS s 0 * a0 ^ 2 + t1S s * a0))).add
      (j1.const_mul (12 * (2 * lamS s 0 * a0 + t1S s)))
  have hsum : IntegrableOn (fun x : ℝ => 12 * (lamS s 0 * a0 ^ 2 + t1S s * a0) * x ^ (s - 1)
      + 12 * (2 * lamS s 0 * a0 + t1S s) * (x ^ (s - 1) * (-Real.log x))
      + 12 * lamS s 0 * (x ^ (s - 1) * (Real.log x * Real.log x))) (Ioc 0 1) :=
    k01.add (j2.const_mul (12 * lamS s 0))
  have hEq : EqOn (fun x : ℝ => 6 * gL x * x ^ s * (Lc x * lamS s 0 + t1S s))
      (fun x : ℝ => 12 * (lamS s 0 * a0 ^ 2 + t1S s * a0) * x ^ (s - 1)
        + 12 * (2 * lamS s 0 * a0 + t1S s) * (x ^ (s - 1) * (-Real.log x))
        + 12 * lamS s 0 * (x ^ (s - 1) * (Real.log x * Real.log x))) (Ioc 0 1) :=
    fun x hx => wM_eq hx.1
  refine ⟨hsum.congr_fun hEq.symm measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc hEq,
    integral_add k01 (j2.const_mul _),
    integral_add (j0.const_mul _) (j1.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_rpow_Ioc01 (a := s - 1) (by linarith), integral_rpow_neg_log hs0,
    integral_rpow_log_sq hs0, show s - 1 + 1 = s by ring]
  ring

/-- The part of the model integrand above the diagonal. -/
noncomputable def psiM (s τ t : ℝ) : ℝ := 3 * gL τ * gL t * kerH s τ t * (if τ < t then 1 else 0)

theorem psiM_nonneg {s τ t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hτ : τ ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) : 0 ≤ psiM s τ t := by
  unfold psiM
  have h1 := gL_nonneg hτ.1 hτ.2
  have h2 := gL_nonneg ht.1 ht.2
  have h3 := kerH_nonneg hs0 (by linarith) hτ.1 ht.1
  have h4 : (0 : ℝ) ≤ if τ < t then 1 else 0 := by split_ifs <;> norm_num
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3) h4

/-- For fixed `t ∈ (0,1]`, the `τ`-integral of `ψ` is `w(t)`. -/
theorem psiM_inner {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    IntegrableOn (fun τ : ℝ => psiM s τ t) (Ioc 0 1) ∧
      ∫ τ in Ioc (0 : ℝ) 1, psiM s τ t = 6 * gL t * t ^ s * (Lc t * lamS s 0 + t1S s) := by
  have hreg : IntegrableOn (fun τ : ℝ => 3 * gL t * (gL τ * kerH s t τ)) (Ioc 0 t) :=
    (integrableOn_region hs0 hs1 ht0 ht1).const_mul (3 * gL t)
  have eA : EqOn (fun τ : ℝ => psiM s τ t) (fun τ : ℝ => 3 * gL t * (gL τ * kerH s t τ)) (Ioo 0 t) := by
    intro τ hτ
    show psiM s τ t = 3 * gL t * (gL τ * kerH s t τ)
    rw [psiM, if_pos hτ.2, kerH_symm]
    ring
  have eB : EqOn (fun τ : ℝ => psiM s τ t) (fun _ : ℝ => (0 : ℝ)) (Icc t 1) := by
    intro τ hτ
    show psiM s τ t = 0
    rw [psiM, if_neg (not_lt.2 hτ.1)]
    ring
  have iA : IntegrableOn (fun τ : ℝ => psiM s τ t) (Ioo 0 t) :=
    (hreg.mono_set Ioo_subset_Ioc_self).congr_fun eA.symm measurableSet_Ioo
  have iB : IntegrableOn (fun τ : ℝ => psiM s τ t) (Icc t 1) :=
    (integrableOn_zero).congr_fun eB.symm measurableSet_Icc
  have hU : Ioo (0 : ℝ) t ∪ Icc t 1 = Ioc 0 1 := Set.Ioo_union_Icc_eq_Ioc ht0 ht1
  have hD : Disjoint (Ioo (0 : ℝ) t) (Icc t 1) :=
    Set.disjoint_left.2 (fun x hx hx' => lt_irrefl _ (hx.2.trans_le hx'.1))
  refine ⟨by rw [← hU]; exact iA.union iB, ?_⟩
  rw [← hU, setIntegral_union hD measurableSet_Icc iA iB, setIntegral_congr_fun measurableSet_Ioo eA,
    setIntegral_congr_fun measurableSet_Icc eB, integral_zero, add_zero, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, region_integral hs0 hs1 ht0 ht1]
  ring

/-- **The model in closed form**, `0 < s ≤ 1`. -/
theorem hM_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    hM s = 24 * (lamS s 0 * (a0 ^ 2 / s + 2 * a0 / s ^ 2 + 2 / s ^ 3) + t1S s * (a0 / s + 1 / s ^ 2)) := by
  have hs2 : s ≤ 2 := by linarith
  obtain ⟨iw, vw⟩ := integral_wM hs0
  -- measurability and integrability of `ψ` on the square
  have hmeas : Measurable (Function.uncurry (psiM s)) := by
    have h1 : Measurable (fun p : ℝ × ℝ => if p.1 < p.2 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const measurable_const
    exact (((measurable_const.mul (measurable_gL.comp measurable_fst)).mul
      (measurable_gL.comp measurable_snd)).mul (continuous_kerH hs0.le).measurable).mul h1
  have hψ : Integrable (Function.uncurry (psiM s)) (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)).prod ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (psiM_inner hs0.le hs1 ht.1 ht.2).1
    · refine Integrable.congr iw ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hn : ∫ τ in Ioc (0 : ℝ) 1, ‖Function.uncurry (psiM s) (τ, t)‖
          = ∫ τ in Ioc (0 : ℝ) 1, psiM s τ t :=
        setIntegral_congr_fun measurableSet_Ioc (fun τ hτ =>
          Real.norm_of_nonneg (psiM_nonneg hs0.le hs1 hτ ht))
      rw [hn, (psiM_inner hs0.le hs1 ht.1 ht.2).2]
  -- the inner split
  have hsplit : EqOn (fun τ : ℝ => ∫ t in Ioc (0 : ℝ) 1, 3 * gL τ * gL t * kerH s τ t)
      (fun τ : ℝ => 6 * gL τ * τ ^ s * (Lc τ * lamS s 0 + t1S s) + ∫ t in Ioc (0 : ℝ) 1, psiM s τ t)
      (Ioc 0 1) := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2
    have hU : Ioc (0 : ℝ) τ ∪ Ioc τ 1 = Ioc 0 1 := Set.Ioc_union_Ioc_eq_Ioc hτ0.le hτ1
    have hD : Disjoint (Ioc (0 : ℝ) τ) (Ioc τ 1) :=
      Set.disjoint_left.2 (fun x hx hx' => lt_irrefl _ (hx'.1.trans_le hx.2))
    have hc : ContinuousOn (fun t : ℝ => 3 * gL τ * gL t * kerH s τ t) (Icc τ 1) := by
      have h := (continuous_const : Continuous fun _ : ℝ => 3 * gL τ).continuousOn.mul
        (continuousOn_mul_kerH (τ := τ) hs0.le continuousOn_gL)
      refine (h.mono (fun t (ht : t ∈ Icc τ 1) => lt_of_lt_of_le hτ0 ht.1)).congr (fun t _ => ?_)
      show 3 * gL τ * gL t * kerH s τ t = 3 * gL τ * (gL t * kerH s τ t)
      ring
    have iB : IntegrableOn (fun t : ℝ => 3 * gL τ * gL t * kerH s τ t) (Ioc τ 1) :=
      (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have iA : IntegrableOn (fun t : ℝ => 3 * gL τ * gL t * kerH s τ t) (Ioc 0 τ) := by
      have h0 : IntegrableOn (fun t : ℝ => 3 * gL τ * (gL t * kerH s τ t)) (Ioc 0 τ) :=
        (integrableOn_region hs0.le hs1 hτ0 hτ1).const_mul (3 * gL τ)
      refine h0.congr_fun (fun t _ => ?_) measurableSet_Ioc
      show 3 * gL τ * (gL t * kerH s τ t) = 3 * gL τ * gL t * kerH s τ t
      ring
    have eA : EqOn (fun t : ℝ => psiM s τ t) (fun _ : ℝ => (0 : ℝ)) (Ioc 0 τ) := by
      intro t ht
      show psiM s τ t = 0
      rw [psiM, if_neg (not_lt.2 ht.2)]
      ring
    have eB : EqOn (fun t : ℝ => psiM s τ t) (fun t : ℝ => 3 * gL τ * gL t * kerH s τ t) (Ioc τ 1) := by
      intro t ht
      show psiM s τ t = 3 * gL τ * gL t * kerH s τ t
      rw [psiM, if_pos ht.1]
      ring
    have jA : IntegrableOn (fun t : ℝ => psiM s τ t) (Ioc 0 τ) :=
      (integrableOn_zero).congr_fun eA.symm measurableSet_Ioc
    have jB : IntegrableOn (fun t : ℝ => psiM s τ t) (Ioc τ 1) := iB.congr_fun eB.symm measurableSet_Ioc
    show ∫ t in Ioc (0 : ℝ) 1, 3 * gL τ * gL t * kerH s τ t
      = 6 * gL τ * τ ^ s * (Lc τ * lamS s 0 + t1S s) + ∫ t in Ioc (0 : ℝ) 1, psiM s τ t
    rw [← hU, setIntegral_union hD measurableSet_Ioc iA iB, setIntegral_union hD measurableSet_Ioc jA jB,
      setIntegral_congr_fun measurableSet_Ioc eA, setIntegral_congr_fun measurableSet_Ioc eB,
      integral_zero, zero_add]
    have hreg : ∫ t in Ioc (0 : ℝ) τ, 3 * gL τ * gL t * kerH s τ t
        = 3 * gL τ * (2 * τ ^ s * (Lc τ * lamS s 0 + t1S s)) := by
      rw [← region_integral hs0.le hs1 hτ0 hτ1, ← integral_const_mul]
      congr 1
      funext t
      ring
    rw [hreg]
    ring
  have hψin : Integrable (fun τ : ℝ => ∫ t in Ioc (0 : ℝ) 1, psiM s τ t)
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) := hψ.integral_prod_left
  have hswap : ∫ τ in Ioc (0 : ℝ) 1, ∫ t in Ioc (0 : ℝ) 1, psiM s τ t
      = ∫ t in Ioc (0 : ℝ) 1, 6 * gL t * t ^ s * (Lc t * lamS s 0 + t1S s) := by
    rw [integral_integral_swap hψ]
    exact setIntegral_congr_fun measurableSet_Ioc (fun t ht => (psiM_inner hs0.le hs1 ht.1 ht.2).2)
  unfold hM
  rw [setIntegral_congr_fun measurableSet_Ioc hsplit, integral_add iw hψin, hswap, vw]
  ring

end Tower.RV6
