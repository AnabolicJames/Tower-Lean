import Mathlib
import Tower.RV6.BPHs

/-!
# RungBP, step 5 (first half): the Gaussian integrals for `R(s)`

* `integral_cos_mul_gauss`: `∫_ℝ cos x e^{-t x²} dx = √(π/t) e^{-1/(4t)}` (real part of `integral_cexp_quadratic`);
* `integral_prod_one_sub_cos_gauss`: `∫_{ℝ²} (1 - cos x₁) e^{-t(x₁² + x₂²)} dx = (π/t)(1 - e^{-1/(4t)})`;
* `integral_rpow_one_sub_exp`: `∫₀^∞ u^{-1-a} (1 - e^{-u}) du = Γ(1 - a)/a` for `0 < a < 1`;
* `integral_t_one_sub_exp`: `∫₀^∞ t^{s/2-1} (1 - e^{-1/(4t)}) dt = 2^{-s} Γ(1 - s/2)/(s/2)` for `0 < s < 2`;
* `rpow_eq_gamma_integral`: `r^{-1-s/2} = Γ(1 + s/2)⁻¹ ∫₀^∞ t^{s/2} e^{-rt} dt` for `r > 0`, `s > -2`.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

/-! ## A majorant with a linear bound at `0` -/

/-- `x^{-1-a} φ(x)` is integrable on `(0, ∞)` when `|φ| ≤ A x` on `(0, 1]`, `|φ| ≤ B` beyond, `0 < a < 1`. -/
theorem integrableOn_rpow_of_lin_bounds {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Ioi 0)) {a A B : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (h1 : ∀ x : ℝ, 0 < x → x ≤ 1 → |φ x| ≤ A * x) (h2 : ∀ x : ℝ, 1 < x → |φ x| ≤ B) :
    IntegrableOn (fun x : ℝ => x ^ (-1 - a) * φ x) (Set.Ioi 0) := by
  have hc : ContinuousOn (fun x : ℝ => x ^ (-1 - a) * φ x) (Set.Ioi 0) :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))).mul hφ
  have i1 : IntegrableOn (fun x : ℝ => x ^ (-1 - a) * φ x) (Set.Ioc 0 1) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => x ^ (-1 - a) * φ x)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (hc.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    have hr : IntegrableOn (fun x : ℝ => x ^ (-a)) (Set.Ioc (0 : ℝ) 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < -a)).1
    refine Integrable.mono' (hr.const_mul A) hm
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_))
    have hx0 : 0 < x := hx.1
    have hp : 0 < x ^ (-1 - a) := Real.rpow_pos_of_pos hx0 _
    have e : x ^ (-1 - a) * x = x ^ (-a) := by
      rw [← Real.rpow_add_one hx0.ne']
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
    calc x ^ (-1 - a) * |φ x| ≤ x ^ (-1 - a) * (A * x) :=
          mul_le_mul_of_nonneg_left (h1 x hx0 hx.2) hp.le
      _ = A * x ^ (-a) := by rw [← e]; ring
  have i2 : IntegrableOn (fun x : ℝ => x ^ (-1 - a) * φ x) (Set.Ioi 1) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => x ^ (-1 - a) * φ x)
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (hc.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    have hr : IntegrableOn (fun x : ℝ => x ^ (-1 - a)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine Integrable.mono' (hr.const_mul B) hm
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have hp : 0 < x ^ (-1 - a) := Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
    calc x ^ (-1 - a) * |φ x| ≤ x ^ (-1 - a) * B := mul_le_mul_of_nonneg_left (h2 x hx) hp.le
      _ = B * x ^ (-1 - a) := mul_comm _ _
  have hu : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hu]
  exact i1.union i2

/-! ## The Gaussian integrals -/

/-- `∫_ℝ cos x e^{-t x²} dx = √(π/t) e^{-1/(4t)}` for `t > 0`. -/
theorem integral_cos_mul_gauss {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, Real.cos x * Real.exp (-t * x ^ 2) = √(π / t) * Real.exp (-(1 / (4 * t))) := by
  have hb : (-(t : ℂ)).re < 0 := by
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  have hq := integral_cexp_quadratic hb Complex.I 0
  have hint : Integrable (fun x : ℝ => Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2 + Complex.I * x + 0)) :=
    integrable_cexp_quadratic' hb _ _
  have hre : ∀ x : ℝ, (Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2 + Complex.I * x + 0)).re
      = Real.cos x * Real.exp (-t * x ^ 2) := by
    intro x
    rw [Complex.exp_re]
    have h1 : (-(t : ℂ) * (x : ℂ) ^ 2 + Complex.I * x + 0).re = -t * x ^ 2 := by
      simp only [sq, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re]
      ring
    have h2 : (-(t : ℂ) * (x : ℂ) ^ 2 + Complex.I * x + 0).im = x := by
      simp only [sq, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_im]
      ring
    rw [h1, h2]
    ring
  have hπt : (0 : ℝ) ≤ π / t := div_nonneg Real.pi_pos.le ht.le
  have e1 : (π : ℂ) / -(-(t : ℂ)) = ((π / t : ℝ) : ℂ) := by
    push_cast
    ring
  have e2 : ((π / t : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√(π / t) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hπt]
    congr 1
    norm_num
  have e3 : (0 : ℂ) - Complex.I ^ 2 / (4 * -(t : ℂ)) = ((-(1 / (4 * t)) : ℝ) : ℂ) := by
    rw [Complex.I_sq]
    push_cast
    ring
  have hfun : (fun x : ℝ => Real.cos x * Real.exp (-t * x ^ 2))
      = fun x : ℝ => (Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2 + Complex.I * x + 0)).re :=
    funext (fun x => (hre x).symm)
  calc ∫ x : ℝ, Real.cos x * Real.exp (-t * x ^ 2)
      = ∫ x : ℝ, (Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2 + Complex.I * x + 0)).re := by rw [hfun]
    _ = (∫ x : ℝ, Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2 + Complex.I * x + 0)).re :=
        Complex.reCLM.integral_comp_comm hint
    _ = √(π / t) * Real.exp (-(1 / (4 * t))) := by
        rw [hq, e1, e2, e3, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem integrable_cos_mul_gauss {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => Real.cos x * Real.exp (-t * x ^ 2)) := by
  have hg := integrable_exp_neg_mul_sq ht
  refine Integrable.mono' hg ?_ (Filter.Eventually.of_forall (fun x => ?_))
  · exact (Real.continuous_cos.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |Real.cos x| * Real.exp (-t * x ^ 2) ≤ 1 * Real.exp (-t * x ^ 2) :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one x) (Real.exp_pos _).le
      _ = Real.exp (-t * x ^ 2) := one_mul _

/-- `∫_ℝ (1 - cos x) e^{-t x²} dx = √(π/t) (1 - e^{-1/(4t)})`. -/
theorem integral_one_sub_cos_gauss {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, (1 - Real.cos x) * Real.exp (-t * x ^ 2)
      = √(π / t) * (1 - Real.exp (-(1 / (4 * t)))) := by
  have hg := integrable_exp_neg_mul_sq ht
  have hc := integrable_cos_mul_gauss ht
  have hfun : (fun x : ℝ => (1 - Real.cos x) * Real.exp (-t * x ^ 2))
      = fun x : ℝ => Real.exp (-t * x ^ 2) - Real.cos x * Real.exp (-t * x ^ 2) := by
    funext x
    ring
  rw [hfun, integral_sub hg hc, integral_gaussian, integral_cos_mul_gauss ht]
  ring

/-- `∫_{ℝ²} (1 - cos x₁) e^{-t(x₁² + x₂²)} dx = (π/t)(1 - e^{-1/(4t)})`. -/
theorem integral_prod_one_sub_cos_gauss {t : ℝ} (ht : 0 < t) :
    ∫ p : ℝ × ℝ, (1 - Real.cos p.1) * Real.exp (-t * (p.1 ^ 2 + p.2 ^ 2))
      = π / t * (1 - Real.exp (-(1 / (4 * t)))) := by
  have hfun : (fun p : ℝ × ℝ => (1 - Real.cos p.1) * Real.exp (-t * (p.1 ^ 2 + p.2 ^ 2)))
      = fun p : ℝ × ℝ => ((1 - Real.cos p.1) * Real.exp (-t * p.1 ^ 2)) * Real.exp (-t * p.2 ^ 2) := by
    funext p
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hfun, Measure.volume_eq_prod,
    integral_prod_mul (fun x : ℝ => (1 - Real.cos x) * Real.exp (-t * x ^ 2))
      (fun y : ℝ => Real.exp (-t * y ^ 2)),
    integral_one_sub_cos_gauss ht, integral_gaussian]
  have hπt : (0 : ℝ) ≤ π / t := div_nonneg Real.pi_pos.le ht.le
  have hs := Real.mul_self_sqrt hπt
  linear_combination (1 - Real.exp (-(1 / (4 * t)))) * hs

/-! ## Two Gamma integrals -/

/-- `∫₀^∞ u^{-1-a} (1 - e^{-u}) du = Γ(1 - a)/a` for `0 < a < 1`. -/
theorem integral_rpow_one_sub_exp {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ u in Set.Ioi (0 : ℝ), u ^ (-1 - a) * (1 - Real.exp (-u)) = Real.Gamma (1 - a) / a := by
  have hF0 : (fun u : ℝ => -(u ^ (-a)) / a * (1 - Real.exp (-u))) 0 = 0 := by
    simp
  have hd : ∀ u : ℝ, 0 < u → HasDerivAt (fun u : ℝ => -(u ^ (-a)) / a * (1 - Real.exp (-u)))
      (u ^ (-1 - a) * (1 - Real.exp (-u)) + (-(u ^ (-a)) / a) * Real.exp (-u)) u := by
    intro u hu
    have d1 : HasDerivAt (fun x : ℝ => x ^ (-a)) (-a * u ^ (-a - 1)) u :=
      Real.hasDerivAt_rpow_const (Or.inl hu.ne')
    have d2 : HasDerivAt (fun x : ℝ => -(x ^ (-a)) / a) (-(-a * u ^ (-a - 1)) / a) u :=
      d1.neg.div_const a
    have d3 : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (-(Real.exp (-u) * -1)) u := by
      have h := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
      exact h.const_sub 1
    have h := d2.mul d3
    refine h.congr_deriv ?_
    have e : u ^ (-a - 1) = u ^ (-1 - a) := by
      congr 1
      ring
    have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
    rw [e]
    linear_combination (u ^ (-1 - a) * (1 - Real.exp (-u))) * hinv
  have hb1 : ∀ u : ℝ, 0 < u → |1 - Real.exp (-u)| ≤ u := by
    intro u hu
    have h1 := Real.add_one_le_exp (-u)
    have h2 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h0 : Tendsto (fun u : ℝ => -(u ^ (-a)) / a * (1 - Real.exp (-u)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hl : Tendsto (fun u : ℝ => u ^ (1 - a) / a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt (fun u : ℝ => u ^ (1 - a)) 0 :=
        Real.continuousAt_rpow_const 0 (1 - a) (Or.inr (by linarith))
      have h := (hc.tendsto.div_const a).mono_left nhdsWithin_le_nhds
      rwa [Real.zero_rpow (by linarith : (1 - a) ≠ 0), zero_div] at h
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : 0 < u := hu
    have hp : 0 < u ^ (-a) := Real.rpow_pos_of_pos hu0 _
    have e : u ^ (-a) * u = u ^ (1 - a) := by
      rw [← Real.rpow_add_one hu0.ne']
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos hp, abs_of_pos ha0]
    calc u ^ (-a) / a * |1 - Real.exp (-u)| ≤ u ^ (-a) / a * u :=
          mul_le_mul_of_nonneg_left (hb1 u hu0) (div_nonneg hp.le ha0.le)
      _ = u ^ (1 - a) / a := by rw [← e]; ring
  have hinf : Tendsto (fun u : ℝ => -(u ^ (-a)) / a * (1 - Real.exp (-u))) atTop (nhds 0) := by
    have hl : Tendsto (fun u : ℝ => u ^ (-a) / a) atTop (nhds 0) := by
      have h := (tendsto_rpow_neg_atTop ha0).div_const a
      rwa [zero_div] at h
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hp : 0 < u ^ (-a) := Real.rpow_pos_of_pos hu _
    have h2 : |1 - Real.exp (-u)| ≤ 1 := by
      have h3 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h4 := Real.exp_pos (-u)
      rw [abs_of_nonneg (by linarith)]
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos hp, abs_of_pos ha0]
    calc u ^ (-a) / a * |1 - Real.exp (-u)| ≤ u ^ (-a) / a * 1 :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg hp.le ha0.le)
      _ = u ^ (-a) / a := mul_one _
  have i1 : IntegrableOn (fun u : ℝ => u ^ (-1 - a) * (1 - Real.exp (-u))) (Set.Ioi 0) := by
    refine integrableOn_rpow_of_lin_bounds (φ := fun u => 1 - Real.exp (-u)) ?_ ha0 ha1
      (A := 1) (B := 1) ?_ ?_
    · exact (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousOn
    · intro x hx _
      show |1 - Real.exp (-x)| ≤ 1 * x
      rw [one_mul]
      exact hb1 x hx
    · intro x hx
      show |1 - Real.exp (-x)| ≤ 1
      have h3 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h4 := Real.exp_pos (-x)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hG := Real.GammaIntegral_convergent (by linarith : (0 : ℝ) < 1 - a)
  have e0 : (1 - a - 1 : ℝ) = -a := by ring
  rw [e0] at hG
  have i2 : IntegrableOn (fun u : ℝ => (-(u ^ (-a)) / a) * Real.exp (-u)) (Set.Ioi 0) := by
    have h := hG.const_mul (-(1 / a))
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    show -(1 / a) * (Real.exp (-u) * u ^ (-a)) = -(u ^ (-a)) / a * Real.exp (-u)
    ring
  have hint : IntegrableOn (fun u : ℝ => u ^ (-1 - a) * (1 - Real.exp (-u))
      + (-(u ^ (-a)) / a) * Real.exp (-u)) (Set.Ioi 0) := Integrable.add i1 i2
  have hz := integral_Ioi_deriv_eq_zero hF0 hd h0 hinf hint
  have a1 := integral_add i1 i2
  have hΓ := Real.Gamma_eq_integral (by linarith : (0 : ℝ) < 1 - a)
  rw [e0] at hΓ
  have a2 : ∫ u in Set.Ioi (0 : ℝ), (-(u ^ (-a)) / a) * Real.exp (-u)
      = -(1 / a) * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ (-a) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    show -(u ^ (-a)) / a * Real.exp (-u) = -(1 / a) * (Real.exp (-u) * u ^ (-a))
    ring
  rw [← hΓ] at a2
  have hz' : ∫ u in Set.Ioi (0 : ℝ), u ^ (-1 - a) * (1 - Real.exp (-u))
      + -(1 / a) * Real.Gamma (1 - a) = 0 := by
    rw [← a2, ← a1]
    exact hz
  have e4 : Real.Gamma (1 - a) / a = (1 / a) * Real.Gamma (1 - a) := by ring
  rw [e4]
  linarith

/-- `∫₀^∞ x^{-1-a} (1 - e^{-x/4}) dx = 4^{-a} Γ(1 - a)/a` for `0 < a < 1`. -/
theorem integral_rpow_one_sub_exp_quarter {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ (-1 - a) * (1 - Real.exp (-(x / 4)))
      = (4 : ℝ) ^ (-a) * (Real.Gamma (1 - a) / a) := by
  have h := integral_comp_mul_left_Ioi'
    (fun x : ℝ => x ^ (-1 - a) * (1 - Real.exp (-(x / 4)))) 0 (by norm_num : (0 : ℝ) < 4)
  rw [mul_zero] at h
  rw [← h]
  have hfun : ∀ u ∈ Set.Ioi (0 : ℝ), (4 * u) ^ (-1 - a) * (1 - Real.exp (-(4 * u / 4)))
      = (4 : ℝ) ^ (-1 - a) * (u ^ (-1 - a) * (1 - Real.exp (-u))) := by
    intro u hu
    have hu0 : 0 < u := hu
    rw [Real.mul_rpow (by norm_num) hu0.le]
    have e : 4 * u / 4 = u := by ring
    rw [e]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul,
    integral_rpow_one_sub_exp ha0 ha1, smul_eq_mul]
  have e4 : (4 : ℝ) * (4 : ℝ) ^ (-1 - a) = (4 : ℝ) ^ (-a) := by
    have h4 := Real.rpow_add (by norm_num : (0 : ℝ) < 4) 1 (-1 - a)
    rw [Real.rpow_one] at h4
    rw [← h4]
    congr 1
    ring
  rw [← mul_assoc, e4]

/-- **`∫₀^∞ t^{s/2-1} (1 - e^{-1/(4t)}) dt = 2^{-s} Γ(1 - s/2)/(s/2)`** for `0 < s < 2`. -/
theorem integral_t_one_sub_exp {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (s / 2 - 1) * (1 - Real.exp (-(1 / (4 * t))))
      = (2 : ℝ) ^ (-s) * (Real.Gamma (1 - s / 2) / (s / 2)) := by
  have h := integral_comp_rpow_Ioi
    (fun t : ℝ => t ^ (s / 2 - 1) * (1 - Real.exp (-(1 / (4 * t))))) (p := -1) (by norm_num)
  rw [← h]
  have hfun : ∀ x ∈ Set.Ioi (0 : ℝ), (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
        ((x ^ (-1 : ℝ)) ^ (s / 2 - 1) * (1 - Real.exp (-(1 / (4 * x ^ (-1 : ℝ))))))
      = x ^ (-1 - s / 2) * (1 - Real.exp (-(x / 4))) := by
    intro x hx
    have hx0 : 0 < x := hx
    have e1 : (x ^ (-1 : ℝ)) ^ (s / 2 - 1) = x ^ (-1 * (s / 2 - 1)) :=
      (Real.rpow_mul hx0.le (-1) (s / 2 - 1)).symm
    have e2 : x ^ ((-1 : ℝ) - 1) * x ^ (-1 * (s / 2 - 1)) = x ^ (-1 - s / 2) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have e3 : 1 / (4 * x ^ (-1 : ℝ)) = x / 4 := by
      rw [Real.rpow_neg_one, one_div, mul_inv, inv_inv]
      ring
    rw [smul_eq_mul, e1, e3, abs_neg, abs_one, one_mul, ← mul_assoc, e2]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun,
    integral_rpow_one_sub_exp_quarter (by linarith : 0 < s / 2) (by linarith : s / 2 < 1)]
  have e4 : (4 : ℝ) ^ (-(s / 2)) = (2 : ℝ) ^ (-s) := by
    have e : (4 : ℝ) = 2 ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      norm_num
    rw [e, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [e4]

/-- **`r^{-1-s/2} = Γ(1 + s/2)⁻¹ ∫₀^∞ t^{s/2} e^{-rt} dt`** for `r > 0`, `s > -2`. -/
theorem rpow_eq_gamma_integral {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : -2 < s) :
    r ^ (-1 - s / 2)
      = (∫ t in Set.Ioi (0 : ℝ), t ^ (s / 2) * Real.exp (-(r * t))) / Real.Gamma (1 + s / 2) := by
  have ha : (0 : ℝ) < 1 + s / 2 := by linarith
  have h := integral_rpow_mul_exp_neg_mul_Ioi ha hr
  have e0 : (1 + s / 2 - 1 : ℝ) = s / 2 := by ring
  rw [e0] at h
  rw [h]
  have hΓ := Real.Gamma_pos_of_pos ha
  have e1 : (1 / r) ^ (1 + s / 2) = r ^ (-1 - s / 2) := by
    rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
    congr 1
    ring
  rw [e1, mul_div_assoc, div_self hΓ.ne', mul_one]

end Tower.RV6
