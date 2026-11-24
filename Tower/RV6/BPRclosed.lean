import Mathlib
import Tower.RV6.BPGauss

/-!
# RungBP, step 5 (second half): `R(s) = s j(s) = 2^{-s} Γ(1 - s/2)/Γ(1 + s/2)`

`Φ_s(p) = (1 - cos p₁)(p₁² + p₂²)^{-1-s/2}` on `ℝ²`, `0 < s < 2`, is integrated twice.

* With `r^{-1-s/2} = Γ(1 + s/2)⁻¹ ∫₀^∞ t^{s/2} e^{-rt} dt` and Fubini (`integrable_kerG`):
  `∫ Φ_s = π 2^{-s} Γ(1 - s/2)/((s/2) Γ(1 + s/2))` (`integral_phiR_gauss`).
* In polar coordinates, `r Φ_s(r cos θ, r sin θ) = (1 - cos(r cos θ)) r^{-1-s}` and
  `∫_{-π}^{π} cos(r cos θ) dθ = 2π J₀(r)`: `∫ Φ_s = 2π j(s)` (`integral_phiR_polar`).
* **`jS_closed`**: `s j(s) = 2^{-s} Γ(1 - s/2)/Γ(1 + s/2)`.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

/-- `Φ_s(p) = (1 - cos p₁)(p₁² + p₂²)^{-1-s/2}`. -/
noncomputable def phiR (s : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - Real.cos p.1) * (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - s / 2)

/-- `K(t, p) = t^{s/2} (1 - cos p₁) e^{-t(p₁² + p₂²)}`. -/
noncomputable def kerG (s : ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  q.1 ^ (s / 2) * ((1 - Real.cos q.2.1) * Real.exp (-q.1 * (q.2.1 ^ 2 + q.2.2 ^ 2)))

theorem one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  have h := Real.cos_le_one x
  linarith

theorem integrable_one_sub_cos_gauss {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => (1 - Real.cos x) * Real.exp (-t * x ^ 2)) := by
  have h : Integrable (fun x : ℝ => Real.exp (-t * x ^ 2) - Real.cos x * Real.exp (-t * x ^ 2)) :=
    (integrable_exp_neg_mul_sq ht).sub (integrable_cos_mul_gauss ht)
  refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
  show Real.exp (-t * x ^ 2) - Real.cos x * Real.exp (-t * x ^ 2)
    = (1 - Real.cos x) * Real.exp (-t * x ^ 2)
  ring

theorem kerG_nonneg (s : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : ℝ × ℝ) : 0 ≤ kerG s (t, p) :=
  mul_nonneg (Real.rpow_nonneg ht _) (mul_nonneg (one_sub_cos_nonneg _) (Real.exp_pos _).le)

/-- `∫_{ℝ²} K(t, p) dp = π t^{s/2-1} (1 - e^{-1/(4t)})` for `t > 0`. -/
theorem integral_kerG_p (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ p : ℝ × ℝ, kerG s (t, p) = π * (t ^ (s / 2 - 1) * (1 - Real.exp (-(1 / (4 * t))))) := by
  have h1 : (fun p : ℝ × ℝ => kerG s (t, p))
      = fun p : ℝ × ℝ => t ^ (s / 2) * ((1 - Real.cos p.1) * Real.exp (-t * (p.1 ^ 2 + p.2 ^ 2))) :=
    rfl
  rw [h1, integral_const_mul, integral_prod_one_sub_cos_gauss ht, Real.rpow_sub_one ht.ne']
  ring

theorem integrableOn_t_one_sub_exp {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) * (1 - Real.exp (-(1 / (4 * t))))) (Set.Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_t_one_sub_exp hs0 hs2]
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos two_pos _
  have h2 : 0 < Real.Gamma (1 - s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h3 : (0 : ℝ) < s / 2 := by linarith
  exact ne_of_gt (mul_pos h1 (div_pos h2 h3))

theorem integrable_kerG {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    Integrable (kerG s)
      (((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure (ℝ × ℝ))) := by
  have hm : Measurable (kerG s) := by
    have h1 : Measurable fun q : ℝ × (ℝ × ℝ) => q.1 ^ (s / 2) := measurable_fst.pow_const _
    have h2 : Continuous fun q : ℝ × (ℝ × ℝ) =>
        (1 - Real.cos q.2.1) * Real.exp (-q.1 * (q.2.1 ^ 2 + q.2.2 ^ 2)) := by
      fun_prop
    exact h1.mul h2.measurable
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := ht
    have hf := integrable_one_sub_cos_gauss ht0
    have hg := integrable_exp_neg_mul_sq ht0
    have hfg : Integrable (fun z : ℝ × ℝ =>
        ((1 - Real.cos z.1) * Real.exp (-t * z.1 ^ 2)) * Real.exp (-t * z.2 ^ 2))
        (volume : Measure (ℝ × ℝ)) := by
      rw [Measure.volume_eq_prod]
      exact hf.mul_prod hg
    have h := hfg.const_mul (t ^ (s / 2))
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    show t ^ (s / 2) * (((1 - Real.cos z.1) * Real.exp (-t * z.1 ^ 2)) * Real.exp (-t * z.2 ^ 2))
      = t ^ (s / 2) * ((1 - Real.cos z.1) * Real.exp (-t * (z.1 ^ 2 + z.2 ^ 2)))
    rw [mul_assoc (1 - Real.cos z.1), ← Real.exp_add]
    congr 3
    ring
  · have hI := integrableOn_t_one_sub_exp hs0 hs2
    have h : IntegrableOn (fun t : ℝ => π * (t ^ (s / 2 - 1) * (1 - Real.exp (-(1 / (4 * t))))))
        (Set.Ioi 0) := Integrable.const_mul hI π
    refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht0 : 0 < t := ht
    have hn : (fun p : ℝ × ℝ => ‖kerG s (t, p)‖) = fun p : ℝ × ℝ => kerG s (t, p) := by
      funext p
      rw [Real.norm_eq_abs, abs_of_nonneg (kerG_nonneg s ht0.le p)]
    show π * (t ^ (s / 2 - 1) * (1 - Real.exp (-(1 / (4 * t))))) = ∫ p : ℝ × ℝ, ‖kerG s (t, p)‖
    rw [hn, integral_kerG_p s ht0]

/-- `Φ_s(p) = Γ(1 + s/2)⁻¹ ∫₀^∞ K(t, p) dt` for every `p` (`s > -2`). -/
theorem phiR_eq_integral {s : ℝ} (hs : -2 < s) (p : ℝ × ℝ) :
    phiR s p = (∫ t in Set.Ioi (0 : ℝ), kerG s (t, p)) / Real.Gamma (1 + s / 2) := by
  by_cases hp : p.1 = 0
  · have h0 : (fun t : ℝ => kerG s (t, p)) = fun _ : ℝ => (0 : ℝ) := by
      funext t
      show t ^ (s / 2) * ((1 - Real.cos p.1) * Real.exp (-t * (p.1 ^ 2 + p.2 ^ 2))) = 0
      rw [hp, Real.cos_zero, sub_self, zero_mul, mul_zero]
    unfold phiR
    rw [h0, integral_zero, zero_div, hp, Real.cos_zero, sub_self, zero_mul]
  · have hr1 : 0 < p.1 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hp))
    have hr : 0 < p.1 ^ 2 + p.2 ^ 2 := by
      have := sq_nonneg p.2
      linarith
    have hg := rpow_eq_gamma_integral hr hs
    have hfun : (fun t : ℝ => kerG s (t, p))
        = fun t : ℝ => (1 - Real.cos p.1) * (t ^ (s / 2) * Real.exp (-((p.1 ^ 2 + p.2 ^ 2) * t))) := by
      funext t
      show t ^ (s / 2) * ((1 - Real.cos p.1) * Real.exp (-t * (p.1 ^ 2 + p.2 ^ 2)))
        = (1 - Real.cos p.1) * (t ^ (s / 2) * Real.exp (-((p.1 ^ 2 + p.2 ^ 2) * t)))
      have e : -t * (p.1 ^ 2 + p.2 ^ 2) = -((p.1 ^ 2 + p.2 ^ 2) * t) := by ring
      rw [e]
      ring
    unfold phiR
    rw [hg, hfun, integral_const_mul, mul_div_assoc]

/-- **`∫_{ℝ²} Φ_s = π 2^{-s} Γ(1 - s/2)/((s/2) Γ(1 + s/2))`** for `0 < s < 2`. -/
theorem integral_phiR_gauss {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ∫ p : ℝ × ℝ, phiR s p
      = π * ((2 : ℝ) ^ (-s) * (Real.Gamma (1 - s / 2) / (s / 2))) / Real.Gamma (1 + s / 2) := by
  have hsw : ∫ t in Set.Ioi (0 : ℝ), ∫ p : ℝ × ℝ, kerG s (t, p)
      = ∫ p : ℝ × ℝ, ∫ t in Set.Ioi (0 : ℝ), kerG s (t, p) :=
    integral_integral_swap (f := fun t p => kerG s (t, p)) (integrable_kerG hs0 hs2)
  have hfun : (fun p : ℝ × ℝ => phiR s p)
      = fun p : ℝ × ℝ => (∫ t in Set.Ioi (0 : ℝ), kerG s (t, p)) / Real.Gamma (1 + s / 2) :=
    funext (fun p => phiR_eq_integral (by linarith) p)
  calc ∫ p : ℝ × ℝ, phiR s p
      = ∫ p : ℝ × ℝ, (∫ t in Set.Ioi (0 : ℝ), kerG s (t, p)) / Real.Gamma (1 + s / 2) := by
        rw [hfun]
    _ = (∫ p : ℝ × ℝ, ∫ t in Set.Ioi (0 : ℝ), kerG s (t, p)) / Real.Gamma (1 + s / 2) :=
        integral_div _ _
    _ = (∫ t in Set.Ioi (0 : ℝ), ∫ p : ℝ × ℝ, kerG s (t, p)) / Real.Gamma (1 + s / 2) := by
        rw [hsw]
    _ = (∫ t in Set.Ioi (0 : ℝ), π * (t ^ (s / 2 - 1) * (1 - Real.exp (-(1 / (4 * t))))))
          / Real.Gamma (1 + s / 2) := by
        rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => integral_kerG_p s ht)]
    _ = π * ((2 : ℝ) ^ (-s) * (Real.Gamma (1 - s / 2) / (s / 2))) / Real.Gamma (1 + s / 2) := by
        rw [integral_const_mul, integral_t_one_sub_exp hs0 hs2]

/-! ## Polar coordinates -/

/-- `∫_{-π}^{π} cos(r cos θ) dθ = 2π J₀(r)` for `r ≥ 0`. -/
theorem integral_cos_cos_two_pi {r : ℝ} (hr : 0 ≤ r) :
    ∫ θ in Set.Ioo (-π) π, Real.cos (r * Real.cos θ) = 2 * π * besselJ0 r := by
  have hπ := Real.pi_pos
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith : -π ≤ π)]
  have hper : Function.Periodic (fun θ : ℝ => Real.cos (r * Real.cos θ)) (2 * π) := by
    intro θ
    show Real.cos (r * Real.cos (θ + 2 * π)) = Real.cos (r * Real.cos θ)
    rw [Real.cos_add_two_pi]
  have h1 := hper.intervalIntegral_add_eq (-π) 0
  have e1 : -π + 2 * π = π := by ring
  rw [e1, zero_add] at h1
  have h2 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (f := fun θ : ℝ => Real.cos (r * Real.cos θ)) (c := 2 * π) (by positivity)
  rw [mul_zero, mul_one] at h2
  have hG : ∫ u in (0 : ℝ)..1, Real.cos (r * Real.cos (2 * π * u)) = besselJ0 r := by
    rw [intervalIntegral.integral_of_le zero_le_one, besselJ0_eq_besG hr]
    rfl
  rw [h1]
  have h3 : ∫ θ in (0 : ℝ)..(2 * π), Real.cos (r * Real.cos θ)
      = 2 * π * ∫ u in (0 : ℝ)..1, Real.cos (r * Real.cos (2 * π * u)) := by
    rw [h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [h3, hG]

/-- `r Φ_s(r cos θ, r sin θ) = (1 - cos(r cos θ)) r^{-1-s}` for `r > 0`. -/
theorem polar_phiR {s r θ : ℝ} (hr : 0 < r) :
    r * phiR s (r * Real.cos θ, r * Real.sin θ) = (1 - Real.cos (r * Real.cos θ)) * r ^ (-1 - s) := by
  unfold phiR
  have e1 : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ
  have e2 : (r ^ 2) ^ (-1 - s / 2) = r ^ (-2 - s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  have e3 : r * r ^ (-2 - s) = r ^ (-1 - s) := by
    have h := Real.rpow_add_one hr.ne' (-2 - s)
    have e : (-2 - s) + 1 = -1 - s := by ring
    rw [e] at h
    rw [h]
    ring
  show r * ((1 - Real.cos (r * Real.cos θ)) * ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) ^ (-1 - s / 2))
    = (1 - Real.cos (r * Real.cos θ)) * r ^ (-1 - s)
  rw [e1, e2, ← e3]
  ring

/-- **`∫_{ℝ²} Φ_s = 2π j(s)`** for `0 < s < 2`. -/
theorem integral_phiR_polar {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    ∫ p : ℝ × ℝ, phiR s p = 2 * π * jS s := by
  have hπ := Real.pi_pos
  have h := integral_comp_polarCoord_symm (phiR s)
  have hpt : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
      q.1 • phiR s (polarCoord.symm q) = (1 - Real.cos (q.1 * Real.cos q.2)) * q.1 ^ (-1 - s) := by
    intro q hq
    have hr : 0 < q.1 := hq.1
    rw [smul_eq_mul]
    exact polar_phiR hr
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [htarget, setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt] at h
  -- the value is not zero, so the polar integrand is integrable on the target
  have hval := integral_phiR_gauss hs0 hs2
  have hne : ∫ p : ℝ × ℝ, phiR s p ≠ 0 := by
    rw [hval]
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos two_pos _
    have h2 : 0 < Real.Gamma (1 - s / 2) := Real.Gamma_pos_of_pos (by linarith)
    have h3 : 0 < Real.Gamma (1 + s / 2) := Real.Gamma_pos_of_pos (by linarith)
    have h4 : (0 : ℝ) < s / 2 := by linarith
    exact ne_of_gt (div_pos (mul_pos hπ (mul_pos h1 (div_pos h2 h4))) h3)
  have hint : IntegrableOn (fun q : ℝ × ℝ => (1 - Real.cos (q.1 * Real.cos q.2)) * q.1 ^ (-1 - s))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [h]
    exact hne
  rw [Measure.volume_eq_prod] at hint h
  rw [setIntegral_prod _ hint] at h
  -- the inner integral
  have hin : ∀ r ∈ Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (-π) π,
      (1 - Real.cos (r * Real.cos θ)) * r ^ (-1 - s) = 2 * π * ((1 - besselJ0 r) * r ^ (-1 - s)) := by
    intro r hr
    have hr0 : 0 ≤ r := le_of_lt hr
    have hc : Continuous fun θ : ℝ => Real.cos (r * Real.cos θ) :=
      Real.continuous_cos.comp (continuous_const.mul Real.continuous_cos)
    have i1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (-π) π) :=
      continuous_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
    have i2 : IntegrableOn (fun θ : ℝ => Real.cos (r * Real.cos θ)) (Set.Ioo (-π) π) :=
      hc.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
    have hone : ∫ _ in Set.Ioo (-π) π, (1 : ℝ) = 2 * π := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith : -π ≤ π),
        intervalIntegral.integral_const]
      simp only [smul_eq_mul, mul_one]
      ring
    rw [integral_mul_const, integral_sub i1 i2, hone, integral_cos_cos_two_pi hr0]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_const_mul] at h
  exact h.symm

/-- **`s j(s) = 2^{-s} Γ(1 - s/2)/Γ(1 + s/2)`** for `0 < s < 2`. -/
theorem jS_closed {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    s * jS s = (2 : ℝ) ^ (-s) * Real.Gamma (1 - s / 2) / Real.Gamma (1 + s / 2) := by
  have hπ := Real.pi_pos
  have h := (integral_phiR_polar hs0 hs2).symm.trans (integral_phiR_gauss hs0 hs2)
  have hsi : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  have hk : (2 * π) * (s * jS s)
      = (2 * π) * ((2 : ℝ) ^ (-s) * Real.Gamma (1 - s / 2) / Real.Gamma (1 + s / 2)) := by
    calc (2 * π) * (s * jS s) = s * (2 * π * jS s) := by ring
      _ = s * (π * ((2 : ℝ) ^ (-s) * (Real.Gamma (1 - s / 2) / (s / 2))) / Real.Gamma (1 + s / 2)) := by
          rw [h]
      _ = (2 * π) * ((2 : ℝ) ^ (-s) * Real.Gamma (1 - s / 2) / Real.Gamma (1 + s / 2)) := by
          linear_combination (2 * π * (2 : ℝ) ^ (-s) * Real.Gamma (1 - s / 2)
            * (Real.Gamma (1 + s / 2))⁻¹) * hsi
  exact mul_left_cancel₀ (by positivity) hk

end Tower.RV6
