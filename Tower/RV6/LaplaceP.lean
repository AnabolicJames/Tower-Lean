import Mathlib
import Tower.RV6.LaplaceIK

/-!
# The Laplace representation of `I₀ K₀`

With the two Laplace forms of `LaplaceIK.lean`, the product `I₀(t) K₀(t) = (I₀ e^{-t})(K₀ e^{t})` is the
Laplace transform of the convolution `ν = ρ_I * ρ_K`:

* `integral_shift_K`: `∫ e^{-tw} ρ_K⁺(w - s) dw = e^{-ts} ∫₀^∞ e^{-tr} ρ_K(r) dr` (translation);
* `integrable_conv` and **`laplace_P`**: `I₀(t) K₀(t) = ∫₀^∞ e^{-tw} ν(w) dw` for `t > 0` (Fubini),
  `ν(w) = ∫₀² ρ_I(s) ρ_K⁺(w - s) ds` (`nuP`), with `integrableOn_laplace_P`;
* `nuP_eq_theta`: for `0 < w ≤ 1`, `ν(w) = (2/π) ∫₀^{π/2} ((2 - w sin²θ)(2 + w cos²θ))^{-1/2} dθ`
  (`s = w sin²θ`);
* **`abs_nuP_sub_half_le`**: `|ν(w) - 1/2| ≤ w²` for `0 < w ≤ 1`.  The term of first order in `w` is
  `(w/8)(cos²θ - sin²θ)`, whose integral over `[0, π/2]` vanishes.

`ν ≥ 0` and the bound near `0` are all that the decay of `θᵏ(I₀ K₀)` at infinity needs.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `ρ_K` extended by `0` on `r ≤ 0`. -/
noncomputable def rhoKp (r : ℝ) : ℝ := (Set.Ioi (0 : ℝ)).indicator rhoK r

/-- **The Laplace density of `I₀ K₀`**: `ν(w) = ∫₀² ρ_I(s) ρ_K⁺(w - s) ds`. -/
noncomputable def nuP (w : ℝ) : ℝ := ∫ s in Set.Ioo (0 : ℝ) 2, rhoI s * rhoKp (w - s)

theorem rhoI_nonneg (s : ℝ) : 0 ≤ rhoI s :=
  inv_nonneg.mpr (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg _))

theorem rhoK_nonneg (r : ℝ) : 0 ≤ rhoK r := inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem rhoKp_nonneg (r : ℝ) : 0 ≤ rhoKp r := by
  unfold rhoKp
  exact Set.indicator_nonneg (fun r _ => rhoK_nonneg r) r

theorem nuP_nonneg (w : ℝ) : 0 ≤ nuP w :=
  setIntegral_nonneg measurableSet_Ioo (fun s _ => mul_nonneg (rhoI_nonneg s) (rhoKp_nonneg _))

theorem measurable_rhoI : Measurable rhoI := by
  have h : Measurable (fun s : ℝ => Real.sqrt (s * (2 - s))) :=
    Real.continuous_sqrt.measurable.comp (by fun_prop)
  have h2 : Measurable (fun s : ℝ => (π * Real.sqrt (s * (2 - s)))⁻¹) :=
    (measurable_const.mul h).inv
  exact h2

theorem measurable_rhoK : Measurable rhoK := by
  have h : Measurable (fun r : ℝ => Real.sqrt (r * (r + 2))) :=
    Real.continuous_sqrt.measurable.comp (by fun_prop)
  have h2 : Measurable (fun r : ℝ => (Real.sqrt (r * (r + 2)))⁻¹) := h.inv
  exact h2

theorem measurable_rhoKp : Measurable rhoKp := measurable_rhoK.indicator measurableSet_Ioi

theorem rhoKp_mul (t r : ℝ) :
    Real.exp (-t * r) * rhoKp r
      = (Set.Ioi (0 : ℝ)).indicator (fun r : ℝ => Real.exp (-t * r) * rhoK r) r := by
  unfold rhoKp
  by_cases h : r ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

theorem nuP_eq_zero_of_nonpos {w : ℝ} (hw : w ≤ 0) : nuP w = 0 := by
  unfold nuP
  have h : ∀ s ∈ Set.Ioo (0 : ℝ) 2, rhoI s * rhoKp (w - s) = (fun _ : ℝ => (0 : ℝ)) s := by
    intro s hs
    have hn : w - s ∉ Set.Ioi (0 : ℝ) := by
      intro hm
      have hm' : 0 < w - s := hm
      linarith [hs.1]
    unfold rhoKp
    rw [Set.indicator_of_notMem hn, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioo h, integral_zero]

/-! ## The translation and Fubini -/

/-- `∫ e^{-tw} ρ_K⁺(w - s) dw = e^{-ts} ∫₀^∞ e^{-tr} ρ_K(r) dr`. -/
theorem integral_shift_K (t s : ℝ) :
    ∫ w, Real.exp (-t * w) * rhoKp (w - s)
      = Real.exp (-t * s) * ∫ r in Set.Ioi (0 : ℝ), Real.exp (-t * r) * rhoK r := by
  have hf : (fun w : ℝ => Real.exp (-t * w) * rhoKp (w - s))
      = fun w : ℝ => Real.exp (-t * s) *
          (Set.Ioi (0 : ℝ)).indicator (fun r : ℝ => Real.exp (-t * r) * rhoK r) (w - s) := by
    funext w
    rw [← rhoKp_mul]
    have e : Real.exp (-t * w) = Real.exp (-t * s) * Real.exp (-t * (w - s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    ring
  rw [hf, integral_const_mul,
    integral_sub_right_eq_self
      ((Set.Ioi (0 : ℝ)).indicator (fun r : ℝ => Real.exp (-t * r) * rhoK r)) s,
    integral_indicator measurableSet_Ioi]

/-- The convolution kernel `ρ_I(s) e^{-tw} ρ_K⁺(w - s)` is integrable on `(0, 2) × ℝ`. -/
theorem integrable_conv {t : ℝ} (ht : 0 < t) :
    Integrable (Function.uncurry fun (s w : ℝ) => rhoI s * (Real.exp (-t * w) * rhoKp (w - s)))
      ((volume.restrict (Set.Ioo (0 : ℝ) 2)).prod volume) := by
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (s w : ℝ) => rhoI s * (Real.exp (-t * w) * rhoKp (w - s)))
      ((volume.restrict (Set.Ioo (0 : ℝ) 2)).prod volume) := by
    have h : Measurable (fun p : ℝ × ℝ => rhoI p.1 * (Real.exp (-t * p.2) * rhoKp (p.2 - p.1))) :=
      (measurable_rhoI.comp measurable_fst).mul
        ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
          (measurable_rhoKp.comp (measurable_snd.sub measurable_fst)))
    exact h.aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  have hK : Integrable ((Set.Ioi (0 : ℝ)).indicator (fun r : ℝ => Real.exp (-t * r) * rhoK r)) :=
    (integrableOn_laplace_K0 ht).integrable_indicator measurableSet_Ioi
  constructor
  · refine Filter.Eventually.of_forall (fun s => ?_)
    have h1 := (hK.comp_sub_right s).const_mul (rhoI s * Real.exp (-t * s))
    refine h1.congr (Filter.Eventually.of_forall (fun w => ?_))
    show rhoI s * Real.exp (-t * s)
        * (Set.Ioi (0 : ℝ)).indicator (fun r : ℝ => Real.exp (-t * r) * rhoK r) (w - s)
      = rhoI s * (Real.exp (-t * w) * rhoKp (w - s))
    rw [← rhoKp_mul]
    have e : Real.exp (-t * w) = Real.exp (-t * s) * Real.exp (-t * (w - s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    ring
  · have h2 : Integrable (fun s : ℝ => Real.exp (-t * s) * rhoI s
        * ∫ r in Set.Ioi (0 : ℝ), Real.exp (-t * r) * rhoK r)
        (volume.restrict (Set.Ioo (0 : ℝ) 2)) :=
      (integrableOn_laplace_I0 t).mul_const _
    refine h2.congr (Filter.Eventually.of_forall (fun s => ?_))
    show Real.exp (-t * s) * rhoI s * (∫ r in Set.Ioi (0 : ℝ), Real.exp (-t * r) * rhoK r)
      = ∫ w, ‖rhoI s * (Real.exp (-t * w) * rhoKp (w - s))‖
    have hn : (fun w : ℝ => ‖rhoI s * (Real.exp (-t * w) * rhoKp (w - s))‖)
        = fun w : ℝ => rhoI s * (Real.exp (-t * w) * rhoKp (w - s)) := by
      funext w
      exact Real.norm_of_nonneg
        (mul_nonneg (rhoI_nonneg s) (mul_nonneg (Real.exp_pos _).le (rhoKp_nonneg _)))
    rw [hn, integral_const_mul, integral_shift_K]
    ring

/-- The inner integral after Fubini. -/
theorem integral_conv_inner (t w : ℝ) :
    (∫ s in Set.Ioo (0 : ℝ) 2, rhoI s * (Real.exp (-t * w) * rhoKp (w - s)))
      = Real.exp (-t * w) * nuP w := by
  unfold nuP
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => ?_)
  show rhoI s * (Real.exp (-t * w) * rhoKp (w - s)) = Real.exp (-t * w) * (rhoI s * rhoKp (w - s))
  ring

/-- **`I₀(t) K₀(t) = ∫₀^∞ e^{-tw} ν(w) dw`** for `t > 0`. -/
theorem laplace_P {t : ℝ} (ht : 0 < t) :
    besselI0 t * besselK0 t = ∫ w in Set.Ioi (0 : ℝ), Real.exp (-t * w) * nuP w := by
  have hI := laplace_I0 t
  have hK := laplace_K0 t
  have hprod : besselI0 t * besselK0 t
      = (∫ s in Set.Ioo (0 : ℝ) 2, Real.exp (-t * s) * rhoI s)
        * ∫ r in Set.Ioi (0 : ℝ), Real.exp (-t * r) * rhoK r := by
    rw [← hI, ← hK]
    have e : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    linear_combination (-(besselI0 t * besselK0 t)) * e
  have hstep : (∫ s in Set.Ioo (0 : ℝ) 2, Real.exp (-t * s) * rhoI s)
        * (∫ r in Set.Ioi (0 : ℝ), Real.exp (-t * r) * rhoK r)
      = ∫ s in Set.Ioo (0 : ℝ) 2, ∫ w, rhoI s * (Real.exp (-t * w) * rhoKp (w - s)) := by
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => ?_)
    show Real.exp (-t * s) * rhoI s * (∫ r in Set.Ioi (0 : ℝ), Real.exp (-t * r) * rhoK r)
      = ∫ w, rhoI s * (Real.exp (-t * w) * rhoKp (w - s))
    rw [integral_const_mul, integral_shift_K]
    ring
  have hswap : (∫ s in Set.Ioo (0 : ℝ) 2, ∫ w, rhoI s * (Real.exp (-t * w) * rhoKp (w - s)))
      = ∫ w, ∫ s in Set.Ioo (0 : ℝ) 2, rhoI s * (Real.exp (-t * w) * rhoKp (w - s)) :=
    integral_integral_swap (integrable_conv ht)
  have hzero : ∀ w : ℝ, w ∉ Set.Ioi (0 : ℝ) → Real.exp (-t * w) * nuP w = 0 := by
    intro w hw
    have hw' : w ≤ 0 := not_lt.mp hw
    rw [nuP_eq_zero_of_nonpos hw', mul_zero]
  rw [hprod, hstep, hswap, setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun w => integral_conv_inner t w))

theorem integrableOn_laplace_P {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun w : ℝ => Real.exp (-t * w) * nuP w) (Set.Ioi (0 : ℝ)) := by
  have h := (integrable_conv ht).integral_prod_right
  have h' : Integrable (fun w : ℝ =>
      ∫ s in Set.Ioo (0 : ℝ) 2, rhoI s * (Real.exp (-t * w) * rhoKp (w - s))) := h
  have h2 : Integrable (fun w : ℝ => Real.exp (-t * w) * nuP w) :=
    h'.congr (Filter.Eventually.of_forall (fun w => integral_conv_inner t w))
  exact h2.integrableOn

/-! ## `ν` near `0` -/

/-- `(2 - w sin²θ)(2 + w cos²θ)`. -/
noncomputable def Hnu (w θ : ℝ) : ℝ := (2 - w * Real.sin θ ^ 2) * (2 + w * Real.cos θ ^ 2)

theorem image_mul_sin_sq {w : ℝ} (hw : 0 < w) :
    (fun θ : ℝ => w * Real.sin θ ^ 2) '' Set.Ioo 0 (π / 2) = Set.Ioo 0 w := by
  ext s
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have ha : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h1 : Real.sin θ < Real.sin (π / 2) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hθ.1, Real.pi_pos]) le_rfl hθ.2
    rw [Real.sin_pi_div_two] at h1
    have hs2 : Real.sin θ ^ 2 < 1 := by nlinarith
    show w * Real.sin θ ^ 2 ∈ Set.Ioo 0 w
    exact ⟨mul_pos hw (pow_pos ha 2), by nlinarith⟩
  · intro hs
    have h0 : 0 < s := hs.1
    have h1 : s < w := hs.2
    have hq0 : 0 < s / w := div_pos h0 hw
    have hq1 : s / w < 1 := (div_lt_one hw).mpr h1
    have hr0 : 0 < Real.sqrt (s / w) := Real.sqrt_pos.mpr hq0
    have hr1 : Real.sqrt (s / w) < 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt hq0.le hq1
    refine ⟨Real.arcsin (Real.sqrt (s / w)),
      ⟨Real.arcsin_pos.mpr hr0, Real.arcsin_lt_pi_div_two.mpr hr1⟩, ?_⟩
    show w * Real.sin (Real.arcsin (Real.sqrt (s / w))) ^ 2 = s
    rw [Real.sin_arcsin (by linarith) hr1.le, Real.sq_sqrt hq0.le]
    field_simp

theorem injOn_mul_sin_sq {w : ℝ} (hw : 0 < w) :
    Set.InjOn (fun θ : ℝ => w * Real.sin θ ^ 2) (Set.Ioo 0 (π / 2)) := by
  intro a ha b hb hab
  have e : w * Real.sin a ^ 2 = w * Real.sin b ^ 2 := hab
  have e2 : Real.sin a ^ 2 = Real.sin b ^ 2 := mul_left_cancel₀ hw.ne' e
  have hpa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2, Real.pi_pos])
  have hpb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 (by linarith [hb.2, Real.pi_pos])
  have e3 : Real.sin a = Real.sin b := by
    rw [← Real.sqrt_sq hpa.le, ← Real.sqrt_sq hpb.le, e2]
  have hai : a ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith [ha.1, Real.pi_pos], ha.2.le⟩
  have hbi : b ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith [hb.1, Real.pi_pos], hb.2.le⟩
  exact Real.injOn_sin hai hbi e3

theorem hasDerivWithinAt_mul_sin_sq (w : ℝ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivWithinAt (fun θ : ℝ => w * Real.sin θ ^ 2)
      (w * (2 * Real.sin θ * Real.cos θ)) (Set.Ioo 0 (π / 2)) θ := by
  intro θ _
  have h := ((Real.hasDerivAt_sin θ).pow 2).const_mul w
  have h2 : HasDerivAt (fun θ : ℝ => w * Real.sin θ ^ 2) (w * (2 * Real.sin θ * Real.cos θ)) θ := by
    refine h.congr_deriv ?_
    norm_num
  exact h2.hasDerivWithinAt

/-- The integrand after `s = w sin²θ`. -/
theorem nuP_pt {w θ : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |w * (2 * Real.sin θ * Real.cos θ)| * (rhoI (w * Real.sin θ ^ 2) * rhoK (w - w * Real.sin θ ^ 2))
      = 2 * π⁻¹ * (Real.sqrt (Hnu w θ))⁻¹ := by
  have ha : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsc := Real.sin_sq_add_cos_sq θ
  have ha1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hX : 0 < 2 - w * Real.sin θ ^ 2 := by nlinarith
  have hY : 0 < 2 + w * Real.cos θ ^ 2 := by nlinarith [sq_nonneg (Real.cos θ)]
  have hwa : 0 < w * Real.sin θ ^ 2 * (2 - w * Real.sin θ ^ 2) :=
    mul_pos (mul_pos hw (pow_pos ha 2)) hX
  have hwc : 0 < (w - w * Real.sin θ ^ 2) * (w - w * Real.sin θ ^ 2 + 2) := by
    have e : w - w * Real.sin θ ^ 2 = w * Real.cos θ ^ 2 := by linear_combination (-w) * hsc
    rw [e]
    exact mul_pos (mul_pos hw (pow_pos hc 2)) (by linarith)
  have hH : 0 < Hnu w θ := mul_pos hX hY
  have hsq1 : w * Real.sin θ ^ 2 * (2 - w * Real.sin θ ^ 2)
        * ((w - w * Real.sin θ ^ 2) * (w - w * Real.sin θ ^ 2 + 2))
      = (w * Real.sin θ * Real.cos θ) ^ 2 * Hnu w θ := by
    unfold Hnu
    linear_combination (-(Real.sin θ ^ 2) * w ^ 2 * (Real.sin θ ^ 2 * w - 2)
      * (Real.sin θ ^ 2 * w - Real.cos θ ^ 2 * w - w - 2)) * hsc
  have hwsc : 0 < w * Real.sin θ * Real.cos θ := mul_pos (mul_pos hw ha) hc
  have hprod : Real.sqrt (w * Real.sin θ ^ 2 * (2 - w * Real.sin θ ^ 2))
        * Real.sqrt ((w - w * Real.sin θ ^ 2) * (w - w * Real.sin θ ^ 2 + 2))
      = w * Real.sin θ * Real.cos θ * Real.sqrt (Hnu w θ) := by
    rw [← Real.sqrt_mul hwa.le, hsq1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hwsc.le]
  have hA : Real.sqrt (w * Real.sin θ ^ 2 * (2 - w * Real.sin θ ^ 2))
      * (Real.sqrt (w * Real.sin θ ^ 2 * (2 - w * Real.sin θ ^ 2)))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hwa).ne'
  have hB : Real.sqrt ((w - w * Real.sin θ ^ 2) * (w - w * Real.sin θ ^ 2 + 2))
      * (Real.sqrt ((w - w * Real.sin θ ^ 2) * (w - w * Real.sin θ ^ 2 + 2)))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hwc).ne'
  have hS : Real.sqrt (Hnu w θ) * (Real.sqrt (Hnu w θ))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hH).ne'
  have habs : |w * (2 * Real.sin θ * Real.cos θ)| = w * (2 * Real.sin θ * Real.cos θ) :=
    abs_of_pos (mul_pos hw (mul_pos (mul_pos two_pos ha) hc))
  unfold rhoI rhoK
  rw [habs, mul_inv]
  linear_combination
    (-2 * π⁻¹ * (Real.sqrt (w * Real.sin θ ^ 2 * (2 - w * Real.sin θ ^ 2)))⁻¹
      * (Real.sqrt ((w - w * Real.sin θ ^ 2) * (w - w * Real.sin θ ^ 2 + 2)))⁻¹
      * (Real.sqrt (Hnu w θ))⁻¹) * hprod
    + (-2 * w * Real.sin θ * Real.cos θ * π⁻¹
      * (Real.sqrt (w * Real.sin θ ^ 2 * (2 - w * Real.sin θ ^ 2)))⁻¹
      * (Real.sqrt ((w - w * Real.sin θ ^ 2) * (w - w * Real.sin θ ^ 2 + 2)))⁻¹) * hS
    + (2 * π⁻¹ * (Real.sqrt (Hnu w θ))⁻¹
      * Real.sqrt ((w - w * Real.sin θ ^ 2) * (w - w * Real.sin θ ^ 2 + 2))
      * (Real.sqrt ((w - w * Real.sin θ ^ 2) * (w - w * Real.sin θ ^ 2 + 2)))⁻¹) * hA
    + (2 * π⁻¹ * (Real.sqrt (Hnu w θ))⁻¹) * hB

/-- `ν(w) = ∫₀^w ρ_I(s) ρ_K(w - s) ds` for `0 < w ≤ 2`. -/
theorem nuP_eq_Ioo {w : ℝ} (hw2 : w ≤ 2) :
    nuP w = ∫ s in Set.Ioo (0 : ℝ) w, rhoI s * rhoK (w - s) := by
  unfold nuP
  have hsub : Set.Ioo (0 : ℝ) w ⊆ Set.Ioo 0 2 := Set.Ioo_subset_Ioo_right hw2
  have hdiff : ∀ s ∈ Set.Ioo (0 : ℝ) 2 \ Set.Ioo 0 w, rhoI s * rhoKp (w - s) = 0 := by
    intro s hs
    have hs1 : ¬ s < w := fun h => hs.2 ⟨hs.1.1, h⟩
    have hn : w - s ∉ Set.Ioi (0 : ℝ) := by
      intro hm
      have hm' : 0 < w - s := hm
      exact hs1 (by linarith)
    unfold rhoKp
    rw [Set.indicator_of_notMem hn, mul_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub hdiff]
  refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
  have hm : w - s ∈ Set.Ioi (0 : ℝ) := by
    show 0 < w - s
    linarith [hs.2]
  show rhoI s * rhoKp (w - s) = rhoI s * rhoK (w - s)
  unfold rhoKp
  rw [Set.indicator_of_mem hm]

/-- **`ν(w) = (2/π) ∫₀^{π/2} H(w, θ)^{-1/2} dθ`** for `0 < w ≤ 1`. -/
theorem nuP_eq_theta {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    nuP w = 2 * π⁻¹ * ∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (Hnu w θ))⁻¹ := by
  rw [nuP_eq_Ioo (by linarith)]
  have hcv := integral_image_eq_integral_abs_deriv_smul
    (f' := fun θ : ℝ => w * (2 * Real.sin θ * Real.cos θ))
    measurableSet_Ioo (hasDerivWithinAt_mul_sin_sq w) (injOn_mul_sin_sq hw)
    (fun s : ℝ => rhoI s * rhoK (w - s))
  rw [image_mul_sin_sq hw] at hcv
  simp only [smul_eq_mul] at hcv
  have hcv' : (∫ s in Set.Ioo (0 : ℝ) w, rhoI s * rhoK (w - s))
      = ∫ θ in Set.Ioo 0 (π / 2), |w * (2 * Real.sin θ * Real.cos θ)|
          * (rhoI (w * Real.sin θ ^ 2) * rhoK (w - w * Real.sin θ ^ 2)) := hcv
  have hpt : (∫ θ in Set.Ioo 0 (π / 2), |w * (2 * Real.sin θ * Real.cos θ)|
          * (rhoI (w * Real.sin θ ^ 2) * rhoK (w - w * Real.sin θ ^ 2)))
      = ∫ θ in Set.Ioo 0 (π / 2), 2 * π⁻¹ * (Real.sqrt (Hnu w θ))⁻¹ :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => nuP_pt hw hw1 hθ)
  have hle : (0 : ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hint : (∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (Hnu w θ))⁻¹)
      = ∫ θ in Set.Ioo 0 (π / 2), (Real.sqrt (Hnu w θ))⁻¹ := by
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
  rw [hcv', hpt, integral_const_mul, ← hint]

/-- `H(w, θ) ≥ 2` for `0 < w ≤ 1`. -/
theorem two_le_Hnu {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (θ : ℝ) : 2 ≤ Hnu w θ := by
  unfold Hnu
  have ha1 := Real.sin_sq_le_one θ
  have hX : 1 ≤ 2 - w * Real.sin θ ^ 2 := by nlinarith [sq_nonneg (Real.sin θ)]
  have hY : 2 ≤ 2 + w * Real.cos θ ^ 2 := by nlinarith [sq_nonneg (Real.cos θ)]
  nlinarith

/-- **The pointwise bound**: `|H^{-1/2} - 1/2 + (w/8)(cos²θ - sin²θ)| ≤ w²` for `0 < w ≤ 1`. -/
theorem abs_Hnu_inv_sqrt_sub_le {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (θ : ℝ) :
    |(Real.sqrt (Hnu w θ))⁻¹ - 1 / 2 + w / 8 * (Real.cos θ ^ 2 - Real.sin θ ^ 2)| ≤ w ^ 2 := by
  have hH2 := two_le_Hnu hw hw1 θ
  set s := Real.sqrt (Hnu w θ) with hs
  have hs2 : s ^ 2 = Hnu w θ := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsv : s * s⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  have hvi : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hv0 : 0 ≤ s⁻¹ := inv_nonneg.mpr (by linarith)
  have hsc := Real.sin_sq_add_cos_sq θ
  have hsn := sq_nonneg (Real.sin θ)
  have hcn := sq_nonneg (Real.cos θ)
  -- H = 4 + 2 w (cos² - sin²) - w² sin² cos²
  have hHexp : Hnu w θ = 4 + 2 * w * (Real.cos θ ^ 2 - Real.sin θ ^ 2)
      - w ^ 2 * (Real.sin θ ^ 2 * Real.cos θ ^ 2) := by
    unfold Hnu
    ring
  have hE : s⁻¹ - 1 / 2 + (s ^ 2 - 4) / 16 = (s - 2) ^ 2 * (s + 4) * s⁻¹ / 16 := by
    linear_combination (3 / 4 - s ^ 2 / 16) * hsv
  have hE0 : 0 ≤ (s - 2) ^ 2 * (s + 4) * s⁻¹ / 16 :=
    div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hv0) (by norm_num)
  have hq : (s + 4) * s⁻¹ ≤ (s + 2) ^ 2 := by
    have h1 : (s + 4) * s⁻¹ ≤ (s + 4) * 1 := mul_le_mul_of_nonneg_left hvi (by linarith)
    have h2 : 0 ≤ s * (s + 3) := mul_nonneg (by linarith) (by linarith)
    have e : (s + 2) ^ 2 = s * (s + 3) + (s + 4) := by ring
    linarith
  have hE1 : (s - 2) ^ 2 * (s + 4) * s⁻¹ / 16 ≤ (s ^ 2 - 4) ^ 2 / 16 := by
    have h1 : (s - 2) ^ 2 * ((s + 4) * s⁻¹) ≤ (s - 2) ^ 2 * (s + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hq (sq_nonneg _)
    have e : (s ^ 2 - 4) ^ 2 = (s - 2) ^ 2 * (s + 2) ^ 2 := by ring
    rw [e]
    have e2 : (s - 2) ^ 2 * (s + 4) * s⁻¹ = (s - 2) ^ 2 * ((s + 4) * s⁻¹) := by ring
    rw [e2]
    linarith
  -- |s² - 4| ≤ 9w/4
  have hp0 : 0 ≤ Real.sin θ ^ 2 * Real.cos θ ^ 2 := mul_nonneg hsn hcn
  have hp1 : Real.sin θ ^ 2 * Real.cos θ ^ 2 ≤ 1 / 4 := by
    have e1 : (Real.sin θ ^ 2 + Real.cos θ ^ 2) ^ 2 = 1 := by rw [hsc]; norm_num
    have e2 := sq_nonneg (Real.sin θ ^ 2 - Real.cos θ ^ 2)
    have e3 : 4 * (Real.sin θ ^ 2 * Real.cos θ ^ 2)
        = (Real.sin θ ^ 2 + Real.cos θ ^ 2) ^ 2 - (Real.sin θ ^ 2 - Real.cos θ ^ 2) ^ 2 := by ring
    linarith
  have hc2 : |Real.cos θ ^ 2 - Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hA := abs_le.mp hc2
  have hwc1 : w * (Real.cos θ ^ 2 - Real.sin θ ^ 2) ≤ w * 1 := mul_le_mul_of_nonneg_left hA.2 hw.le
  have hwc2 : w * (-1) ≤ w * (Real.cos θ ^ 2 - Real.sin θ ^ 2) := mul_le_mul_of_nonneg_left hA.1 hw.le
  have hpw : 0 ≤ w ^ 2 * (Real.sin θ ^ 2 * Real.cos θ ^ 2) := mul_nonneg (sq_nonneg w) hp0
  have hpw2 : w ^ 2 * (Real.sin θ ^ 2 * Real.cos θ ^ 2) ≤ w ^ 2 * (1 / 4) :=
    mul_le_mul_of_nonneg_left hp1 (sq_nonneg w)
  have hww : w ^ 2 ≤ w * 1 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw1 hw.le
  have hd : |s ^ 2 - 4| ≤ 9 * w / 4 := by
    rw [hs2, hHexp, abs_le]
    constructor <;> linarith
  have hd2 : (s ^ 2 - 4) ^ 2 ≤ (9 * w / 4) ^ 2 := by
    have h := abs_le.mp hd
    exact sq_le_sq' h.1 h.2
  -- the target is E + w² sin²cos²/16
  have hT : (s⁻¹ - 1 / 2 + w / 8 * (Real.cos θ ^ 2 - Real.sin θ ^ 2))
      = (s - 2) ^ 2 * (s + 4) * s⁻¹ / 16 + w ^ 2 * (Real.sin θ ^ 2 * Real.cos θ ^ 2) / 16 := by
    rw [← hE, hs2, hHexp]
    ring
  have hsq : (9 * w / 4) ^ 2 = 81 / 16 * w ^ 2 := by ring
  rw [hT, abs_le]
  constructor
  · linarith
  · linarith

/-- `∫₀^{π/2} (cos²θ - sin²θ) dθ = 0`. -/
theorem integral_cos_sq_sub_sin_sq_half_pi :
    (∫ θ in (0 : ℝ)..(π / 2), (Real.cos θ ^ 2 - Real.sin θ ^ 2)) = 0 := by
  rw [integral_cos_sq_sub_sin_sq, Real.cos_pi_div_two, Real.sin_zero]
  ring

theorem continuous_Hnu_inv_sqrt {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    Continuous (fun θ : ℝ => (Real.sqrt (Hnu w θ))⁻¹) := by
  have hc : Continuous (fun θ : ℝ => Real.sqrt (Hnu w θ)) := by
    unfold Hnu
    fun_prop
  exact hc.inv₀ (fun θ => (Real.sqrt_pos.mpr (by linarith [two_le_Hnu hw hw1 θ])).ne')

/-- **`|ν(w) - 1/2| ≤ w²`** for `0 < w ≤ 1`. -/
theorem abs_nuP_sub_half_le {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) : |nuP w - 1 / 2| ≤ w ^ 2 := by
  have hc := continuous_Hnu_inv_sqrt hw hw1
  have hcs : Continuous (fun θ : ℝ => Real.cos θ ^ 2 - Real.sin θ ^ 2) := by fun_prop
  have hF : Continuous (fun θ : ℝ =>
      (Real.sqrt (Hnu w θ))⁻¹ - 1 / 2 + w / 8 * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) := by
    have h1 : Continuous (fun θ : ℝ => (Real.sqrt (Hnu w θ))⁻¹ - 1 / 2) := hc.sub continuous_const
    exact h1.add (continuous_const.mul hcs)
  have hsplit : (∫ θ in (0 : ℝ)..(π / 2),
        ((Real.sqrt (Hnu w θ))⁻¹ - 1 / 2 + w / 8 * (Real.cos θ ^ 2 - Real.sin θ ^ 2)))
      = (∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (Hnu w θ))⁻¹) - (π / 2) * (1 / 2)
        + w / 8 * ∫ θ in (0 : ℝ)..(π / 2), (Real.cos θ ^ 2 - Real.sin θ ^ 2) := by
    have h1 : Continuous (fun θ : ℝ => (Real.sqrt (Hnu w θ))⁻¹ - 1 / 2) := hc.sub continuous_const
    have hc3 : Continuous (fun θ : ℝ => w / 8 * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) :=
      continuous_const.mul hcs
    rw [intervalIntegral.integral_add (h1.intervalIntegrable 0 (π / 2)) (hc3.intervalIntegrable 0 (π / 2)),
      intervalIntegral.integral_sub (hc.intervalIntegrable 0 (π / 2)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hbound : ‖∫ θ in (0 : ℝ)..(π / 2),
      ((Real.sqrt (Hnu w θ))⁻¹ - 1 / 2 + w / 8 * (Real.cos θ ^ 2 - Real.sin θ ^ 2))‖
      ≤ w ^ 2 * |π / 2 - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun θ _ => by rw [Real.norm_eq_abs]; exact abs_Hnu_inv_sqrt_sub_le hw hw1 θ)
  rw [hsplit, integral_cos_sq_sub_sin_sq_half_pi, Real.norm_eq_abs,
    abs_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2 - 0)] at hbound
  rw [nuP_eq_theta hw hw1]
  have hpi : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  have hpos : 0 < π⁻¹ := inv_pos.mpr Real.pi_pos
  have e : 2 * π⁻¹ * (∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (Hnu w θ))⁻¹) - 1 / 2
      = 2 * π⁻¹ * ((∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (Hnu w θ))⁻¹) - π / 2 * (1 / 2)
        + w / 8 * 0) := by
    linear_combination (1 / 2 : ℝ) * hpi
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π⁻¹)]
  have h2 : 2 * π⁻¹ * |(∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (Hnu w θ))⁻¹) - π / 2 * (1 / 2)
        + w / 8 * 0| ≤ 2 * π⁻¹ * (w ^ 2 * (π / 2 - 0)) :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  have e2 : 2 * π⁻¹ * (w ^ 2 * (π / 2 - 0)) = w ^ 2 := by
    linear_combination w ^ 2 * hpi
  linarith

end Tower.RV6
