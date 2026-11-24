import Mathlib
import Tower.RV6.BPIbp
import Tower.RV6.BPProd

/-!
# RungBP, step 3 (first half): `j(s)`, its scaling, and the kernel `k_s`

For `0 < s < 2`:

* `jS s = ∫₀^∞ (1 - J₀(y)) y^{-1-s} dy`, and `∫₀^∞ (1 - J₀(xa)) x^{-1-s} dx = a^s j(s)` for `a ≥ 0` (`jS_scale`);
* `kerS s τ t = ∫₀^∞ (1 - J₀(xτ))(1 - J₀(xt)) x^{-1-s} dx = j(s) [τ^s + t^s - M_s(τ, t)]` for `τ, t ≥ 0`
  (`kerS_eq`), with `M_s(τ, t) = ∫₀¹ |τ + t e^{2πiθ}|^s dθ` (`angM`): the product formula of `J₀`, then Fubini on
  `(0, ∞) × (0, 1]` against the majorant `min(x²(τ + t)²/4, 2) x^{-1-s}`.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

/-- `j(s) = ∫₀^∞ (1 - J₀(y)) y^{-1-s} dy`. -/
noncomputable def jS (s : ℝ) : ℝ := ∫ y in Set.Ioi (0 : ℝ), (1 - besselJ0 y) * y ^ (-1 - s)

/-- `ρ(θ) = |τ + t e^{2πiθ}|`. -/
noncomputable def rhoN (τ t θ : ℝ) : ℝ := ‖(τ : ℂ) + t * cexpR (2 * π * θ)‖

/-- `M_s(τ, t) = ∫₀¹ |τ + t e^{2πiθ}|^s dθ`. -/
noncomputable def angM (s τ t : ℝ) : ℝ := ∫ θ in Set.Ioc (0 : ℝ) 1, rhoN τ t θ ^ s

/-- `k_s(τ, t) = ∫₀^∞ (1 - J₀(xτ))(1 - J₀(xt)) x^{-1-s} dx`. -/
noncomputable def kerS (s τ t : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (1 - besselJ0 (x * τ)) * (1 - besselJ0 (x * t)) * x ^ (-1 - s)

/-! ## Integrability -/

/-- `φ(x) x^{-1-s}` is integrable on `(0, ∞)` when `|φ| ≤ A x²` on `(0, 1]`, `|φ| ≤ B` beyond, `0 < s < 2`. -/
theorem integrableOn_rpow_of_bounds {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Ioi 0)) {s A B : ℝ}
    (hs0 : 0 < s) (hs2 : s < 2)
    (h1 : ∀ x : ℝ, 0 < x → x ≤ 1 → |φ x| ≤ A * x ^ 2) (h2 : ∀ x : ℝ, 1 < x → |φ x| ≤ B) :
    IntegrableOn (fun x : ℝ => φ x * x ^ (-1 - s)) (Set.Ioi 0) := by
  have hc : ContinuousOn (fun x : ℝ => φ x * x ^ (-1 - s)) (Set.Ioi 0) :=
    hφ.mul (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx)))
  have i1 : IntegrableOn (fun x : ℝ => φ x * x ^ (-1 - s)) (Set.Ioc 0 1) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => φ x * x ^ (-1 - s))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (hc.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    have hr : IntegrableOn (fun x : ℝ => x ^ (1 - s)) (Set.Ioc (0 : ℝ) 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 1 - s)).1
    refine Integrable.mono' (hr.const_mul A) hm
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_))
    have hx0 : 0 < x := hx.1
    have hp : 0 < x ^ (-1 - s) := Real.rpow_pos_of_pos hx0 _
    have e : x ^ 2 * x ^ (-1 - s) = x ^ (1 - s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
      congr 1
      push_cast
      ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
    calc |φ x| * x ^ (-1 - s) ≤ A * x ^ 2 * x ^ (-1 - s) :=
          mul_le_mul_of_nonneg_right (h1 x hx0 hx.2) hp.le
      _ = A * x ^ (1 - s) := by rw [mul_assoc, e]
  have i2 : IntegrableOn (fun x : ℝ => φ x * x ^ (-1 - s)) (Set.Ioi 1) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => φ x * x ^ (-1 - s))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (hc.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    have hr : IntegrableOn (fun x : ℝ => x ^ (-1 - s)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine Integrable.mono' (hr.const_mul B) hm
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have hp : 0 < x ^ (-1 - s) := Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_right (h2 x hx) hp.le
  have hu : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hu]
  exact i1.union i2

theorem integrableOn_one_sub_scale {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => (1 - besselJ0 (x * a)) * x ^ (-1 - s)) (Set.Ioi 0) := by
  refine integrableOn_rpow_of_bounds (φ := fun x => 1 - besselJ0 (x * a)) ?_ hs0 hs2
    (A := a ^ 2 / 4) (B := 2) ?_ ?_
  · exact (continuous_const.sub (continuous_besselJ0.comp
      (continuous_id.mul (continuous_const : Continuous fun _ : ℝ => a)))).continuousOn
  · intro x hx _
    have h0 := one_sub_besselJ0_nonneg (mul_nonneg hx.le ha)
    have h1 := one_sub_besselJ0_le_sq (mul_nonneg hx.le ha)
    show |1 - besselJ0 (x * a)| ≤ a ^ 2 / 4 * x ^ 2
    rw [abs_of_nonneg h0]
    have e : (x * a) ^ 2 / 4 = a ^ 2 / 4 * x ^ 2 := by ring
    linarith
  · intro x hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have h0 := one_sub_besselJ0_nonneg (mul_nonneg hx0 ha)
    have h := (abs_le.mp (abs_besselJ0_le_one (mul_nonneg hx0 ha))).1
    show |1 - besselJ0 (x * a)| ≤ 2
    rw [abs_of_nonneg h0]
    linarith

/-! ## The scaling of `j` -/

/-- `∫₀^∞ (1 - J₀(xa)) x^{-1-s} dx = a^s j(s)` for `a ≥ 0`, `s > 0`. -/
theorem jS_scale {s : ℝ} (hs0 : 0 < s) {a : ℝ} (ha : 0 ≤ a) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - besselJ0 (x * a)) * x ^ (-1 - s) = a ^ s * jS s := by
  rcases ha.lt_or_eq with ha' | ha'
  · have h := integral_comp_mul_left_Ioi (fun y : ℝ => (1 - besselJ0 y) * y ^ (-1 - s)) 0 ha'
    rw [mul_zero] at h
    have e : a ^ (1 + s) * a ^ (-1 - s) = 1 := by
      rw [← Real.rpow_add ha']
      have e0 : (1 + s) + (-1 - s) = 0 := by ring
      rw [e0, Real.rpow_zero]
    have hfun : ∀ x ∈ Set.Ioi (0 : ℝ), (1 - besselJ0 (x * a)) * x ^ (-1 - s)
        = a ^ (1 + s) * ((1 - besselJ0 (a * x)) * (a * x) ^ (-1 - s)) := by
      intro x hx
      have hx0 : 0 < x := hx
      rw [Real.mul_rpow ha'.le hx0.le, mul_comm x a]
      linear_combination (-((1 - besselJ0 (a * x)) * x ^ (-1 - s))) * e
    rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul, h]
    have e2 : a ^ (1 + s) * a⁻¹ = a ^ s := by
      rw [Real.rpow_add ha', Real.rpow_one, mul_comm a, mul_assoc, mul_inv_cancel₀ ha'.ne',
        mul_one]
    rw [smul_eq_mul, ← mul_assoc, e2]
    rfl
  · subst ha'
    simp [besselJ0_zero, Real.zero_rpow hs0.ne']

/-! ## The angular radius -/

theorem norm_cexpR (y : ℝ) : ‖cexpR y‖ = 1 := Complex.norm_exp_ofReal_mul_I y

theorem rhoN_nonneg (τ t θ : ℝ) : 0 ≤ rhoN τ t θ := norm_nonneg _

theorem rhoN_le {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) (θ : ℝ) : rhoN τ t θ ≤ τ + t := by
  show ‖(τ : ℂ) + t * cexpR (2 * π * θ)‖ ≤ τ + t
  calc ‖(τ : ℂ) + t * cexpR (2 * π * θ)‖ ≤ ‖(τ : ℂ)‖ + ‖(t : ℂ) * cexpR (2 * π * θ)‖ :=
        norm_add_le _ _
    _ = τ + t := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hτ,
          Real.norm_of_nonneg ht, norm_cexpR, mul_one]

theorem continuous_rhoN (τ t : ℝ) : Continuous (rhoN τ t) := by
  have h1 : Continuous fun θ : ℝ => 2 * π * θ := continuous_const.mul continuous_id
  have h2 : Continuous fun θ : ℝ => cexpR (2 * π * θ) := continuous_cexpR.comp h1
  have h3 : Continuous fun θ : ℝ => (τ : ℂ) + t * cexpR (2 * π * θ) :=
    continuous_const.add (continuous_const.mul h2)
  exact h3.norm

theorem norm_smul_add_cexpR {x : ℝ} (hx : 0 ≤ x) (τ t y : ℝ) :
    ‖((x * τ : ℝ) : ℂ) + ((x * t : ℝ) : ℂ) * cexpR y‖ = x * ‖(τ : ℂ) + t * cexpR y‖ := by
  have e : ((x * τ : ℝ) : ℂ) + ((x * t : ℝ) : ℂ) * cexpR y = (x : ℂ) * ((τ : ℂ) + t * cexpR y) := by
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx]

/-- `J₀(xτ) J₀(xt) = ∫₀¹ J₀(x ρ(θ)) dθ` for `x, τ, t ≥ 0`. -/
theorem besselJ0_mul_scale {x : ℝ} (hx : 0 ≤ x) {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    besselJ0 (x * τ) * besselJ0 (x * t)
      = ∫ θ in Set.Ioc (0 : ℝ) 1, besselJ0 (x * rhoN τ t θ) := by
  rw [besselJ0_mul_besselJ0 (mul_nonneg hx hτ) (mul_nonneg hx ht)]
  refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
  show besselJ0 ‖((x * τ : ℝ) : ℂ) + ((x * t : ℝ) : ℂ) * cexpR (2 * π * θ)‖
    = besselJ0 (x * ‖(τ : ℂ) + t * cexpR (2 * π * θ)‖)
  rw [norm_smul_add_cexpR hx]

/-! ## The kernel -/

/-- **`k_s(τ, t) = j(s) [τ^s + t^s - M_s(τ, t)]`** for `τ, t ≥ 0` and `0 < s < 2`. -/
theorem kerS_eq {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    kerS s τ t = jS s * (τ ^ s + t ^ s - angM s τ t) := by
  have hρc := continuous_rhoN τ t
  -- the majorant
  have hgint : IntegrableOn
      (fun x : ℝ => min (x ^ 2 * (τ + t) ^ 2 / 4) 2 * x ^ (-1 - s)) (Set.Ioi 0) := by
    refine integrableOn_rpow_of_bounds (φ := fun x => min (x ^ 2 * (τ + t) ^ 2 / 4) 2) ?_ hs0 hs2
      (A := (τ + t) ^ 2 / 4) (B := 2) ?_ ?_
    · exact ((by fun_prop : Continuous fun x : ℝ => x ^ 2 * (τ + t) ^ 2 / 4).min
        continuous_const).continuousOn
    · intro x _ _
      have h0 : 0 ≤ min (x ^ 2 * (τ + t) ^ 2 / 4) 2 :=
        le_min (by positivity) (by norm_num)
      show |min (x ^ 2 * (τ + t) ^ 2 / 4) 2| ≤ (τ + t) ^ 2 / 4 * x ^ 2
      rw [abs_of_nonneg h0]
      have h1 := min_le_left (x ^ 2 * (τ + t) ^ 2 / 4) 2
      have e : x ^ 2 * (τ + t) ^ 2 / 4 = (τ + t) ^ 2 / 4 * x ^ 2 := by ring
      linarith
    · intro x _
      have h0 : 0 ≤ min (x ^ 2 * (τ + t) ^ 2 / 4) 2 :=
        le_min (by positivity) (by norm_num)
      show |min (x ^ 2 * (τ + t) ^ 2 / 4) 2| ≤ 2
      rw [abs_of_nonneg h0]
      exact min_le_right _ _
  -- the integrand on the product
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      (1 - besselJ0 (p.1 * rhoN τ t p.2)) * p.1 ^ (-1 - s)) := by
    have hc : Continuous (fun p : ℝ × ℝ => 1 - besselJ0 (p.1 * rhoN τ t p.2)) :=
      continuous_const.sub (continuous_besselJ0.comp (continuous_fst.mul (hρc.comp continuous_snd)))
    exact hc.measurable.mul (measurable_fst.pow_const (-1 - s))
  have hμ : ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).prod
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
      = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) 1) := Measure.prod_restrict _ _
  have hint : Integrable (Function.uncurry fun (x : ℝ) (θ : ℝ) =>
      (1 - besselJ0 (x * rhoN τ t θ)) * x ^ (-1 - s))
      (((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hG : Integrable (fun z : ℝ × ℝ =>
        (min (z.1 ^ 2 * (τ + t) ^ 2 / 4) 2 * z.1 ^ (-1 - s)) * (fun _ : ℝ => (1 : ℝ)) z.2)
        (((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).prod
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) :=
      Integrable.mul_prod hgint (integrable_const (1 : ℝ))
    rw [hμ] at hG ⊢
    refine Integrable.mono' hG hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioc) (fun p hp => ?_))
    have hx : 0 < p.1 := hp.1
    have hρ0 := rhoN_nonneg τ t p.2
    have hρ1 := rhoN_le hτ ht p.2
    have hxρ : 0 ≤ p.1 * rhoN τ t p.2 := mul_nonneg hx.le hρ0
    have hj0 := one_sub_besselJ0_nonneg hxρ
    have hj1 := one_sub_besselJ0_le_sq hxρ
    have hj2 : 1 - besselJ0 (p.1 * rhoN τ t p.2) ≤ 2 := by
      have h := (abs_le.mp (abs_besselJ0_le_one hxρ)).1
      linarith
    have hsq : (p.1 * rhoN τ t p.2) ^ 2 ≤ (p.1 * (τ + t)) ^ 2 :=
      pow_le_pow_left₀ hxρ (mul_le_mul_of_nonneg_left hρ1 hx.le) 2
    have hmin : 1 - besselJ0 (p.1 * rhoN τ t p.2) ≤ min (p.1 ^ 2 * (τ + t) ^ 2 / 4) 2 := by
      refine le_min ?_ hj2
      have e : (p.1 * (τ + t)) ^ 2 / 4 = p.1 ^ 2 * (τ + t) ^ 2 / 4 := by ring
      linarith
    have hp' : 0 < p.1 ^ (-1 - s) := Real.rpow_pos_of_pos hx _
    show ‖(1 - besselJ0 (p.1 * rhoN τ t p.2)) * p.1 ^ (-1 - s)‖
      ≤ min (p.1 ^ 2 * (τ + t) ^ 2 / 4) 2 * p.1 ^ (-1 - s) * 1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hj0, abs_of_pos hp', mul_one]
    exact mul_le_mul_of_nonneg_right hmin hp'.le
  have hsw : ∫ x in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioc (0 : ℝ) 1,
        (1 - besselJ0 (x * rhoN τ t θ)) * x ^ (-1 - s)
      = ∫ θ in Set.Ioc (0 : ℝ) 1, ∫ x in Set.Ioi (0 : ℝ),
        (1 - besselJ0 (x * rhoN τ t θ)) * x ^ (-1 - s) :=
    integral_integral_swap hint
  have iC : IntegrableOn (fun x : ℝ => ∫ θ in Set.Ioc (0 : ℝ) 1,
      (1 - besselJ0 (x * rhoN τ t θ)) * x ^ (-1 - s)) (Set.Ioi 0) :=
    hint.integral_prod_left
  have iA := integrableOn_one_sub_scale hs0 hs2 hτ
  have iB := integrableOn_one_sub_scale hs0 hs2 ht
  -- the inner angular integral at fixed `x`
  have hC : ∀ x ∈ Set.Ioi (0 : ℝ),
      (1 - besselJ0 (x * τ)) * (1 - besselJ0 (x * t)) * x ^ (-1 - s)
        = ((1 - besselJ0 (x * τ)) * x ^ (-1 - s) + (1 - besselJ0 (x * t)) * x ^ (-1 - s))
          - ∫ θ in Set.Ioc (0 : ℝ) 1, (1 - besselJ0 (x * rhoN τ t θ)) * x ^ (-1 - s) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hcJ : Continuous fun θ : ℝ => besselJ0 (x * rhoN τ t θ) :=
      continuous_besselJ0.comp ((continuous_const : Continuous fun _ : ℝ => x).mul hρc)
    have i1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
      continuous_const.integrableOn_Ioc
    have i2 : IntegrableOn (fun θ : ℝ => besselJ0 (x * rhoN τ t θ)) (Set.Ioc (0 : ℝ) 1) :=
      hcJ.integrableOn_Ioc
    have h1 : ∫ θ in Set.Ioc (0 : ℝ) 1, (1 - besselJ0 (x * rhoN τ t θ)) * x ^ (-1 - s)
        = (1 - besselJ0 (x * τ) * besselJ0 (x * t)) * x ^ (-1 - s) := by
      rw [integral_mul_const, integral_sub i1 i2, besselJ0_mul_scale hx0 hτ ht]
      congr 2
      rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const]
      norm_num
    rw [h1]
    ring
  have hfun : (fun θ : ℝ => ∫ x in Set.Ioi (0 : ℝ),
      (1 - besselJ0 (x * rhoN τ t θ)) * x ^ (-1 - s))
      = fun θ : ℝ => rhoN τ t θ ^ s * jS s :=
    funext (fun θ => jS_scale hs0 (rhoN_nonneg τ t θ))
  unfold kerS
  have iAB : IntegrableOn (fun x : ℝ => (1 - besselJ0 (x * τ)) * x ^ (-1 - s)
      + (1 - besselJ0 (x * t)) * x ^ (-1 - s)) (Set.Ioi 0) := iA.add iB
  rw [setIntegral_congr_fun measurableSet_Ioi hC, integral_sub iAB iC,
    integral_add iA iB, jS_scale hs0 hτ, jS_scale hs0 ht, hsw, hfun, integral_mul_const]
  unfold angM
  ring

end Tower.RV6
