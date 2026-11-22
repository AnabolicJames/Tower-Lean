import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselI
import Tower.RV6.BesselJ

/-!
# The Laplace transform of `J₀`

`lapl φ δ = ∫₀^∞ e^{-δt} φ(t) dt`.

* `integrable_lapl`, `hasDerivAt_lapl`, `abs_lapl_le`, `lapl_ibp` (integration by parts),
  `lapl_one`.
* For `a ≥ 0`, `δ > 0`, with `L = lapl (J₀(a ·))` and `N = lapl (a J₁(a ·))`:
  `lapl_J1_eq : N = 1 - δ L`, `lapl_J_second : a² lapl (t J₀(at)) = δ lapl (t a J₁(at))`,
  `lapl_J_ode : (a² + δ²) lapl (t J₀(at)) = δ L`, i.e. `(a² + δ²) L' = -δ L`.
* `laplS_eq_one : (a² + δ²) L(δ)² = 1`, `lapl_besselJ0_pos`, and
  **`lapl_besselJ0 : ∫₀^∞ e^{-δt} J₀(at) dt = 1/√(a² + δ²)`**.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## Two elementary bounds -/

/-- `t e^{-ct} ≤ (2/c) e^{-(c/2)t}`. -/
theorem mul_exp_neg_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    t * Real.exp (-c * t) ≤ 2 / c * Real.exp (-(c / 2) * t) := by
  have h1 := Real.add_one_le_exp (c / 2 * t)
  have h2 : t ≤ 2 / c * Real.exp (c / 2 * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  have h5 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-c * t)).le
  have e : Real.exp (c / 2 * t) * Real.exp (-c * t) = Real.exp (-(c / 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc t * Real.exp (-c * t) ≤ 2 / c * Real.exp (c / 2 * t) * Real.exp (-c * t) := h5
    _ = 2 / c * (Real.exp (c / 2 * t) * Real.exp (-c * t)) := by ring
    _ = 2 / c * Real.exp (-(c / 2) * t) := by rw [e]

/-- `(1 + t) e^{-ct} ≤ (1 + 2/c) e^{-(c/2)t}` for `t ≥ 0`. -/
theorem one_add_mul_exp_neg_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) * Real.exp (-c * t) ≤ (1 + 2 / c) * Real.exp (-(c / 2) * t) := by
  have h1 := mul_exp_neg_le hc t
  have hct := mul_nonneg hc.le ht
  have h2 : Real.exp (-c * t) ≤ Real.exp (-(c / 2) * t) :=
    Real.exp_le_exp.mpr (by linarith)
  calc (1 + t) * Real.exp (-c * t) = Real.exp (-c * t) + t * Real.exp (-c * t) := by ring
    _ ≤ Real.exp (-(c / 2) * t) + 2 / c * Real.exp (-(c / 2) * t) := add_le_add h2 h1
    _ = (1 + 2 / c) * Real.exp (-(c / 2) * t) := by ring

/-- For every `ε > 0` there is `y ≥ max 1 δ` with `K/y ≤ ε`. -/
theorem exists_large {δ K ε : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ y : ℝ, 1 ≤ y ∧ δ ≤ y ∧ K * (1 / y) ≤ ε := by
  have hd := div_nonneg hK hε.le
  refine ⟨δ + 1 + K / ε, by linarith, by linarith, ?_⟩
  have hy0 : 0 < δ + 1 + K / ε := by linarith
  have h4 : ε * (K / ε) = K := mul_div_cancel₀ K hε.ne'
  have h5 : 0 ≤ ε * δ := (mul_pos hε hδ).le
  have e : ε * (δ + 1 + K / ε) = ε * δ + ε + ε * (K / ε) := by ring
  rw [mul_one_div, div_le_iff₀ hy0, e, h4]
  linarith

/-! ## The Laplace transform -/

/-- `lapl φ δ = ∫₀^∞ e^{-δt} φ(t) dt`. -/
noncomputable def lapl (φ : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-δ * t) * φ t

theorem continuous_exp_neg_mul (x : ℝ) : Continuous fun t : ℝ => Real.exp (-x * t) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_id')

theorem integrable_lapl {φ : ℝ → ℝ} {C δ : ℝ} (hφ : Continuous φ)
    (hb : ∀ t : ℝ, 0 < t → |φ t| ≤ C * (1 + t)) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => Real.exp (-δ * t) * φ t) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hC : 0 ≤ C := by
    have h := le_trans (abs_nonneg _) (hb 1 one_pos)
    linarith
  have hmaj0 : IntegrableOn (fun t : ℝ => Real.exp (-(δ / 2) * t)) (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 (half_pos hδ)
  have hmaj : Integrable (fun t : ℝ => C * (1 + 2 / δ) * Real.exp (-(δ / 2) * t))
      (volume.restrict (Set.Ioi (0 : ℝ))) := Integrable.const_mul hmaj0 (C * (1 + 2 / δ))
  refine hmaj.mono' ((continuous_exp_neg_mul δ).mul hφ).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
  have ht0 : (0 : ℝ) < t := ht
  have h1 := hb t ht0
  have h2 := one_add_mul_exp_neg_le hδ ht0.le
  have hE := Real.exp_pos (-δ * t)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE]
  calc Real.exp (-δ * t) * |φ t| ≤ Real.exp (-δ * t) * (C * (1 + t)) :=
        mul_le_mul_of_nonneg_left h1 hE.le
    _ = C * ((1 + t) * Real.exp (-δ * t)) := by ring
    _ ≤ C * ((1 + 2 / δ) * Real.exp (-(δ / 2) * t)) := mul_le_mul_of_nonneg_left h2 hC
    _ = C * (1 + 2 / δ) * Real.exp (-(δ / 2) * t) := by ring

theorem integrable_one_lapl {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => Real.exp (-δ * t) * 1) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hb : ∀ t : ℝ, 0 < t → |(fun _ : ℝ => (1 : ℝ)) t| ≤ 1 * (1 + t) := by
    intro t ht
    show |(1 : ℝ)| ≤ 1 * (1 + t)
    rw [abs_one]
    linarith
  have h := integrable_lapl (φ := fun _ : ℝ => (1 : ℝ)) (C := 1) continuous_const hb hδ
  exact h

/-- Integration by parts: `lapl φ' δ = δ lapl φ δ - φ(0)`. -/
theorem lapl_ibp {φ φ' : ℝ → ℝ} {C δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ t : ℝ, HasDerivAt φ (φ' t) t) (hφ' : Continuous φ')
    (hb : ∀ t : ℝ, 0 < t → |φ t| ≤ C * (1 + t))
    (hb' : ∀ t : ℝ, 0 < t → |φ' t| ≤ C * (1 + t)) :
    lapl φ' δ = δ * lapl φ δ - φ 0 := by
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hC : 0 ≤ C := by
    have h := le_trans (abs_nonneg _) (hb 1 one_pos)
    linarith
  have i1 := integrable_lapl hφ hb hδ
  have i2 := integrable_lapl hφ' hb' hδ
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => Real.exp (-δ * y) * φ y)
        (Real.exp (-δ * t) * φ' t - δ * (Real.exp (-δ * t) * φ t)) t := by
    intro t _
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-δ * y)) (Real.exp (-δ * t) * (-δ * 1)) t :=
      ((hasDerivAt_id' t).const_mul (-δ)).exp
    have h2 := h1.mul (hd t)
    have h2' : HasDerivAt (fun y : ℝ => Real.exp (-δ * y) * φ y)
        (Real.exp (-δ * t) * (-δ * 1) * φ t + Real.exp (-δ * t) * φ' t) t := h2
    exact h2'.congr_deriv (by ring)
  have hint : IntegrableOn
      (fun t : ℝ => Real.exp (-δ * t) * φ' t - δ * (Real.exp (-δ * t) * φ t))
      (Set.Ioi (0 : ℝ)) := i2.sub (i1.const_mul δ)
  have hlim : Filter.Tendsto (fun y : ℝ => Real.exp (-δ * y) * φ y) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun y : ℝ => Real.exp (-(δ / 2 * y))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((Filter.tendsto_const_mul_atTop_of_pos (half_pos hδ)).mpr Filter.tendsto_id)
    have hg := h0.const_mul (C * (1 + 2 / δ))
    rw [mul_zero] at hg
    refine squeeze_zero_norm' ((Filter.eventually_gt_atTop (0 : ℝ)).mono (fun y hy => ?_)) hg
    show ‖Real.exp (-δ * y) * φ y‖ ≤ C * (1 + 2 / δ) * Real.exp (-(δ / 2 * y))
    have h1 := hb y hy
    have h2 := one_add_mul_exp_neg_le hδ hy.le
    have hE := Real.exp_pos (-δ * y)
    have e : -(δ / 2 * y) = -(δ / 2) * y := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE, e]
    calc Real.exp (-δ * y) * |φ y| ≤ Real.exp (-δ * y) * (C * (1 + y)) :=
          mul_le_mul_of_nonneg_left h1 hE.le
      _ = C * ((1 + y) * Real.exp (-δ * y)) := by ring
      _ ≤ C * ((1 + 2 / δ) * Real.exp (-(δ / 2) * y)) := mul_le_mul_of_nonneg_left h2 hC
      _ = C * (1 + 2 / δ) * Real.exp (-(δ / 2) * y) := by ring
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [integral_sub i2 (i1.const_mul δ), integral_const_mul] at hftc
  simp only [mul_zero, Real.exp_zero, one_mul, zero_sub] at hftc
  unfold lapl
  linarith

theorem lapl_one {δ : ℝ} (hδ : 0 < δ) : lapl (fun _ : ℝ => (1 : ℝ)) δ = 1 / δ := by
  have hb : ∀ t : ℝ, 0 < t → |(fun _ : ℝ => (1 : ℝ)) t| ≤ 1 * (1 + t) := by
    intro t ht
    show |(1 : ℝ)| ≤ 1 * (1 + t)
    rw [abs_one]
    linarith
  have hb' : ∀ t : ℝ, 0 < t → |(fun _ : ℝ => (0 : ℝ)) t| ≤ 1 * (1 + t) := by
    intro t ht
    show |(0 : ℝ)| ≤ 1 * (1 + t)
    rw [abs_zero]
    linarith
  have h := lapl_ibp (φ := fun _ : ℝ => (1 : ℝ)) (φ' := fun _ : ℝ => (0 : ℝ)) (C := 1) hδ
    (fun t => hasDerivAt_const t (1 : ℝ)) continuous_const hb hb'
  have h' : lapl (fun _ : ℝ => (0 : ℝ)) δ = δ * lapl (fun _ : ℝ => (1 : ℝ)) δ - 1 := h
  have h0 : lapl (fun _ : ℝ => (0 : ℝ)) δ = 0 := by
    unfold lapl
    simp
  rw [h0] at h'
  rw [eq_div_iff hδ.ne']
  linarith

theorem lapl_const_mul (c : ℝ) (ψ : ℝ → ℝ) (δ : ℝ) :
    lapl (fun t => c * ψ t) δ = c * lapl ψ δ := by
  unfold lapl
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  show Real.exp (-δ * t) * (c * ψ t) = c * (Real.exp (-δ * t) * ψ t)
  ring

theorem lapl_neg (ψ : ℝ → ℝ) (δ : ℝ) : lapl (fun t => -ψ t) δ = -lapl ψ δ := by
  unfold lapl
  rw [← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  show Real.exp (-δ * t) * -ψ t = -(Real.exp (-δ * t) * ψ t)
  ring

/-- `|lapl φ δ| ≤ C/δ` when `|φ| ≤ C` on `(0, ∞)`. -/
theorem abs_lapl_le {φ : ℝ → ℝ} {C δ : ℝ} (hb : ∀ t : ℝ, 0 < t → |φ t| ≤ C) (hδ : 0 < δ) :
    |lapl φ δ| ≤ C / δ := by
  have hg : Integrable (fun t : ℝ => C * (Real.exp (-δ * t) * 1))
      (volume.restrict (Set.Ioi (0 : ℝ))) := Integrable.const_mul (integrable_one_lapl hδ) C
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Real.exp (-δ * t) * φ t‖ ≤ C * (Real.exp (-δ * t) * 1) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hE := Real.exp_pos (-δ * t)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE, mul_one, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hb t ht0) hE.le
  have h := norm_integral_le_of_norm_le hg hae
  rw [integral_const_mul, Real.norm_eq_abs] at h
  have h1 : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-δ * t) * 1) = 1 / δ := lapl_one hδ
  rw [h1] at h
  have e : C * (1 / δ) = C / δ := by ring
  rw [e] at h
  exact h

/-- Differentiation under the integral sign: `(lapl φ)' = -lapl (t φ(t))`. -/
theorem hasDerivAt_lapl {φ : ℝ → ℝ} {C δ : ℝ} (hφ : Continuous φ)
    (hb : ∀ t : ℝ, 0 < t → |φ t| ≤ C) (hδ : 0 < δ) :
    HasDerivAt (lapl φ) (-lapl (fun t => t * φ t) δ) δ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 1 one_pos)
  have hb1 : ∀ t : ℝ, 0 < t → |φ t| ≤ C * (1 + t) := by
    intro t ht
    have h := hb t ht
    have h2 : C ≤ C * (1 + t) := le_mul_of_one_le_right hC (by linarith)
    linarith
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hs : Set.Ioi (δ / 2) ∈ nhds δ := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun t : ℝ => Real.exp (-x * t) * φ t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun x => ((continuous_exp_neg_mul x).mul hφ).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => -(Real.exp (-δ * t) * (t * φ t)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (((continuous_exp_neg_mul δ).mul (continuous_id'.mul hφ)).neg).aestronglyMeasurable
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ x ∈ Set.Ioi (δ / 2),
      ‖-(Real.exp (-x * t) * (t * φ t))‖
        ≤ C * (2 / (δ / 2) * Real.exp (-(δ / 2 / 2) * t)) := by
    intro t ht x hx
    have ht0 : (0 : ℝ) < t := ht
    have hx' : δ / 2 < x := hx
    have hE := Real.exp_pos (-x * t)
    have hxt := mul_le_mul_of_nonneg_right hx'.le ht0.le
    have hE2 : Real.exp (-x * t) ≤ Real.exp (-(δ / 2) * t) :=
      Real.exp_le_exp.mpr (by linarith)
    have hM := mul_exp_neg_le hδ2 t
    rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul t (φ t), abs_of_pos hE, abs_of_pos ht0]
    calc Real.exp (-x * t) * (t * |φ t|)
        ≤ Real.exp (-(δ / 2) * t) * (t * C) :=
          mul_le_mul hE2 (mul_le_mul_of_nonneg_left (hb t ht0) ht0.le)
            (mul_nonneg ht0.le (abs_nonneg _)) (Real.exp_pos _).le
      _ = C * (t * Real.exp (-(δ / 2) * t)) := by ring
      _ ≤ C * (2 / (δ / 2) * Real.exp (-(δ / 2 / 2) * t)) :=
          mul_le_mul_of_nonneg_left hM hC
  have hdiff : ∀ t : ℝ, ∀ x ∈ Set.Ioi (δ / 2),
      HasDerivAt (fun y : ℝ => Real.exp (-y * t) * φ t)
        (-(Real.exp (-x * t) * (t * φ t))) x := by
    intro t x _
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y * t))
        (Real.exp (-x * t) * (-1 * t)) x :=
      (((hasDerivAt_id' x).neg).mul_const t).exp
    have h2 := h1.mul_const (φ t)
    exact h2.congr_deriv (by ring)
  have hbi : Integrable (fun t : ℝ => C * (2 / (δ / 2) * Real.exp (-(δ / 2 / 2) * t)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.const_mul
      (Integrable.const_mul (exp_neg_integrableOn_Ioi 0 (half_pos hδ2)) (2 / (δ / 2))) C
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun x t => Real.exp (-x * t) * φ t)
    (F' := fun x t => -(Real.exp (-x * t) * (t * φ t)))
    (bound := fun t => C * (2 / (δ / 2) * Real.exp (-(δ / 2 / 2) * t))) hs
    (Filter.Eventually.of_forall hmeas) (integrable_lapl hφ hb1 hδ) hmeas'
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound) hbi
    (Filter.Eventually.of_forall hdiff)
  have h3 : HasDerivAt (fun x : ℝ => ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * t) * φ t)
      (∫ t in Set.Ioi (0 : ℝ), -(Real.exp (-δ * t) * (t * φ t))) δ := key.2
  rw [integral_neg] at h3
  exact h3

/-! ## `J₀(at)` and `a J₁(at)` -/

theorem hasDerivAt_besselJ0_comp (a t : ℝ) :
    HasDerivAt (fun y : ℝ => besselJ0 (a * y)) (-(a * besselJ1 (a * t))) t := by
  have h := (hasDerivAt_besselJ0 (a * t)).comp t ((hasDerivAt_id' t).const_mul a)
  have h' : HasDerivAt (fun y : ℝ => besselJ0 (a * y)) (-besselJ1 (a * t) * (a * 1)) t := h
  exact h'.congr_deriv (by ring)

theorem hasDerivAt_mul_besselJ1_comp (a t : ℝ) :
    HasDerivAt (fun y : ℝ => y * (a * besselJ1 (a * y)))
      (a * a * (t * besselJ0 (a * t))) t := by
  have h := (hasDerivAt_mul_besselJ1 (a * t)).comp t ((hasDerivAt_id' t).const_mul a)
  have h' : HasDerivAt (fun y : ℝ => a * y * besselJ1 (a * y))
      (a * t * besselJ0 (a * t) * (a * 1)) t := h
  have hfun : (fun y : ℝ => y * (a * besselJ1 (a * y)))
      = fun y : ℝ => a * y * besselJ1 (a * y) := by
    funext y
    ring
  rw [hfun]
  exact h'.congr_deriv (by ring)

theorem continuous_besselJ0_comp (a : ℝ) : Continuous fun t : ℝ => besselJ0 (a * t) :=
  continuous_besselJ0.comp (continuous_const.mul continuous_id')

theorem continuous_besselJ1_comp (a : ℝ) : Continuous fun t : ℝ => a * besselJ1 (a * t) :=
  continuous_const.mul (continuous_besselJ1.comp (continuous_const.mul continuous_id'))

theorem abs_besselJ0_comp_le {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    |besselJ0 (a * t)| ≤ 1 :=
  abs_besselJ0_le_one (mul_nonneg ha ht.le)

theorem abs_besselJ1_comp_le {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    |a * besselJ1 (a * t)| ≤ a := by
  have h := abs_besselJ1_le_one (mul_nonneg ha ht.le)
  rw [abs_mul, abs_of_nonneg ha]
  calc a * |besselJ1 (a * t)| ≤ a * 1 := mul_le_mul_of_nonneg_left h ha
    _ = a := mul_one a

/-- `N(δ) = 1 - δ L(δ)`. -/
theorem lapl_J1_eq {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    lapl (fun t => a * besselJ1 (a * t)) δ
      = 1 - δ * lapl (fun t => besselJ0 (a * t)) δ := by
  have hb0 : ∀ t : ℝ, 0 < t → |besselJ0 (a * t)| ≤ (1 + a) * (1 + t) := by
    intro t ht
    have h := abs_besselJ0_comp_le ha ht
    have h2 : 0 ≤ a * t := mul_nonneg ha ht.le
    have e : (1 + a) * (1 + t) = 1 + t + a + a * t := by ring
    rw [e]
    linarith
  have hb1 : ∀ t : ℝ, 0 < t → |-(a * besselJ1 (a * t))| ≤ (1 + a) * (1 + t) := by
    intro t ht
    have h := abs_besselJ1_comp_le ha ht
    have h2 : 0 ≤ a * t := mul_nonneg ha ht.le
    have e : (1 + a) * (1 + t) = 1 + t + a + a * t := by ring
    rw [abs_neg, e]
    linarith
  have h := lapl_ibp (C := 1 + a) hδ (fun t => hasDerivAt_besselJ0_comp a t)
    (continuous_besselJ1_comp a).neg hb0 hb1
  have h' : lapl (fun t => -(a * besselJ1 (a * t))) δ
      = δ * lapl (fun t => besselJ0 (a * t)) δ - besselJ0 (a * 0) := h
  have e : lapl (fun t => -(a * besselJ1 (a * t))) δ
      = -lapl (fun t => a * besselJ1 (a * t)) δ := lapl_neg _ _
  rw [e, mul_zero, besselJ0_zero] at h'
  linarith

/-- `a² lapl (t J₀(at)) = δ lapl (t a J₁(at))`. -/
theorem lapl_J_second {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    a * a * lapl (fun t => t * besselJ0 (a * t)) δ
      = δ * lapl (fun t => t * (a * besselJ1 (a * t))) δ := by
  have haa : 0 ≤ a * a := mul_nonneg ha ha
  have hb0 : ∀ t : ℝ, 0 < t → |t * (a * besselJ1 (a * t))| ≤ (a + a * a) * (1 + t) := by
    intro t ht
    have h := abs_besselJ1_comp_le ha ht
    have h1 := mul_le_mul_of_nonneg_left h ht.le
    have h2 : 0 ≤ a + a * a + a * a * t := add_nonneg (add_nonneg ha haa) (mul_nonneg haa ht.le)
    have e : (a + a * a) * (1 + t) = t * a + (a + a * a + a * a * t) := by ring
    rw [abs_mul, abs_of_pos ht, e]
    linarith
  have hb1 : ∀ t : ℝ, 0 < t → |a * a * (t * besselJ0 (a * t))| ≤ (a + a * a) * (1 + t) := by
    intro t ht
    have h := abs_besselJ0_comp_le ha ht
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h ht.le) haa
    have h2 : 0 ≤ a + a * t + a * a := add_nonneg (add_nonneg ha (mul_nonneg ha ht.le)) haa
    have e : (a + a * a) * (1 + t) = a * a * (t * 1) + (a + a * t + a * a) := by ring
    rw [abs_mul, abs_mul t (besselJ0 (a * t)), abs_of_nonneg haa, abs_of_pos ht, e]
    linarith
  have hc : Continuous fun t : ℝ => a * a * (t * besselJ0 (a * t)) :=
    continuous_const.mul (continuous_id'.mul (continuous_besselJ0_comp a))
  have h := lapl_ibp (C := a + a * a) hδ (fun t => hasDerivAt_mul_besselJ1_comp a t) hc hb0 hb1
  have h' : lapl (fun t => a * a * (t * besselJ0 (a * t))) δ
      = δ * lapl (fun t => t * (a * besselJ1 (a * t))) δ - 0 * (a * besselJ1 (a * 0)) := h
  have e : lapl (fun t => a * a * (t * besselJ0 (a * t))) δ
      = a * a * lapl (fun t => t * besselJ0 (a * t)) δ := lapl_const_mul _ _ _
  rw [e, zero_mul, sub_zero] at h'
  exact h'

/-- `(a² + δ²) lapl (t J₀(at)) = δ lapl (J₀(at))`: the equation `(a² + δ²) L' = -δ L`. -/
theorem lapl_J_ode {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    (a * a + δ * δ) * lapl (fun t => t * besselJ0 (a * t)) δ
      = δ * lapl (fun t => besselJ0 (a * t)) δ := by
  have hL : HasDerivAt (lapl (fun t => besselJ0 (a * t)))
      (-lapl (fun t => t * besselJ0 (a * t)) δ) δ :=
    hasDerivAt_lapl (C := 1) (continuous_besselJ0_comp a)
      (fun t ht => abs_besselJ0_comp_le ha ht) hδ
  have hN : HasDerivAt (lapl (fun t => a * besselJ1 (a * t)))
      (-lapl (fun t => t * (a * besselJ1 (a * t))) δ) δ :=
    hasDerivAt_lapl (C := a) (continuous_besselJ1_comp a)
      (fun t ht => abs_besselJ1_comp_le ha ht) hδ
  have hEq : (lapl (fun t => a * besselJ1 (a * t)))
      =ᶠ[nhds δ] fun x : ℝ => 1 - x * lapl (fun t => besselJ0 (a * t)) x := by
    filter_upwards [Ioi_mem_nhds hδ] with x hx
    exact lapl_J1_eq ha hx
  have hd1 : HasDerivAt (fun x : ℝ => 1 - x * lapl (fun t => besselJ0 (a * t)) x)
      (-(1 * lapl (fun t => besselJ0 (a * t)) δ
        + δ * -lapl (fun t => t * besselJ0 (a * t)) δ)) δ :=
    ((hasDerivAt_id' δ).mul hL).const_sub 1
  have hd2 := hd1.congr_of_eventuallyEq hEq
  have hu := hN.unique hd2
  have h2 := lapl_J_second ha hδ
  linear_combination h2 - δ * hu

/-! ## `(a² + δ²) L(δ)² = 1` -/

/-- `S(x) = (a² + x²) L(x)²`. -/
noncomputable def laplS (a x : ℝ) : ℝ :=
  (a * a + x * x)
    * (lapl (fun t => besselJ0 (a * t)) x * lapl (fun t => besselJ0 (a * t)) x)

theorem hasDerivAt_laplS {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    HasDerivAt (laplS a) 0 δ := by
  have hL : HasDerivAt (lapl (fun t => besselJ0 (a * t)))
      (-lapl (fun t => t * besselJ0 (a * t)) δ) δ :=
    hasDerivAt_lapl (C := 1) (continuous_besselJ0_comp a)
      (fun t ht => abs_besselJ0_comp_le ha ht) hδ
  have hq : HasDerivAt (fun x : ℝ => a * a + x * x) (1 * δ + δ * 1) δ :=
    ((hasDerivAt_id' δ).mul (hasDerivAt_id' δ)).const_add (a * a)
  have h := hq.mul (hL.mul hL)
  have h' : HasDerivAt (fun x : ℝ => (a * a + x * x)
        * (lapl (fun t => besselJ0 (a * t)) x * lapl (fun t => besselJ0 (a * t)) x))
      ((1 * δ + δ * 1)
          * (lapl (fun t => besselJ0 (a * t)) δ * lapl (fun t => besselJ0 (a * t)) δ)
        + (a * a + δ * δ)
          * (-lapl (fun t => t * besselJ0 (a * t)) δ * lapl (fun t => besselJ0 (a * t)) δ
            + lapl (fun t => besselJ0 (a * t)) δ
              * -lapl (fun t => t * besselJ0 (a * t)) δ)) δ := h
  have hode := lapl_J_ode ha hδ
  have hfun : laplS a = fun x : ℝ => (a * a + x * x)
        * (lapl (fun t => besselJ0 (a * t)) x * lapl (fun t => besselJ0 (a * t)) x) := rfl
  rw [hfun]
  refine h'.congr_deriv ?_
  linear_combination (-2 * lapl (fun t => besselJ0 (a * t)) δ) * hode

theorem laplS_const {a : ℝ} (ha : 0 ≤ a) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    laplS a y = laplS a x := by
  have hcont : ContinuousOn (laplS a) (Set.Icc x y) := fun z hz =>
    (hasDerivAt_laplS ha (lt_of_lt_of_le hx hz.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ z ∈ Set.Ico x y, HasDerivWithinAt (laplS a) 0 (Set.Ici z) z := fun z hz =>
    (hasDerivAt_laplS ha (lt_of_lt_of_le hx hz.1)).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hcont hderiv y ⟨hxy, le_rfl⟩

/-- The estimate behind `S(y) → 1`. -/
theorem laplS_aux {a y l n ε : ℝ} (ha : 0 ≤ a) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hl : |l| ≤ ε) (hn : |n| ≤ a * ε) (hrel : n = 1 - y * l) :
    |(a * a + y * y) * (l * l) - 1| ≤ (2 * (a * a) + 2 * a) * ε := by
  have hyl : y * l = 1 - n := by linarith
  have eS : (a * a + y * y) * (l * l) - 1 = a * a * (l * l) - 2 * n + n * n := by
    linear_combination (y * l + (1 - n)) * hyl
  have hll : l * l ≤ ε * ε := by
    rw [← abs_mul_abs_self l]
    exact mul_le_mul hl hl (abs_nonneg l) hε0.le
  have hnn : n * n ≤ a * ε * (a * ε) := by
    rw [← abs_mul_abs_self n]
    exact mul_le_mul hn hn (abs_nonneg n) (mul_nonneg ha hε0.le)
  have hεε : ε * ε ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 hε0.le
  have haa : 0 ≤ a * a := mul_nonneg ha ha
  have p1 : a * a * (l * l) ≤ a * a * (ε * ε) := mul_le_mul_of_nonneg_left hll haa
  have p2 : a * a * (ε * ε) ≤ a * a * (ε * 1) := mul_le_mul_of_nonneg_left hεε haa
  have p4 : a * ε * (a * ε) = a * a * (ε * ε) := by ring
  have p5 : 0 ≤ a * a * (l * l) := mul_nonneg haa (mul_self_nonneg l)
  have p6 : 0 ≤ n * n := mul_self_nonneg n
  have p7 : 0 ≤ a * a * (ε * 1) := mul_nonneg haa (mul_nonneg hε0.le zero_le_one)
  have hn2 := abs_le.mp hn
  have hn3 := hn2.1
  have hn4 := hn2.2
  rw [eS, abs_le]
  constructor
  · linarith
  · linarith

theorem abs_laplS_sub_one_le {a : ℝ} (ha : 0 ≤ a) {y : ℝ} (hy : 1 ≤ y) :
    |laplS a y - 1| ≤ (2 * (a * a) + 2 * a) * (1 / y) := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have hl := abs_lapl_le (φ := fun t => besselJ0 (a * t)) (C := 1)
    (fun t ht => abs_besselJ0_comp_le ha ht) hy0
  have hn := abs_lapl_le (φ := fun t => a * besselJ1 (a * t)) (C := a)
    (fun t ht => abs_besselJ1_comp_le ha ht) hy0
  have hn' : |lapl (fun t => a * besselJ1 (a * t)) y| ≤ a * (1 / y) := by
    rw [mul_one_div]
    exact hn
  have hε0 : 0 < 1 / y := one_div_pos.mpr hy0
  have hε1 : 1 / y ≤ 1 := by
    rw [div_le_iff₀ hy0]
    linarith
  exact laplS_aux ha hε0 hε1 hl hn' (lapl_J1_eq ha hy0)

theorem laplS_eq_one {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) : laplS a δ = 1 := by
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  rw [Real.dist_eq]
  have hK : 0 ≤ 2 * (a * a) + 2 * a :=
    add_nonneg (mul_nonneg zero_le_two (mul_nonneg ha ha)) (mul_nonneg zero_le_two ha)
  obtain ⟨y, hy1, hδy, hKy⟩ := exists_large hδ hK hε
  have hc := laplS_const ha hδ hδy
  have hb := abs_laplS_sub_one_le ha hy1
  rw [hc] at hb
  exact le_trans hb hKy

/-! ## The sign, and the formula -/

theorem lapl_besselJ0_pos {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    0 < lapl (fun t => besselJ0 (a * t)) δ := by
  by_contra hcon
  push_neg at hcon
  have hy : δ ≤ δ + a + 1 := by linarith
  have hy0 : 0 < δ + a + 1 := by linarith
  have hrel := lapl_J1_eq ha hy0
  have hn := abs_lapl_le (φ := fun t => a * besselJ1 (a * t)) (C := a)
    (fun t ht => abs_besselJ1_comp_le ha ht) hy0
  have hn1 := (abs_le.mp hn).2
  have h2 : a / (δ + a + 1) < 1 := by
    rw [div_lt_one hy0]
    linarith
  have h3 : 0 < (δ + a + 1) * lapl (fun t => besselJ0 (a * t)) (δ + a + 1) := by linarith
  have hLy : 0 < lapl (fun t => besselJ0 (a * t)) (δ + a + 1) :=
    (mul_pos_iff_of_pos_left hy0).mp h3
  have hcont : ContinuousOn (lapl (fun t => besselJ0 (a * t))) (Set.Icc δ (δ + a + 1)) :=
    fun z hz =>
      (hasDerivAt_lapl (C := 1) (continuous_besselJ0_comp a)
        (fun t ht => abs_besselJ0_comp_le ha ht)
        (lt_of_lt_of_le hδ hz.1)).continuousAt.continuousWithinAt
  have hivt := intermediate_value_Icc hy hcont
  have hmem : (0 : ℝ) ∈ Set.Icc (lapl (fun t => besselJ0 (a * t)) δ)
      (lapl (fun t => besselJ0 (a * t)) (δ + a + 1)) := ⟨hcon, hLy.le⟩
  obtain ⟨c, hc, hc0⟩ := hivt hmem
  have hS := laplS_eq_one ha (lt_of_lt_of_le hδ hc.1)
  unfold laplS at hS
  rw [hc0, mul_zero, mul_zero] at hS
  exact zero_ne_one hS

/-- **The Laplace transform of `J₀`.** `∫₀^∞ e^{-δt} J₀(at) dt = 1/√(a² + δ²)` for `a ≥ 0`,
`δ > 0`. -/
theorem lapl_besselJ0 {a : ℝ} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    lapl (fun t => besselJ0 (a * t)) δ = (Real.sqrt (a * a + δ * δ))⁻¹ := by
  have hpos := lapl_besselJ0_pos ha hδ
  have hS := laplS_eq_one ha hδ
  unfold laplS at hS
  have hq : 0 < a * a + δ * δ := by
    have h1 := mul_nonneg ha ha
    have h2 := mul_pos hδ hδ
    linarith
  have hr : 0 < Real.sqrt (a * a + δ * δ) := Real.sqrt_pos.mpr hq
  have hrr : Real.sqrt (a * a + δ * δ) * Real.sqrt (a * a + δ * δ) = a * a + δ * δ :=
    Real.mul_self_sqrt hq.le
  have hprod : 0 < Real.sqrt (a * a + δ * δ) * lapl (fun t => besselJ0 (a * t)) δ :=
    mul_pos hr hpos
  have hsq : Real.sqrt (a * a + δ * δ) * lapl (fun t => besselJ0 (a * t)) δ
      * (Real.sqrt (a * a + δ * δ) * lapl (fun t => besselJ0 (a * t)) δ) = 1 := by
    linear_combination hS
      + (lapl (fun t => besselJ0 (a * t)) δ * lapl (fun t => besselJ0 (a * t)) δ) * hrr
  have h1 : Real.sqrt (a * a + δ * δ) * lapl (fun t => besselJ0 (a * t)) δ = 1 := by
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact h
    · linarith
  exact eq_inv_of_mul_eq_one_right h1

end Tower.RV6
