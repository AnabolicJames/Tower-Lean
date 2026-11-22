import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselI

/-!
# The Bessel functions `J₀`, `J₁`: calculus, decay, and the walk side

`besselJ0` of `Defs.lean` is `A(-(t/2)²)` with the series `A` of `BesselI.lean`; `besselJ1 t` is
`(t/2) B(-(t/2)²)`.

* `hasDerivAt_besselJ0 : J₀' = -J₁`, `hasDerivAt_mul_besselJ1 : (t J₁(t))' = t J₀(t)`,
  `hasDerivAt_besselJ1 : J₁' = J₀ - J₁/t` for `t ≠ 0`.
* `besselJ_sq_le_one : J₀(t)² + J₁(t)² ≤ 1` for `t ≥ 0` (the derivative is `-2 J₁²/t`).
* `besselJE`, the energy `t J₀² + t J₁² - J₀ J₁ + J₀²/(2t)` of `√t J₀`, has derivative
  `-J₀²/(2t²)`; hence `besselJ0_sq_le : J₀(t)² ≤ E(1)/t` for `t ≥ 1`.
* `integrableOn_walk_integrand`: `t ↦ (e^{-t} - J₀(t)⁶)/t` is integrable on `(0, ∞)`, so the
  integral in `walkSide` (`Defs.lean`) converges.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## The series -/

/-- `J₁(t) = (t/2) B(-(t/2)²) = ∑ (-1)^k (t/2)^{2k+1} / (k! (k+1)!)`. -/
noncomputable def besselJ1 (t : ℝ) : ℝ := t / 2 * Bser (-(t / 2 * (t / 2)))

theorem besselJ0_eq (t : ℝ) : besselJ0 t = Aser (-(t / 2 * (t / 2))) := by
  unfold besselJ0 Aser
  refine tsum_congr (fun k => ?_)
  have e : (t / 2) ^ (2 * k) = (t / 2 * (t / 2)) ^ k := by rw [pow_mul, pow_two]
  rw [e, neg_pow (t / 2 * (t / 2)) k]
  unfold cA
  ring

theorem Aser_zero : Aser 0 = 1 := by
  have h := besselI0_eq 0
  rw [besselI0_zero, zero_div, zero_mul] at h
  exact h.symm

theorem besselJ0_zero : besselJ0 0 = 1 := by
  rw [besselJ0_eq, zero_div, zero_mul, neg_zero]
  exact Aser_zero

theorem besselJ1_zero : besselJ1 0 = 0 := by
  unfold besselJ1
  rw [zero_div, zero_mul]

/-! ## Derivatives -/

/-- `J₀' = -J₁`. -/
theorem hasDerivAt_besselJ0 (t : ℝ) : HasDerivAt besselJ0 (-besselJ1 t) t := by
  have hin0 := (((hasDerivAt_id' t).div_const 2).mul ((hasDerivAt_id' t).div_const 2)).neg
  have hin : HasDerivAt (fun x : ℝ => -(x / 2 * (x / 2)))
      (-(1 / 2 * (t / 2) + t / 2 * (1 / 2))) t := hin0
  have hA := hasDerivAt_Aser (-(t / 2 * (t / 2)))
  have hcomp0 := hA.comp t hin
  have hcomp : HasDerivAt (fun x : ℝ => Aser (-(x / 2 * (x / 2))))
      (Bser (-(t / 2 * (t / 2))) * (-(1 / 2 * (t / 2) + t / 2 * (1 / 2)))) t := hcomp0
  have hfun : besselJ0 = fun x : ℝ => Aser (-(x / 2 * (x / 2))) := funext besselJ0_eq
  rw [hfun]
  refine hcomp.congr_deriv ?_
  unfold besselJ1
  ring

/-- `(t J₁(t))' = t J₀(t)`. -/
theorem hasDerivAt_mul_besselJ1 (t : ℝ) :
    HasDerivAt (fun x : ℝ => x * besselJ1 x) (t * besselJ0 t) t := by
  have hin0 := (((hasDerivAt_id' t).div_const 2).mul ((hasDerivAt_id' t).div_const 2)).neg
  have hin : HasDerivAt (fun x : ℝ => -(x / 2 * (x / 2)))
      (-(1 / 2 * (t / 2) + t / 2 * (1 / 2))) t := hin0
  have hD := hasDerivAt_mul_Bser (-(t / 2 * (t / 2)))
  have hcomp0 := hD.comp t hin
  have hcomp : HasDerivAt (fun x : ℝ => -(x / 2 * (x / 2)) * Bser (-(x / 2 * (x / 2))))
      (Aser (-(t / 2 * (t / 2))) * (-(1 / 2 * (t / 2) + t / 2 * (1 / 2)))) t := hcomp0
  have h2 := hcomp.const_mul (-2)
  have hfun : (fun x : ℝ => x * besselJ1 x)
      = fun x : ℝ => -2 * (-(x / 2 * (x / 2)) * Bser (-(x / 2 * (x / 2)))) := by
    funext x
    unfold besselJ1
    ring
  rw [hfun, besselJ0_eq]
  exact h2.congr_deriv (by ring)

/-- `J₁' = J₀ - J₁/t` for `t ≠ 0`. -/
theorem hasDerivAt_besselJ1 {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt besselJ1 (besselJ0 t - besselJ1 t / t) t := by
  have h := (hasDerivAt_mul_besselJ1 t).fun_div (hasDerivAt_id' t) ht
  have h' : HasDerivAt (fun x : ℝ => x * besselJ1 x / x)
      ((t * besselJ0 t * t - t * besselJ1 t * 1) / t ^ 2) t := h
  have heq : besselJ1 =ᶠ[nhds t] fun x : ℝ => x * besselJ1 x / x := by
    filter_upwards [isOpen_ne.mem_nhds ht] with x hx
    rw [mul_div_cancel_left₀ _ hx]
  have h2 := h'.congr_of_eventuallyEq heq
  refine h2.congr_deriv ?_
  rw [div_eq_iff (pow_ne_zero 2 ht)]
  have hd : besselJ1 t / t * t = besselJ1 t := div_mul_cancel₀ _ ht
  linear_combination t * hd

theorem continuous_besselJ0 : Continuous besselJ0 :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_besselJ0 t).continuousAt)

theorem continuous_besselJ1 : Continuous besselJ1 := by
  have hs : Continuous fun x : ℝ => -(x / 2 * (x / 2)) :=
    ((continuous_id.div_const 2).mul (continuous_id.div_const 2)).neg
  have h : Continuous fun x : ℝ => x / 2 * Bser (-(x / 2 * (x / 2))) :=
    (continuous_id.div_const 2).mul (continuous_Bser.comp hs)
  have hfun : besselJ1 = fun x : ℝ => x / 2 * Bser (-(x / 2 * (x / 2))) := rfl
  rw [hfun]
  exact h

/-! ## A monotonicity lemma -/

/-- A function that is continuous on `[a, ∞)` and has a nonpositive derivative on `(a, ∞)` is
nonincreasing on `[a, ∞)`. -/
theorem antitone_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} {a : ℝ} (hc : ContinuousOn f (Set.Ici a))
    (hd : ∀ x : ℝ, a < x → HasDerivAt f (f' x) x) (hn : ∀ x : ℝ, a < x → f' x ≤ 0)
    {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) : f y ≤ f x := by
  have hdiff : DifferentiableOn ℝ f (interior (Set.Ici a)) := by
    intro z hz
    rw [interior_Ici] at hz
    exact (hd z hz).differentiableAt.differentiableWithinAt
  have hder : ∀ z ∈ interior (Set.Ici a), deriv f z ≤ 0 := by
    intro z hz
    rw [interior_Ici] at hz
    rw [(hd z hz).deriv]
    exact hn z hz
  have hanti := antitoneOn_of_deriv_nonpos (convex_Ici a) hc hdiff hder
  exact hanti (show x ∈ Set.Ici a from hx) (show y ∈ Set.Ici a from le_trans hx hxy) hxy

/-! ## `J₀² + J₁² ≤ 1` -/

theorem hasDerivAt_besselJ_sq {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => besselJ0 x * besselJ0 x + besselJ1 x * besselJ1 x)
      (-(2 * (besselJ1 t * besselJ1 t)) / t) t := by
  have hA := hasDerivAt_besselJ0 t
  have hB := hasDerivAt_besselJ1 ht.ne'
  have h := (hA.mul hA).add (hB.mul hB)
  have h' : HasDerivAt (fun x : ℝ => besselJ0 x * besselJ0 x + besselJ1 x * besselJ1 x)
      (-besselJ1 t * besselJ0 t + besselJ0 t * -besselJ1 t
        + ((besselJ0 t - besselJ1 t / t) * besselJ1 t
          + besselJ1 t * (besselJ0 t - besselJ1 t / t))) t := h
  refine h'.congr_deriv ?_
  ring

/-- `J₀(t)² + J₁(t)² ≤ 1` for `t ≥ 0`. -/
theorem besselJ_sq_le_one {t : ℝ} (ht : 0 ≤ t) :
    besselJ0 t * besselJ0 t + besselJ1 t * besselJ1 t ≤ 1 := by
  have hc : ContinuousOn (fun x : ℝ => besselJ0 x * besselJ0 x + besselJ1 x * besselJ1 x)
      (Set.Ici (0 : ℝ)) :=
    ((continuous_besselJ0.mul continuous_besselJ0).add
      (continuous_besselJ1.mul continuous_besselJ1)).continuousOn
  have h : besselJ0 t * besselJ0 t + besselJ1 t * besselJ1 t
      ≤ besselJ0 0 * besselJ0 0 + besselJ1 0 * besselJ1 0 :=
    antitone_of_hasDerivAt_nonpos
      (f' := fun x => -(2 * (besselJ1 x * besselJ1 x)) / x) hc
      (fun x hx => hasDerivAt_besselJ_sq hx)
      (fun x hx => div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg zero_le_two (mul_self_nonneg (besselJ1 x)))) hx.le)
      (le_refl (0 : ℝ)) ht
  rw [besselJ0_zero, besselJ1_zero] at h
  linarith

theorem abs_besselJ0_le_one {t : ℝ} (ht : 0 ≤ t) : |besselJ0 t| ≤ 1 := by
  have h := besselJ_sq_le_one ht
  have h1 := mul_self_nonneg (besselJ1 t)
  exact abs_le_one_iff_mul_self_le_one.mpr (by linarith)

theorem abs_besselJ1_le_one {t : ℝ} (ht : 0 ≤ t) : |besselJ1 t| ≤ 1 := by
  have h := besselJ_sq_le_one ht
  have h1 := mul_self_nonneg (besselJ0 t)
  exact abs_le_one_iff_mul_self_le_one.mpr (by linarith)

/-- `1 - J₀(t) ≤ t` for `t ≥ 0`. -/
theorem one_sub_besselJ0_le {t : ℝ} (ht : 0 ≤ t) : 1 - besselJ0 t ≤ t := by
  have hc : ContinuousOn (fun x : ℝ => 1 - besselJ0 x - x) (Set.Ici (0 : ℝ)) :=
    ((continuous_const.sub continuous_besselJ0).sub continuous_id').continuousOn
  have hd : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ => 1 - besselJ0 y - y) (besselJ1 x - 1) x := by
    intro x _
    have h := ((hasDerivAt_besselJ0 x).const_sub 1).sub (hasDerivAt_id' x)
    have h' : HasDerivAt (fun y : ℝ => 1 - besselJ0 y - y) (-(-besselJ1 x) - 1) x := h
    exact h'.congr_deriv (by ring)
  have hn : ∀ x : ℝ, 0 < x → besselJ1 x - 1 ≤ 0 := by
    intro x hx
    have h1 := abs_besselJ1_le_one hx.le
    have h2 := (abs_le.mp h1).2
    linarith
  have h : 1 - besselJ0 t - t ≤ 1 - besselJ0 0 - 0 :=
    antitone_of_hasDerivAt_nonpos (f' := fun x => besselJ1 x - 1) hc hd hn
      (le_refl (0 : ℝ)) ht
  rw [besselJ0_zero] at h
  linarith

/-! ## The energy of `√t J₀` -/

/-- `t² J₀² + (t J₁)² - J₀ (t J₁) + J₀²/2`. -/
noncomputable def besselJQ (x : ℝ) : ℝ :=
  x * x * (besselJ0 x * besselJ0 x) + x * besselJ1 x * (x * besselJ1 x)
    - besselJ0 x * (x * besselJ1 x) + besselJ0 x * besselJ0 x / 2

/-- For `t > 0`: `t J₀² + t J₁² - J₀ J₁ + J₀²/(2t)`, the energy `u'² + (1 + 1/(4t²)) u²` of
`u = √t J₀`. -/
noncomputable def besselJE (x : ℝ) : ℝ := besselJQ x / x

theorem hasDerivAt_besselJQ (t : ℝ) :
    HasDerivAt besselJQ
      (t * (besselJ0 t * besselJ0 t) + t * (besselJ1 t * besselJ1 t)
        - besselJ0 t * besselJ1 t) t := by
  have hx := hasDerivAt_id' t
  have hA := hasDerivAt_besselJ0 t
  have hD := hasDerivAt_mul_besselJ1 t
  have hAA := hA.mul hA
  have h1 := (hx.mul hx).mul hAA
  have h2 := hD.mul hD
  have h3 := hA.mul hD
  have h4 := hAA.div_const 2
  have h := ((h1.add h2).sub h3).add h4
  have h' : HasDerivAt (fun x : ℝ => x * x * (besselJ0 x * besselJ0 x)
        + x * besselJ1 x * (x * besselJ1 x) - besselJ0 x * (x * besselJ1 x)
        + besselJ0 x * besselJ0 x / 2)
      ((1 * t + t * 1) * (besselJ0 t * besselJ0 t)
          + t * t * (-besselJ1 t * besselJ0 t + besselJ0 t * -besselJ1 t)
        + (t * besselJ0 t * (t * besselJ1 t) + t * besselJ1 t * (t * besselJ0 t))
        - (-besselJ1 t * (t * besselJ1 t) + besselJ0 t * (t * besselJ0 t))
        + (-besselJ1 t * besselJ0 t + besselJ0 t * -besselJ1 t) / 2) t := h
  have hfun : besselJQ = fun x : ℝ => x * x * (besselJ0 x * besselJ0 x)
        + x * besselJ1 x * (x * besselJ1 x) - besselJ0 x * (x * besselJ1 x)
        + besselJ0 x * besselJ0 x / 2 := rfl
  rw [hfun]
  exact h'.congr_deriv (by ring)

/-- `E'(t) = -J₀(t)²/(2t²)` for `t > 0`. -/
theorem hasDerivAt_besselJE {t : ℝ} (ht : 0 < t) :
    HasDerivAt besselJE (-(besselJ0 t * besselJ0 t) / (2 * t ^ 2)) t := by
  have h := (hasDerivAt_besselJQ t).fun_div (hasDerivAt_id' t) ht.ne'
  have h' : HasDerivAt (fun x : ℝ => besselJQ x / x)
      (((t * (besselJ0 t * besselJ0 t) + t * (besselJ1 t * besselJ1 t)
          - besselJ0 t * besselJ1 t) * t - besselJQ t * 1) / t ^ 2) t := h
  have hfun : besselJE = fun x : ℝ => besselJQ x / x := rfl
  rw [hfun]
  refine h'.congr_deriv ?_
  unfold besselJQ
  ring

/-- The energy is nonincreasing on `[1, ∞)`. -/
theorem besselJE_anti {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) : besselJE t ≤ besselJE s := by
  have hc : ContinuousOn besselJE (Set.Ici (1 : ℝ)) := fun x hx =>
    (hasDerivAt_besselJE
      (lt_of_lt_of_le one_pos (show (1 : ℝ) ≤ x from hx))).continuousAt.continuousWithinAt
  exact antitone_of_hasDerivAt_nonpos
    (f' := fun x => -(besselJ0 x * besselJ0 x) / (2 * x ^ 2)) hc
    (fun x hx => hasDerivAt_besselJE (lt_trans one_pos hx))
    (fun x _ => div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_self_nonneg (besselJ0 x))) (by positivity))
    hs hst

/-- `t² J₀(t)² ≤ Q(t)`. -/
theorem besselJQ_lower (t : ℝ) : t * t * (besselJ0 t * besselJ0 t) ≤ besselJQ t := by
  have e : besselJQ t - t * t * (besselJ0 t * besselJ0 t)
      = (t * besselJ1 t - besselJ0 t / 2) * (t * besselJ1 t - besselJ0 t / 2)
        + besselJ0 t * besselJ0 t / 4 := by
    unfold besselJQ
    ring
  have h1 := mul_self_nonneg (t * besselJ1 t - besselJ0 t / 2)
  have h2 := mul_self_nonneg (besselJ0 t)
  linarith

/-- **Decay.** `J₀(t)² ≤ E(1)/t` for `t ≥ 1`. -/
theorem besselJ0_sq_le {t : ℝ} (ht : 1 ≤ t) : besselJ0 t * besselJ0 t ≤ besselJE 1 / t := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hQ := besselJQ_lower t
  have hE := besselJE_anti (le_refl (1 : ℝ)) ht
  have hQE : besselJQ t = besselJE t * t := by
    unfold besselJE
    rw [div_mul_cancel₀ _ ht0.ne']
  rw [le_div_iff₀ ht0]
  have h1 : t * (besselJ0 t * besselJ0 t * t) ≤ t * besselJE 1 := by
    calc t * (besselJ0 t * besselJ0 t * t)
        = t * t * (besselJ0 t * besselJ0 t) := by ring
      _ ≤ besselJQ t := hQ
      _ = besselJE t * t := hQE
      _ ≤ besselJE 1 * t := mul_le_mul_of_nonneg_right hE ht0.le
      _ = t * besselJE 1 := by ring
  exact le_of_mul_le_mul_left h1 ht0

theorem besselJE_one_nonneg : 0 ≤ besselJE 1 := by
  have h := besselJ0_sq_le (le_refl (1 : ℝ))
  rw [div_one] at h
  exact le_trans (mul_self_nonneg _) h

/-! ## The integrand of the walk side -/

/-- For `|a| ≤ 1`: `0 ≤ 1 - a⁶ ≤ 6 (1 - a)`. -/
theorem pow_six_bound {a : ℝ} (ha : |a| ≤ 1) : 0 ≤ 1 - a ^ 6 ∧ 1 - a ^ 6 ≤ 6 * (1 - a) := by
  have hk : ∀ k : ℕ, a ^ k ≤ 1 := by
    intro k
    have h1 : a ^ k ≤ |a ^ k| := le_abs_self _
    have h2 : |a ^ k| = |a| ^ k := abs_pow a k
    have h3 : |a| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg a) ha
    linarith
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  have h5 := hk 5
  have h6 := hk 6
  rw [pow_one] at h1
  have hS : 1 + a + a ^ 2 + a ^ 3 + a ^ 4 + a ^ 5 ≤ 6 := by linarith
  have h1a : 0 ≤ 1 - a := by linarith
  have e : 1 - a ^ 6 = (1 - a) * (1 + a + a ^ 2 + a ^ 3 + a ^ 4 + a ^ 5) := by ring
  refine ⟨by linarith, ?_⟩
  rw [e, mul_comm 6 (1 - a)]
  exact mul_le_mul_of_nonneg_left hS h1a

/-- On `(0, 1]` the integrand is bounded by `6`. -/
theorem walk_integrand_abs_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |(Real.exp (-t) - besselJ0 t ^ 6) / t| ≤ 6 := by
  have hJ := abs_besselJ0_le_one ht0.le
  obtain ⟨hp0, hp1⟩ := pow_six_bound hJ
  have h1J := one_sub_besselJ0_le ht0.le
  have he1 : Real.exp (-t) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (by linarith : -t ≤ 0)
    rw [Real.exp_zero] at h
    exact h
  have he2 : -t + 1 ≤ Real.exp (-t) := Real.add_one_le_exp (-t)
  rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0, abs_le]
  constructor
  · linarith
  · linarith

/-- On `[1, ∞)` the integrand is bounded by `e^{-t} + 2 E(1)/(1 + t²)`. -/
theorem walk_integrand_abs_le_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    |(Real.exp (-t) - besselJ0 t ^ 6) / t|
      ≤ Real.exp (-t) + 2 * besselJE 1 * (1 + t ^ 2)⁻¹ := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hsq := besselJ0_sq_le ht
  have hsq' : besselJ0 t * besselJ0 t * t ≤ besselJE 1 := (le_div_iff₀ ht0).mp hsq
  have hA2 : besselJ0 t * besselJ0 t ≤ 1 := by
    have h := besselJ_sq_le_one ht0.le
    have h1 := mul_self_nonneg (besselJ1 t)
    linarith
  have hA2n : 0 ≤ besselJ0 t * besselJ0 t := mul_self_nonneg _
  have h6 : besselJ0 t ^ 6 ≤ besselJ0 t * besselJ0 t := by
    have e : besselJ0 t ^ 6 = besselJ0 t * besselJ0 t
        * ((besselJ0 t * besselJ0 t) * (besselJ0 t * besselJ0 t)) := by ring
    have h44 : (besselJ0 t * besselJ0 t) * (besselJ0 t * besselJ0 t) ≤ 1 := by
      calc (besselJ0 t * besselJ0 t) * (besselJ0 t * besselJ0 t)
          ≤ 1 * 1 := mul_le_mul hA2 hA2 hA2n zero_le_one
        _ = 1 := one_mul 1
    rw [e]
    calc besselJ0 t * besselJ0 t * ((besselJ0 t * besselJ0 t) * (besselJ0 t * besselJ0 t))
        ≤ besselJ0 t * besselJ0 t * 1 := mul_le_mul_of_nonneg_left h44 hA2n
      _ = besselJ0 t * besselJ0 t := mul_one _
  have h6n : 0 ≤ besselJ0 t ^ 6 := by
    have e : besselJ0 t ^ 6 = (besselJ0 t ^ 3) ^ 2 := by ring
    rw [e]
    exact sq_nonneg _
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hw : 0 < (1 + t ^ 2)⁻¹ := inv_pos.mpr hpos
  have htt : 1 * 1 ≤ t * t := mul_le_mul ht ht zero_le_one ht0.le
  have ht2 : 0 ≤ t ^ 2 - 1 := by
    rw [pow_two]
    linarith
  have e1 : (1 + t ^ 2) * (1 + t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have e2 : (1 + t ^ 2)⁻¹ * (t ^ 2 - 1)
      = 2 * (1 + t ^ 2)⁻¹ * t ^ 2 - (1 + t ^ 2) * (1 + t ^ 2)⁻¹ := by ring
  have h3 : 0 ≤ (1 + t ^ 2)⁻¹ * (t ^ 2 - 1) := mul_nonneg hw.le ht2
  have h2w : 1 ≤ 2 * (1 + t ^ 2)⁻¹ * t ^ 2 := by linarith
  have key : Real.exp (-t) + besselJ0 t ^ 6
      ≤ (Real.exp (-t) + 2 * besselJE 1 * (1 + t ^ 2)⁻¹) * t := by
    have hi : Real.exp (-t) ≤ Real.exp (-t) * t :=
      le_mul_of_one_le_right (Real.exp_pos _).le ht
    have hii : besselJ0 t * besselJ0 t ≤ 2 * besselJE 1 * (1 + t ^ 2)⁻¹ * t := by
      calc besselJ0 t * besselJ0 t
          ≤ besselJ0 t * besselJ0 t * (2 * (1 + t ^ 2)⁻¹ * t ^ 2) :=
            le_mul_of_one_le_right hA2n h2w
        _ = besselJ0 t * besselJ0 t * t * (2 * (1 + t ^ 2)⁻¹ * t) := by ring
        _ ≤ besselJE 1 * (2 * (1 + t ^ 2)⁻¹ * t) :=
            mul_le_mul_of_nonneg_right hsq'
              (mul_nonneg (mul_nonneg zero_le_two hw.le) ht0.le)
        _ = 2 * besselJE 1 * (1 + t ^ 2)⁻¹ * t := by ring
    have e : (Real.exp (-t) + 2 * besselJE 1 * (1 + t ^ 2)⁻¹) * t
        = Real.exp (-t) * t + 2 * besselJE 1 * (1 + t ^ 2)⁻¹ * t := by ring
    rw [e]
    linarith
  have hexp := Real.exp_pos (-t)
  rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0, abs_le]
  constructor
  · linarith
  · linarith

theorem measurable_walk_integrand :
    Measurable fun t : ℝ => (Real.exp (-t) - besselJ0 t ^ 6) / t := by
  have h1 : Continuous fun t : ℝ => Real.exp (-t) - besselJ0 t ^ 6 :=
    (Real.continuous_exp.comp continuous_neg).sub (continuous_besselJ0.pow 6)
  exact h1.measurable.div measurable_id

/-- **The walk side exists.** `t ↦ (e^{-t} - J₀(t)⁶)/t` is integrable on `(0, ∞)`. -/
theorem integrableOn_walk_integrand :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) - besselJ0 t ^ 6) / t) (Set.Ioi (0 : ℝ)) := by
  have hm := measurable_walk_integrand
  have h01 : IntegrableOn (fun t : ℝ => (Real.exp (-t) - besselJ0 t ^ 6) / t)
      (Set.Ioc (0 : ℝ) 1) := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable 6
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))
    rw [Real.norm_eq_abs]
    exact walk_integrand_abs_le ht.1 ht.2
  have h1 : IntegrableOn (fun t : ℝ => (Real.exp (-t) - besselJ0 t ^ 6) / t)
      (Set.Ioi (1 : ℝ)) := by
    have hb1 : Integrable (fun t : ℝ => Real.exp (-t)) (volume.restrict (Set.Ioi (1 : ℝ))) :=
      integrableOn_exp_neg_Ioi 1
    have hb0 : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Set.Ioi (1 : ℝ)) :=
      integrable_inv_one_add_sq.integrableOn
    have hb2 : Integrable (fun t : ℝ => 2 * besselJE 1 * (1 + t ^ 2)⁻¹)
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      Integrable.const_mul hb0 (2 * besselJE 1)
    have hb : Integrable (fun t : ℝ => Real.exp (-t) + 2 * besselJE 1 * (1 + t ^ 2)⁻¹)
        (volume.restrict (Set.Ioi (1 : ℝ))) := hb1.add hb2
    show Integrable (fun t : ℝ => (Real.exp (-t) - besselJ0 t ^ 6) / t)
      (volume.restrict (Set.Ioi (1 : ℝ)))
    refine Integrable.mono' hb hm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht1 : (1 : ℝ) < t := ht
    rw [Real.norm_eq_abs]
    exact walk_integrand_abs_le_of_one_le ht1.le
  have hu := h01.union h1
  rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at hu
  exact hu

end Tower.RV6
