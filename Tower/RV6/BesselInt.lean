import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselJ

/-!
# Bessel's integral

`besG x = ∫₀¹ cos(x cos 2πθ) dθ` and `besH x = ∫₀¹ sin(x cos 2πθ) cos 2πθ dθ` satisfy
`G' = -H` and `(x H)' = x G`, with `G(0) = 1`, `H(0) = 0`: the system of `J₀`, `J₁`.

* `hasDerivAt_besG`, `hasDerivAt_besH`, `besH_relation`, `hasDerivAt_mul_besH`.
* `bessel_system_zero`: a solution of `A' = -B`, `(x B)' = x A` with `A(0) = B(0) = 0` and `B`
  continuous vanishes on `[0, ∞)` (`A² + B²` has derivative `-2B²/x` on `x > 0`).
* **`besselJ0_eq_besG`**, **`besselJ1_eq_besH`**: `J₀(x) = ∫₀¹ cos(x cos 2πθ) dθ` and
  `J₁(x) = ∫₀¹ sin(x cos 2πθ) cos 2πθ dθ` for `x ≥ 0`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `G(x) = ∫₀¹ cos(x cos 2πθ) dθ`. -/
noncomputable def besG (x : ℝ) : ℝ :=
  ∫ θ in Set.Ioc (0 : ℝ) 1, Real.cos (x * Real.cos (2 * π * θ))

/-- `H(x) = ∫₀¹ sin(x cos 2πθ) cos 2πθ dθ`. -/
noncomputable def besH (x : ℝ) : ℝ :=
  ∫ θ in Set.Ioc (0 : ℝ) 1, Real.sin (x * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ)

/-- `K(x) = ∫₀¹ cos(x cos 2πθ) cos² 2πθ dθ`. -/
noncomputable def besK (x : ℝ) : ℝ :=
  ∫ θ in Set.Ioc (0 : ℝ) 1,
    Real.cos (x * Real.cos (2 * π * θ)) * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ))

theorem continuous_cos_two_pi : Continuous fun θ : ℝ => Real.cos (2 * π * θ) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_id')

theorem continuous_besG_integrand (x : ℝ) :
    Continuous fun θ : ℝ => Real.cos (x * Real.cos (2 * π * θ)) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_cos_two_pi)

theorem continuous_besH_integrand (x : ℝ) :
    Continuous fun θ : ℝ => Real.sin (x * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ) :=
  (Real.continuous_sin.comp (continuous_const.mul continuous_cos_two_pi)).mul
    continuous_cos_two_pi

theorem continuous_besK_integrand (x : ℝ) :
    Continuous fun θ : ℝ =>
      Real.cos (x * Real.cos (2 * π * θ)) * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ)) :=
  (continuous_besG_integrand x).mul (continuous_cos_two_pi.mul continuous_cos_two_pi)

/-! ## Values at `0` -/

theorem besG_zero : besG 0 = 1 := by
  have hfun : (fun θ : ℝ => Real.cos (0 * Real.cos (2 * π * θ))) = fun _ : ℝ => (1 : ℝ) := by
    funext θ
    rw [zero_mul, Real.cos_zero]
  unfold besG
  rw [hfun, ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_const]
  simp

theorem besH_zero : besH 0 = 0 := by
  have hfun : (fun θ : ℝ => Real.sin (0 * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))
      = fun _ : ℝ => (0 : ℝ) := by
    funext θ
    rw [zero_mul, Real.sin_zero, zero_mul]
  unfold besH
  rw [hfun]
  simp

/-! ## Derivatives -/

/-- `G' = -H`. -/
theorem hasDerivAt_besG (x : ℝ) : HasDerivAt besG (-besH x) x := by
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable
      (fun θ : ℝ => Real.cos (y * Real.cos (2 * π * θ)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    fun y => (continuous_besG_integrand y).aestronglyMeasurable
  have hbound : ∀ θ : ℝ, ∀ y ∈ (Set.univ : Set ℝ),
      ‖-(Real.sin (y * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))‖ ≤ (1 : ℝ) := by
    intro θ y _
    rw [norm_neg, Real.norm_eq_abs, abs_mul]
    calc |Real.sin (y * Real.cos (2 * π * θ))| * |Real.cos (2 * π * θ)| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hdiff : ∀ θ : ℝ, ∀ y ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun z : ℝ => Real.cos (z * Real.cos (2 * π * θ)))
        (-(Real.sin (y * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))) y := by
    intro θ y _
    have h := ((hasDerivAt_id' y).mul_const (Real.cos (2 * π * θ))).cos
    have h' : HasDerivAt (fun z : ℝ => Real.cos (z * Real.cos (2 * π * θ)))
        (-Real.sin (y * Real.cos (2 * π * θ)) * (1 * Real.cos (2 * π * θ))) y := h
    exact h'.congr_deriv (by ring)
  have hbi : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).integrableOn_Ioc
  have hint : Integrable (fun θ : ℝ => Real.cos (x * Real.cos (2 * π * θ)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := (continuous_besG_integrand x).integrableOn_Ioc
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (F := fun y θ => Real.cos (y * Real.cos (2 * π * θ)))
    (F' := fun y θ => -(Real.sin (y * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ)))
    (bound := fun _ => (1 : ℝ)) Filter.univ_mem
    (Filter.Eventually.of_forall hmeas) hint
    ((continuous_besH_integrand x).neg.aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound) hbi
    (Filter.Eventually.of_forall hdiff)
  have h3 : HasDerivAt
      (fun y : ℝ => ∫ θ in Set.Ioc (0 : ℝ) 1, Real.cos (y * Real.cos (2 * π * θ)))
      (∫ θ in Set.Ioc (0 : ℝ) 1,
        -(Real.sin (x * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))) x := key.2
  rw [integral_neg] at h3
  exact h3

/-- `H' = K`. -/
theorem hasDerivAt_besH (x : ℝ) : HasDerivAt besH (besK x) x := by
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable
      (fun θ : ℝ => Real.sin (y * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    fun y => (continuous_besH_integrand y).aestronglyMeasurable
  have hbound : ∀ θ : ℝ, ∀ y ∈ (Set.univ : Set ℝ),
      ‖Real.cos (y * Real.cos (2 * π * θ)) * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ))‖
        ≤ (1 : ℝ) := by
    intro θ y _
    rw [Real.norm_eq_abs, abs_mul, abs_mul (Real.cos (2 * π * θ)) (Real.cos (2 * π * θ))]
    calc |Real.cos (y * Real.cos (2 * π * θ))|
          * (|Real.cos (2 * π * θ)| * |Real.cos (2 * π * θ)|) ≤ 1 * (1 * 1) :=
          mul_le_mul (Real.abs_cos_le_one _)
            (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _)
              zero_le_one)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
      _ = 1 := by norm_num
  have hdiff : ∀ θ : ℝ, ∀ y ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun z : ℝ => Real.sin (z * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))
        (Real.cos (y * Real.cos (2 * π * θ))
          * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ))) y := by
    intro θ y _
    have h := (((hasDerivAt_id' y).mul_const (Real.cos (2 * π * θ))).sin).mul_const
      (Real.cos (2 * π * θ))
    have h' : HasDerivAt
        (fun z : ℝ => Real.sin (z * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))
        (Real.cos (y * Real.cos (2 * π * θ)) * (1 * Real.cos (2 * π * θ))
          * Real.cos (2 * π * θ)) y := h
    exact h'.congr_deriv (by ring)
  have hbi : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).integrableOn_Ioc
  have hint : Integrable
      (fun θ : ℝ => Real.sin (x * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := (continuous_besH_integrand x).integrableOn_Ioc
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (F := fun y θ => Real.sin (y * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))
    (F' := fun y θ => Real.cos (y * Real.cos (2 * π * θ))
      * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ)))
    (bound := fun _ => (1 : ℝ)) Filter.univ_mem
    (Filter.Eventually.of_forall hmeas) hint
    ((continuous_besK_integrand x).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound) hbi
    (Filter.Eventually.of_forall hdiff)
  have h3 : HasDerivAt
      (fun y : ℝ => ∫ θ in Set.Ioc (0 : ℝ) 1,
        Real.sin (y * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))
      (∫ θ in Set.Ioc (0 : ℝ) 1,
        Real.cos (x * Real.cos (2 * π * θ))
          * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ))) x := key.2
  exact h3

theorem continuous_besH : Continuous besH :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_besH x).continuousAt)

/-- `H(x) + x K(x) - x G(x) = 0`: the integrand is `(2π)⁻¹ d/dθ (sin 2πθ · sin(x cos 2πθ))`. -/
theorem besH_relation (x : ℝ) : besH x + x * besK x - x * besG x = 0 := by
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => Real.sin (2 * π * u) * Real.sin (x * Real.cos (2 * π * u)))
        (2 * π * (Real.sin (x * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ)
          + x * (Real.cos (x * Real.cos (2 * π * θ))
            * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ)))
          - x * Real.cos (x * Real.cos (2 * π * θ)))) θ := by
    intro θ _
    have hin : HasDerivAt (fun u : ℝ => 2 * π * u) (2 * π * 1) θ :=
      (hasDerivAt_id' θ).const_mul (2 * π)
    have hs : HasDerivAt (fun u : ℝ => Real.sin (2 * π * u))
        (Real.cos (2 * π * θ) * (2 * π * 1)) θ := hin.sin
    have hc : HasDerivAt (fun u : ℝ => Real.cos (2 * π * u))
        (-Real.sin (2 * π * θ) * (2 * π * 1)) θ := hin.cos
    have hxc : HasDerivAt (fun u : ℝ => x * Real.cos (2 * π * u))
        (x * (-Real.sin (2 * π * θ) * (2 * π * 1))) θ := hc.const_mul x
    have hsx : HasDerivAt (fun u : ℝ => Real.sin (x * Real.cos (2 * π * u)))
        (Real.cos (x * Real.cos (2 * π * θ))
          * (x * (-Real.sin (2 * π * θ) * (2 * π * 1)))) θ := hxc.sin
    have hP := hs.mul hsx
    have hP' : HasDerivAt
        (fun u : ℝ => Real.sin (2 * π * u) * Real.sin (x * Real.cos (2 * π * u)))
        (Real.cos (2 * π * θ) * (2 * π * 1) * Real.sin (x * Real.cos (2 * π * θ))
          + Real.sin (2 * π * θ)
            * (Real.cos (x * Real.cos (2 * π * θ))
              * (x * (-Real.sin (2 * π * θ) * (2 * π * 1))))) θ := hP
    refine hP'.congr_deriv ?_
    have htrig := Real.sin_sq_add_cos_sq (2 * π * θ)
    linear_combination (-(2 * π * x * Real.cos (x * Real.cos (2 * π * θ)))) * htrig
  have hcont : Continuous fun θ : ℝ =>
      2 * π * (Real.sin (x * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ)
        + x * (Real.cos (x * Real.cos (2 * π * θ))
          * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ)))
        - x * Real.cos (x * Real.cos (2 * π * θ))) :=
    continuous_const.mul (((continuous_besH_integrand x).add
      (continuous_const.mul (continuous_besK_integrand x))).sub
      (continuous_const.mul (continuous_besG_integrand x)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 1)
  simp only [mul_one, mul_zero, Real.sin_two_pi, Real.sin_zero, zero_mul, sub_zero] at hftc
  rw [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hftc
  have iH : Integrable
      (fun θ : ℝ => Real.sin (x * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := (continuous_besH_integrand x).integrableOn_Ioc
  have iK0 : Integrable (fun θ : ℝ => Real.cos (x * Real.cos (2 * π * θ))
      * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := (continuous_besK_integrand x).integrableOn_Ioc
  have iK : Integrable (fun θ : ℝ => x * (Real.cos (x * Real.cos (2 * π * θ))
      * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ))))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := Integrable.const_mul iK0 x
  have iG0 : Integrable (fun θ : ℝ => Real.cos (x * Real.cos (2 * π * θ)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := (continuous_besG_integrand x).integrableOn_Ioc
  have iG : Integrable (fun θ : ℝ => x * Real.cos (x * Real.cos (2 * π * θ)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := Integrable.const_mul iG0 x
  have iHK : Integrable (fun θ : ℝ =>
      Real.sin (x * Real.cos (2 * π * θ)) * Real.cos (2 * π * θ)
        + x * (Real.cos (x * Real.cos (2 * π * θ))
          * (Real.cos (2 * π * θ) * Real.cos (2 * π * θ))))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := iH.add iK
  rw [integral_const_mul, integral_sub iHK iG, integral_add iH iK, integral_const_mul,
    integral_const_mul] at hftc
  have hpi : (2 * π) ≠ 0 := (mul_pos two_pos Real.pi_pos).ne'
  have h0 := (mul_eq_zero.mp hftc).resolve_left hpi
  unfold besH besK besG
  exact h0

/-- `(x H(x))' = x G(x)`. -/
theorem hasDerivAt_mul_besH (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * besH y) (x * besG x) x := by
  have h := (hasDerivAt_id' x).mul (hasDerivAt_besH x)
  have h' : HasDerivAt (fun y : ℝ => y * besH y) (1 * besH x + x * besK x) x := h
  refine h'.congr_deriv ?_
  linear_combination besH_relation x

/-! ## Uniqueness -/

/-- A solution of `A' = -B`, `(x B)' = x A` with `A(0) = B(0) = 0` and `B` continuous vanishes on
`[0, ∞)`. -/
theorem bessel_system_zero {A B : ℝ → ℝ}
    (hA : ∀ t : ℝ, HasDerivAt A (-B t) t)
    (hB : ∀ t : ℝ, HasDerivAt (fun x : ℝ => x * B x) (t * A t) t)
    (hBc : Continuous B) (hA0 : A 0 = 0) (hB0 : B 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    A t = 0 ∧ B t = 0 := by
  have hAc : Continuous A := continuous_iff_continuousAt.mpr (fun s => (hA s).continuousAt)
  have hB' : ∀ s : ℝ, s ≠ 0 → HasDerivAt B (A s - B s / s) s := by
    intro s hs
    have h := (hB s).fun_div (hasDerivAt_id' s) hs
    have h' : HasDerivAt (fun x : ℝ => x * B x / x)
        ((s * A s * s - s * B s * 1) / s ^ 2) s := h
    have heq : B =ᶠ[nhds s] fun x : ℝ => x * B x / x := by
      filter_upwards [isOpen_ne.mem_nhds hs] with x hx
      rw [mul_div_cancel_left₀ _ hx]
    have h2 := h'.congr_of_eventuallyEq heq
    refine h2.congr_deriv ?_
    rw [div_eq_iff (pow_ne_zero 2 hs)]
    have hd : B s / s * s = B s := div_mul_cancel₀ _ hs
    linear_combination s * hd
  have hsq : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun x : ℝ => A x * A x + B x * B x) (-(2 * (B s * B s)) / s) s := by
    intro s hs
    have h := ((hA s).mul (hA s)).add ((hB' s hs.ne').mul (hB' s hs.ne'))
    have h' : HasDerivAt (fun x : ℝ => A x * A x + B x * B x)
        (-B s * A s + A s * -B s
          + ((A s - B s / s) * B s + B s * (A s - B s / s))) s := h
    refine h'.congr_deriv ?_
    ring
  have hc : ContinuousOn (fun x : ℝ => A x * A x + B x * B x) (Set.Ici (0 : ℝ)) :=
    ((hAc.mul hAc).add (hBc.mul hBc)).continuousOn
  have h : A t * A t + B t * B t ≤ A 0 * A 0 + B 0 * B 0 :=
    antitone_of_hasDerivAt_nonpos (f' := fun x => -(2 * (B x * B x)) / x) hc hsq
      (fun x hx => div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg zero_le_two (mul_self_nonneg (B x)))) hx.le)
      (le_refl (0 : ℝ)) ht
  rw [hA0, hB0] at h
  have h1 := mul_self_nonneg (A t)
  have h2 := mul_self_nonneg (B t)
  have hAt : A t * A t = 0 := by linarith
  have hBt : B t * B t = 0 := by linarith
  exact ⟨mul_self_eq_zero.mp hAt, mul_self_eq_zero.mp hBt⟩

/-! ## Bessel's integral -/

theorem bessel_eq_bes {x : ℝ} (hx : 0 ≤ x) : besselJ0 x = besG x ∧ besselJ1 x = besH x := by
  have hA : ∀ t : ℝ, HasDerivAt (fun y : ℝ => besG y - besselJ0 y)
      (-(besH t - besselJ1 t)) t := by
    intro t
    have h := (hasDerivAt_besG t).sub (hasDerivAt_besselJ0 t)
    have h' : HasDerivAt (fun y : ℝ => besG y - besselJ0 y) (-besH t - -besselJ1 t) t := h
    exact h'.congr_deriv (by ring)
  have hB : ∀ t : ℝ, HasDerivAt (fun y : ℝ => y * (besH y - besselJ1 y))
      (t * (besG t - besselJ0 t)) t := by
    intro t
    have h := (hasDerivAt_mul_besH t).sub (hasDerivAt_mul_besselJ1 t)
    have h' : HasDerivAt (fun y : ℝ => y * besH y - y * besselJ1 y)
        (t * besG t - t * besselJ0 t) t := h
    have hfun : (fun y : ℝ => y * (besH y - besselJ1 y))
        = fun y : ℝ => y * besH y - y * besselJ1 y := by
      funext y
      ring
    rw [hfun]
    exact h'.congr_deriv (by ring)
  have hBc : Continuous fun y : ℝ => besH y - besselJ1 y :=
    continuous_besH.sub continuous_besselJ1
  have hA0 : (fun y : ℝ => besG y - besselJ0 y) 0 = 0 := by
    show besG 0 - besselJ0 0 = 0
    rw [besG_zero, besselJ0_zero, sub_self]
  have hB0 : (fun y : ℝ => besH y - besselJ1 y) 0 = 0 := by
    show besH 0 - besselJ1 0 = 0
    rw [besH_zero, besselJ1_zero, sub_self]
  have h := bessel_system_zero (A := fun y : ℝ => besG y - besselJ0 y)
    (B := fun y : ℝ => besH y - besselJ1 y) hA hB hBc hA0 hB0 hx
  have h1 : besG x - besselJ0 x = 0 := h.1
  have h2 : besH x - besselJ1 x = 0 := h.2
  constructor
  · linarith
  · linarith

/-- **Bessel's integral.** `J₀(x) = ∫₀¹ cos(x cos 2πθ) dθ` for `x ≥ 0`. -/
theorem besselJ0_eq_besG {x : ℝ} (hx : 0 ≤ x) : besselJ0 x = besG x := (bessel_eq_bes hx).1

/-- `J₁(x) = ∫₀¹ sin(x cos 2πθ) cos 2πθ dθ` for `x ≥ 0`. -/
theorem besselJ1_eq_besH {x : ℝ} (hx : 0 ≤ x) : besselJ1 x = besH x := (bessel_eq_bes hx).2

end Tower.RV6
