import Mathlib
import Tower.RV6.CJSeries
import Tower.RV6.BesselR
import Tower.RV6.BesselK

/-!
# Laplace forms of `I₀(t) e^{-t}` and `K₀(t) e^{t}`

* `besselI0_eq_integral`: `I₀(t) = (2/π) ∫₀^{π/2} cosh(t sin φ) dφ` (termwise integration of the
  series of `cosh`, with `integral_sin_pow_even_half`);
* `besselI0_eq_poisson`: `I₀(t) = π⁻¹ ∫_{-π/2}^{π/2} e^{t sin φ} dφ`;
* **`laplace_I0`**: `I₀(t) e^{-t} = ∫₀² e^{-ts} ρ_I(s) ds`, `ρ_I(s) = 1/(π √(s(2-s)))`
  (`s = 1 - sin φ`), and `integrableOn_laplace_I0`;
* **`laplace_K0`**: `K₀(t) e^{t} = ∫₀^∞ e^{-tr} ρ_K(r) dr`, `ρ_K(r) = 1/√(r(r+2))`
  (`r = cosh u - 1`), and `integrableOn_laplace_K0` for `t > 0`.

These are the two factors of the Laplace representation of `I₀ K₀` (`LaplaceP.lean`), from which
the decay of `θᵏ(I₀² K₀²)` at infinity follows.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## `I₀` as a Poisson integral -/

/-- `∫₀^{π/2} cosh(t sin φ) dφ = Σ_k ∫₀^{π/2} (t sin φ)^{2k}/(2k)! dφ`. -/
theorem hasSum_integral_cosh_mul_sin (t : ℝ) :
    HasSum (fun k : ℕ => ∫ φ in (0 : ℝ)..(π / 2), (t * Real.sin φ) ^ (2 * k) / ((2 * k).factorial : ℝ))
      (∫ φ in (0 : ℝ)..(π / 2), Real.cosh (t * Real.sin φ)) := by
  have hsum : Summable (fun k : ℕ => |t| ^ (2 * k) / ((2 * k).factorial : ℝ)) :=
    (Real.hasSum_cosh |t|).summable
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun φ : ℝ => (t * Real.sin φ) ^ (2 * k) / ((2 * k).factorial : ℝ))
      (volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) := by
    intro k
    have h : Continuous (fun φ : ℝ => (t * Real.sin φ) ^ (2 * k) / ((2 * k).factorial : ℝ)) := by
      fun_prop
    exact h.aestronglyMeasurable
  have hbound : ∀ k : ℕ, ∀ᵐ φ ∂(volume : Measure ℝ), φ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ‖(t * Real.sin φ) ^ (2 * k) / ((2 * k).factorial : ℝ)‖
        ≤ |t| ^ (2 * k) / ((2 * k).factorial : ℝ) := by
    intro k
    refine Filter.Eventually.of_forall (fun φ _ => ?_)
    have h1 : |t * Real.sin φ| ≤ |t| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg t) (Real.abs_sin_le_one φ)
    have h2 : |t * Real.sin φ| ^ (2 * k) ≤ |t| ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg _) h1 (2 * k)
    have h3 : (0 : ℝ) < ((2 * k).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos h3]
    exact div_le_div_of_nonneg_right h2 h3.le
  have hsummable : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      Summable (fun k : ℕ => |t| ^ (2 * k) / ((2 * k).factorial : ℝ)) :=
    Filter.Eventually.of_forall (fun _ _ => hsum)
  have hbi : IntervalIntegrable
      (fun _ : ℝ => ∑' k : ℕ, |t| ^ (2 * k) / ((2 * k).factorial : ℝ)) volume (0 : ℝ) (π / 2) :=
    intervalIntegrable_const
  have hlim : ∀ᵐ φ ∂(volume : Measure ℝ), φ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      HasSum (fun k : ℕ => (t * Real.sin φ) ^ (2 * k) / ((2 * k).factorial : ℝ))
        (Real.cosh (t * Real.sin φ)) :=
    Filter.Eventually.of_forall (fun φ _ => Real.hasSum_cosh (t * Real.sin φ))
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun (k : ℕ) (_ : ℝ) => |t| ^ (2 * k) / ((2 * k).factorial : ℝ)) hmeas hbound hsummable hbi hlim

/-- One term: `(2/π) ∫₀^{π/2} (t sin φ)^{2k}/(2k)! dφ = (t/2)^{2k}/(k!)²`. -/
theorem I0_series_term (t : ℝ) (k : ℕ) :
    2 / π * (∫ φ in (0 : ℝ)..(π / 2), (t * Real.sin φ) ^ (2 * k) / ((2 * k).factorial : ℝ))
      = (t / 2) ^ (2 * k) / ((k.factorial : ℝ) ^ 2) := by
  have hfun : (fun φ : ℝ => (t * Real.sin φ) ^ (2 * k) / ((2 * k).factorial : ℝ))
      = fun φ : ℝ => t ^ (2 * k) / ((2 * k).factorial : ℝ) * Real.sin φ ^ (2 * k) := by
    funext φ
    rw [mul_pow]
    ring
  have hmul : (∫ φ in (0 : ℝ)..(π / 2), t ^ (2 * k) / ((2 * k).factorial : ℝ) * Real.sin φ ^ (2 * k))
      = t ^ (2 * k) / ((2 * k).factorial : ℝ) * ∫ φ in (0 : ℝ)..(π / 2), Real.sin φ ^ (2 * k) :=
    intervalIntegral.integral_const_mul _ _
  rw [hfun, hmul]
  have hW := integral_sin_pow_even_half k
  have hP : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  have hF : ((2 * k).factorial : ℝ) * ((2 * k).factorial : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * k)))
  have hq : (4 : ℝ) ^ k * ((4 : ℝ) ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero k (by norm_num))
  have hf : ((k.factorial : ℝ) ^ 2) * ((k.factorial : ℝ) ^ 2)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)))
  have hz : (t / 2) ^ (2 * k) = t ^ (2 * k) * ((4 : ℝ) ^ k)⁻¹ := by
    rw [div_pow, pow_mul (2 : ℝ) 2 k, div_eq_mul_inv (t ^ (2 * k)) (((2 : ℝ) ^ 2) ^ k)]
    norm_num
  rw [hz]
  linear_combination (t ^ (2 * k))
    * (2 * π⁻¹ * ((2 * k).factorial : ℝ)⁻¹ * ((4 : ℝ) ^ k)⁻¹ * ((k.factorial : ℝ) ^ 2)⁻¹ * hW
      - 2 * π⁻¹ * ((2 * k).factorial : ℝ)⁻¹ * (∫ x in (0 : ℝ)..(π / 2), Real.sin x ^ (2 * k))
          * (k.factorial : ℝ) ^ 2 * ((k.factorial : ℝ) ^ 2)⁻¹ * hq
      - 2 * π⁻¹ * ((2 * k).factorial : ℝ)⁻¹ * (∫ x in (0 : ℝ)..(π / 2), Real.sin x ^ (2 * k)) * hf
      + ((4 : ℝ) ^ k)⁻¹ * ((k.factorial : ℝ) ^ 2)⁻¹ * ((2 * k).factorial : ℝ)⁻¹
          * ((2 * k).factorial : ℝ) * hP
      + ((4 : ℝ) ^ k)⁻¹ * ((k.factorial : ℝ) ^ 2)⁻¹ * hF)

/-- **`I₀(t) = (2/π) ∫₀^{π/2} cosh(t sin φ) dφ`.** -/
theorem besselI0_eq_integral (t : ℝ) :
    besselI0 t = 2 / π * ∫ φ in (0 : ℝ)..(π / 2), Real.cosh (t * Real.sin φ) := by
  have h := (hasSum_integral_cosh_mul_sin t).mul_left (2 / π)
  have hterm : (fun k : ℕ => 2 / π * ∫ φ in (0 : ℝ)..(π / 2),
      (t * Real.sin φ) ^ (2 * k) / ((2 * k).factorial : ℝ))
      = fun k : ℕ => (t / 2) ^ (2 * k) / ((k.factorial : ℝ) ^ 2) := funext (I0_series_term t)
  rw [hterm] at h
  unfold besselI0
  exact h.tsum_eq

/-- `∫_{-π/2}^{π/2} e^{t sin φ} dφ = 2 ∫₀^{π/2} cosh(t sin φ) dφ`. -/
theorem integral_exp_mul_sin_symm (t : ℝ) :
    (∫ φ in (-(π / 2))..(π / 2), Real.exp (t * Real.sin φ))
      = 2 * ∫ φ in (0 : ℝ)..(π / 2), Real.cosh (t * Real.sin φ) := by
  have hc : Continuous (fun φ : ℝ => Real.exp (t * Real.sin φ)) := by fun_prop
  have hc2 : Continuous (fun φ : ℝ => Real.exp (-(t * Real.sin φ))) := by fun_prop
  have hadd : (∫ φ in (-(π / 2))..(0 : ℝ), Real.exp (t * Real.sin φ))
      + (∫ φ in (0 : ℝ)..(π / 2), Real.exp (t * Real.sin φ))
      = ∫ φ in (-(π / 2))..(π / 2), Real.exp (t * Real.sin φ) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-(π / 2)) 0) (hc.intervalIntegrable 0 (π / 2))
  have hneg0 : (∫ φ in (0 : ℝ)..(π / 2), Real.exp (t * Real.sin (-φ)))
      = ∫ φ in (-(π / 2))..(-0 : ℝ), Real.exp (t * Real.sin φ) :=
    intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π / 2)
      (fun φ : ℝ => Real.exp (t * Real.sin φ))
  have hneg : (∫ φ in (0 : ℝ)..(π / 2), Real.exp (-(t * Real.sin φ)))
      = ∫ φ in (-(π / 2))..(0 : ℝ), Real.exp (t * Real.sin φ) := by
    rw [neg_zero] at hneg0
    rw [← hneg0]
    refine intervalIntegral.integral_congr (fun φ _ => ?_)
    show Real.exp (-(t * Real.sin φ)) = Real.exp (t * Real.sin (-φ))
    rw [Real.sin_neg, mul_neg]
  have hsum : (∫ φ in (0 : ℝ)..(π / 2), (Real.exp (t * Real.sin φ) + Real.exp (-(t * Real.sin φ))))
      = (∫ φ in (0 : ℝ)..(π / 2), Real.exp (t * Real.sin φ))
        + ∫ φ in (0 : ℝ)..(π / 2), Real.exp (-(t * Real.sin φ)) :=
    intervalIntegral.integral_add (hc.intervalIntegrable 0 (π / 2)) (hc2.intervalIntegrable 0 (π / 2))
  have hcosh : (∫ φ in (0 : ℝ)..(π / 2), Real.cosh (t * Real.sin φ))
      = 1 / 2 * ∫ φ in (0 : ℝ)..(π / 2),
          (Real.exp (t * Real.sin φ) + Real.exp (-(t * Real.sin φ))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun φ _ => ?_)
    show Real.cosh (t * Real.sin φ)
      = 1 / 2 * (Real.exp (t * Real.sin φ) + Real.exp (-(t * Real.sin φ)))
    rw [Real.cosh_eq]
    ring
  rw [← hadd, ← hneg, hcosh, hsum]
  ring

/-- `I₀(t) = π⁻¹ ∫_{-π/2}^{π/2} e^{t sin φ} dφ`. -/
theorem besselI0_eq_poisson (t : ℝ) :
    besselI0 t = π⁻¹ * ∫ φ in (-(π / 2))..(π / 2), Real.exp (t * Real.sin φ) := by
  rw [besselI0_eq_integral, integral_exp_mul_sin_symm]
  ring

/-! ## `I₀(t) e^{-t}` as a Laplace transform (`s = 1 - sin φ`) -/

/-- The density of `I₀(t) e^{-t}`: `ρ_I(s) = 1/(π √(s(2-s)))`. -/
noncomputable def rhoI (s : ℝ) : ℝ := (π * Real.sqrt (s * (2 - s)))⁻¹

/-- The density of `K₀(t) e^{t}`: `ρ_K(r) = 1/√(r(r+2))`. -/
noncomputable def rhoK (r : ℝ) : ℝ := (Real.sqrt (r * (r + 2)))⁻¹

theorem image_one_sub_sin :
    (fun φ : ℝ => 1 - Real.sin φ) '' Set.Ioo (-(π / 2)) (π / 2) = Set.Ioo (0 : ℝ) 2 := by
  ext s
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    have h1 : Real.sin φ < Real.sin (π / 2) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two hφ.1.le le_rfl hφ.2
    have h2 : Real.sin (-(π / 2)) < Real.sin φ :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two le_rfl hφ.2.le hφ.1
    rw [Real.sin_pi_div_two] at h1
    rw [Real.sin_neg, Real.sin_pi_div_two] at h2
    show 1 - Real.sin φ ∈ Set.Ioo (0 : ℝ) 2
    exact ⟨by linarith, by linarith⟩
  · intro hs
    have h0 : 0 < s := hs.1
    have h2 : s < 2 := hs.2
    refine ⟨Real.arcsin (1 - s),
      ⟨Real.neg_pi_div_two_lt_arcsin.mpr (by linarith), Real.arcsin_lt_pi_div_two.mpr (by linarith)⟩,
      ?_⟩
    show 1 - Real.sin (Real.arcsin (1 - s)) = s
    rw [Real.sin_arcsin (by linarith) (by linarith)]
    ring

theorem injOn_one_sub_sin :
    Set.InjOn (fun φ : ℝ => 1 - Real.sin φ) (Set.Ioo (-(π / 2)) (π / 2)) := by
  intro a ha b hb hab
  have e : 1 - Real.sin a = 1 - Real.sin b := hab
  exact Real.injOn_sin (Set.Ioo_subset_Icc_self ha) (Set.Ioo_subset_Icc_self hb) (by linarith)

theorem hasDerivWithinAt_one_sub_sin :
    ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2),
      HasDerivWithinAt (fun φ : ℝ => 1 - Real.sin φ) (-Real.cos φ) (Set.Ioo (-(π / 2)) (π / 2)) φ := by
  intro φ _
  have h := (Real.hasDerivAt_sin φ).const_sub 1
  exact h.hasDerivWithinAt

/-- The integrand after `s = 1 - sin φ`. -/
theorem laplace_I0_pt (t : ℝ) {φ : ℝ} (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    |-Real.cos φ| * (Real.exp (-t * (1 - Real.sin φ)) * rhoI (1 - Real.sin φ))
      = Real.exp (-t) * π⁻¹ * Real.exp (t * Real.sin φ) := by
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo hφ
  have hsq : (1 - Real.sin φ) * (2 - (1 - Real.sin φ)) = Real.cos φ ^ 2 := by
    linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq φ
  have he : Real.exp (-t * (1 - Real.sin φ)) = Real.exp (-t) * Real.exp (t * Real.sin φ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hci : Real.cos φ * (Real.cos φ)⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  unfold rhoI
  rw [hsq, Real.sqrt_sq hc.le, abs_neg, abs_of_pos hc, he, mul_inv]
  linear_combination (Real.exp (-t) * Real.exp (t * Real.sin φ) * π⁻¹) * hci

/-- **`I₀(t) e^{-t} = ∫₀² e^{-ts} ρ_I(s) ds`.** -/
theorem laplace_I0 (t : ℝ) :
    besselI0 t * Real.exp (-t) = ∫ s in Set.Ioo (0 : ℝ) 2, Real.exp (-t * s) * rhoI s := by
  have hcv := integral_image_eq_integral_abs_deriv_smul (f' := fun φ : ℝ => -Real.cos φ)
    measurableSet_Ioo hasDerivWithinAt_one_sub_sin injOn_one_sub_sin
    (fun s : ℝ => Real.exp (-t * s) * rhoI s)
  rw [image_one_sub_sin] at hcv
  simp only [smul_eq_mul] at hcv
  have hcv' : (∫ s in Set.Ioo (0 : ℝ) 2, Real.exp (-t * s) * rhoI s)
      = ∫ φ in Set.Ioo (-(π / 2)) (π / 2),
          |-Real.cos φ| * (Real.exp (-t * (1 - Real.sin φ)) * rhoI (1 - Real.sin φ)) := hcv
  have hpt : (∫ φ in Set.Ioo (-(π / 2)) (π / 2),
      |-Real.cos φ| * (Real.exp (-t * (1 - Real.sin φ)) * rhoI (1 - Real.sin φ)))
      = ∫ φ in Set.Ioo (-(π / 2)) (π / 2), Real.exp (-t) * π⁻¹ * Real.exp (t * Real.sin φ) :=
    setIntegral_congr_fun measurableSet_Ioo (fun φ hφ => laplace_I0_pt t hφ)
  have hle : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  have hint : (∫ φ in (-(π / 2))..(π / 2), Real.exp (t * Real.sin φ))
      = ∫ φ in Set.Ioo (-(π / 2)) (π / 2), Real.exp (t * Real.sin φ) := by
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
  rw [hcv', hpt, integral_const_mul, ← hint, besselI0_eq_poisson]
  ring

theorem integrableOn_laplace_I0 (t : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-t * s) * rhoI s) (Set.Ioo (0 : ℝ) 2) := by
  have hcont : Continuous (fun φ : ℝ => Real.exp (-t) * π⁻¹ * Real.exp (t * Real.sin φ)) := by
    fun_prop
  have hI : IntegrableOn (fun φ : ℝ => Real.exp (-t) * π⁻¹ * Real.exp (t * Real.sin φ))
      (Set.Ioo (-(π / 2)) (π / 2)) :=
    (hcont.integrableOn_Icc (a := -(π / 2)) (b := π / 2)).mono_set Set.Ioo_subset_Icc_self
  have hI2 : IntegrableOn (fun φ : ℝ => |-Real.cos φ| • (Real.exp (-t * (1 - Real.sin φ))
      * rhoI (1 - Real.sin φ))) (Set.Ioo (-(π / 2)) (π / 2)) := by
    refine hI.congr_fun (fun φ hφ => ?_) measurableSet_Ioo
    show Real.exp (-t) * π⁻¹ * Real.exp (t * Real.sin φ)
      = |-Real.cos φ| • (Real.exp (-t * (1 - Real.sin φ)) * rhoI (1 - Real.sin φ))
    rw [smul_eq_mul, laplace_I0_pt t hφ]
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (f' := fun φ : ℝ => -Real.cos φ)
    measurableSet_Ioo hasDerivWithinAt_one_sub_sin injOn_one_sub_sin
    (fun s : ℝ => Real.exp (-t * s) * rhoI s)).mpr hI2
  rw [image_one_sub_sin] at h
  exact h

/-! ## `K₀(t) e^{t}` as a Laplace transform (`r = cosh u - 1`) -/

theorem image_cosh_sub_one :
    (fun u : ℝ => Real.cosh u - 1) '' Set.Ioi 0 = Set.Ioi (0 : ℝ) := by
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu0 : (0 : ℝ) < u := hu
    have h : Real.cosh 0 < Real.cosh u :=
      Real.cosh_lt_cosh.mpr (by rw [abs_zero, abs_of_pos hu0]; exact hu0)
    rw [Real.cosh_zero] at h
    show (0 : ℝ) < Real.cosh u - 1
    linarith
  · intro hr
    have hr0 : (0 : ℝ) < r := hr
    have hpos : (0 : ℝ) < r * (r + 2) := mul_pos hr0 (by linarith)
    refine ⟨Real.arsinh (Real.sqrt (r * (r + 2))),
      Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr hpos), ?_⟩
    show Real.cosh (Real.arsinh (Real.sqrt (r * (r + 2)))) - 1 = r
    rw [Real.cosh_arsinh, Real.sq_sqrt hpos.le]
    have e : 1 + r * (r + 2) = (r + 1) ^ 2 := by ring
    rw [e, Real.sqrt_sq (by linarith)]
    ring

theorem injOn_cosh_sub_one : Set.InjOn (fun u : ℝ => Real.cosh u - 1) (Set.Ioi 0) := by
  intro a ha b hb hab
  have e : Real.cosh a - 1 = Real.cosh b - 1 := hab
  have e2 : Real.cosh a = Real.cosh b := by linarith
  exact Real.cosh_strictMonoOn.injOn (Set.mem_Ici.mpr (le_of_lt ha))
    (Set.mem_Ici.mpr (le_of_lt hb)) e2

theorem hasDerivWithinAt_cosh_sub_one :
    ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => Real.cosh u - 1) (Real.sinh u) (Set.Ioi 0) u := by
  intro u _
  have h := (Real.hasDerivAt_cosh u).sub_const 1
  exact h.hasDerivWithinAt

/-- The integrand after `r = cosh u - 1`. -/
theorem laplace_K0_pt (t : ℝ) {u : ℝ} (hu : u ∈ Set.Ioi (0 : ℝ)) :
    |Real.sinh u| * (Real.exp (-t * (Real.cosh u - 1)) * rhoK (Real.cosh u - 1))
      = Real.exp t * Real.exp (-t * Real.cosh u) := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have hsq : (Real.cosh u - 1) * (Real.cosh u - 1 + 2) = Real.sinh u ^ 2 := by
    linear_combination Real.cosh_sq u
  have he : Real.exp (-t * (Real.cosh u - 1)) = Real.exp t * Real.exp (-t * Real.cosh u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsi : Real.sinh u * (Real.sinh u)⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  unfold rhoK
  rw [hsq, Real.sqrt_sq hs.le, abs_of_pos hs, he]
  linear_combination (Real.exp t * Real.exp (-t * Real.cosh u)) * hsi

/-- **`K₀(t) e^{t} = ∫₀^∞ e^{-tr} ρ_K(r) dr`.** -/
theorem laplace_K0 (t : ℝ) :
    besselK0 t * Real.exp t = ∫ r in Set.Ioi (0 : ℝ), Real.exp (-t * r) * rhoK r := by
  have hcv := integral_image_eq_integral_abs_deriv_smul (f' := fun u : ℝ => Real.sinh u)
    measurableSet_Ioi hasDerivWithinAt_cosh_sub_one injOn_cosh_sub_one
    (fun r : ℝ => Real.exp (-t * r) * rhoK r)
  rw [image_cosh_sub_one] at hcv
  simp only [smul_eq_mul] at hcv
  have hcv' : (∫ r in Set.Ioi (0 : ℝ), Real.exp (-t * r) * rhoK r)
      = ∫ u in Set.Ioi (0 : ℝ),
          |Real.sinh u| * (Real.exp (-t * (Real.cosh u - 1)) * rhoK (Real.cosh u - 1)) := hcv
  have hpt : (∫ u in Set.Ioi (0 : ℝ),
      |Real.sinh u| * (Real.exp (-t * (Real.cosh u - 1)) * rhoK (Real.cosh u - 1)))
      = ∫ u in Set.Ioi (0 : ℝ), Real.exp t * Real.exp (-t * Real.cosh u) :=
    setIntegral_congr_fun measurableSet_Ioi (fun u hu => laplace_K0_pt t hu)
  rw [hcv', hpt, integral_const_mul]
  unfold besselK0
  ring

theorem integrableOn_laplace_K0 {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun r : ℝ => Real.exp (-t * r) * rhoK r) (Set.Ioi (0 : ℝ)) := by
  have hk : Integrable (fun u : ℝ => kf t 0 u) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_kf ht 0 (by norm_num)
  have hI : IntegrableOn (fun u : ℝ => Real.exp t * kf t 0 u) (Set.Ioi (0 : ℝ)) :=
    hk.const_mul (Real.exp t)
  have hI2 : IntegrableOn (fun u : ℝ => |Real.sinh u| • (Real.exp (-t * (Real.cosh u - 1))
      * rhoK (Real.cosh u - 1))) (Set.Ioi (0 : ℝ)) := by
    refine hI.congr_fun (fun u hu => ?_) measurableSet_Ioi
    show Real.exp t * kf t 0 u
      = |Real.sinh u| • (Real.exp (-t * (Real.cosh u - 1)) * rhoK (Real.cosh u - 1))
    rw [smul_eq_mul, laplace_K0_pt t hu]
    unfold kf
    rw [pow_zero, mul_one]
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (f' := fun u : ℝ => Real.sinh u)
    measurableSet_Ioi hasDerivWithinAt_cosh_sub_one injOn_cosh_sub_one
    (fun r : ℝ => Real.exp (-t * r) * rhoK r)).mpr hI2
  rw [image_cosh_sub_one] at h
  exact h

end Tower.RV6
