import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselI
import Tower.RV6.BesselK
import Tower.RV6.BesselW

/-!
# Bounds for `I₀`, `I₁`, `K₀`, and the existence of `R₆,₂`

`R₆,₂ = (8/5) ∫₀^∞ I₀² I₁ K₀⁵ dt` (`Defs.lean`).  A Bochner integral of a non-integrable function
is `0` in Lean, so the integrability of the integrand is part of what `R₆,₂` means.

* `besselI0_le_cosh`, `besselI1_le_sinh`: termwise against the series of `cosh` and `sinh`,
  with `(2k)! ≤ 2^{2k} (k!)²` and `(2k+1)! ≤ 2^{2k+1} k! (k+1)!`.
* `besselK0_pos`, `besselI1_pos`.
* `besselI0_le_exp : I₀(t) ≤ e^t` and `besselI1_mul_besselK0_le : I₁(t) K₀(t) ≤ 1/t` for `t > 0`:
  both are read off the Wronskian `I₀ K₁ + I₁ K₀ = 1/t`, with `e^{-t} ≤ t K₁(t)`.
* `besselK0_le_of_one_le : K₀(t) ≤ e^{1-t} K₀(1)` for `t ≥ 1`.
* `besselK0_le_exp_mul_sqrt : K₀(t) ≤ e^{-t} √(π/(2t))` (`cosh u ≥ 1 + u²/2` and the Gaussian
  integral).
* `besselK0_le_log : K₀(t) ≤ log(t/2 + 1) - log(t/2)` (`e^{-x} ≤ 1/(1+x)`, `cosh u ≥ e^u/2`, and
  `∫₀^∞ e^{-u}/(c + e^{-u}) du = log(c+1) - log c`); `besselK0_le_one_add_log`.
* `integrableOn_R62_integrand`: `t ↦ I₀(t)² I₁(t) K₀(t)⁵` is integrable on `(0, ∞)`; `R62_pos`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## `I₀ ≤ cosh` and `I₁ ≤ sinh` -/

/-- `(2k)! ≤ 2^{2k} (k!)²`. -/
theorem fact_two_mul_le (k : ℕ) :
    ((2 * k).factorial : ℝ) ≤ 2 ^ (2 * k) * ((k.factorial : ℝ) * (k.factorial : ℝ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  have h2 : 2 * k - k = k := by omega
  rw [h2] at h
  have hc := Nat.choose_le_two_pow (2 * k) k
  have hN : (2 * k).factorial ≤ 2 ^ (2 * k) * (k.factorial * k.factorial) := by
    rw [← h, mul_assoc]
    exact Nat.mul_le_mul_right _ hc
  exact_mod_cast hN

/-- `(2k+1)! ≤ 2^{2k+1} k! (k+1)!`. -/
theorem fact_two_mul_add_one_le (k : ℕ) :
    ((2 * k + 1).factorial : ℝ)
      ≤ 2 ^ (2 * k + 1) * ((k.factorial : ℝ) * ((k + 1).factorial : ℝ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k + 1 by omega)
  have h2 : 2 * k + 1 - k = k + 1 := by omega
  rw [h2] at h
  have hc := Nat.choose_le_two_pow (2 * k + 1) k
  have hN : (2 * k + 1).factorial ≤ 2 ^ (2 * k + 1) * (k.factorial * (k + 1).factorial) := by
    rw [← h, mul_assoc]
    exact Nat.mul_le_mul_right _ hc
  exact_mod_cast hN

/-- The series of `I₀`, in the form of `Defs.lean`, is summable. -/
theorem summable_besselI0 (t : ℝ) :
    Summable fun k : ℕ => (t / 2) ^ (2 * k) / ((k.factorial : ℝ) ^ 2) := by
  refine (summable_fact_series cA_le (t / 2 * (t / 2))).congr (fun k => ?_)
  show cA k * (t / 2 * (t / 2)) ^ k = (t / 2) ^ (2 * k) / ((k.factorial : ℝ) ^ 2)
  have e : (t / 2) ^ (2 * k) = (t / 2 * (t / 2)) ^ k := by rw [pow_mul, pow_two]
  rw [e]
  unfold cA
  ring

/-- The series of `I₁`, in the form of `Defs.lean`, is summable. -/
theorem summable_besselI1 (t : ℝ) :
    Summable fun k : ℕ =>
      (t / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ)) := by
  refine ((summable_fact_series cB_le (t / 2 * (t / 2))).mul_left (t / 2)).congr (fun k => ?_)
  show t / 2 * (cB k * (t / 2 * (t / 2)) ^ k)
    = (t / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))
  have e : (t / 2) ^ (2 * k + 1) = (t / 2 * (t / 2)) ^ k * (t / 2) := by
    rw [pow_succ, pow_mul, pow_two]
  rw [e]
  unfold cB
  ring

theorem besselI0_term_le (t : ℝ) (k : ℕ) :
    (t / 2) ^ (2 * k) / ((k.factorial : ℝ) ^ 2) ≤ t ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  have hX : 0 ≤ t ^ (2 * k) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg t) k
  have hD : (0 : ℝ) < ((2 * k).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hE := fact_two_mul_le k
  have e : (t / 2) ^ (2 * k) / ((k.factorial : ℝ) ^ 2)
      = t ^ (2 * k) / (2 ^ (2 * k) * ((k.factorial : ℝ) * (k.factorial : ℝ))) := by
    rw [div_pow, div_div, pow_two]
  rw [e]
  exact div_le_div_of_nonneg_left hX hD hE

theorem besselI1_term_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (t / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))
      ≤ t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
  have hX : 0 ≤ t ^ (2 * k + 1) := pow_nonneg ht _
  have hD : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hE := fact_two_mul_add_one_le k
  have e : (t / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))
      = t ^ (2 * k + 1)
        / (2 ^ (2 * k + 1) * ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))) := by
    rw [div_pow, div_div]
  rw [e]
  exact div_le_div_of_nonneg_left hX hD hE

/-- `I₀(t) ≤ cosh t`, for every real `t`. -/
theorem besselI0_le_cosh (t : ℝ) : besselI0 t ≤ Real.cosh t := by
  have hc := Real.hasSum_cosh t
  have h : ∑' k : ℕ, (t / 2) ^ (2 * k) / ((k.factorial : ℝ) ^ 2)
      ≤ ∑' k : ℕ, t ^ (2 * k) / ((2 * k).factorial : ℝ) :=
    (summable_besselI0 t).tsum_le_tsum (besselI0_term_le t) hc.summable
  rw [hc.tsum_eq] at h
  unfold besselI0
  exact h

/-- `I₁(t) ≤ sinh t` for `t ≥ 0`. -/
theorem besselI1_le_sinh {t : ℝ} (ht : 0 ≤ t) : besselI1 t ≤ Real.sinh t := by
  have hc := Real.hasSum_sinh t
  have h : ∑' k : ℕ, (t / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))
      ≤ ∑' k : ℕ, t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) :=
    (summable_besselI1 t).tsum_le_tsum (besselI1_term_le ht) hc.summable
  rw [hc.tsum_eq] at h
  unfold besselI1
  exact h

/-! ## Positivity -/

/-- `K₀(t) > 0` for `t > 0`. -/
theorem besselK0_pos {t : ℝ} (ht : 0 < t) : 0 < besselK0 t := by
  have hi : Integrable (fun u : ℝ => kf t 0 u) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_kf ht 0 (by norm_num)
  have hnn : (0 : ℝ → ℝ) ≤ fun u : ℝ => kf t 0 u := fun u => kf_nonneg t 0 u
  have hsupp : Function.support (fun u : ℝ => kf t 0 u) = Set.univ :=
    Set.eq_univ_of_forall (fun u => Function.mem_support.mpr (kf_pos t 0 u).ne')
  have hmeas : 0 < (volume.restrict (Set.Ioi (0 : ℝ)))
      (Function.support (fun u : ℝ => kf t 0 u)) := by
    rw [hsupp, Measure.restrict_apply_univ, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  rw [besselK0_eq]
  exact (integral_pos_iff_support_of_nonneg hnn hi).mpr hmeas

theorem cB_zero : cB 0 = 1 := by
  first
    | simp [cB]
    | norm_num [cB, Nat.factorial]

/-- `B(x) ≥ 1` for `x ≥ 0`. -/
theorem one_le_Bser {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Bser x := by
  have h := (summable_fact_series cB_le x).le_tsum 0
    (fun j _ => mul_nonneg (cB_nonneg j) (pow_nonneg hx j))
  have h' : cB 0 * x ^ 0 ≤ Bser x := h
  rw [cB_zero, pow_zero, mul_one] at h'
  exact h'

/-- `I₁(t) > 0` for `t > 0`. -/
theorem besselI1_pos {t : ℝ} (ht : 0 < t) : 0 < besselI1 t := by
  rw [besselI1_eq]
  exact mul_pos (half_pos ht)
    (lt_of_lt_of_le one_pos (one_le_Bser (mul_self_nonneg (t / 2))))

/-! ## Read off the Wronskian -/

/-- `I₀(t) ≤ e^t` for `t > 0`. -/
theorem besselI0_le_exp {t : ℝ} (ht : 0 < t) : besselI0 t ≤ Real.exp t := by
  have hw := wronskian ht
  have h1 := exp_neg_le_mul_besselK1 ht
  have hI0 := besselI0_pos t
  have hnn : 0 ≤ besselI1 t * besselK0 t :=
    mul_nonneg (besselI1_nonneg ht.le) (besselK0_nonneg t)
  have h2 : besselI0 t * besselK1 t ≤ 1 / t := by linarith
  have h2' := mul_le_mul_of_nonneg_left h2 ht.le
  rw [mul_one_div_cancel ht.ne'] at h2'
  have h3 : besselI0 t * (t * besselK1 t) ≤ 1 := by
    have e : besselI0 t * (t * besselK1 t) = t * (besselI0 t * besselK1 t) := by ring
    rw [e]
    exact h2'
  have h4 : besselI0 t * Real.exp (-t) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left h1 hI0.le) h3
  have h5 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h6 := mul_le_mul_of_nonneg_right h4 (Real.exp_pos t).le
  calc besselI0 t = besselI0 t * (Real.exp (-t) * Real.exp t) := by rw [h5, mul_one]
    _ = besselI0 t * Real.exp (-t) * Real.exp t := by ring
    _ ≤ 1 * Real.exp t := h6
    _ = Real.exp t := one_mul _

/-- `I₁(t) K₀(t) ≤ 1/t` for `t > 0`. -/
theorem besselI1_mul_besselK0_le {t : ℝ} (ht : 0 < t) : besselI1 t * besselK0 t ≤ 1 / t := by
  have hw := wronskian ht
  have hnn : 0 ≤ besselI0 t * besselK1 t :=
    mul_nonneg (besselI0_pos t).le (besselK1_pos ht).le
  linarith

/-! ## Bounds for `K₀` -/

/-- `K₀(t) ≤ e^{1-t} K₀(1)` for `t ≥ 1`. -/
theorem besselK0_le_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    besselK0 t ≤ Real.exp (1 - t) * besselK0 1 := by
  have ht0 : 0 < t := by linarith
  have hpt : ∀ u : ℝ, kf t 0 u ≤ Real.exp (1 - t) * kf 1 0 u := by
    intro u
    show Real.exp (-t * Real.cosh u) * Real.cosh u ^ 0
      ≤ Real.exp (1 - t) * (Real.exp (-1 * Real.cosh u) * Real.cosh u ^ 0)
    have hc := Real.one_le_cosh u
    have hprod : 0 ≤ (t - 1) * (Real.cosh u - 1) :=
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hc)
    have hlin : -t * Real.cosh u ≤ 1 - t + -1 * Real.cosh u := by
      calc -t * Real.cosh u
          = (1 - t + -1 * Real.cosh u) - (t - 1) * (Real.cosh u - 1) := by ring
        _ ≤ 1 - t + -1 * Real.cosh u := sub_le_self _ hprod
    have hE : Real.exp (-t * Real.cosh u)
        ≤ Real.exp (1 - t) * Real.exp (-1 * Real.cosh u) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hlin
    rw [pow_zero, mul_one, mul_one]
    exact hE
  have hint : Integrable (fun u : ℝ => Real.exp (1 - t) * kf 1 0 u)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrable_kf one_pos 0 (by norm_num)).const_mul _
  have h : ∫ u in Set.Ioi (0 : ℝ), kf t 0 u
      ≤ ∫ u in Set.Ioi (0 : ℝ), Real.exp (1 - t) * kf 1 0 u :=
    integral_mono (integrable_kf ht0 0 (by norm_num)) hint hpt
  rw [integral_const_mul] at h
  rw [besselK0_eq t, besselK0_eq 1]
  exact h

/-- `cosh u ≥ 1 + u²/2` for `u ≥ 0`. -/
theorem one_add_sq_div_two_le_cosh {u : ℝ} (hu : 0 ≤ u) : 1 + u ^ 2 / 2 ≤ Real.cosh u := by
  have h1 := Real.cosh_two_mul (u / 2)
  have h2 := Real.cosh_sq (u / 2)
  have e : 2 * (u / 2) = u := by ring
  rw [e] at h1
  have h0 : (0 : ℝ) ≤ u / 2 := by linarith
  have h3 : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.mpr h0
  have h4 : (u / 2) ^ 2 ≤ Real.sinh (u / 2) ^ 2 := pow_le_pow_left₀ h0 h3 2
  have e2 : (u / 2) ^ 2 = u ^ 2 / 4 := by ring
  rw [e2] at h4
  linarith

/-- `K₀(t) ≤ e^{-t} · √(π/(t/2))/2`: the Gaussian integral, as Mathlib writes it. -/
theorem besselK0_le_gauss {t : ℝ} (ht : 0 < t) :
    besselK0 t ≤ Real.exp (-t) * (Real.sqrt (π / (t / 2)) / 2) := by
  have ht2 : 0 < t / 2 := half_pos ht
  have hk : IntegrableOn (fun u : ℝ => kf t 0 u) (Set.Ioi (0 : ℝ)) :=
    integrable_kf ht 0 (by norm_num)
  have hg0 : IntegrableOn (fun u : ℝ => Real.exp (-(t / 2) * u ^ 2)) (Set.Ioi (0 : ℝ)) :=
    (integrable_exp_neg_mul_sq ht2).integrableOn
  have hg : IntegrableOn (fun u : ℝ => Real.exp (-t) * Real.exp (-(t / 2) * u ^ 2))
      (Set.Ioi (0 : ℝ)) := Integrable.const_mul hg0 (Real.exp (-t))
  have hpt : ∀ u ∈ Set.Ioi (0 : ℝ),
      kf t 0 u ≤ Real.exp (-t) * Real.exp (-(t / 2) * u ^ 2) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hc := one_add_sq_div_two_le_cosh hu0.le
    have hm := mul_le_mul_of_nonneg_left hc ht.le
    have e0 : kf t 0 u = Real.exp (-(t * Real.cosh u)) := by
      show Real.exp (-t * Real.cosh u) * Real.cosh u ^ 0 = Real.exp (-(t * Real.cosh u))
      rw [pow_zero, mul_one, neg_mul]
    rw [e0, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have h : ∫ u in Set.Ioi (0 : ℝ), kf t 0 u
      ≤ ∫ u in Set.Ioi (0 : ℝ), Real.exp (-t) * Real.exp (-(t / 2) * u ^ 2) :=
    setIntegral_mono_on hk hg measurableSet_Ioi hpt
  rw [integral_const_mul, integral_gaussian_Ioi] at h
  rw [besselK0_eq]
  exact h

/-- `K₀(t) ≤ e^{-t} √(π/(2t))` for `t > 0`. -/
theorem besselK0_le_exp_mul_sqrt {t : ℝ} (ht : 0 < t) :
    besselK0 t ≤ Real.exp (-t) * Real.sqrt (π / (2 * t)) := by
  have h := besselK0_le_gauss ht
  have h4 : π / (t / 2) = 2 ^ 2 * (π / (2 * t)) := by
    rw [div_div_eq_mul_div, ← mul_div_assoc, div_eq_div_iff ht.ne' (mul_pos two_pos ht).ne']
    ring
  have e : Real.sqrt (π / (t / 2)) / 2 = Real.sqrt (π / (2 * t)) := by
    rw [h4, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [e] at h
  exact h

/-- `∫₀^∞ e^{-u}/(c + e^{-u}) du = log(c + 1) - log c` for `c > 0`. -/
theorem integral_logistic {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / (c + Real.exp (-u))) (Set.Ioi (0 : ℝ))
      ∧ ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) / (c + Real.exp (-u))
        = Real.log (c + 1) - Real.log c := by
  have hderiv : ∀ u ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => -Real.log (c + Real.exp (-y)))
        (Real.exp (-u) / (c + Real.exp (-u))) u := by
    intro u _
    have hpos : 0 < c + Real.exp (-u) := add_pos hc (Real.exp_pos _)
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-u) * (-1)) u :=
      ((hasDerivAt_id' u).neg).exp
    have h2 : HasDerivAt (fun y : ℝ => c + Real.exp (-y)) (Real.exp (-u) * (-1)) u :=
      h1.const_add c
    have h3 : HasDerivAt (fun y : ℝ => -Real.log (c + Real.exp (-y)))
        (-(Real.exp (-u) * (-1) / (c + Real.exp (-u)))) u := (h2.log hpos.ne').neg
    refine h3.congr_deriv ?_
    ring
  have hpos : ∀ u ∈ Set.Ioi (0 : ℝ), 0 ≤ Real.exp (-u) / (c + Real.exp (-u)) :=
    fun u _ => div_nonneg (Real.exp_pos _).le (add_pos hc (Real.exp_pos _)).le
  have hlim : Filter.Tendsto (fun y : ℝ => -Real.log (c + Real.exp (-y))) Filter.atTop
      (nhds (-Real.log c)) := by
    have h1 : Filter.Tendsto (fun y : ℝ => c + Real.exp (-y)) Filter.atTop (nhds (c + 0)) :=
      tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero
    rw [add_zero] at h1
    exact (h1.log hc.ne').neg
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  simp only [neg_zero, Real.exp_zero] at hval
  refine ⟨hint, ?_⟩
  rw [hval]
  ring

/-- `e^{-t cosh u} ≤ e^{-u}/(t/2 + e^{-u})`. -/
theorem kf_zero_le_logistic {t : ℝ} (ht : 0 < t) (u : ℝ) :
    kf t 0 u ≤ Real.exp (-u) / (t / 2 + Real.exp (-u)) := by
  have hE := Real.exp_pos u
  have hEn := Real.exp_pos (-u)
  have hEE : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hcosh : Real.exp u ≤ 2 * Real.cosh u := by
    rw [Real.cosh_eq]
    linarith
  have hx0 := mul_le_mul_of_nonneg_left hcosh (half_pos ht).le
  have hx : t / 2 * Real.exp u ≤ t * Real.cosh u := by
    have e : t / 2 * (2 * Real.cosh u) = t * Real.cosh u := by ring
    rw [e] at hx0
    exact hx0
  have h1 : t * Real.cosh u + 1 ≤ Real.exp (t * Real.cosh u) := Real.add_one_le_exp _
  have hpos : 0 < t / 2 * Real.exp u + 1 := add_pos (mul_pos (half_pos ht) hE) one_pos
  have h6 : Real.exp (-(t * Real.cosh u)) = 1 / Real.exp (t * Real.cosh u) := by
    rw [Real.exp_neg, one_div]
  have h2 : Real.exp (-(t * Real.cosh u)) ≤ 1 / (t / 2 * Real.exp u + 1) := by
    rw [h6]
    exact one_div_le_one_div_of_le hpos (by linarith)
  have h3 : 1 / (t / 2 * Real.exp u + 1) = Real.exp (-u) / (t / 2 + Real.exp (-u)) := by
    rw [div_eq_div_iff hpos.ne' (add_pos (half_pos ht) hEn).ne']
    linear_combination (-(t / 2)) * hEE
  have e0 : kf t 0 u = Real.exp (-(t * Real.cosh u)) := by
    show Real.exp (-t * Real.cosh u) * Real.cosh u ^ 0 = Real.exp (-(t * Real.cosh u))
    rw [pow_zero, mul_one, neg_mul]
  rw [e0, ← h3]
  exact h2

/-- `K₀(t) ≤ log(t/2 + 1) - log(t/2)` for `t > 0`. -/
theorem besselK0_le_log {t : ℝ} (ht : 0 < t) :
    besselK0 t ≤ Real.log (t / 2 + 1) - Real.log (t / 2) := by
  obtain ⟨hint, hval⟩ := integral_logistic (half_pos ht)
  have hk : IntegrableOn (fun u : ℝ => kf t 0 u) (Set.Ioi (0 : ℝ)) :=
    integrable_kf ht 0 (by norm_num)
  have h : ∫ u in Set.Ioi (0 : ℝ), kf t 0 u
      ≤ ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) / (t / 2 + Real.exp (-u)) :=
    setIntegral_mono_on hk hint measurableSet_Ioi (fun u _ => kf_zero_le_logistic ht u)
  rw [hval] at h
  rw [besselK0_eq]
  exact h

/-- `K₀(t) ≤ 1 + log(2/t)` for `0 < t ≤ 1`. -/
theorem besselK0_le_one_add_log {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    besselK0 t ≤ 1 + Real.log (2 / t) := by
  have h := besselK0_le_log ht
  have h1 : Real.log (t / 2 + 1) ≤ t / 2 + 1 - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have h2 : Real.log (t / 2) = Real.log t - Real.log 2 := Real.log_div ht.ne' two_ne_zero
  have h3 : Real.log (2 / t) = Real.log 2 - Real.log t := Real.log_div two_ne_zero ht.ne'
  linarith

/-! ## The integrand of `R₆,₂` -/

/-- `x⁵ ≤ 3125 eˣ` for `x ≥ 0`. -/
theorem pow_five_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 5 ≤ 3125 * Real.exp x := by
  have h1 : x / 5 + 1 ≤ Real.exp (x / 5) := Real.add_one_le_exp (x / 5)
  have h2 : x / 5 ≤ Real.exp (x / 5) := by linarith
  have h0 : (0 : ℝ) ≤ x / 5 := by linarith
  have h3 : (x / 5) ^ 5 ≤ Real.exp (x / 5) ^ 5 := pow_le_pow_left₀ h0 h2 5
  have h4 : Real.exp (x / 5) ^ 5 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    first
      | (push_cast; ring)
      | norm_num
  rw [h4] at h3
  have e : x ^ 5 = 3125 * (x / 5) ^ 5 := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h3 (by norm_num)

/-- `t K₀(t)⁵ ≤ 3125 (t + 2)` for `t > 0`. -/
theorem mul_besselK0_pow_five_le {t : ℝ} (ht : 0 < t) :
    t * besselK0 t ^ 5 ≤ 3125 * (t + 2) := by
  have ht2 : 0 < t / 2 := half_pos ht
  have ht21 : 0 < t / 2 + 1 := by linarith
  have hK := besselK0_le_log ht
  have hK0 := besselK0_nonneg t
  have hL0 : 0 ≤ Real.log (t / 2 + 1) - Real.log (t / 2) := le_trans hK0 hK
  have hexp : Real.exp (Real.log (t / 2 + 1) - Real.log (t / 2)) = (t / 2 + 1) / (t / 2) := by
    rw [Real.exp_sub, Real.exp_log ht21, Real.exp_log ht2]
  have h5 := pow_five_le_exp hL0
  rw [hexp] at h5
  have hK5 : besselK0 t ^ 5 ≤ (Real.log (t / 2 + 1) - Real.log (t / 2)) ^ 5 :=
    pow_le_pow_left₀ hK0 hK 5
  have h6 : besselK0 t ^ 5 ≤ 3125 * ((t / 2 + 1) / (t / 2)) := le_trans hK5 h5
  have h7 := mul_le_mul_of_nonneg_left h6 ht.le
  have hR : (t / 2 + 1) / (t / 2) * (t / 2) = t / 2 + 1 := div_mul_cancel₀ _ ht2.ne'
  have e : t * (3125 * ((t / 2 + 1) / (t / 2))) = 3125 * (t + 2) := by
    linear_combination 6250 * hR
  rw [e] at h7
  exact h7

/-- `B` is monotone on `[0, ∞)`. -/
theorem Bser_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : Bser x ≤ Bser y := by
  unfold Bser
  exact (summable_fact_series cB_le x).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy k) (cB_nonneg k))
    (summable_fact_series cB_le y)

/-- `I₁(t) ≤ t B(1)` for `0 ≤ t ≤ 1`. -/
theorem besselI1_le_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : besselI1 t ≤ t * Bser 1 := by
  have hs0 : 0 ≤ t / 2 * (t / 2) := mul_self_nonneg (t / 2)
  have hs1 : t / 2 * (t / 2) ≤ 1 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hB := Bser_mono hs0 hs1
  have hB1 : 0 ≤ Bser 1 := Bser_nonneg zero_le_one
  have h2 : t / 2 * Bser (t / 2 * (t / 2)) ≤ t / 2 * Bser 1 :=
    mul_le_mul_of_nonneg_left hB (by linarith)
  have h3 : 0 ≤ t * Bser 1 := mul_nonneg ht0 hB1
  have e : t / 2 * Bser 1 = t * Bser 1 / 2 := by ring
  rw [besselI1_eq]
  linarith

/-- For `t ≥ 1`: `I₀(t)² I₁(t) K₀(t)⁵ ≤ (e K₀(1))⁴ e^{-2t}`. -/
theorem R62_integrand_le {t : ℝ} (ht : 1 ≤ t) :
    besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5
      ≤ (Real.exp 1 * besselK0 1) ^ 4 * Real.exp (-(2 * t)) := by
  have ht0 : 0 < t := by linarith
  have hI0 := besselI0_le_exp ht0
  have hI0p := (besselI0_pos t).le
  have hIK := besselI1_mul_besselK0_le ht0
  have hK := besselK0_le_of_one_le ht
  have hK0 := besselK0_nonneg t
  have hI1 := besselI1_nonneg ht0.le
  have h1t : 1 / t ≤ 1 := by
    rw [div_le_iff₀ ht0]
    linarith
  have hIK1 : besselI1 t * besselK0 t ≤ 1 := le_trans hIK h1t
  have hIKnn : 0 ≤ besselI1 t * besselK0 t := mul_nonneg hI1 hK0
  have hsq : besselI0 t ^ 2 ≤ Real.exp t ^ 2 := pow_le_pow_left₀ hI0p hI0 2
  have hK4 : besselK0 t ^ 4 ≤ (Real.exp (1 - t) * besselK0 1) ^ 4 :=
    pow_le_pow_left₀ hK0 hK 4
  have hK4nn : 0 ≤ besselK0 t ^ 4 := pow_nonneg hK0 4
  have hE2nn : 0 ≤ Real.exp t ^ 2 := pow_nonneg (Real.exp_pos t).le 2
  have e1 : besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5
      = besselI0 t ^ 2 * (besselI1 t * besselK0 t) * besselK0 t ^ 4 := by ring
  have hexp : Real.exp t ^ 2 * (Real.exp (1 - t) * besselK0 1) ^ 4
      = (Real.exp 1 * besselK0 1) ^ 4 * Real.exp (-(2 * t)) := by
    have ha : Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) := by
      rw [sub_eq_add_neg, Real.exp_add]
    have hb : Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      first
        | (push_cast; ring)
        | norm_num
    have hc : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [ha, hb]
    linear_combination (Real.exp 1 ^ 4 * besselK0 1 ^ 4 * Real.exp (-t) ^ 2
      * (Real.exp t * Real.exp (-t) + 1)) * hc
  rw [e1, ← hexp]
  calc besselI0 t ^ 2 * (besselI1 t * besselK0 t) * besselK0 t ^ 4
      ≤ Real.exp t ^ 2 * 1 * besselK0 t ^ 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hsq hIK1 hIKnn hE2nn) hK4nn
    _ = Real.exp t ^ 2 * besselK0 t ^ 4 := by ring
    _ ≤ Real.exp t ^ 2 * (Real.exp (1 - t) * besselK0 1) ^ 4 :=
        mul_le_mul_of_nonneg_left hK4 hE2nn

/-- For `0 < t ≤ 1`: `I₀(t)² I₁(t) K₀(t)⁵ ≤ 9375 e² B(1)`. -/
theorem R62_integrand_le_of_le_one {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5 ≤ Real.exp 1 ^ 2 * Bser 1 * 9375 := by
  have hI0 := besselI0_le_exp ht0
  have hI0p := (besselI0_pos t).le
  have hE : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr ht1
  have hsq : besselI0 t ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ hI0p (le_trans hI0 hE) 2
  have hI1 := besselI1_le_mul ht0.le ht1
  have hI1p := besselI1_nonneg ht0.le
  have hK := mul_besselK0_pow_five_le ht0
  have hK5 : 0 ≤ besselK0 t ^ 5 := pow_nonneg (besselK0_nonneg t) 5
  have hB1 : 0 ≤ Bser 1 := Bser_nonneg zero_le_one
  have hE2 : 0 ≤ Real.exp 1 ^ 2 := pow_nonneg (Real.exp_pos 1).le 2
  have h1 : besselI1 t * besselK0 t ^ 5 ≤ t * Bser 1 * besselK0 t ^ 5 :=
    mul_le_mul_of_nonneg_right hI1 hK5
  have h2 : t * Bser 1 * besselK0 t ^ 5 = Bser 1 * (t * besselK0 t ^ 5) := by ring
  have hK' : t * besselK0 t ^ 5 ≤ 9375 := by linarith
  have h3 : Bser 1 * (t * besselK0 t ^ 5) ≤ Bser 1 * 9375 :=
    mul_le_mul_of_nonneg_left hK' hB1
  have h4 : besselI1 t * besselK0 t ^ 5 ≤ Bser 1 * 9375 := by
    rw [h2] at h1
    exact le_trans h1 h3
  have h5 : 0 ≤ besselI1 t * besselK0 t ^ 5 := mul_nonneg hI1p hK5
  calc besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5
      = besselI0 t ^ 2 * (besselI1 t * besselK0 t ^ 5) := by ring
    _ ≤ Real.exp 1 ^ 2 * (Bser 1 * 9375) := mul_le_mul hsq h4 h5 hE2
    _ = Real.exp 1 ^ 2 * Bser 1 * 9375 := by ring

theorem R62_integrand_pos {t : ℝ} (ht : 0 < t) :
    0 < besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5 :=
  mul_pos (mul_pos (pow_pos (besselI0_pos t) 2) (besselI1_pos ht)) (pow_pos (besselK0_pos ht) 5)

theorem continuousOn_besselK0 : ContinuousOn besselK0 (Set.Ioi (0 : ℝ)) :=
  fun t ht =>
    (hasDerivAt_besselK0 (show (0 : ℝ) < t from ht)).continuousAt.continuousWithinAt

theorem continuousOn_R62_integrand :
    ContinuousOn (fun t : ℝ => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5)
      (Set.Ioi (0 : ℝ)) :=
  (((continuous_besselI0.pow 2).mul continuous_besselI1).continuousOn).mul
    (continuousOn_besselK0.pow 5)

/-- The integrand of `R₆,₂` is integrable on `(0, ∞)`. -/
theorem integrableOn_R62_integrand :
    IntegrableOn (fun t : ℝ => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5)
      (Set.Ioi (0 : ℝ)) := by
  have hcont := continuousOn_R62_integrand
  have h01 : IntegrableOn (fun t : ℝ => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5)
      (Set.Ioc (0 : ℝ) 1) := by
    have hm : AEStronglyMeasurable
        (fun t : ℝ => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    refine IntegrableOn.of_bound measure_Ioc_lt_top hm (Real.exp 1 ^ 2 * Bser 1 * 9375)
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (R62_integrand_pos ht.1).le]
    exact R62_integrand_le_of_le_one ht.1 ht.2
  have h1 : IntegrableOn (fun t : ℝ => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5)
      (Set.Ioi (1 : ℝ)) := by
    have hm : AEStronglyMeasurable
        (fun t : ℝ => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5)
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (hcont.mono (Set.Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).aestronglyMeasurable
        measurableSet_Ioi
    have hb : Integrable (fun t : ℝ => (Real.exp 1 * besselK0 1) ^ 4 * Real.exp (-t))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      Integrable.const_mul (integrableOn_exp_neg_Ioi 1) ((Real.exp 1 * besselK0 1) ^ 4)
    show Integrable (fun t : ℝ => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5)
      (volume.restrict (Set.Ioi (1 : ℝ)))
    refine Integrable.mono' hb hm
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have h := R62_integrand_le ht1.le
    have hexp : Real.exp (-(2 * t)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    have hC : 0 ≤ (Real.exp 1 * besselK0 1) ^ 4 :=
      pow_nonneg (mul_nonneg (Real.exp_pos 1).le (besselK0_nonneg 1)) 4
    rw [Real.norm_eq_abs, abs_of_nonneg (R62_integrand_pos ht0).le]
    exact le_trans h (mul_le_mul_of_nonneg_left hexp hC)
  have hu := h01.union h1
  rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at hu
  exact hu

theorem R62_integral_pos :
    0 < ∫ t in Set.Ioi (0 : ℝ), besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5 := by
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun t : ℝ => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5 :=
    ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => (R62_integrand_pos (show (0 : ℝ) < t from ht)).le)
  have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support
      (fun t : ℝ => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    exact Function.mem_support.mpr (R62_integrand_pos ht').ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn integrableOn_R62_integrand,
    Set.inter_eq_self_of_subset_right hsub, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- **`R₆,₂ > 0`.** -/
theorem R62_pos : 0 < R62 := by
  unfold R62
  exact mul_pos (by norm_num) R62_integral_pos

end Tower.RV6
