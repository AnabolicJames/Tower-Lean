import Mathlib
import Tower.RV6.Defs

/-!
# The modified Bessel functions `K₀`, `K₁` as integrals

`besselK0 t = ∫₀^∞ exp(-t cosh u) du` (`Defs.lean`), and `besselK1 t = ∫₀^∞ exp(-t cosh u) cosh u du`.

* `kf t m u = exp(-t cosh u) cosh^m u`; `kf_le`: for `m ≤ 2` it is at most `(54/t³) e^{-u}`,
  so it is integrable on `(0, ∞)` (`integrable_kf`).
* `hasDerivAt_Kint`: `d/dt ∫₀^∞ kf t m = -∫₀^∞ kf t (m+1)` for `m ≤ 1` (differentiation under
  the integral sign).
* `hasDerivAt_besselK0 : K₀' = -K₁`; `hasDerivAt_besselK1 : K₁' = -∫₀^∞ exp(-t cosh u) cosh² u du`.
* `besselK0_le_besselK1`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `e^{-x} ≤ 27/x³` for `x > 0`. -/
theorem exp_neg_le_cube {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 27 / x ^ 3 := by
  have h1 : x / 3 + 1 ≤ Real.exp (x / 3) := Real.add_one_le_exp (x / 3)
  have h2 : x / 3 ≤ Real.exp (x / 3) := by linarith
  have h0 : (0 : ℝ) ≤ x / 3 := by linarith
  have h3 : (x / 3) ^ 3 ≤ Real.exp (x / 3) ^ 3 := pow_le_pow_left₀ h0 h2 3
  have h4 : Real.exp (x / 3) ^ 3 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    first
      | (push_cast; ring)
      | norm_num
  rw [h4] at h3
  have h5 : (0 : ℝ) < (x / 3) ^ 3 := pow_pos (by linarith) 3
  have h6 : Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
  rw [h6]
  calc 1 / Real.exp x ≤ 1 / (x / 3) ^ 3 := one_div_le_one_div_of_le h5 h3
    _ = 27 / x ^ 3 := by ring

/-- `exp(-t cosh u) cosh² u ≤ (54/t³) e^{-u}`. -/
theorem K_dom {t : ℝ} (ht : 0 < t) (u : ℝ) :
    Real.exp (-t * Real.cosh u) * Real.cosh u ^ 2 ≤ 54 / t ^ 3 * Real.exp (-u) := by
  have hy : 0 < Real.cosh u := Real.cosh_pos u
  have hE := exp_neg_le_cube (mul_pos ht hy)
  have hEpos := Real.exp_pos u
  have hEu : Real.exp u ≤ 2 * Real.cosh u := by
    rw [Real.cosh_eq]
    have hneg := Real.exp_pos (-u)
    linarith
  have hinv : 1 / Real.cosh u ≤ 2 * Real.exp (-u) := by
    rw [div_le_iff₀ hy, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_right hEu (inv_nonneg.mpr hEpos.le)
    rw [mul_inv_cancel₀ hEpos.ne'] at h
    calc (1 : ℝ) ≤ 2 * Real.cosh u * (Real.exp u)⁻¹ := h
      _ = 2 * (Real.exp u)⁻¹ * Real.cosh u := by ring
  have e1 : -t * Real.cosh u = -(t * Real.cosh u) := by ring
  have e2 : 27 / (t * Real.cosh u) ^ 3 * Real.cosh u ^ 2 = 27 / t ^ 3 * (1 / Real.cosh u) := by
    rw [div_mul_eq_mul_div, div_mul_div_comm,
      div_eq_div_iff (pow_pos (mul_pos ht hy) 3).ne' (mul_pos (pow_pos ht 3) hy).ne']
    ring
  have h27 : (0 : ℝ) ≤ 27 / t ^ 3 := (div_pos (by norm_num) (pow_pos ht 3)).le
  rw [e1]
  calc Real.exp (-(t * Real.cosh u)) * Real.cosh u ^ 2
      ≤ 27 / (t * Real.cosh u) ^ 3 * Real.cosh u ^ 2 :=
        mul_le_mul_of_nonneg_right hE (pow_nonneg hy.le 2)
    _ = 27 / t ^ 3 * (1 / Real.cosh u) := e2
    _ ≤ 27 / t ^ 3 * (2 * Real.exp (-u)) := mul_le_mul_of_nonneg_left hinv h27
    _ = 54 / t ^ 3 * Real.exp (-u) := by ring

/-! ## The kernels `exp(-t cosh u) cosh^m u` -/

/-- `exp(-t cosh u) cosh^m u`. -/
noncomputable def kf (t : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-t * Real.cosh u) * Real.cosh u ^ m

theorem kf_pos (t : ℝ) (m : ℕ) (u : ℝ) : 0 < kf t m u :=
  mul_pos (Real.exp_pos _) (pow_pos (Real.cosh_pos u) m)

theorem kf_nonneg (t : ℝ) (m : ℕ) (u : ℝ) : 0 ≤ kf t m u := (kf_pos t m u).le

theorem continuous_kf (t : ℝ) (m : ℕ) : Continuous fun u : ℝ => kf t m u := by
  unfold kf
  exact (Real.continuous_exp.comp (continuous_const.mul Real.continuous_cosh)).mul
    (Real.continuous_cosh.pow m)

/-- The kernel decreases in `t`. -/
theorem kf_anti {s t : ℝ} (h : s ≤ t) (m : ℕ) (u : ℝ) : kf t m u ≤ kf s m u := by
  unfold kf
  have hc := Real.cosh_pos u
  have h1 := mul_le_mul_of_nonneg_right h hc.le
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (pow_nonneg hc.le m)

/-- The kernel increases in `m`. -/
theorem kf_mono_pow (t : ℝ) {m n : ℕ} (h : m ≤ n) (u : ℝ) : kf t m u ≤ kf t n u := by
  unfold kf
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Real.one_le_cosh u) h) (Real.exp_pos _).le

theorem kf_le {t : ℝ} (ht : 0 < t) (m : ℕ) (hm : m ≤ 2) (u : ℝ) :
    kf t m u ≤ 54 / t ^ 3 * Real.exp (-u) :=
  le_trans (kf_mono_pow t hm u) (K_dom ht u)

theorem integrable_kf {t : ℝ} (ht : 0 < t) (m : ℕ) (hm : m ≤ 2) :
    Integrable (fun u : ℝ => kf t m u) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hb : Integrable (fun u : ℝ => 54 / t ^ 3 * Real.exp (-u))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) (54 / t ^ 3)
  refine hb.mono' (continuous_kf t m).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (kf_nonneg t m u)]
  exact kf_le ht m hm u

/-- Differentiation under the integral sign. -/
theorem hasDerivAt_Kint {t : ℝ} (ht : 0 < t) (m : ℕ) (hm : m + 1 ≤ 2) :
    HasDerivAt (fun x : ℝ => ∫ u in Set.Ioi (0 : ℝ), kf x m u)
      (-∫ u in Set.Ioi (0 : ℝ), kf t (m + 1) u) t := by
  have ht2 : 0 < t / 2 := by linarith
  have hs : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun u : ℝ => kf x m u)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun x => (continuous_kf x m).aestronglyMeasurable
  have hbound : ∀ u : ℝ, ∀ x ∈ Set.Ioi (t / 2),
      ‖-kf x (m + 1) u‖ ≤ 54 / (t / 2) ^ 3 * Real.exp (-u) := by
    intro u x hx
    have hx' : t / 2 < x := hx
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (kf_nonneg x (m + 1) u)]
    exact le_trans (kf_anti hx'.le (m + 1) u) (kf_le ht2 (m + 1) hm u)
  have hdiff : ∀ u : ℝ, ∀ x ∈ Set.Ioi (t / 2),
      HasDerivAt (fun y : ℝ => kf y m u) (-kf x (m + 1) u) x := by
    intro u x _
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y * Real.cosh u))
        (Real.exp (-x * Real.cosh u) * (-1 * Real.cosh u)) x :=
      (((hasDerivAt_id' x).neg).mul_const (Real.cosh u)).exp
    have h2 := h1.mul_const (Real.cosh u ^ m)
    refine h2.congr_deriv ?_
    unfold kf
    rw [pow_succ]
    ring
  have hbi : Integrable (fun u : ℝ => 54 / (t / 2) ^ 3 * Real.exp (-u))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi 0) (54 / (t / 2) ^ 3)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun x u => kf x m u) (F' := fun x u => -kf x (m + 1) u)
    (bound := fun u => 54 / (t / 2) ^ 3 * Real.exp (-u)) hs
    (Filter.Eventually.of_forall hmeas) (integrable_kf ht m (by omega))
    ((continuous_kf t (m + 1)).neg.aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound) hbi
    (Filter.Eventually.of_forall hdiff)
  have h3 : HasDerivAt (fun x : ℝ => ∫ u in Set.Ioi (0 : ℝ), kf x m u)
      (∫ u in Set.Ioi (0 : ℝ), -kf t (m + 1) u) t := key.2
  rw [integral_neg] at h3
  exact h3

/-! ## `K₀` and `K₁` -/

/-- `K₁(t) = ∫₀^∞ exp(-t cosh u) cosh u du`. -/
noncomputable def besselK1 (t : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), Real.exp (-t * Real.cosh u) * Real.cosh u

theorem besselK0_eq (t : ℝ) : besselK0 t = ∫ u in Set.Ioi (0 : ℝ), kf t 0 u := by
  unfold besselK0 kf
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  show Real.exp (-t * Real.cosh u) = Real.exp (-t * Real.cosh u) * Real.cosh u ^ 0
  rw [pow_zero, mul_one]

theorem besselK1_eq (t : ℝ) : besselK1 t = ∫ u in Set.Ioi (0 : ℝ), kf t 1 u := by
  unfold besselK1 kf
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  show Real.exp (-t * Real.cosh u) * Real.cosh u
    = Real.exp (-t * Real.cosh u) * Real.cosh u ^ 1
  rw [pow_one]

/-- `K₀' = -K₁`. -/
theorem hasDerivAt_besselK0 {t : ℝ} (ht : 0 < t) : HasDerivAt besselK0 (-besselK1 t) t := by
  have h := hasDerivAt_Kint ht 0 (by norm_num)
  have hfun : besselK0 = fun x : ℝ => ∫ u in Set.Ioi (0 : ℝ), kf x 0 u := funext besselK0_eq
  rw [hfun, besselK1_eq]
  exact h

/-- `K₁' = -∫₀^∞ exp(-t cosh u) cosh² u du`. -/
theorem hasDerivAt_besselK1 {t : ℝ} (ht : 0 < t) :
    HasDerivAt besselK1 (-∫ u in Set.Ioi (0 : ℝ), kf t 2 u) t := by
  have h := hasDerivAt_Kint ht 1 (by norm_num)
  have hfun : besselK1 = fun x : ℝ => ∫ u in Set.Ioi (0 : ℝ), kf x 1 u := funext besselK1_eq
  rw [hfun]
  exact h

/-- `K₀(t) ≤ K₁(t)`. -/
theorem besselK0_le_besselK1 {t : ℝ} (ht : 0 < t) : besselK0 t ≤ besselK1 t := by
  rw [besselK0_eq, besselK1_eq]
  exact integral_mono (integrable_kf ht 0 (by norm_num)) (integrable_kf ht 1 (by norm_num))
    (fun u => kf_mono_pow t (by norm_num) u)

end Tower.RV6
