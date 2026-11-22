import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselI
import Tower.RV6.BesselK

/-!
# The modified Bessel equation for `K₁` and the Wronskian

* `K_ibp`: `K₁(t) - t ∫₀^∞ e^{-t cosh u} cosh² u du + t K₀(t) = 0` (integration by parts: the
  integrand is the derivative of `sinh u · e^{-t cosh u}`).
* `hasDerivAt_mul_besselK1 : (t K₁(t))' = -t K₀(t)`.
* `exp_neg_le_mul_besselK1`, `mul_besselK1_le_one`: `e^{-t} ≤ t K₁(t) ≤ 1`
  (`∫₀^∞ t cosh u · e^{-t sinh u} du = 1`).
* `wronskian : I₀(t) K₁(t) + I₁(t) K₀(t) = 1/t` for `t > 0`: the function
  `t (I₀ K₁ + I₁ K₀)` has derivative zero, and it lies between `e^{-s}` and `I₀(s) + I₁(s)`
  for every `s ≤ t`.
-/

namespace Tower.RV6

open Real MeasureTheory

theorem tendsto_const_mul_exp_neg (c : ℝ) :
    Filter.Tendsto (fun u : ℝ => c * Real.exp (-u)) Filter.atTop (nhds 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul c
  rw [mul_zero] at h
  exact h

/-! ## Integration by parts -/

theorem K_ibp {t : ℝ} (ht : 0 < t) :
    besselK1 t - t * (∫ u in Set.Ioi (0 : ℝ), kf t 2 u) + t * besselK0 t = 0 := by
  have hderiv : ∀ u ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => Real.sinh y * Real.exp (-t * Real.cosh y))
        (kf t 1 u - t * kf t 2 u + t * kf t 0 u) u := by
    intro u _
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-t * Real.cosh y))
        (Real.exp (-t * Real.cosh u) * (-t * Real.sinh u)) u :=
      ((Real.hasDerivAt_cosh u).const_mul (-t)).exp
    have h2 := (Real.hasDerivAt_sinh u).mul h1
    refine h2.congr_deriv ?_
    unfold kf
    linear_combination (t * Real.exp (-t * Real.cosh u)) * Real.cosh_sq u
  have i1 : Integrable (fun u : ℝ => kf t 1 u) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_kf ht 1 (by norm_num)
  have i2 : Integrable (fun u : ℝ => t * kf t 2 u) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrable_kf ht 2 le_rfl).const_mul t
  have i0 : Integrable (fun u : ℝ => t * kf t 0 u) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrable_kf ht 0 (by norm_num)).const_mul t
  have i12 : Integrable (fun u : ℝ => kf t 1 u - t * kf t 2 u)
      (volume.restrict (Set.Ioi (0 : ℝ))) := i1.sub i2
  have hint : IntegrableOn (fun u : ℝ => kf t 1 u - t * kf t 2 u + t * kf t 0 u)
      (Set.Ioi (0 : ℝ)) := i12.add i0
  have hlim : Filter.Tendsto (fun y : ℝ => Real.sinh y * Real.exp (-t * Real.cosh y))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero' ((Filter.eventually_ge_atTop (0 : ℝ)).mono (fun u hu => ?_))
      (Filter.Eventually.of_forall (fun u => ?_)) (tendsto_const_mul_exp_neg (54 / t ^ 3))
    · exact mul_nonneg (Real.sinh_nonneg_iff.mpr hu) (Real.exp_pos _).le
    · have h1 : Real.sinh u ≤ Real.cosh u := (Real.sinh_lt_cosh u).le
      have h2 := kf_le ht 1 (by norm_num) u
      have h3 : Real.sinh u * Real.exp (-t * Real.cosh u) ≤ kf t 1 u := by
        show Real.sinh u * Real.exp (-t * Real.cosh u)
          ≤ Real.exp (-t * Real.cosh u) * Real.cosh u ^ 1
        rw [pow_one, mul_comm]
        exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      exact le_trans h3 h2
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  simp only [Real.sinh_zero, zero_mul, sub_zero] at hftc
  have hsplit : ∫ u in Set.Ioi (0 : ℝ), (kf t 1 u - t * kf t 2 u + t * kf t 0 u)
      = (∫ u in Set.Ioi (0 : ℝ), kf t 1 u) - t * (∫ u in Set.Ioi (0 : ℝ), kf t 2 u)
        + t * ∫ u in Set.Ioi (0 : ℝ), kf t 0 u := by
    rw [integral_add i12 i0, integral_sub i1 i2, integral_const_mul, integral_const_mul]
  rw [besselK1_eq, besselK0_eq]
  linarith [hsplit, hftc]

/-- `(t K₁(t))' = -t K₀(t)`. -/
theorem hasDerivAt_mul_besselK1 {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => x * besselK1 x) (-(t * besselK0 t)) t := by
  have h := (hasDerivAt_id' t).mul (hasDerivAt_besselK1 ht)
  have h' : HasDerivAt (fun x : ℝ => x * besselK1 x)
      (1 * besselK1 t + t * (-∫ u in Set.Ioi (0 : ℝ), kf t 2 u)) t := h
  refine h'.congr_deriv ?_
  linear_combination K_ibp ht

/-! ## `e^{-t} ≤ t K₁(t) ≤ 1` -/

theorem integral_psi {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => t * Real.cosh u * Real.exp (-t * Real.sinh u)) (Set.Ioi (0 : ℝ))
      ∧ ∫ u in Set.Ioi (0 : ℝ), t * Real.cosh u * Real.exp (-t * Real.sinh u) = 1 := by
  have hderiv : ∀ u ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => -Real.exp (-t * Real.sinh y))
        (t * Real.cosh u * Real.exp (-t * Real.sinh u)) u := by
    intro u _
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-t * Real.sinh y))
        (Real.exp (-t * Real.sinh u) * (-t * Real.cosh u)) u :=
      ((Real.hasDerivAt_sinh u).const_mul (-t)).exp
    refine h1.neg.congr_deriv ?_
    ring
  have hpos : ∀ u ∈ Set.Ioi (0 : ℝ), 0 ≤ t * Real.cosh u * Real.exp (-t * Real.sinh u) :=
    fun u _ => mul_nonneg (mul_nonneg ht.le (Real.cosh_pos u).le) (Real.exp_pos _).le
  have h0 : Filter.Tendsto (fun y : ℝ => Real.exp (-t * Real.sinh y)) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun y : ℝ => Real.exp (-(t * y))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((Filter.tendsto_const_mul_atTop_of_pos ht).mpr Filter.tendsto_id)
    refine squeeze_zero' (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))
      ((Filter.eventually_ge_atTop (0 : ℝ)).mono (fun u hu => ?_)) hg
    refine Real.exp_le_exp.mpr ?_
    have h1 : u ≤ Real.sinh u := Real.self_le_sinh_iff.mpr hu
    have h2 := mul_le_mul_of_nonneg_left h1 ht.le
    linarith
  have hlim : Filter.Tendsto (fun y : ℝ => -Real.exp (-t * Real.sinh y))
      Filter.atTop (nhds 0) := by
    have h1 := h0.neg
    rw [neg_zero] at h1
    exact h1
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  simp only [Real.sinh_zero, mul_zero, Real.exp_zero, zero_sub, neg_neg] at hval
  exact ⟨hint, hval⟩

theorem mul_besselK1_le_one {t : ℝ} (ht : 0 < t) : t * besselK1 t ≤ 1 := by
  obtain ⟨hint, hval⟩ := integral_psi ht
  have hmulint : IntegrableOn (fun u : ℝ => t * kf t 1 u) (Set.Ioi (0 : ℝ)) :=
    Integrable.const_mul (integrable_kf ht 1 (by norm_num)) t
  have hpt : ∀ u ∈ Set.Ioi (0 : ℝ),
      t * kf t 1 u ≤ t * Real.cosh u * Real.exp (-t * Real.sinh u) := by
    intro u _
    have h1 : Real.sinh u ≤ Real.cosh u := (Real.sinh_lt_cosh u).le
    have h2 := mul_le_mul_of_nonneg_left h1 ht.le
    have hE : Real.exp (-t * Real.cosh u) ≤ Real.exp (-t * Real.sinh u) :=
      Real.exp_le_exp.mpr (by linarith)
    show t * (Real.exp (-t * Real.cosh u) * Real.cosh u ^ 1)
      ≤ t * Real.cosh u * Real.exp (-t * Real.sinh u)
    rw [pow_one]
    calc t * (Real.exp (-t * Real.cosh u) * Real.cosh u)
        = t * Real.cosh u * Real.exp (-t * Real.cosh u) := by ring
      _ ≤ t * Real.cosh u * Real.exp (-t * Real.sinh u) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg ht.le (Real.cosh_pos u).le)
  have h : ∫ u in Set.Ioi (0 : ℝ), t * kf t 1 u
      ≤ ∫ u in Set.Ioi (0 : ℝ), t * Real.cosh u * Real.exp (-t * Real.sinh u) :=
    setIntegral_mono_on hmulint hint measurableSet_Ioi hpt
  rw [integral_const_mul, hval] at h
  rw [besselK1_eq]
  exact h

theorem exp_neg_le_mul_besselK1 {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≤ t * besselK1 t := by
  obtain ⟨hint, hval⟩ := integral_psi ht
  have hmulint : IntegrableOn (fun u : ℝ => t * kf t 1 u) (Set.Ioi (0 : ℝ)) :=
    Integrable.const_mul (integrable_kf ht 1 (by norm_num)) t
  have hint' : IntegrableOn
      (fun u : ℝ => Real.exp (-t) * (t * Real.cosh u * Real.exp (-t * Real.sinh u)))
      (Set.Ioi (0 : ℝ)) := Integrable.const_mul hint (Real.exp (-t))
  have hpt : ∀ u ∈ Set.Ioi (0 : ℝ),
      Real.exp (-t) * (t * Real.cosh u * Real.exp (-t * Real.sinh u)) ≤ t * kf t 1 u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hcs : Real.cosh u - Real.sinh u = Real.exp (-u) := Real.cosh_sub_sinh u
    have he : Real.exp (-u) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (by linarith : -u ≤ 0)
      rw [Real.exp_zero] at h
      exact h
    have hcsl : Real.cosh u ≤ 1 + Real.sinh u := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcsl ht.le
    have hE : Real.exp (-t) * Real.exp (-t * Real.sinh u) ≤ Real.exp (-t * Real.cosh u) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      linarith
    have hc := (Real.cosh_pos u).le
    show Real.exp (-t) * (t * Real.cosh u * Real.exp (-t * Real.sinh u))
      ≤ t * (Real.exp (-t * Real.cosh u) * Real.cosh u ^ 1)
    rw [pow_one]
    calc Real.exp (-t) * (t * Real.cosh u * Real.exp (-t * Real.sinh u))
        = t * Real.cosh u * (Real.exp (-t) * Real.exp (-t * Real.sinh u)) := by ring
      _ ≤ t * Real.cosh u * Real.exp (-t * Real.cosh u) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg ht.le hc)
      _ = t * (Real.exp (-t * Real.cosh u) * Real.cosh u) := by ring
  have h : ∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-t) * (t * Real.cosh u * Real.exp (-t * Real.sinh u))
      ≤ ∫ u in Set.Ioi (0 : ℝ), t * kf t 1 u :=
    setIntegral_mono_on hint' hmulint measurableSet_Ioi hpt
  rw [integral_const_mul, integral_const_mul, hval, mul_one] at h
  rw [besselK1_eq]
  exact h

theorem besselK0_nonneg (t : ℝ) : 0 ≤ besselK0 t := by
  rw [besselK0_eq]
  exact integral_nonneg (fun u => kf_nonneg t 0 u)

theorem besselK1_pos {t : ℝ} (ht : 0 < t) : 0 < besselK1 t := by
  have h := exp_neg_le_mul_besselK1 ht
  have he := Real.exp_pos (-t)
  by_contra hn
  push_neg at hn
  have h2 := mul_nonneg ht.le (neg_nonneg.mpr hn)
  linarith

/-! ## The Wronskian -/

/-- `t (I₀(t) K₁(t) + I₁(t) K₀(t))`. -/
noncomputable def wr (x : ℝ) : ℝ := besselI0 x * (x * besselK1 x) + x * besselI1 x * besselK0 x

theorem hasDerivAt_wr {t : ℝ} (ht : 0 < t) : HasDerivAt wr 0 t := by
  have h := ((hasDerivAt_besselI0 t).mul (hasDerivAt_mul_besselK1 ht)).add
    ((hasDerivAt_mul_besselI1 t).mul (hasDerivAt_besselK0 ht))
  have h' : HasDerivAt
      (fun x : ℝ => besselI0 x * (x * besselK1 x) + x * besselI1 x * besselK0 x)
      (besselI1 t * (t * besselK1 t) + besselI0 t * (-(t * besselK0 t))
        + (t * besselI0 t * besselK0 t + t * besselI1 t * (-besselK1 t))) t := h
  have e : besselI1 t * (t * besselK1 t) + besselI0 t * (-(t * besselK0 t))
      + (t * besselI0 t * besselK0 t + t * besselI1 t * (-besselK1 t)) = 0 := by ring
  rw [e] at h'
  exact h'

theorem wr_const {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : wr b = wr a := by
  have hcont : ContinuousOn wr (Set.Icc a b) := fun x hx =>
    (hasDerivAt_wr (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt wr 0 (Set.Ici x) x := fun x hx =>
    (hasDerivAt_wr (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hcont hderiv b ⟨hab, le_rfl⟩

theorem wr_lower {s : ℝ} (hs : 0 < s) : Real.exp (-s) ≤ wr s := by
  have h1 := exp_neg_le_mul_besselK1 hs
  have h2 := one_le_besselI0 s
  have h3 := besselI1_nonneg hs.le
  have h4 := besselK0_nonneg s
  have he := (Real.exp_pos (-s)).le
  have hX : 0 ≤ s * besselK1 s := le_trans he h1
  have hA := mul_le_mul_of_nonneg_right h2 hX
  have hB : 0 ≤ s * besselI1 s * besselK0 s := mul_nonneg (mul_nonneg hs.le h3) h4
  unfold wr
  linarith

theorem wr_upper {s : ℝ} (hs : 0 < s) : wr s ≤ besselI0 s + besselI1 s := by
  have h1 := mul_besselK1_le_one hs
  have h2 := besselI0_pos s
  have h3 := besselI1_nonneg hs.le
  have h4 := besselK0_le_besselK1 hs
  have hA : besselI0 s * (s * besselK1 s) ≤ besselI0 s * 1 :=
    mul_le_mul_of_nonneg_left h1 h2.le
  have h5 : s * besselK0 s ≤ s * besselK1 s := mul_le_mul_of_nonneg_left h4 hs.le
  have hB : besselI1 s * (s * besselK0 s) ≤ besselI1 s * 1 :=
    mul_le_mul_of_nonneg_left (le_trans h5 h1) h3
  have e : s * besselI1 s * besselK0 s = besselI1 s * (s * besselK0 s) := by ring
  unfold wr
  linarith

theorem wr_eq_one {t : ℝ} (ht : 0 < t) : wr t = 1 := by
  have hlow : ∀ s : ℝ, 0 < s → s ≤ t → 1 - s ≤ wr t := by
    intro s hs hst
    have h1 := wr_lower hs
    have h2 := wr_const hs hst
    have h3 : -s + 1 ≤ Real.exp (-s) := Real.add_one_le_exp (-s)
    linarith
  have hup : ∀ s : ℝ, 0 < s → s ≤ t → wr t ≤ besselI0 s + besselI1 s := by
    intro s hs hst
    have h1 := wr_upper hs
    have h2 := wr_const hs hst
    linarith
  apply le_antisymm
  · by_contra hcon
    push_neg at hcon
    have hc : ContinuousAt (fun s : ℝ => besselI0 s + besselI1 s) 0 :=
      (continuous_besselI0.add continuous_besselI1).continuousAt
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hc (wr t - 1) (by linarith)
    have hs0 : 0 < min t (δ / 2) := lt_min ht (by linarith)
    have hmin := min_le_right t (δ / 2)
    have hd : dist (min t (δ / 2)) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
      linarith
    have h1 : dist (besselI0 (min t (δ / 2)) + besselI1 (min t (δ / 2)))
        (besselI0 0 + besselI1 0) < wr t - 1 := hball hd
    rw [Real.dist_eq, besselI0_zero, besselI1_zero, add_zero] at h1
    have h2 := hup (min t (δ / 2)) hs0 (min_le_left t (δ / 2))
    have h3 := (abs_lt.mp h1).2
    linarith
  · by_contra hcon
    push_neg at hcon
    have hs0 : 0 < min t ((1 - wr t) / 2) := lt_min ht (by linarith)
    have h1 := hlow (min t ((1 - wr t) / 2)) hs0 (min_le_left _ _)
    have h2 := min_le_right t ((1 - wr t) / 2)
    linarith

/-- **The Wronskian.** `I₀(t) K₁(t) + I₁(t) K₀(t) = 1/t` for `t > 0`. -/
theorem wronskian {t : ℝ} (ht : 0 < t) :
    besselI0 t * besselK1 t + besselI1 t * besselK0 t = 1 / t := by
  have h := wr_eq_one ht
  unfold wr at h
  rw [eq_div_iff ht.ne']
  linear_combination h

end Tower.RV6
