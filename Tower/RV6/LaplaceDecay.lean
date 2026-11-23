import Mathlib
import Tower.RV6.LaplaceP
import Tower.RV6.MellinSeries
import Tower.RV6.BesselW
import Tower.RV6.BesselL5

/-!
# Decay of `θʲ(I₀ K₀)` at infinity, from the Laplace representation

With `I₀(t) K₀(t) = ∫₀^∞ e^{-tw} ν(w) dw` (`laplace_P`) and the moments
`M_m(t) = ∫₀^∞ w^m e^{-tw} ν(w) dw` (`momP`):

* `momP_le`: `t^{m+1} M_m(t) ≤ m! 2^{m+1}` (`w^m e^{-tw} ≤ m! (2/t)^m e^{-tw/2}` and `I₀K₀(s) ≤ 1/s`);
* `hasDerivAt_momP`: `M_m' = -M_{m+1}` (dominated differentiation);
* **`abs_momP_sub_le`**: `|t^{k+3} M_k(t) - (k!/2) t²| ≤ (k+2)! (3/2 + 2^{k+3})`, because
  `|ν(w) - 1/2| ≤ w² (3/2 + ν(w))` (`abs_nuP_sub_half_le'`) and `∫₀^∞ w^k e^{-tw} dw = k!/t^{k+1}`;
* the chain `pB0 = I₀K₀`, `pB1 = θ pB0`, `pB2 = θ pB1`, `pB3 = θ pB2 = 4t²(pB0 + pB1)` in Bessel form and
  in moment form (`pB0_eq` … `pB3_eq`, by uniqueness of derivatives);
* **`abs_mul_pB0_le` … `abs_mul_pB3_le`**: `|t pBⱼ(t)| ≤ 2, 4, 20, 148`, and
  **`abs_pB01_le`, `abs_pB12_le`, `abs_pB23_le`**: `|t³(pBⱼ + pBⱼ₊₁)| ≤ 124, 1014, 11286`, for all `t > 0`.

The second family is where the cancellation sits: `Σ aₖ k! = 0` for each combination, so the
`1/2` of `ν(0)` drops out and only `ν - 1/2 = O(w²)` remains.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- The moments `M_m(t) = ∫₀^∞ w^m e^{-tw} ν(w) dw`. -/
noncomputable def momP (m : ℕ) (t : ℝ) : ℝ :=
  ∫ w in Set.Ioi (0 : ℝ), w ^ m * Real.exp (-t * w) * nuP w

/-- `I₀(t) K₀(t) ≤ 1/t`. -/
theorem besselI0_mul_besselK0_le {t : ℝ} (ht : 0 < t) : besselI0 t * besselK0 t ≤ 1 / t := by
  have hw := wronskian ht
  have h1 : 0 ≤ besselI1 t * besselK0 t := mul_nonneg (besselI1_nonneg ht.le) (besselK0_nonneg t)
  have h2 : besselI0 t * besselK0 t ≤ besselI0 t * besselK1 t :=
    mul_le_mul_of_nonneg_left (besselK0_le_besselK1 ht) (besselI0_pos t).le
  linarith

/-- `w^m e^{-tw} ≤ m! (2/t)^m e^{-tw/2}`. -/
theorem pow_mul_exp_le (m : ℕ) {t w : ℝ} (ht : 0 < t) (hw : 0 ≤ w) :
    w ^ m * Real.exp (-t * w) ≤ (m.factorial : ℝ) * (2 / t) ^ m * Real.exp (-(t / 2) * w) := by
  have hf : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have hx : 0 ≤ t * w / 2 := div_nonneg (mul_nonneg ht.le hw) two_pos.le
  have h := Real.pow_div_factorial_le_exp hx m
  have h1 : (t * w / 2) ^ m ≤ Real.exp (t * w / 2) * (m.factorial : ℝ) := (div_le_iff₀ hf).mp h
  have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have e1 : w = 2 / t * (t * w / 2) := by
    linear_combination (-w) * hti
  have e2 : Real.exp (t * w / 2) * Real.exp (-t * w) = Real.exp (-(t / 2) * w) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp : 0 ≤ (2 / t) ^ m := pow_nonneg (div_nonneg two_pos.le ht.le) m
  have hE : 0 ≤ Real.exp (-t * w) := (Real.exp_pos _).le
  calc w ^ m * Real.exp (-t * w) = (2 / t) ^ m * (t * w / 2) ^ m * Real.exp (-t * w) := by
        rw [← mul_pow, ← e1]
    _ ≤ (2 / t) ^ m * (Real.exp (t * w / 2) * (m.factorial : ℝ)) * Real.exp (-t * w) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hp) hE
    _ = (m.factorial : ℝ) * (2 / t) ^ m * Real.exp (-(t / 2) * w) := by
        rw [← e2]
        ring

theorem integrableOn_momP (m : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun w : ℝ => w ^ m * Real.exp (-t * w) * nuP w) (Set.Ioi (0 : ℝ)) := by
  have hg : IntegrableOn
      (fun w : ℝ => (m.factorial : ℝ) * (2 / t) ^ m * (Real.exp (-(t / 2) * w) * nuP w))
      (Set.Ioi (0 : ℝ)) :=
    (integrableOn_laplace_P (half_pos ht)).const_mul _
  have hmeas : AEStronglyMeasurable (fun w : ℝ => w ^ m * Real.exp (-t * w) * nuP w)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 := (integrableOn_laplace_P ht).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun w : ℝ => w ^ m) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (continuous_pow m).aestronglyMeasurable
    refine (h2.mul h1).congr (Filter.Eventually.of_forall (fun w => ?_))
    show w ^ m * (Real.exp (-t * w) * nuP w) = w ^ m * Real.exp (-t * w) * nuP w
    ring
  refine hg.mono' hmeas (ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_))
  have hw0 : 0 ≤ w := le_of_lt hw
  have hnu := nuP_nonneg w
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hw0 m) (Real.exp_pos _).le) hnu)]
  have h := pow_mul_exp_le m ht hw0
  calc w ^ m * Real.exp (-t * w) * nuP w
      ≤ (m.factorial : ℝ) * (2 / t) ^ m * Real.exp (-(t / 2) * w) * nuP w :=
        mul_le_mul_of_nonneg_right h hnu
    _ = (m.factorial : ℝ) * (2 / t) ^ m * (Real.exp (-(t / 2) * w) * nuP w) := by ring

theorem momP_nonneg (m : ℕ) (t : ℝ) : 0 ≤ momP m t :=
  setIntegral_nonneg measurableSet_Ioi (fun w hw =>
    mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hw) m) (Real.exp_pos _).le) (nuP_nonneg w))

/-- **`t^{m+1} M_m(t) ≤ m! 2^{m+1}`.** -/
theorem momP_le (m : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ (m + 1) * momP m t ≤ (m.factorial : ℝ) * 2 ^ (m + 1) := by
  have hP := laplace_P (half_pos ht)
  have hle := besselI0_mul_besselK0_le (half_pos ht)
  have hmono : momP m t ≤ ∫ w in Set.Ioi (0 : ℝ),
      (m.factorial : ℝ) * (2 / t) ^ m * (Real.exp (-(t / 2) * w) * nuP w) := by
    unfold momP
    refine setIntegral_mono_on (integrableOn_momP m ht)
      ((integrableOn_laplace_P (half_pos ht)).const_mul _) measurableSet_Ioi (fun w hw => ?_)
    have hw0 : 0 ≤ w := le_of_lt hw
    have h := pow_mul_exp_le m ht hw0
    have hnu := nuP_nonneg w
    calc w ^ m * Real.exp (-t * w) * nuP w
        ≤ (m.factorial : ℝ) * (2 / t) ^ m * Real.exp (-(t / 2) * w) * nuP w :=
          mul_le_mul_of_nonneg_right h hnu
      _ = (m.factorial : ℝ) * (2 / t) ^ m * (Real.exp (-(t / 2) * w) * nuP w) := by ring
  rw [integral_const_mul, ← hP] at hmono
  have hfp : 0 ≤ (m.factorial : ℝ) * (2 / t) ^ m :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg two_pos.le ht.le) m)
  have h2 : momP m t ≤ (m.factorial : ℝ) * (2 / t) ^ m * (1 / (t / 2)) :=
    le_trans hmono (mul_le_mul_of_nonneg_left hle hfp)
  have htp : 0 < t ^ (m + 1) := pow_pos ht _
  have h3 : t ^ (m + 1) * momP m t
      ≤ t ^ (m + 1) * ((m.factorial : ℝ) * (2 / t) ^ m * (1 / (t / 2))) :=
    mul_le_mul_of_nonneg_left h2 htp.le
  have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hk : (t * t⁻¹) ^ (m + 1) = 1 := by rw [hti, one_pow]
  have e : t ^ (m + 1) * ((m.factorial : ℝ) * (2 / t) ^ m * (1 / (t / 2)))
      = (m.factorial : ℝ) * 2 ^ (m + 1) := by
    linear_combination ((m.factorial : ℝ) * 2 ^ (m + 1)) * hk
  linarith

/-- `∫₀^∞ w^k e^{-tw} dw = k!/t^{k+1}`. -/
theorem integral_pow_mul_exp (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ w in Set.Ioi (0 : ℝ), w ^ k * Real.exp (-t * w) = (k.factorial : ℝ) / t ^ (k + 1) := by
  rw [← integral_exp_mul_pow ht k]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
  show w ^ k * Real.exp (-t * w) = Real.exp (-(t * w)) * w ^ k
  rw [neg_mul]
  ring

theorem integrableOn_pow_mul_exp (k : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun w : ℝ => w ^ k * Real.exp (-t * w)) (Set.Ioi (0 : ℝ)) := by
  have hg : IntegrableOn (fun w : ℝ => (k.factorial : ℝ) * (2 / t) ^ k * Real.exp (-(t / 2) * w))
      (Set.Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 (half_pos ht)).const_mul _
  have hc : Continuous (fun w : ℝ => w ^ k * Real.exp (-t * w)) := by fun_prop
  refine hg.mono' hc.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi (fun w hw => ?_))
  have hw0 : 0 ≤ w := le_of_lt hw
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hw0 k) (Real.exp_pos _).le)]
  exact pow_mul_exp_le k ht hw0

/-- `|ν(w) - 1/2| ≤ w² (3/2 + ν(w))` for every `w > 0`. -/
theorem abs_nuP_sub_half_le' {w : ℝ} (hw : 0 < w) : |nuP w - 1 / 2| ≤ w ^ 2 * (3 / 2 + nuP w) := by
  have hn := nuP_nonneg w
  rcases le_or_lt w 1 with h1 | h1
  · have h := abs_nuP_sub_half_le hw h1
    have h3 : 0 ≤ w ^ 2 * (1 / 2 + nuP w) := mul_nonneg (sq_nonneg w) (by linarith)
    have e : w ^ 2 * (3 / 2 + nuP w) = w ^ 2 + w ^ 2 * (1 / 2 + nuP w) := by ring
    linarith
  · have hw2 : 1 ≤ w ^ 2 := by
      have h4 : 1 * 1 ≤ w * w := mul_le_mul h1.le h1.le zero_le_one (by linarith)
      rw [pow_two]
      linarith
    have h2 : |nuP w - 1 / 2| ≤ nuP w + 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have h3 : 0 ≤ (w ^ 2 - 1) * (3 / 2 + nuP w) := mul_nonneg (by linarith) (by linarith)
    have e : w ^ 2 * (3 / 2 + nuP w) = (w ^ 2 - 1) * (3 / 2 + nuP w) + (3 / 2 + nuP w) := by ring
    linarith

/-- **`|t^{k+3} M_k(t) - (k!/2) t²| ≤ (k+2)! (3/2 + 2^{k+3})`.** -/
theorem abs_momP_sub_le (k : ℕ) {t : ℝ} (ht : 0 < t) :
    |t ^ (k + 3) * momP k t - (k.factorial : ℝ) / 2 * t ^ 2|
      ≤ ((k + 2).factorial : ℝ) * (3 / 2 + 2 ^ (k + 2 + 1)) := by
  have hE := integral_pow_mul_exp k ht
  have hint1 : IntegrableOn (fun w : ℝ => 1 / 2 * (w ^ k * Real.exp (-t * w))) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_pow_mul_exp k ht).const_mul _
  have h1 : (∫ w in Set.Ioi (0 : ℝ), w ^ k * Real.exp (-t * w) * (nuP w - 1 / 2))
      = momP k t - 1 / 2 * ((k.factorial : ℝ) / t ^ (k + 1)) := by
    rw [← hE, ← integral_const_mul]
    unfold momP
    rw [← integral_sub (integrableOn_momP k ht) hint1]
    refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
    show w ^ k * Real.exp (-t * w) * (nuP w - 1 / 2)
      = w ^ k * Real.exp (-t * w) * nuP w - 1 / 2 * (w ^ k * Real.exp (-t * w))
    ring
  have hb : ∀ w ∈ Set.Ioi (0 : ℝ), ‖w ^ k * Real.exp (-t * w) * (nuP w - 1 / 2)‖
      ≤ 3 / 2 * (w ^ (k + 2) * Real.exp (-t * w)) + w ^ (k + 2) * Real.exp (-t * w) * nuP w := by
    intro w hw
    have hw0 : (0 : ℝ) < w := hw
    have hn := abs_nuP_sub_half_le' hw0
    have hp : 0 ≤ w ^ k * Real.exp (-t * w) := mul_nonneg (pow_nonneg hw0.le k) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    calc w ^ k * Real.exp (-t * w) * |nuP w - 1 / 2|
        ≤ w ^ k * Real.exp (-t * w) * (w ^ 2 * (3 / 2 + nuP w)) := mul_le_mul_of_nonneg_left hn hp
      _ = 3 / 2 * (w ^ (k + 2) * Real.exp (-t * w)) + w ^ (k + 2) * Real.exp (-t * w) * nuP w := by
          ring
  have hgi1 : IntegrableOn (fun w : ℝ => 3 / 2 * (w ^ (k + 2) * Real.exp (-t * w))) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_pow_mul_exp (k + 2) ht).const_mul _
  have hgi : IntegrableOn (fun w : ℝ => 3 / 2 * (w ^ (k + 2) * Real.exp (-t * w))
      + w ^ (k + 2) * Real.exp (-t * w) * nuP w) (Set.Ioi (0 : ℝ)) :=
    hgi1.add (integrableOn_momP (k + 2) ht)
  have hn := norm_integral_le_of_norm_le hgi (ae_restrict_of_forall_mem measurableSet_Ioi hb)
  rw [integral_add hgi1 (integrableOn_momP (k + 2) ht), integral_const_mul,
    integral_pow_mul_exp (k + 2) ht, h1, Real.norm_eq_abs] at hn
  have hm := momP_le (k + 2) ht
  have hm' : (∫ w in Set.Ioi (0 : ℝ), w ^ (k + 2) * Real.exp (-t * w) * nuP w) = momP (k + 2) t := rfl
  rw [hm'] at hn
  -- multiply by t^{k+3}
  have htp : 0 < t ^ (k + 3) := pow_pos ht _
  have h2 : t ^ (k + 3) * |momP k t - 1 / 2 * ((k.factorial : ℝ) / t ^ (k + 1))|
      ≤ t ^ (k + 3) * (3 / 2 * (((k + 2).factorial : ℝ) / t ^ (k + 2 + 1)) + momP (k + 2) t) :=
    mul_le_mul_of_nonneg_left hn htp.le
  have hv : t ^ (k + 1) * (t ^ (k + 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ ht.ne')
  have hw' : t ^ (k + 2 + 1) * (t ^ (k + 2 + 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ ht.ne')
  have eX : t ^ (k + 3) * (momP k t - 1 / 2 * ((k.factorial : ℝ) / t ^ (k + 1)))
      = t ^ (k + 3) * momP k t - (k.factorial : ℝ) / 2 * t ^ 2 := by
    linear_combination (-(1 / 2 : ℝ) * (k.factorial : ℝ) * t ^ 2) * hv
  have e1 : t ^ (k + 3) * |momP k t - 1 / 2 * ((k.factorial : ℝ) / t ^ (k + 1))|
      = |t ^ (k + 3) * momP k t - (k.factorial : ℝ) / 2 * t ^ 2| := by
    rw [← eX, abs_mul, abs_of_pos htp]
  have e2 : t ^ (k + 3) * (3 / 2 * (((k + 2).factorial : ℝ) / t ^ (k + 2 + 1)) + momP (k + 2) t)
      = 3 / 2 * ((k + 2).factorial : ℝ) + t ^ (k + 2 + 1) * momP (k + 2) t := by
    linear_combination (3 / 2 * ((k + 2).factorial : ℝ)) * hw'
  rw [e1, e2] at h2
  have e3 : ((k + 2).factorial : ℝ) * (3 / 2 + 2 ^ (k + 2 + 1))
      = 3 / 2 * ((k + 2).factorial : ℝ) + ((k + 2).factorial : ℝ) * 2 ^ (k + 2 + 1) := by ring
  rw [e3]
  linarith

/-! ## The derivative of the moments -/

theorem hasDerivAt_momP (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (momP m) (-momP (m + 1) t) t := by
  have hs : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ s ∈ Set.Ioi (t / 2), AEStronglyMeasurable
      (fun w : ℝ => w ^ m * Real.exp (-s * w) * nuP w) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro s hs'
    have hs0 : 0 < s := lt_trans (by linarith) (Set.mem_Ioi.mp hs')
    exact (integrableOn_momP m hs0).aestronglyMeasurable
  have hint : Integrable (fun w : ℝ => w ^ m * Real.exp (-t * w) * nuP w)
      (volume.restrict (Set.Ioi (0 : ℝ))) := integrableOn_momP m ht
  have hmeas' : AEStronglyMeasurable (fun w : ℝ => -(w ^ (m + 1) * Real.exp (-t * w) * nuP w))
      (volume.restrict (Set.Ioi (0 : ℝ))) := (integrableOn_momP (m + 1) ht).neg.aestronglyMeasurable
  have hbound : ∀ w ∈ Set.Ioi (0 : ℝ), ∀ s ∈ Set.Ioi (t / 2),
      ‖-(w ^ (m + 1) * Real.exp (-s * w) * nuP w)‖
        ≤ w ^ (m + 1) * Real.exp (-(t / 2) * w) * nuP w := by
    intro w hw s hs'
    have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
    have hs1 : t / 2 < s := hs'
    have hnu := nuP_nonneg w
    have hpw : 0 ≤ w ^ (m + 1) := pow_nonneg hw0 _
    rw [norm_neg, Real.norm_of_nonneg (mul_nonneg (mul_nonneg hpw (Real.exp_pos _).le) hnu)]
    have hsw : t / 2 * w ≤ s * w := mul_le_mul_of_nonneg_right hs1.le hw0
    have he : Real.exp (-s * w) ≤ Real.exp (-(t / 2) * w) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hpw) hnu
  have hbi : Integrable (fun w : ℝ => w ^ (m + 1) * Real.exp (-(t / 2) * w) * nuP w)
      (volume.restrict (Set.Ioi (0 : ℝ))) := integrableOn_momP (m + 1) (half_pos ht)
  have hdiff : ∀ w ∈ Set.Ioi (0 : ℝ), ∀ s ∈ Set.Ioi (t / 2),
      HasDerivAt (fun s : ℝ => w ^ m * Real.exp (-s * w) * nuP w)
        (-(w ^ (m + 1) * Real.exp (-s * w) * nuP w)) s := by
    intro w _ s _
    have h1 : HasDerivAt (fun y : ℝ => -y * w) (-1 * w) s := ((hasDerivAt_id' s).neg).mul_const w
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y * w)) (Real.exp (-s * w) * (-1 * w)) s := h1.exp
    have h3 : HasDerivAt (fun y : ℝ => w ^ m * Real.exp (-y * w) * nuP w)
        (w ^ m * (Real.exp (-s * w) * (-1 * w)) * nuP w) s :=
      (h2.const_mul (w ^ m)).mul_const (nuP w)
    refine h3.congr_deriv ?_
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun s w => w ^ m * Real.exp (-s * w) * nuP w)
    (F' := fun s w => -(w ^ (m + 1) * Real.exp (-s * w) * nuP w))
    (bound := fun w => w ^ (m + 1) * Real.exp (-(t / 2) * w) * nuP w) hs
    (Filter.eventually_of_mem hs hmeas) hint hmeas'
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound) hbi
    (ae_restrict_of_forall_mem measurableSet_Ioi hdiff)
  have h3 : HasDerivAt (momP m)
      (∫ w in Set.Ioi (0 : ℝ), -(w ^ (m + 1) * Real.exp (-t * w) * nuP w)) t := key.2
  rw [integral_neg] at h3
  exact h3

/-! ## The chain `θʲ(I₀ K₀)`, in Bessel form and in moment form -/

theorem hasDerivAt_prod2 {a b : ℝ → ℝ} {a1 b1 t : ℝ} (ha : HasDerivAt a a1 t)
    (hb : HasDerivAt b b1 t) : HasDerivAt (fun x => a x * b x) (a1 * b t + a t * b1) t := ha.mul hb

theorem hasDerivAt_prod3 {a b c : ℝ → ℝ} {a1 b1 c1 t : ℝ} (ha : HasDerivAt a a1 t)
    (hb : HasDerivAt b b1 t) (hc : HasDerivAt c c1 t) :
    HasDerivAt (fun x => a x * b x * c x) (a1 * b t * c t + a t * b1 * c t + a t * b t * c1) t := by
  have h0 := (ha.mul hb).mul hc
  have h1 : HasDerivAt (fun x => a x * b x * c x) ((a1 * b t + a t * b1) * c t + a t * b t * c1) t := h0
  exact h1.congr_deriv (by ring)

/-- `pB0 = I₀ K₀`. -/
noncomputable def pB0 (t : ℝ) : ℝ := besselI0 t * besselK0 t

/-- `pB1 = θ pB0 = t (I₁K₀ - I₀K₁)`. -/
noncomputable def pB1 (t : ℝ) : ℝ := t * besselI1 t * besselK0 t - besselI0 t * (t * besselK1 t)

/-- `pB2 = θ pB1 = 2t²(I₀K₀ - I₁K₁)`. -/
noncomputable def pB2 (t : ℝ) : ℝ :=
  2 * (t ^ 2 * besselI0 t * besselK0 t) - 2 * ((t * besselI1 t) * (t * besselK1 t))

/-- `pB3 = θ pB2 = 4t²(pB0 + pB1)`. -/
noncomputable def pB3 (t : ℝ) : ℝ := 4 * t ^ 2 * (pB0 t + pB1 t)

theorem hasDerivAt_pB0 {t : ℝ} (ht : 0 < t) : HasDerivAt pB0 (pB1 t / t) t := by
  have h0 := hasDerivAt_prod2 (hasDerivAt_besselI0 t) (hasDerivAt_besselK0 ht)
  have hfun : pB0 = fun x : ℝ => besselI0 x * besselK0 x := rfl
  rw [hfun]
  refine h0.congr_deriv ?_
  rw [eq_div_iff ht.ne']
  unfold pB1
  ring

theorem hasDerivAt_pB1 {t : ℝ} (ht : 0 < t) : HasDerivAt pB1 (pB2 t / t) t := by
  have m1 := (hasDerivAt_prod2 (hasDerivAt_mul_besselI1 t) (hasDerivAt_besselK0 ht)).const_mul (1 : ℝ)
  have m2 := (hasDerivAt_prod2 (hasDerivAt_besselI0 t) (hasDerivAt_mul_besselK1 ht)).const_mul (-1 : ℝ)
  have h0 := m1.add m2
  have hfun : pB1 = fun x : ℝ =>
      1 * ((x * besselI1 x) * besselK0 x) + (-1) * (besselI0 x * (x * besselK1 x)) := by
    funext x
    unfold pB1
    ring
  rw [hfun]
  refine h0.congr_deriv ?_
  rw [eq_div_iff ht.ne']
  unfold pB2
  ring

theorem hasDerivAt_pB2 {t : ℝ} (ht : 0 < t) : HasDerivAt pB2 (pB3 t / t) t := by
  have m1 := (hasDerivAt_prod3 (hasDerivAt_sqx t) (hasDerivAt_besselI0 t)
    (hasDerivAt_besselK0 ht)).const_mul (2 : ℝ)
  have m2 := (hasDerivAt_prod2 (hasDerivAt_mul_besselI1 t) (hasDerivAt_mul_besselK1 ht)).const_mul (-2 : ℝ)
  have h0 := m1.add m2
  have hfun : pB2 = fun x : ℝ =>
      2 * (x ^ 2 * besselI0 x * besselK0 x) + (-2) * ((x * besselI1 x) * (x * besselK1 x)) := by
    funext x
    unfold pB2
    ring
  rw [hfun]
  refine h0.congr_deriv ?_
  rw [eq_div_iff ht.ne']
  unfold pB3 pB0 pB1
  ring

/-- The moment forms: `lB0 = M₀`, `lB1 = -t M₁`, `lB2 = t² M₂ - t M₁`, `lB3 = -t³ M₃ + 3t² M₂ - t M₁`. -/
noncomputable def lB0 (t : ℝ) : ℝ := momP 0 t
noncomputable def lB1 (t : ℝ) : ℝ := -(t * momP 1 t)
noncomputable def lB2 (t : ℝ) : ℝ := t ^ 2 * momP 2 t - t * momP 1 t
noncomputable def lB3 (t : ℝ) : ℝ := -(t ^ 3 * momP 3 t) + 3 * (t ^ 2 * momP 2 t) - t * momP 1 t

theorem hasDerivAt_lB0 {t : ℝ} (ht : 0 < t) : HasDerivAt lB0 (lB1 t / t) t := by
  have h := hasDerivAt_momP 0 ht
  have hfun : lB0 = momP 0 := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  rw [eq_div_iff ht.ne']
  unfold lB1
  ring

theorem hasDerivAt_lB1 {t : ℝ} (ht : 0 < t) : HasDerivAt lB1 (lB2 t / t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x * momP 1 x) (1 * momP 1 t + t * -momP 2 t) t :=
    (hasDerivAt_id' t).mul (hasDerivAt_momP 1 ht)
  have h2 : HasDerivAt (fun x : ℝ => -(x * momP 1 x)) (-(1 * momP 1 t + t * -momP 2 t)) t :=
    h1.neg
  have hfun : lB1 = fun x : ℝ => -(x * momP 1 x) := rfl
  rw [hfun]
  refine h2.congr_deriv ?_
  rw [eq_div_iff ht.ne']
  unfold lB2
  ring

theorem hasDerivAt_lB2 {t : ℝ} (ht : 0 < t) : HasDerivAt lB2 (lB3 t / t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 * momP 2 x) (2 * t * momP 2 t + t ^ 2 * -momP 3 t) t :=
    (hasDerivAt_sqx t).mul (hasDerivAt_momP 2 ht)
  have h2 : HasDerivAt (fun x : ℝ => x * momP 1 x) (1 * momP 1 t + t * -momP 2 t) t :=
    (hasDerivAt_id' t).mul (hasDerivAt_momP 1 ht)
  have h3 : HasDerivAt (fun x : ℝ => x ^ 2 * momP 2 x - x * momP 1 x)
      ((2 * t * momP 2 t + t ^ 2 * -momP 3 t) - (1 * momP 1 t + t * -momP 2 t)) t :=
    h1.sub h2
  have hfun : lB2 = fun x : ℝ => x ^ 2 * momP 2 x - x * momP 1 x := rfl
  rw [hfun]
  refine h3.congr_deriv ?_
  rw [eq_div_iff ht.ne']
  unfold lB3
  ring

/-- Uniqueness of derivatives on `(0, ∞)`. -/
theorem eq_of_hasDerivAt_of_eqOn {f g : ℝ → ℝ} {f' g' t : ℝ} (ht : 0 < t)
    (hfg : ∀ s, 0 < s → f s = g s) (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) : f' = g' := by
  have he : g =ᶠ[nhds t] f :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht) (fun s hs => (hfg s hs).symm)
  exact (hf.congr_of_eventuallyEq he).unique hg

theorem pB0_eq {t : ℝ} (ht : 0 < t) : pB0 t = lB0 t := by
  unfold pB0 lB0 momP
  rw [laplace_P ht]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
  show Real.exp (-t * w) * nuP w = w ^ 0 * Real.exp (-t * w) * nuP w
  rw [pow_zero, one_mul]

theorem pB1_eq {t : ℝ} (ht : 0 < t) : pB1 t = lB1 t := by
  have h := eq_of_hasDerivAt_of_eqOn ht (fun s hs => pB0_eq hs) (hasDerivAt_pB0 ht) (hasDerivAt_lB0 ht)
  exact (div_left_inj' ht.ne').mp h

theorem pB2_eq {t : ℝ} (ht : 0 < t) : pB2 t = lB2 t := by
  have h := eq_of_hasDerivAt_of_eqOn ht (fun s hs => pB1_eq hs) (hasDerivAt_pB1 ht) (hasDerivAt_lB1 ht)
  exact (div_left_inj' ht.ne').mp h

theorem pB3_eq {t : ℝ} (ht : 0 < t) : pB3 t = lB3 t := by
  have h := eq_of_hasDerivAt_of_eqOn ht (fun s hs => pB2_eq hs) (hasDerivAt_pB2 ht) (hasDerivAt_lB2 ht)
  exact (div_left_inj' ht.ne').mp h

/-! ## The bounds -/

theorem momP_bounds {t : ℝ} (ht : 0 < t) :
    t * momP 0 t ≤ 2 ∧ t ^ 2 * momP 1 t ≤ 4 ∧ t ^ 3 * momP 2 t ≤ 16 ∧ t ^ 4 * momP 3 t ≤ 96 := by
  have h0 := momP_le 0 ht
  have h1 := momP_le 1 ht
  have h2 := momP_le 2 ht
  have h3 := momP_le 3 ht
  have e0 : t ^ (0 + 1) * momP 0 t = t * momP 0 t := by ring
  have e1 : t ^ (1 + 1) * momP 1 t = t ^ 2 * momP 1 t := by ring
  have e2 : t ^ (2 + 1) * momP 2 t = t ^ 3 * momP 2 t := by ring
  have e3 : t ^ (3 + 1) * momP 3 t = t ^ 4 * momP 3 t := by ring
  have c0 : ((Nat.factorial 0 : ℕ) : ℝ) * 2 ^ (0 + 1) = 2 := by norm_num [Nat.factorial]
  have c1 : ((Nat.factorial 1 : ℕ) : ℝ) * 2 ^ (1 + 1) = 4 := by norm_num [Nat.factorial]
  have c2 : ((Nat.factorial 2 : ℕ) : ℝ) * 2 ^ (2 + 1) = 16 := by norm_num [Nat.factorial]
  have c3 : ((Nat.factorial 3 : ℕ) : ℝ) * 2 ^ (3 + 1) = 96 := by norm_num [Nat.factorial]
  rw [e0, c0] at h0
  rw [e1, c1] at h1
  rw [e2, c2] at h2
  rw [e3, c3] at h3
  exact ⟨h0, h1, h2, h3⟩

/-- **`|t pB0(t)| ≤ 2`.** -/
theorem abs_mul_pB0_le {t : ℝ} (ht : 0 < t) : |t * pB0 t| ≤ 2 := by
  obtain ⟨h0, -, -, -⟩ := momP_bounds ht
  rw [pB0_eq ht]
  unfold lB0
  rw [abs_of_nonneg (mul_nonneg ht.le (momP_nonneg 0 t))]
  exact h0

/-- **`|t pB1(t)| ≤ 4`.** -/
theorem abs_mul_pB1_le {t : ℝ} (ht : 0 < t) : |t * pB1 t| ≤ 4 := by
  obtain ⟨-, h1, -, -⟩ := momP_bounds ht
  have hm := momP_nonneg 1 t
  rw [pB1_eq ht]
  unfold lB1
  have e : t * -(t * momP 1 t) = -(t ^ 2 * momP 1 t) := by ring
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg t) hm)]
  exact h1

/-- **`|t pB2(t)| ≤ 20`.** -/
theorem abs_mul_pB2_le {t : ℝ} (ht : 0 < t) : |t * pB2 t| ≤ 20 := by
  obtain ⟨-, h1, h2, -⟩ := momP_bounds ht
  have hm1 := momP_nonneg 1 t
  have hm2 := momP_nonneg 2 t
  rw [pB2_eq ht]
  unfold lB2
  have e : t * (t ^ 2 * momP 2 t - t * momP 1 t) = t ^ 3 * momP 2 t - t ^ 2 * momP 1 t := by ring
  rw [e, abs_le]
  have a1 : 0 ≤ t ^ 2 * momP 1 t := mul_nonneg (sq_nonneg t) hm1
  have a2 : 0 ≤ t ^ 3 * momP 2 t := mul_nonneg (pow_pos ht 3).le hm2
  constructor <;> linarith

/-- **`|t pB3(t)| ≤ 148`.** -/
theorem abs_mul_pB3_le {t : ℝ} (ht : 0 < t) : |t * pB3 t| ≤ 148 := by
  obtain ⟨-, h1, h2, h3⟩ := momP_bounds ht
  have hm1 := momP_nonneg 1 t
  have hm2 := momP_nonneg 2 t
  have hm3 := momP_nonneg 3 t
  rw [pB3_eq ht]
  unfold lB3
  have e : t * (-(t ^ 3 * momP 3 t) + 3 * (t ^ 2 * momP 2 t) - t * momP 1 t)
      = -(t ^ 4 * momP 3 t) + 3 * (t ^ 3 * momP 2 t) - t ^ 2 * momP 1 t := by ring
  rw [e, abs_le]
  have a1 : 0 ≤ t ^ 2 * momP 1 t := mul_nonneg (sq_nonneg t) hm1
  have a2 : 0 ≤ t ^ 3 * momP 2 t := mul_nonneg (pow_pos ht 3).le hm2
  have a3 : 0 ≤ t ^ 4 * momP 3 t := mul_nonneg (pow_pos ht 4).le hm3
  constructor <;> linarith

theorem abs_momP_sub_bounds {t : ℝ} (ht : 0 < t) :
    |t ^ 3 * momP 0 t - 1 / 2 * t ^ 2| ≤ 19 ∧ |t ^ 4 * momP 1 t - 1 / 2 * t ^ 2| ≤ 105 ∧
      |t ^ 5 * momP 2 t - t ^ 2| ≤ 804 ∧ |t ^ 6 * momP 3 t - 3 * t ^ 2| ≤ 7860 := by
  have h0 := abs_momP_sub_le 0 ht
  have h1 := abs_momP_sub_le 1 ht
  have h2 := abs_momP_sub_le 2 ht
  have h3 := abs_momP_sub_le 3 ht
  have e0 : t ^ (0 + 3) * momP 0 t - ((Nat.factorial 0 : ℕ) : ℝ) / 2 * t ^ 2
      = t ^ 3 * momP 0 t - 1 / 2 * t ^ 2 := by norm_num [Nat.factorial]
  have e1 : t ^ (1 + 3) * momP 1 t - ((Nat.factorial 1 : ℕ) : ℝ) / 2 * t ^ 2
      = t ^ 4 * momP 1 t - 1 / 2 * t ^ 2 := by norm_num [Nat.factorial]
  have e2 : t ^ (2 + 3) * momP 2 t - ((Nat.factorial 2 : ℕ) : ℝ) / 2 * t ^ 2
      = t ^ 5 * momP 2 t - t ^ 2 := by norm_num [Nat.factorial]
  have e3 : t ^ (3 + 3) * momP 3 t - ((Nat.factorial 3 : ℕ) : ℝ) / 2 * t ^ 2
      = t ^ 6 * momP 3 t - 3 * t ^ 2 := by norm_num [Nat.factorial]
  have c0 : ((Nat.factorial (0 + 2) : ℕ) : ℝ) * (3 / 2 + 2 ^ (0 + 2 + 1)) = 19 := by
    norm_num [Nat.factorial]
  have c1 : ((Nat.factorial (1 + 2) : ℕ) : ℝ) * (3 / 2 + 2 ^ (1 + 2 + 1)) = 105 := by
    norm_num [Nat.factorial]
  have c2 : ((Nat.factorial (2 + 2) : ℕ) : ℝ) * (3 / 2 + 2 ^ (2 + 2 + 1)) = 804 := by
    norm_num [Nat.factorial]
  have c3 : ((Nat.factorial (3 + 2) : ℕ) : ℝ) * (3 / 2 + 2 ^ (3 + 2 + 1)) = 7860 := by
    norm_num [Nat.factorial]
  rw [e0, c0] at h0
  rw [e1, c1] at h1
  rw [e2, c2] at h2
  rw [e3, c3] at h3
  exact ⟨h0, h1, h2, h3⟩

/-- **`|t³ (pB0 + pB1)| ≤ 124`.** -/
theorem abs_pB01_le {t : ℝ} (ht : 0 < t) : |t ^ 3 * (pB0 t + pB1 t)| ≤ 124 := by
  obtain ⟨h0, h1, -, -⟩ := abs_momP_sub_bounds ht
  rw [pB0_eq ht, pB1_eq ht]
  unfold lB0 lB1
  have e : t ^ 3 * (momP 0 t + -(t * momP 1 t))
      = (t ^ 3 * momP 0 t - 1 / 2 * t ^ 2) - (t ^ 4 * momP 1 t - 1 / 2 * t ^ 2) := by ring
  rw [e]
  have a := abs_add_le (t ^ 3 * momP 0 t - 1 / 2 * t ^ 2) (-(t ^ 4 * momP 1 t - 1 / 2 * t ^ 2))
  rw [abs_neg, ← sub_eq_add_neg] at a
  linarith

/-- **`|t³ (pB1 + pB2)| ≤ 1014`.** -/
theorem abs_pB12_le {t : ℝ} (ht : 0 < t) : |t ^ 3 * (pB1 t + pB2 t)| ≤ 1014 := by
  obtain ⟨-, h1, h2, -⟩ := abs_momP_sub_bounds ht
  rw [pB1_eq ht, pB2_eq ht]
  unfold lB1 lB2
  have e : t ^ 3 * (-(t * momP 1 t) + (t ^ 2 * momP 2 t - t * momP 1 t))
      = -2 * (t ^ 4 * momP 1 t - 1 / 2 * t ^ 2) + (t ^ 5 * momP 2 t - t ^ 2) := by ring
  rw [e]
  have a := abs_add_le (-2 * (t ^ 4 * momP 1 t - 1 / 2 * t ^ 2)) (t ^ 5 * momP 2 t - t ^ 2)
  have b : |-2 * (t ^ 4 * momP 1 t - 1 / 2 * t ^ 2)| = 2 * |t ^ 4 * momP 1 t - 1 / 2 * t ^ 2| := by
    rw [abs_mul]
    norm_num
  linarith

/-- **`|t³ (pB2 + pB3)| ≤ 11286`.** -/
theorem abs_pB23_le {t : ℝ} (ht : 0 < t) : |t ^ 3 * (pB2 t + pB3 t)| ≤ 11286 := by
  obtain ⟨-, h1, h2, h3⟩ := abs_momP_sub_bounds ht
  rw [pB2_eq ht, pB3_eq ht]
  unfold lB2 lB3
  have e : t ^ 3 * ((t ^ 2 * momP 2 t - t * momP 1 t)
        + (-(t ^ 3 * momP 3 t) + 3 * (t ^ 2 * momP 2 t) - t * momP 1 t))
      = -2 * (t ^ 4 * momP 1 t - 1 / 2 * t ^ 2) + 4 * (t ^ 5 * momP 2 t - t ^ 2)
        - (t ^ 6 * momP 3 t - 3 * t ^ 2) := by ring
  rw [e]
  have a := abs_add_le (-2 * (t ^ 4 * momP 1 t - 1 / 2 * t ^ 2) + 4 * (t ^ 5 * momP 2 t - t ^ 2))
    (-(t ^ 6 * momP 3 t - 3 * t ^ 2))
  rw [abs_neg, ← sub_eq_add_neg] at a
  have a2 := abs_add_le (-2 * (t ^ 4 * momP 1 t - 1 / 2 * t ^ 2)) (4 * (t ^ 5 * momP 2 t - t ^ 2))
  have b1 : |-2 * (t ^ 4 * momP 1 t - 1 / 2 * t ^ 2)| = 2 * |t ^ 4 * momP 1 t - 1 / 2 * t ^ 2| := by
    rw [abs_mul]
    norm_num
  have b2 : |4 * (t ^ 5 * momP 2 t - t ^ 2)| = 4 * |t ^ 5 * momP 2 t - t ^ 2| := by
    rw [abs_mul]
    norm_num
  linarith

end Tower.RV6
