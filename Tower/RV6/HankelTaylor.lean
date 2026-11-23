import Mathlib
import Tower.RV6.BesselJ
import Tower.RV6.BesselR
import Tower.RV6.HankelIBP

/-!
# The Hankel transform near `x = 0`

* `abs_besselJ1_sub_le`, `abs_besselJ0_taylor_le`: `|J₁(t) - t/2| ≤ t²` and `|J₀(z) - 1 + z²/4| ≤ z³`
  for `t, z ≥ 0` (mean value inequality, from `0 ≤ 1 - J₀(s) ≤ s`);
* **`hk_taylor`**: `|hk ψ x - hk ψ 0 + (x²/4) hk (t² ψ) 0| ≤ x³ ∫ |t⁴ ψ|` for `ψ ∈ HDom`, `x ≥ 0`;
* `hk_shift_zero`, `hk_shift3_zero`: for a chain `(ψ, ψ₁ = θψ)`, `hk ψ₁ 0 = -2 hk ψ 0` and
  `hk (t² ψ₁) 0 = -4 hk (t² ψ) 0` (the first integration by parts at `x = 0`);
* `Bser_one_le` (`B(1) = I₁(2) ≤ 2e`) and `ity_bserI1` (`B(t²/4)/2 = I₁(t)/t` has the bounds `ITy`);
* elementary bounds (`abs_quart_le`, `abs_x4_le`, `abs_mul_le_mul_of`, `abs_add5_le`) and two limits:
  `eq_zero_of_abs_le_mul` and `log_consts_eq_zero` (`|c₁ + c₂ log x| ≤ K x` on `(0, 1]` forces
  `c₁ = c₂ = 0`).
-/

namespace Tower.RV6

open MeasureTheory

/-! ## `I₁(t)/t` -/

/-- `B(1) = I₁(2) ≤ sinh 2 ≤ e²/2 ≤ 2e`. -/
theorem Bser_one_le : Bser 1 ≤ 2 * Real.exp 1 := by
  have h1 : besselI1 2 = Bser 1 := by
    rw [besselI1_eq]
    norm_num
  have h2 : besselI1 2 ≤ Real.sinh 2 := besselI1_le_sinh (by norm_num)
  have h3 : Real.sinh 2 ≤ Real.exp 2 / 2 := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (-2)
    linarith
  have h4 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h5 : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9
    linarith
  have h6 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith [mul_pos h6 (sub_pos.mpr h5)]

/-- `B(t²/4)/2` (`= I₁(t)/t` for `t ≠ 0`) has the bounds of `I₀` and `t I₁`. -/
theorem ity_bserI1 : ITy (fun t : ℝ => Bser (t / 2 * (t / 2)) / 2) := by
  have hm : Continuous (fun t : ℝ => t / 2 * (t / 2)) :=
    (continuous_id.div_const 2).mul (continuous_id.div_const 2)
  have hc : Continuous (fun t : ℝ => Bser (t / 2 * (t / 2)) / 2) :=
    (continuous_Bser.comp hm).div_const 2
  refine ⟨hc.continuousOn, fun t ht ht1 => ?_, fun t ht => ?_⟩
  · show |Bser (t / 2 * (t / 2)) / 2| ≤ Real.exp 1
    have hs0 : 0 ≤ t / 2 * (t / 2) := mul_self_nonneg (t / 2)
    have hs1 : t / 2 * (t / 2) ≤ 1 := by
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
    have hB := Bser_mono hs0 hs1
    have hB0 : 0 ≤ Bser (t / 2 * (t / 2)) := Bser_nonneg hs0
    have hB1 := Bser_one_le
    rw [abs_of_nonneg (by linarith)]
    linarith
  · show |Bser (t / 2 * (t / 2)) / 2| ≤ t * Real.exp t
    have hs0 : 0 ≤ t / 2 * (t / 2) := mul_self_nonneg (t / 2)
    have hB0 : 0 ≤ Bser (t / 2 * (t / 2)) := Bser_nonneg hs0
    have hI : besselI1 t = t * (Bser (t / 2 * (t / 2)) / 2) := by
      rw [besselI1_eq]
      ring
    have h1 : besselI1 t ≤ Real.sinh t := besselI1_le_sinh (by linarith)
    have h2 : Real.sinh t ≤ Real.exp t := sinh_le_exp_self t
    have h3 : 0 < Real.exp t := Real.exp_pos t
    rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hB0, mul_nonneg (sub_nonneg.mpr ht) h3.le]

/-! ## The kernel near `0` -/

/-- `|J₁(t) - t/2| ≤ t²` for `t ≥ 0`. -/
theorem abs_besselJ1_sub_le {t : ℝ} (ht : 0 ≤ t) : |besselJ1 t - t / 2| ≤ t ^ 2 := by
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, besselJ1_zero]
    norm_num
  have hq : ∀ s ∈ Set.Icc (0 : ℝ) t, HasDerivWithinAt (fun s : ℝ => s * besselJ1 s - s ^ 2 / 2)
      (s * besselJ0 s - s) (Set.Icc 0 t) s := by
    intro s _
    have h1 := hasDerivAt_mul_besselJ1 s
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) (2 * s / 2) s := (hasDerivAt_sqx s).div_const 2
    have h3 := h1.sub h2
    have h4 : HasDerivAt (fun s : ℝ => s * besselJ1 s - s ^ 2 / 2) (s * besselJ0 s - s) s := by
      have e : s * besselJ0 s - 2 * s / 2 = s * besselJ0 s - s := by ring
      rw [← e]
      exact h3
    exact h4.hasDerivWithinAt
  have hb : ∀ s ∈ Set.Ico (0 : ℝ) t, ‖s * besselJ0 s - s‖ ≤ t ^ 2 := by
    intro s hs
    rw [Real.norm_eq_abs]
    have j1 := one_sub_besselJ0_le hs.1
    have j3 : besselJ0 s ≤ 1 := (abs_le.mp (abs_besselJ0_le_one hs.1)).2
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr j1),
        mul_nonneg (sub_nonneg.mpr hs.2.le) (add_nonneg hs.1 ht)]
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr j3), sq_nonneg t]
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hq hb t ⟨ht, le_rfl⟩
  rw [Real.norm_eq_abs] at hm
  have hm' : |t * besselJ1 t - t ^ 2 / 2 - (0 * besselJ1 0 - 0 ^ 2 / 2)| ≤ t ^ 2 * (t - 0) := hm
  have e : t * besselJ1 t - t ^ 2 / 2 - (0 * besselJ1 0 - 0 ^ 2 / 2) = t * (besselJ1 t - t / 2) := by
    ring
  have e2 : t ^ 2 * (t - 0) = t * t ^ 2 := by ring
  rw [e, e2, abs_mul, abs_of_pos hpos] at hm'
  exact le_of_mul_le_mul_left hm' hpos

/-- `|J₀(z) - 1 + z²/4| ≤ z³` for `z ≥ 0`. -/
theorem abs_besselJ0_taylor_le {z : ℝ} (hz : 0 ≤ z) : |besselJ0 z - 1 + z ^ 2 / 4| ≤ z ^ 3 := by
  have hr : ∀ s ∈ Set.Icc (0 : ℝ) z, HasDerivWithinAt (fun s : ℝ => besselJ0 s - 1 + s ^ 2 / 4)
      (-(besselJ1 s - s / 2)) (Set.Icc 0 z) s := by
    intro s _
    have h1 := ((hasDerivAt_besselJ0 s).sub_const 1).add ((hasDerivAt_sqx s).div_const 4)
    have h2 : HasDerivAt (fun s : ℝ => besselJ0 s - 1 + s ^ 2 / 4) (-(besselJ1 s - s / 2)) s := by
      have e : -besselJ1 s + 2 * s / 4 = -(besselJ1 s - s / 2) := by ring
      rw [← e]
      exact h1
    exact h2.hasDerivWithinAt
  have hb : ∀ s ∈ Set.Ico (0 : ℝ) z, ‖-(besselJ1 s - s / 2)‖ ≤ z ^ 2 := by
    intro s hs
    rw [norm_neg, Real.norm_eq_abs]
    have h1 := abs_besselJ1_sub_le hs.1
    have h2 : s ^ 2 ≤ z ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2.le) (add_nonneg hs.1 hz)]
    linarith
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hr hb z ⟨hz, le_rfl⟩
  rw [Real.norm_eq_abs] at hm
  have hm' : |besselJ0 z - 1 + z ^ 2 / 4 - (besselJ0 0 - 1 + 0 ^ 2 / 4)| ≤ z ^ 2 * (z - 0) := hm
  rw [besselJ0_zero] at hm'
  have e1 : besselJ0 z - 1 + z ^ 2 / 4 - (1 - 1 + 0 ^ 2 / 4) = besselJ0 z - 1 + z ^ 2 / 4 := by ring
  have e2 : z ^ 2 * (z - 0) = z ^ 3 := by ring
  rw [e1, e2] at hm'
  exact hm'

/-! ## `hk` near `x = 0` -/

/-- **`hk ψ x = hk ψ 0 - (x²/4) hk (t² ψ) 0 + O(x³)`**, with the constant `∫ |t⁴ ψ|`. -/
theorem hk_taylor {ψ : ℝ → ℝ} (hψ : HDom ψ) {x : ℝ} (hx : 0 ≤ x) :
    |hk ψ x - hk ψ 0 + x ^ 2 / 4 * hk (fun t => t ^ 2 * ψ t) 0|
      ≤ x ^ 3 * ∫ t in Set.Ioi (0 : ℝ), |t ^ 4 * ψ t| := by
  have i1 : IntegrableOn (fun t : ℝ => besselJ0 (x * t) * ψ t * t) (Set.Ioi 0) :=
    integrableOn_hk hψ hx
  have i0 : IntegrableOn (fun t : ℝ => besselJ0 (0 * t) * ψ t * t) (Set.Ioi 0) :=
    integrableOn_hk hψ (le_refl 0)
  have i2 : IntegrableOn (fun t : ℝ => besselJ0 (0 * t) * (t ^ 2 * ψ t) * t) (Set.Ioi 0) :=
    integrableOn_hk (hdom_pow_mul 2 hψ) (le_refl 0)
  have i4 : IntegrableOn (fun t : ℝ => t ^ 4 * ψ t) (Set.Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => t ^ 4 * ψ t * (fun _ : ℝ => (1 : ℝ)) t) (Set.Ioi 0) :=
      integrableOn_hdom (g := fun _ : ℝ => (1 : ℝ)) hψ continuousOn_const (G := 1)
        (fun _ _ => by simp) (j := 4) (by norm_num)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    show t ^ 4 * ψ t * 1 = t ^ 4 * ψ t
    ring
  have i10 : IntegrableOn
      (fun t : ℝ => besselJ0 (x * t) * ψ t * t - besselJ0 (0 * t) * ψ t * t) (Set.Ioi 0) :=
    Integrable.sub i1 i0
  have i3 : IntegrableOn (fun t : ℝ => x ^ 2 / 4 * (besselJ0 (0 * t) * (t ^ 2 * ψ t) * t))
      (Set.Ioi 0) := Integrable.const_mul i2 (x ^ 2 / 4)
  have a1 := integral_add i10 i3
  have a2 := integral_sub i1 i0
  have a3 : ∫ t in Set.Ioi (0 : ℝ), x ^ 2 / 4 * (besselJ0 (0 * t) * (t ^ 2 * ψ t) * t)
      = x ^ 2 / 4 * ∫ t in Set.Ioi (0 : ℝ), besselJ0 (0 * t) * (t ^ 2 * ψ t) * t :=
    integral_const_mul _ _
  have e : hk ψ x - hk ψ 0 + x ^ 2 / 4 * hk (fun t => t ^ 2 * ψ t) 0
      = ∫ t in Set.Ioi (0 : ℝ), (besselJ0 (x * t) * ψ t * t - besselJ0 (0 * t) * ψ t * t
          + x ^ 2 / 4 * (besselJ0 (0 * t) * (t ^ 2 * ψ t) * t)) := by
    show (∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * ψ t * t)
        - (∫ t in Set.Ioi (0 : ℝ), besselJ0 (0 * t) * ψ t * t)
        + x ^ 2 / 4 * (∫ t in Set.Ioi (0 : ℝ), besselJ0 (0 * t) * (t ^ 2 * ψ t) * t) = _
    linarith [a1, a2, a3]
  have hg : Integrable (fun t : ℝ => x ^ 3 * |t ^ 4 * ψ t|) (volume.restrict (Set.Ioi 0)) :=
    Integrable.const_mul (Integrable.abs i4) (x ^ 3)
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖besselJ0 (x * t) * ψ t * t - besselJ0 (0 * t) * ψ t * t
          + x ^ 2 / 4 * (besselJ0 (0 * t) * (t ^ 2 * ψ t) * t)‖ ≤ x ^ 3 * |t ^ 4 * ψ t| := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => ?_))
    have htp : 0 < t := ht
    rw [Real.norm_eq_abs]
    have hr := abs_besselJ0_taylor_le (mul_nonneg hx htp.le)
    have ef : besselJ0 (x * t) * ψ t * t - besselJ0 (0 * t) * ψ t * t
        + x ^ 2 / 4 * (besselJ0 (0 * t) * (t ^ 2 * ψ t) * t)
        = (besselJ0 (x * t) - 1 + (x * t) ^ 2 / 4) * (ψ t * t) := by
      rw [zero_mul, besselJ0_zero]
      ring
    rw [ef, abs_mul]
    have e4 : (x * t) ^ 3 * |ψ t * t| = x ^ 3 * |t ^ 4 * ψ t| := by
      rw [abs_mul, abs_mul, abs_of_pos htp, abs_of_pos (pow_pos htp 4)]
      ring
    rw [← e4]
    exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)
  have hb := norm_integral_le_of_norm_le hg hae
  have hc : ∫ t in Set.Ioi (0 : ℝ), x ^ 3 * |t ^ 4 * ψ t|
      = x ^ 3 * ∫ t in Set.Ioi (0 : ℝ), |t ^ 4 * ψ t| := integral_const_mul _ _
  rw [Real.norm_eq_abs, hc] at hb
  rw [e]
  exact hb

/-- At `x = 0` the first integration by parts gives `hk ψ₁ 0 = -2 hk ψ 0`. -/
theorem hk_shift_zero {ψ ψ1 : ℝ → ℝ} (hc : HChain ψ ψ1) : hk ψ1 0 + 2 * hk ψ 0 = 0 := by
  have h : ∫ t in Set.Ioi (0 : ℝ), t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (0 * t)
      = ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * ψ t * (0 * besselJ1 (0 * t)) := hk_ibpA hc (le_refl 0)
  have e1 : ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * ψ t * (0 * besselJ1 (0 * t)) = 0 := by simp
  have e2 : hk (fun t => ψ1 t + 2 * ψ t) 0
      = ∫ t in Set.Ioi (0 : ℝ), t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (0 * t) := by
    unfold hk
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show besselJ0 (0 * t) * (ψ1 t + 2 * ψ t) * t = t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (0 * t)
    ring
  have e3 : hk (fun t => ψ1 t + 2 * ψ t) 0 = hk ψ1 0 + 2 * hk ψ 0 :=
    hk_add_cmul hc.2.1 hc.1 2 (le_refl 0)
  linarith [h, e1, e2, e3]

/-- The same for `t² ψ`: `hk (t² ψ₁) 0 = -4 hk (t² ψ) 0`. -/
theorem hk_shift3_zero {ψ ψ1 : ℝ → ℝ} (hc : HChain ψ ψ1) :
    hk (fun t => t ^ 2 * ψ1 t) 0 + 4 * hk (fun t => t ^ 2 * ψ t) 0 = 0 := by
  have h : hk (fun t => t ^ 2 * (ψ1 t + 2 * ψ t)) 0 + 2 * hk (fun t => t ^ 2 * ψ t) 0 = 0 :=
    hk_shift_zero (hchain_tsq hc)
  have e : hk (fun t => t ^ 2 * (ψ1 t + 2 * ψ t)) 0
      = hk (fun t => t ^ 2 * ψ1 t + 2 * (t ^ 2 * ψ t)) 0 := hk_congr (fun t => by ring) 0
  have e2 : hk (fun t => t ^ 2 * ψ1 t + 2 * (t ^ 2 * ψ t)) 0
      = hk (fun t => t ^ 2 * ψ1 t) 0 + 2 * hk (fun t => t ^ 2 * ψ t) 0 :=
    hk_add_cmul (hdom_pow_mul 2 hc.2.1) (hdom_pow_mul 2 hc.1) 2 (le_refl 0)
  linarith [h, e, e2]

/-! ## Elementary bounds -/

theorem abs_quart_le {a b c x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ha : a ≤ 0) (hb : b ≤ 0)
    (hc : c ≤ 0) : |a * x ^ 4 + b * x ^ 2 + c| ≤ -(a + b + c) := by
  have h2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
  have h4 : x ^ 4 ≤ 1 := pow_le_one₀ hx0 hx1
  have h2' : 0 ≤ x ^ 2 := pow_nonneg hx0 2
  have h4' : 0 ≤ x ^ 4 := pow_nonneg hx0 4
  have e1 : a ≤ a * x ^ 4 := by nlinarith
  have e2 : b ≤ b * x ^ 2 := by nlinarith
  have e3 : a * x ^ 4 ≤ 0 := by nlinarith
  have e4 : b * x ^ 2 ≤ 0 := by nlinarith
  rw [abs_le]
  constructor <;> linarith

theorem abs_x4_le {q4 q6 x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x ^ 4 * (q4 + q6 * x ^ 2)| ≤ x ^ 3 * (|q4| + |q6|) := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 4)]
  have a1 : |q4 + q6 * x ^ 2| ≤ |q4| + |q6| := by
    have t1 := abs_add_le q4 (q6 * x ^ 2)
    have t2 : |q6 * x ^ 2| ≤ |q6| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 2)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hx0 hx1)
    linarith
  have a2 : x ^ 4 ≤ x ^ 3 := by
    have := pow_nonneg hx0 3
    nlinarith
  exact mul_le_mul a2 a1 (abs_nonneg _) (pow_nonneg hx0 3)

theorem abs_mul_le_mul_of {p r P R : ℝ} (hp : |p| ≤ P) (hr : |r| ≤ R) : |p * r| ≤ P * R := by
  rw [abs_mul]
  exact mul_le_mul hp hr (abs_nonneg _) ((abs_nonneg _).trans hp)

theorem abs_add5_le (a b c d e : ℝ) : |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have t1 := abs_add_le (a + b + c + d) e
  have t2 := abs_add_le (a + b + c) d
  have t3 := abs_add_le (a + b) c
  have t4 := abs_add_le a b
  linarith

/-! ## Two limits at `0+` -/

theorem eq_zero_of_abs_le_mul {a K δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : ℝ, 0 < x → x ≤ δ → |a| ≤ K * x) : a = 0 := by
  have hlim : Filter.Tendsto (fun x : ℝ => K * x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun x : ℝ => K * x) (nhds 0) (nhds (K * 0)) :=
      Filter.tendsto_id.const_mul K
    rw [mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), |a| ≤ K * x := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    exact h x hx.1 hx.2.le
  have h1 : |a| ≤ 0 := ge_of_tendsto hlim hev
  exact abs_nonpos_iff.mp h1

/-- `|c₁ + c₂ log x| ≤ K x` on `(0, 1]` forces `c₁ = c₂ = 0`. -/
theorem log_consts_eq_zero {c1 c2 K : ℝ}
    (h : ∀ x : ℝ, 0 < x → x ≤ 1 → |c1 + c2 * Real.log x| ≤ K * x) : c1 = 0 ∧ c2 = 0 := by
  have hc1 : c1 = 0 := by
    refine eq_zero_of_abs_le_mul (K := 3 * K) one_pos (fun x hx hx1 => ?_)
    have h1 := h x hx hx1
    have h2 := h (x ^ 2) (pow_pos hx 2) (pow_le_one₀ hx.le hx1)
    have hl : Real.log (x ^ 2) = 2 * Real.log x := by
      rw [Real.log_pow]
      norm_num
    rw [hl] at h2
    have hK : 0 ≤ K := by
      have := abs_nonneg (c1 + c2 * Real.log x)
      nlinarith
    have hxx : K * x ^ 2 ≤ K * x := by
      nlinarith [mul_nonneg hK (mul_nonneg hx.le (sub_nonneg.mpr hx1))]
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    rw [abs_le]
    constructor <;> linarith
  refine ⟨hc1, eq_zero_of_abs_le_mul (K := 2 * K) (δ := 1 / 2) (by norm_num) (fun x hx hx1 => ?_)⟩
  have h1 := h x hx (by linarith)
  rw [hc1, zero_add, abs_mul] at h1
  have hl : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
  have hl2 : 1 / 2 ≤ |Real.log x| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have := mul_le_mul_of_nonneg_left hl2 (abs_nonneg c2)
  linarith

end Tower.RV6
