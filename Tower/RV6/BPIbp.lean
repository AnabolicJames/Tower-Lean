import Mathlib
import Tower.RV6.SmallG
import Tower.RV6.CuspBesselF

/-!
# RungBP, step 1: the two integrations by parts

For `x > 0`, with `F₂ = θ²f/t` and `G = -θg/t`:

* `x2_hjF_eq`: `x² hjF(x) = ∫₀^∞ F₂(t) (1 - J₀(xt)) dt` (boundary function `f · xtJ₁(xt) + θf · (J₀(xt) - 1)`);
* `ajG_eq_one_sub`: `ajG(x) = ∫₀^∞ G(t) (1 - J₀(xt)) dt` (boundary function `g · (1 - J₀(xt))`), from the general
  `AJ_eq_one_sub` for a chain `ψ, ψ₁ = θψ` in `PDom`;
* `one_sub_besselJ0_le_sq`: `0 ≤ 1 - J₀(z) ≤ z²/4` for `z ≥ 0`.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

theorem one_sub_besselJ0_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ 1 - besselJ0 z := by
  have h := (abs_le.mp (abs_besselJ0_le_one hz)).2
  linarith

/-- `1 - J₀(z) ≤ z²/4` for `z ≥ 0`. -/
theorem one_sub_besselJ0_le_sq {z : ℝ} (hz : 0 ≤ z) : 1 - besselJ0 z ≤ z ^ 2 / 4 := by
  have hc : ContinuousOn (fun x : ℝ => 1 - besselJ0 x - x ^ 2 / 4) (Set.Ici (0 : ℝ)) :=
    ((continuous_const.sub continuous_besselJ0).sub
      ((continuous_pow 2 : Continuous fun x : ℝ => x ^ 2).div_const 4)).continuousOn
  have hd : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ => 1 - besselJ0 y - y ^ 2 / 4) (besselJ1 x - x / 2) x := by
    intro x _
    have h := ((hasDerivAt_besselJ0 x).const_sub 1).sub ((hasDerivAt_sqx x).div_const 4)
    exact h.congr_deriv (by ring)
  have hn : ∀ x : ℝ, 0 < x → besselJ1 x - x / 2 ≤ 0 := by
    intro x hx
    have h1 := abs_besselJ1_le_half hx.le
    have h2 := (abs_le.mp h1).2
    linarith
  have h : 1 - besselJ0 z - z ^ 2 / 4 ≤ 1 - besselJ0 0 - (0 : ℝ) ^ 2 / 4 :=
    antitone_of_hasDerivAt_nonpos (f' := fun x => besselJ1 x - x / 2) hc hd hn
      (le_refl (0 : ℝ)) hz
  have e : (0 : ℝ) ^ 2 / 4 = 0 := by norm_num
  rw [besselJ0_zero, e] at h
  linarith

/-! ## The `J₀` side: `x² hjF(x) = ∫ F₂ (1 - J₀(xt))` -/

/-- **`x² hjF(x) = ∫₀^∞ (θ²f/t)(1 - J₀(xt)) dt`** for `x > 0`. -/
theorem x2_hjF_eq {x : ℝ} (hx : 0 < x) :
    x ^ 2 * hjF x = ∫ t in Set.Ioi (0 : ℝ), thF2 t / t * (1 - besselJ0 (x * t)) := by
  have hF0 : (fun t : ℝ => thF0 t * (x * t * besselJ1 (x * t))
      + thF1 t * (besselJ0 (x * t) - 1)) 0 = 0 := by
    simp [besselJ0_zero]
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt
      (fun t : ℝ => thF0 t * (x * t * besselJ1 (x * t)) + thF1 t * (besselJ0 (x * t) - 1))
      (x ^ 2 * (besselJ0 (x * t) * thF0 t * t) + thF2 t / t * (besselJ0 (x * t) - 1)) t := by
    intro t ht
    have d1 := hasDerivAt_thF0 ht
    have d2 : HasDerivAt (fun t : ℝ => x * t * besselJ1 (x * t))
        (x * t * besselJ0 (x * t) * (x * 1)) t :=
      (hasDerivAt_mul_besselJ1 (x * t)).comp t ((hasDerivAt_id' t).const_mul x)
    have d3 := hasDerivAt_thF1 ht
    have d4 : HasDerivAt (fun t : ℝ => besselJ0 (x * t) - 1)
        (-besselJ1 (x * t) * (x * 1)) t :=
      ((hasDerivAt_besselJ0 (x * t)).comp t ((hasDerivAt_id' t).const_mul x)).sub_const 1
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    have h := (d1.mul d2).add (d3.mul d4)
    exact h.congr_deriv (by
      linear_combination (x * thF1 t * besselJ1 (x * t)) * hinv)
  have h0 : Tendsto
      (fun t : ℝ => thF0 t * (x * t * besselJ1 (x * t)) + thF1 t * (besselJ0 (x * t) - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have T1 := tendsto_hdom_one_zero (g := fun t => x * besselJ1 (x * t)) hdom_thF0 (G := x)
      (abs_mul_besselJ1_mul_le hx.le)
    have T2 := tendsto_hdom_one_zero (g := fun t => (besselJ0 (x * t) - 1) / t) hdom_thF1
      (G := x) (fun t ht => by
        show |(besselJ0 (x * t) - 1) / t| ≤ x
        have j1 := one_sub_besselJ0_le (mul_nonneg hx.le ht.le)
        have j2 : besselJ0 (x * t) ≤ 1 :=
          (abs_le.mp (abs_besselJ0_le_one (mul_nonneg hx.le ht.le))).2
        rw [abs_div, abs_of_pos ht, abs_sub_comm, abs_of_nonneg (by linarith),
          div_le_iff₀ ht]
        linarith)
    have T := T1.add T2
    rw [add_zero] at T
    refine T.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ht)
    rw [div_eq_mul_inv]
    linear_combination (thF1 t * (besselJ0 (x * t) - 1)) * hinv
  have hinf : Tendsto
      (fun t : ℝ => thF0 t * (x * t * besselJ1 (x * t)) + thF1 t * (besselJ0 (x * t) - 1))
      atTop (nhds 0) := by
    have U1 := tendsto_hdom_pow_atTop 1 (g := fun t => x * besselJ1 (x * t)) hdom_thF0 (G := x)
      (abs_mul_besselJ1_mul_le hx.le)
    have U2 := tendsto_hdom_pow_atTop 0 (g := fun t => besselJ0 (x * t) - 1) hdom_thF1 (G := 2)
      (fun t ht => by
        show |besselJ0 (x * t) - 1| ≤ 2
        have j := abs_besselJ0_le_one (mul_nonneg hx.le ht.le)
        have := abs_sub (besselJ0 (x * t)) 1
        rw [abs_one] at this
        linarith)
    have U := U1.add U2
    rw [add_zero] at U
    refine U.congr' ?_
    filter_upwards with t
    ring
  have i1 : IntegrableOn (fun t : ℝ => besselJ0 (x * t) * thF0 t * t) (Set.Ioi 0) :=
    integrableOn_hk hdom_thF0 hx.le
  have i2 : IntegrableOn (fun t : ℝ => thF2 t / t * (besselJ0 (x * t) - 1)) (Set.Ioi 0) := by
    have hcg : ContinuousOn (fun t : ℝ => (besselJ0 (x * t) - 1) / t ^ 2) (Set.Ioi 0) :=
      ((continuousOn_besselJ0_mul x).sub continuousOn_const).div
        (continuous_pow 2).continuousOn (fun t ht => pow_ne_zero 2 (ne_of_gt ht))
    have h : IntegrableOn (fun t : ℝ => t ^ 1 * thF2 t * (fun t => (besselJ0 (x * t) - 1) / t ^ 2) t)
        (Set.Ioi 0) :=
      integrableOn_hdom (g := fun t => (besselJ0 (x * t) - 1) / t ^ 2) hdom_thF2 hcg
        (G := x ^ 2 / 4)
        (fun t ht => by
          show |(besselJ0 (x * t) - 1) / t ^ 2| ≤ x ^ 2 / 4
          have j0 := one_sub_besselJ0_nonneg (mul_nonneg hx.le ht.le)
          have j1 := one_sub_besselJ0_le_sq (mul_nonneg hx.le ht.le)
          have ht2 : 0 < t ^ 2 := pow_pos ht 2
          rw [abs_div, abs_of_pos ht2, abs_sub_comm, abs_of_nonneg j0, div_le_iff₀ ht2]
          have e : (x * t) ^ 2 / 4 = x ^ 2 / 4 * t ^ 2 := by ring
          linarith) (le_refl 1)
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ht)
    show t ^ 1 * thF2 t * ((besselJ0 (x * t) - 1) / t ^ 2) = thF2 t / t * (besselJ0 (x * t) - 1)
    linear_combination (thF2 t * (besselJ0 (x * t) - 1) * t⁻¹) * hinv
  have i12 : IntegrableOn (fun t : ℝ => x ^ 2 * (besselJ0 (x * t) * thF0 t * t)) (Set.Ioi 0) :=
    Integrable.const_mul i1 (x ^ 2)
  have hint : IntegrableOn
      (fun t : ℝ => x ^ 2 * (besselJ0 (x * t) * thF0 t * t) + thF2 t / t * (besselJ0 (x * t) - 1))
      (Set.Ioi 0) := Integrable.add i12 i2
  have hz := integral_Ioi_deriv_eq_zero hF0 hd h0 hinf hint
  have a1 := integral_add i12 i2
  have a2 : ∫ t in Set.Ioi (0 : ℝ), x ^ 2 * (besselJ0 (x * t) * thF0 t * t)
      = x ^ 2 * ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * thF0 t * t := integral_const_mul _ _
  have e3 : ∫ t in Set.Ioi (0 : ℝ), thF2 t / t * (1 - besselJ0 (x * t))
      = -∫ t in Set.Ioi (0 : ℝ), thF2 t / t * (besselJ0 (x * t) - 1) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show thF2 t / t * (1 - besselJ0 (x * t)) = -(thF2 t / t * (besselJ0 (x * t) - 1))
    ring
  rw [hjF_eq_hk, ← thF0_eq_fB]
  show x ^ 2 * (∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * thF0 t * t) = _
  linarith [hz, a1, a2, e3]

/-! ## The `J₁` side: `AJ ψ x = ∫ (-ψ₁/t)(1 - J₀(xt))` -/

/-- `(ψ₁(t)/t)(1 - J₀(xt))` is integrable on `(0, ∞)` for `ψ₁ ∈ PDom` and `x ≥ 0`. -/
theorem integrableOn_div_one_sub {ψ1 : ℝ → ℝ} (h1 : PDom ψ1) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => ψ1 t / t * (1 - besselJ0 (x * t))) (Set.Ioi 0) := by
  obtain ⟨hc, C, hC0, hn, hf⟩ := h1
  have hcont : ContinuousOn (fun t : ℝ => ψ1 t / t * (1 - besselJ0 (x * t))) (Set.Ioi 0) :=
    (hc.div continuousOn_id (fun t ht => ne_of_gt ht)).mul
      (continuousOn_const.sub (continuous_besselJ0_mul' x).continuousOn)
  refine integrableOn_Ioi_of_bounds hcont (A := C * x ^ 2 / 4) (B := 2 * C)
    (fun t ht ht1 => ?_) (fun t ht => ?_)
  · have ha := abs_le_of_sqrt_mul_le ht (hn t ht ht1)
    have hj0 := one_sub_besselJ0_nonneg (mul_nonneg hx ht.le)
    have hj := one_sub_besselJ0_le_sq (mul_nonneg hx ht.le)
    have hs := Real.sqrt_pos.mpr ht
    have hsi : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hs
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    rw [abs_mul, abs_div, abs_of_pos ht, abs_of_nonneg hj0]
    have hX : 0 ≤ C * x ^ 2 / 4 * (Real.sqrt t)⁻¹ :=
      mul_nonneg (div_nonneg (mul_nonneg hC0 (sq_nonneg x)) (by norm_num)) hsi.le
    calc |ψ1 t| / t * (1 - besselJ0 (x * t))
        ≤ C * (Real.sqrt t)⁻¹ / t * ((x * t) ^ 2 / 4) :=
          mul_le_mul (div_le_div_of_nonneg_right ha ht.le) hj hj0
            (div_nonneg (mul_nonneg hC0 hsi.le) ht.le)
      _ = C * x ^ 2 / 4 * (Real.sqrt t)⁻¹ * t := by
          linear_combination (C * x ^ 2 / 4 * (Real.sqrt t)⁻¹ * t) * hinv
      _ ≤ C * x ^ 2 / 4 * (Real.sqrt t)⁻¹ := mul_le_of_le_one_right hX ht1
  · have ht0 : 0 < t := by linarith
    have ha := abs_le_of_sq_mul_le ht0 (hf t ht.le)
    have hj0 := one_sub_besselJ0_nonneg (mul_nonneg hx ht0.le)
    have hj2 : 1 - besselJ0 (x * t) ≤ 2 := by
      have h := (abs_le.mp (abs_besselJ0_le_one (mul_nonneg hx ht0.le))).1
      linarith
    rw [abs_mul, abs_div, abs_of_pos ht0, abs_of_nonneg hj0]
    have hd : |ψ1 t| / t ≤ |ψ1 t| := div_le_self (abs_nonneg _) ht.le
    calc |ψ1 t| / t * (1 - besselJ0 (x * t)) ≤ |ψ1 t| * 2 :=
          mul_le_mul hd hj2 hj0 (abs_nonneg _)
      _ ≤ C * (t ^ 2)⁻¹ * 2 := by linarith
      _ = 2 * C * (t ^ 2)⁻¹ := by ring

/-- **`AJ ψ x = ∫₀^∞ (-ψ₁(t)/t)(1 - J₀(xt)) dt`** for a chain `ψ, ψ₁ = θψ` in `PDom` and `x > 0`. -/
theorem AJ_eq_one_sub {ψ ψ1 : ℝ → ℝ} (h0 : PDom ψ) (h1 : PDom ψ1)
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt ψ (ψ1 t / t) t) {x : ℝ} (hx : 0 < x) :
    AJ ψ x = ∫ t in Set.Ioi (0 : ℝ), -ψ1 t / t * (1 - besselJ0 (x * t)) := by
  have i1 := integrableOn_div_one_sub h1 hx.le
  obtain ⟨hc0, C, hC0, hn, hf⟩ := h0
  have hF0 : (fun t : ℝ => ψ t * (1 - besselJ0 (x * t))) 0 = 0 := by
    simp [besselJ0_zero]
  have hdF : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => ψ t * (1 - besselJ0 (x * t)))
      (ψ1 t / t * (1 - besselJ0 (x * t)) + ψ t * (x * besselJ1 (x * t))) t := by
    intro t ht
    have d4 : HasDerivAt (fun t : ℝ => besselJ0 (x * t)) (-besselJ1 (x * t) * (x * 1)) t :=
      (hasDerivAt_besselJ0 (x * t)).comp t ((hasDerivAt_id' t).const_mul x)
    have h := (hd t ht).mul (d4.const_sub 1)
    exact h.congr_deriv (by ring)
  have hb0 : ∀ t : ℝ, 0 < t → t ≤ 1 → |ψ t * (1 - besselJ0 (x * t))| ≤ C * x ^ 2 / 4 * t := by
    intro t ht ht1
    have hj0 := one_sub_besselJ0_nonneg (mul_nonneg hx.le ht.le)
    have hj := one_sub_besselJ0_le_sq (mul_nonneg hx.le ht.le)
    have hs0 := Real.sqrt_nonneg t
    have hs1 : Real.sqrt t ≤ 1 := by
      have h := Real.sqrt_le_sqrt ht1
      rwa [Real.sqrt_one] at h
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    have hx4t : 0 ≤ x ^ 2 / 4 * t := mul_nonneg (div_nonneg (sq_nonneg x) (by norm_num)) ht.le
    rw [abs_mul, abs_of_nonneg hj0]
    calc |ψ t| * (1 - besselJ0 (x * t)) ≤ |ψ t| * ((x * t) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left hj (abs_nonneg _)
      _ = x ^ 2 / 4 * t * Real.sqrt t * (Real.sqrt t * |ψ t|) := by
          linear_combination (-(x ^ 2 * t * |ψ t| / 4)) * hsq
      _ ≤ x ^ 2 / 4 * t * Real.sqrt t * C :=
          mul_le_mul_of_nonneg_left (hn t ht ht1) (mul_nonneg hx4t hs0)
      _ ≤ x ^ 2 / 4 * t * 1 * C :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs1 hx4t) hC0
      _ = C * x ^ 2 / 4 * t := by ring
  have h0' : Tendsto (fun t : ℝ => ψ t * (1 - besselJ0 (x * t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hl : Tendsto (fun t : ℝ => C * x ^ 2 / 4 * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h : Tendsto (fun t : ℝ => C * x ^ 2 / 4 * t) (nhds 0) (nhds (C * x ^ 2 / 4 * 0)) :=
        (by fun_prop : Continuous (fun t : ℝ => C * x ^ 2 / 4 * t)).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (one_pos : (0 : ℝ) < 1))] with t ht ht1
    rw [Real.norm_eq_abs]
    exact hb0 t ht (le_of_lt ht1)
  have hinf : Tendsto (fun t : ℝ => ψ t * (1 - besselJ0 (x * t))) atTop (nhds 0) := by
    have h2' := tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0) : Tendsto (fun x : ℝ => x ^ 2) atTop atTop)
    have h2 : Tendsto (fun t : ℝ => (t ^ 2)⁻¹) atTop (nhds 0) := h2'
    have hl := h2.const_mul (2 * C)
    rw [mul_zero] at hl
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have ha := abs_le_of_sq_mul_le ht0 (hf t ht)
    have hj0 := one_sub_besselJ0_nonneg (mul_nonneg hx.le ht0.le)
    have hj2 : 1 - besselJ0 (x * t) ≤ 2 := by
      have h := (abs_le.mp (abs_besselJ0_le_one (mul_nonneg hx.le ht0.le))).1
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hj0]
    calc |ψ t| * (1 - besselJ0 (x * t)) ≤ |ψ t| * 2 :=
          mul_le_mul_of_nonneg_left hj2 (abs_nonneg _)
      _ ≤ C * (t ^ 2)⁻¹ * 2 := by linarith
      _ = 2 * C * (t ^ 2)⁻¹ := by ring
  have i2 : IntegrableOn (fun t : ℝ => ψ t * (x * besselJ1 (x * t))) (Set.Ioi 0) := by
    have hcont : ContinuousOn (fun t : ℝ => ψ t * (x * besselJ1 (x * t))) (Set.Ioi 0) :=
      hc0.mul (continuousOn_const.mul (continuous_besselJ1_mul' x).continuousOn)
    refine integrableOn_Ioi_of_bounds hcont (A := C * x) (B := C * x)
      (fun t ht ht1 => ?_) (fun t ht => ?_)
    · have ha := abs_le_of_sqrt_mul_le ht (hn t ht ht1)
      have hb := abs_mul_besselJ1_mul_le hx.le t ht
      rw [abs_mul]
      have hsi : 0 ≤ (Real.sqrt t)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg t)
      calc |ψ t| * |x * besselJ1 (x * t)| ≤ C * (Real.sqrt t)⁻¹ * x :=
            mul_le_mul ha hb (abs_nonneg _) (mul_nonneg hC0 hsi)
        _ = C * x * (Real.sqrt t)⁻¹ := by ring
    · have ht0 : 0 < t := by linarith
      have ha := abs_le_of_sq_mul_le ht0 (hf t ht.le)
      have hb := abs_mul_besselJ1_mul_le hx.le t ht0
      rw [abs_mul]
      have hsi : 0 ≤ (t ^ 2)⁻¹ := inv_nonneg.mpr (pow_nonneg ht0.le 2)
      calc |ψ t| * |x * besselJ1 (x * t)| ≤ C * (t ^ 2)⁻¹ * x :=
            mul_le_mul ha hb (abs_nonneg _) (mul_nonneg hC0 hsi)
        _ = C * x * (t ^ 2)⁻¹ := by ring
  have hint : IntegrableOn
      (fun t : ℝ => ψ1 t / t * (1 - besselJ0 (x * t)) + ψ t * (x * besselJ1 (x * t)))
      (Set.Ioi 0) := Integrable.add i1 i2
  have hz := integral_Ioi_deriv_eq_zero hF0 hdF h0' hinf hint
  have a1 := integral_add i1 i2
  have a2 : ∫ t in Set.Ioi (0 : ℝ), ψ t * (x * besselJ1 (x * t))
      = x * ∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * ψ t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show ψ t * (x * besselJ1 (x * t)) = x * (besselJ1 (x * t) * ψ t)
    ring
  have e3 : ∫ t in Set.Ioi (0 : ℝ), -ψ1 t / t * (1 - besselJ0 (x * t))
      = -∫ t in Set.Ioi (0 : ℝ), ψ1 t / t * (1 - besselJ0 (x * t)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show -ψ1 t / t * (1 - besselJ0 (x * t)) = -(ψ1 t / t * (1 - besselJ0 (x * t)))
    ring
  show x * (∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * ψ t) = _
  linarith [hz, a1, a2, e3]

/-- **`ajG(x) = ∫₀^∞ (-θg/t)(1 - J₀(xt)) dt`** for `x > 0`. -/
theorem ajG_eq_one_sub {x : ℝ} (hx : 0 < x) :
    ajG x = ∫ t in Set.Ioi (0 : ℝ), -thG1 t / t * (1 - besselJ0 (x * t)) := by
  rw [ajG_eq_AJ, ← thG0_eq_gB]
  exact AJ_eq_one_sub pdom_thG0 pdom_thG1 (fun t ht => hasDerivAt_thG0 ht) hx

end Tower.RV6
