import Mathlib
import Tower.RV6.HankelZeroF
import Tower.RV6.BesselW
import Tower.RV6.BesselR

/-!
# The Bessel side of the cusp `x → ∞`: `x² hk(θ²f)(x) → 6`

* `x2_hk_thF2_eq`: for `x > 0`, `x² hk(θ²f)(x) = ∫₀^∞ (θ⁴f(t)/t)(1 - J₀(xt)) dt` (one integration by parts
  with `F = θ²f · x t J₁(xt) + θ³f · (J₀(xt) - 1)`, whose `J₁` terms cancel);
* `tendsto_thF3_zero`: `θ³f → -6` at `0+` (`e^{-t} ≤ t K₁ ≤ 1`, `0 ≤ t K₀ ≤ t K₁`);
* `integral_thF4_div`: `∫₀^∞ θ⁴f/t = 6`;
* **`tendsto_x2_hk_thF2`**: `x² hk(θ²f)(x) → 6` as `x → ∞` (dominated convergence, `J₀ → 0`).

With `A_k = hk(θᵏ f)`, `x² A₂ = ϑ²(x² hjF)`; the modular side of the same limit gives the constant `a₀`.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

/-! ## Limits of `HDom` functions -/

/-- `t φ(t) g(t) → 0` as `t → 0+`. -/
theorem tendsto_hdom_one_zero {φ g : ℝ → ℝ} (hφ : HDom φ) {G : ℝ}
    (hG : ∀ t : ℝ, 0 < t → |g t| ≤ G) :
    Tendsto (fun t : ℝ => t * φ t * g t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨_, C, hC0, _, hn, _⟩ := hφ
  have hlim : Tendsto (fun t : ℝ => C * G * Real.sqrt t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 : Tendsto (fun t : ℝ => C * G * Real.sqrt t) (nhds 0) (nhds (C * G * Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).const_mul (C * G)
    rw [Real.sqrt_zero, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  rw [Real.norm_eq_abs]
  have ht0 : 0 < t := ht.1
  have h1 := hn t ht0 ht.2.le
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hs0 := Real.sqrt_nonneg t
  rw [abs_mul, abs_mul, abs_of_pos ht0]
  have e : t * |φ t| = Real.sqrt t * (Real.sqrt t * |φ t|) := by
    rw [← mul_assoc, hss]
  have hA : t * |φ t| ≤ Real.sqrt t * C := by
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 hs0
  have hB : t * |φ t| * |g t| ≤ Real.sqrt t * C * G :=
    mul_le_mul hA (hG t ht0) (abs_nonneg _) (mul_nonneg hs0 hC0)
  linarith

/-- `tʲ φ(t) g(t) → 0` as `t → ∞`. -/
theorem tendsto_hdom_pow_atTop (j : ℕ) {φ g : ℝ → ℝ} (hφ : HDom φ) {G : ℝ}
    (hG : ∀ t : ℝ, 0 < t → |g t| ≤ G) :
    Tendsto (fun t : ℝ => t ^ j * φ t * g t) atTop (nhds 0) := by
  obtain ⟨_, C, hC0, N, _, hf⟩ := hφ
  have hlim : Tendsto (fun t : ℝ => C * G * (t ^ (N + j) * Real.exp (-t))) atTop
      (nhds (C * G * 0)) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (N + j)).const_mul (C * G)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ((eventually_ge_atTop (1 : ℝ)).mono (fun t ht => ?_)) hlim
  show ‖t ^ j * φ t * g t‖ ≤ C * G * (t ^ (N + j) * Real.exp (-t))
  rw [Real.norm_eq_abs]
  have ht0 : 0 < t := by linarith
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0.le j)]
  have h1 := hf t ht
  have h2 := hG t ht0
  have hA : t ^ j * |φ t| ≤ t ^ j * (C * t ^ N * Real.exp (-t)) :=
    mul_le_mul_of_nonneg_left h1 (pow_nonneg ht0.le j)
  have hB : t ^ j * |φ t| * |g t| ≤ t ^ j * (C * t ^ N * Real.exp (-t)) * G :=
    mul_le_mul hA h2 (abs_nonneg _) (mul_nonneg (pow_nonneg ht0.le j)
      (mul_nonneg (mul_nonneg hC0 (pow_nonneg ht0.le N)) (Real.exp_pos _).le))
  have e : t ^ j * (C * t ^ N * Real.exp (-t)) * G = C * G * (t ^ (N + j) * Real.exp (-t)) := by
    rw [pow_add]
    ring
  linarith

/-- `J₀(z) → 0` as `z → ∞`. -/
theorem tendsto_besselJ0_atTop : Tendsto besselJ0 atTop (nhds 0) := by
  have hlim : Tendsto (fun z : ℝ => Real.sqrt (besselJE 1 / z)) atTop (nhds 0) := by
    have h1 : Tendsto (fun z : ℝ => besselJE 1 / z) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    exact h2
  refine squeeze_zero_norm' ((eventually_ge_atTop (1 : ℝ)).mono (fun z hz => ?_)) hlim
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  rw [sq]
  exact besselJ0_sq_le hz

/-- `t K₁(t) → 1` as `t → 0+`. -/
theorem tendsto_mul_besselK1_zero :
    Tendsto (fun t : ℝ => t * besselK1 t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hlo : Tendsto (fun t : ℝ => Real.exp (-t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : Tendsto (fun t : ℝ => Real.exp (-t)) (nhds 0) (nhds (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).tendsto 0
    rw [neg_zero, Real.exp_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact exp_neg_le_mul_besselK1 ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_besselK1_le_one ht

/-- `θ³ f → -6` as `t → 0+`. -/
theorem tendsto_thF3_zero : Tendsto thF3 (nhdsWithin 0 (Set.Ioi 0)) (nhds (-6)) := by
  have hq := tendsto_mul_besselK1_zero
  have hI0 : Tendsto besselI0 (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : Tendsto besselI0 (nhds 0) (nhds (besselI0 0)) := continuous_besselI0.tendsto 0
    rw [besselI0_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hI1 : Tendsto (fun t : ℝ => |besselI1 t|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun t : ℝ => |besselI1 t|) (nhds 0) (nhds (|besselI1 0|)) :=
      (continuous_besselI1.tendsto 0).abs
    rw [besselI1_zero, abs_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hX : Tendsto (fun t : ℝ => besselI1 t * (t * besselK0 t) * (t * besselK1 t) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hI1
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have k0 : 0 ≤ t * besselK0 t := mul_nonneg ht0.le (besselK0_nonneg t)
    have k1 : t * besselK0 t ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (besselK0_le_besselK1 ht0) ht0.le)
        (mul_besselK1_le_one ht0)
    have q0 : 0 ≤ t * besselK1 t := mul_nonneg ht0.le (besselK1_pos ht0).le
    have q1 : t * besselK1 t ≤ 1 := mul_besselK1_le_one ht0
    have q2 : (t * besselK1 t) ^ 2 ≤ 1 := pow_le_one₀ q0 q1
    rw [abs_of_nonneg k0, abs_of_nonneg (pow_nonneg q0 2)]
    have a0 := abs_nonneg (besselI1 t)
    calc |besselI1 t| * (t * besselK0 t) * (t * besselK1 t) ^ 2
        ≤ |besselI1 t| * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left k1 a0) q2 (pow_nonneg q0 2) (by linarith)
      _ = |besselI1 t| := by ring
  have h1 : Tendsto (fun t : ℝ => t ^ 2 * ldF1 t * (fun _ : ℝ => (1 : ℝ)) t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_hdom_zero (g := fun _ : ℝ => (1 : ℝ)) hdom_ldF1 (G := 1) (fun _ _ => by simp)
  have h0 : Tendsto (fun t : ℝ => t ^ 2 * ldF0 t * (fun _ : ℝ => (1 : ℝ)) t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_hdom_zero (g := fun _ : ℝ => (1 : ℝ)) hdom_ldF0 (G := 1) (fun _ _ => by simp)
  have hlim : Tendsto (fun t : ℝ =>
      6 * (3 * (besselI1 t * (t * besselK0 t) * (t * besselK1 t) ^ 2)
        + (-1) * (besselI0 t * (t * besselK1 t) ^ 3))
      + 10 * (t ^ 2 * ldF1 t * (fun _ : ℝ => (1 : ℝ)) t)
      + 8 * (t ^ 2 * ldF0 t * (fun _ : ℝ => (1 : ℝ)) t))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (6 * (3 * 0 + (-1) * (1 * 1 ^ 3)) + 10 * 0 + 8 * 0)) :=
    ((((hX.const_mul 3).add ((hI0.mul (hq.pow 3)).const_mul (-1))).const_mul 6).add
      (h1.const_mul 10)).add (h0.const_mul 8)
  have e : (6 * (3 * 0 + (-1) * (1 * 1 ^ 3)) + 10 * 0 + 8 * 0 : ℝ) = -6 := by norm_num
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards with t
  unfold thF3 ldF3
  ring

theorem tendsto_thF3_atTop : Tendsto thF3 atTop (nhds 0) := by
  have h : Tendsto (fun t : ℝ => t ^ 0 * thF3 t * (fun _ : ℝ => (1 : ℝ)) t) atTop (nhds 0) :=
    tendsto_hdom_pow_atTop 0 (g := fun _ : ℝ => (1 : ℝ)) hdom_thF3 (G := 1) (fun _ _ => by simp)
  refine h.congr' ?_
  filter_upwards with t
  ring

/-- The fundamental theorem on `(0, ∞)` with a left limit `L₀`: `∫₀^∞ F' = -L₀`. -/
theorem integral_Ioi_deriv_eq_neg {F F' : ℝ → ℝ} {L0 : ℝ}
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt F (F' t) t)
    (h0 : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds L0))
    (hinf : Tendsto F atTop (nhds 0)) (hint : IntegrableOn F' (Set.Ioi 0)) :
    ∫ t in Set.Ioi (0 : ℝ), F' t = -L0 := by
  have hE0 : Tendsto (fun t : ℝ => Real.exp (-t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : Tendsto (fun t : ℝ => Real.exp (-t)) (nhds 0) (nhds (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).tendsto 0
    rw [neg_zero, Real.exp_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hEi : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 0) := by
    have h := exp_neg_integrableOn_Ioi 0 (one_pos : (0 : ℝ) < 1)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    show Real.exp (-1 * t) = Real.exp (-t)
    rw [neg_one_mul]
  have hG0 : (fun t : ℝ => if t = 0 then (0 : ℝ) else F t - L0 * Real.exp (-t)) 0 = 0 := by
    simp
  have hdG : ∀ t : ℝ, 0 < t → HasDerivAt
      (fun t : ℝ => if t = 0 then (0 : ℝ) else F t - L0 * Real.exp (-t))
      (F' t + L0 * Real.exp (-t)) t := by
    intro t ht
    have h1 := (hd t ht).sub (((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_mul L0)
    have h2 : HasDerivAt (fun s : ℝ => F s - L0 * Real.exp (-s))
        (F' t + L0 * Real.exp (-t)) t := by
      refine h1.congr_deriv ?_
      ring
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs0 : s ≠ 0 := (ne_of_gt hs)
    simp [hs0]
  have h0G : Tendsto (fun t : ℝ => if t = 0 then (0 : ℝ) else F t - L0 * Real.exp (-t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := h0.sub (hE0.const_mul L0)
    rw [mul_one, sub_self] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := (ne_of_gt hs)
    simp [hs0]
  have hinfG : Tendsto (fun t : ℝ => if t = 0 then (0 : ℝ) else F t - L0 * Real.exp (-t))
      atTop (nhds 0) := by
    have h := hinf.sub (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul L0)
    rw [mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hs0 : s ≠ 0 := (ne_of_gt hs)
    simp [hs0]
  have hintG : IntegrableOn (fun t : ℝ => F' t + L0 * Real.exp (-t)) (Set.Ioi 0) :=
    Integrable.add hint (Integrable.const_mul hEi L0)
  have hz := integral_Ioi_deriv_eq_zero hG0 hdG h0G hinfG hintG
  have a1 := integral_add hint (Integrable.const_mul hEi L0)
  have a2 : ∫ t in Set.Ioi (0 : ℝ), L0 * Real.exp (-t)
      = L0 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) := integral_const_mul _ _
  rw [integral_exp_neg_Ioi_zero] at a2
  linarith

theorem integrableOn_thF4_div : IntegrableOn (fun t : ℝ => thF4 t / t) (Set.Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => t ^ 1 * psiF4 t * (fun _ : ℝ => (1 : ℝ)) t) (Set.Ioi 0) :=
    integrableOn_hdom (g := fun _ : ℝ => (1 : ℝ)) hdom_psiF4 continuousOn_const (G := 1)
      (fun _ _ => by simp) (le_refl 1)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
  show t ^ 1 * psiF4 t * 1 = thF4 t / t
  rw [thF4_eq_sq, eq_div_iff ht0]
  ring

/-- `∫₀^∞ θ⁴f/t dt = 6`. -/
theorem integral_thF4_div : ∫ t in Set.Ioi (0 : ℝ), thF4 t / t = 6 := by
  have h := integral_Ioi_deriv_eq_neg (F := thF3) (F' := fun t => thF4 t / t) (L0 := -6)
    (fun t ht => hasDerivAt_thF3 ht) tendsto_thF3_zero tendsto_thF3_atTop integrableOn_thF4_div
  rw [neg_neg] at h
  exact h

/-- **`x² hk(θ²f)(x) = ∫₀^∞ (θ⁴f/t)(1 - J₀(xt)) dt`** for `x > 0`. -/
theorem x2_hk_thF2_eq {x : ℝ} (hx : 0 < x) :
    x ^ 2 * hk thF2 x = ∫ t in Set.Ioi (0 : ℝ), thF4 t / t * (1 - besselJ0 (x * t)) := by
  have hF0 : (fun t : ℝ => thF2 t * (x * t * besselJ1 (x * t))
      + thF3 t * (besselJ0 (x * t) - 1)) 0 = 0 := by
    simp [besselJ0_zero]
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt
      (fun t : ℝ => thF2 t * (x * t * besselJ1 (x * t)) + thF3 t * (besselJ0 (x * t) - 1))
      (x ^ 2 * (besselJ0 (x * t) * thF2 t * t) + thF4 t / t * (besselJ0 (x * t) - 1)) t := by
    intro t ht
    have d1 := hasDerivAt_thF2 ht
    have d2 : HasDerivAt (fun t : ℝ => x * t * besselJ1 (x * t))
        (x * t * besselJ0 (x * t) * (x * 1)) t :=
      (hasDerivAt_mul_besselJ1 (x * t)).comp t ((hasDerivAt_id' t).const_mul x)
    have d3 := hasDerivAt_thF3 ht
    have d4 : HasDerivAt (fun t : ℝ => besselJ0 (x * t) - 1)
        (-besselJ1 (x * t) * (x * 1)) t :=
      ((hasDerivAt_besselJ0 (x * t)).comp t ((hasDerivAt_id' t).const_mul x)).sub_const 1
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    have h := (d1.mul d2).add (d3.mul d4)
    exact h.congr_deriv (by
      linear_combination (x * thF3 t * besselJ1 (x * t)) * hinv)
  have h0 : Tendsto
      (fun t : ℝ => thF2 t * (x * t * besselJ1 (x * t)) + thF3 t * (besselJ0 (x * t) - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have T1 := tendsto_hdom_one_zero (g := fun t => x * besselJ1 (x * t)) hdom_thF2 (G := x)
      (abs_mul_besselJ1_mul_le hx.le)
    have T2 := tendsto_hdom_one_zero (g := fun t => (besselJ0 (x * t) - 1) / t) hdom_thF3
      (G := x) (fun t ht => by
        show |(besselJ0 (x * t) - 1) / t| ≤ x
        have j1 := one_sub_besselJ0_le (mul_nonneg hx.le ht.le)
        have j2 : besselJ0 (x * t) ≤ 1 := (abs_le.mp (abs_besselJ0_le_one (mul_nonneg hx.le ht.le))).2
        rw [abs_div, abs_of_pos ht, abs_sub_comm, abs_of_nonneg (by linarith),
          div_le_iff₀ ht]
        linarith)
    have T := T1.add T2
    rw [add_zero] at T
    refine T.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ht)
    rw [div_eq_mul_inv]
    linear_combination (thF3 t * (besselJ0 (x * t) - 1)) * hinv
  have hinf : Tendsto
      (fun t : ℝ => thF2 t * (x * t * besselJ1 (x * t)) + thF3 t * (besselJ0 (x * t) - 1))
      atTop (nhds 0) := by
    have U1 := tendsto_hdom_pow_atTop 1 (g := fun t => x * besselJ1 (x * t)) hdom_thF2 (G := x)
      (abs_mul_besselJ1_mul_le hx.le)
    have U2 := tendsto_hdom_pow_atTop 0 (g := fun t => besselJ0 (x * t) - 1) hdom_thF3 (G := 2)
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
  have i1 : IntegrableOn (fun t : ℝ => besselJ0 (x * t) * thF2 t * t) (Set.Ioi 0) :=
    integrableOn_hk hdom_thF2 hx.le
  have i2 : IntegrableOn (fun t : ℝ => thF4 t / t * (besselJ0 (x * t) - 1)) (Set.Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => t ^ 1 * psiF4 t * (fun t => besselJ0 (x * t) - 1) t)
        (Set.Ioi 0) :=
      integrableOn_hdom (g := fun t => besselJ0 (x * t) - 1) hdom_psiF4
        ((continuousOn_besselJ0_mul x).sub continuousOn_const) (G := 2)
        (fun t ht => by
          show |besselJ0 (x * t) - 1| ≤ 2
          have j := abs_besselJ0_le_one (mul_nonneg hx.le ht.le)
          have := abs_sub (besselJ0 (x * t)) 1
          rw [abs_one] at this
          linarith) (le_refl 1)
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
    have e : t ^ 2 * psiF4 t / t = t ^ 1 * psiF4 t := by
      rw [div_eq_iff ht0]
      ring
    show t ^ 1 * psiF4 t * (besselJ0 (x * t) - 1) = thF4 t / t * (besselJ0 (x * t) - 1)
    rw [thF4_eq_sq, e]
  have i12 : IntegrableOn (fun t : ℝ => x ^ 2 * (besselJ0 (x * t) * thF2 t * t)) (Set.Ioi 0) :=
    Integrable.const_mul i1 (x ^ 2)
  have hint : IntegrableOn
      (fun t : ℝ => x ^ 2 * (besselJ0 (x * t) * thF2 t * t) + thF4 t / t * (besselJ0 (x * t) - 1))
      (Set.Ioi 0) := Integrable.add i12 i2
  have hz := integral_Ioi_deriv_eq_zero hF0 hd h0 hinf hint
  have a1 := integral_add i12 i2
  have a2 : ∫ t in Set.Ioi (0 : ℝ), x ^ 2 * (besselJ0 (x * t) * thF2 t * t)
      = x ^ 2 * ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * thF2 t * t := integral_const_mul _ _
  have e3 : ∫ t in Set.Ioi (0 : ℝ), thF4 t / t * (1 - besselJ0 (x * t))
      = -∫ t in Set.Ioi (0 : ℝ), thF4 t / t * (besselJ0 (x * t) - 1) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show thF4 t / t * (1 - besselJ0 (x * t)) = -(thF4 t / t * (besselJ0 (x * t) - 1))
    ring
  show x ^ 2 * (∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * thF2 t * t) = _
  linarith [hz, a1, a2, e3]

/-- **`x² hk(θ²f)(x) → 6`** as `x → ∞`. -/
theorem tendsto_x2_hk_thF2 : Tendsto (fun x : ℝ => x ^ 2 * hk thF2 x) atTop (nhds 6) := by
  have hD : Tendsto (fun x : ℝ => ∫ t in Set.Ioi (0 : ℝ), thF4 t / t * (1 - besselJ0 (x * t)))
      atTop (nhds (∫ t in Set.Ioi (0 : ℝ), thF4 t / t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => 2 * |thF4 t / t|) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall (fun x => ?_)
      have hc : ContinuousOn (fun t : ℝ => thF4 t / t * (1 - besselJ0 (x * t))) (Set.Ioi 0) :=
        (hdom_thF4.1.div continuousOn_id (fun t ht => ne_of_gt ht)).mul
          (continuousOn_const.sub (continuousOn_besselJ0_mul x))
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
      have ht0 : 0 < t := ht
      rw [Real.norm_eq_abs, abs_mul]
      have j := abs_besselJ0_le_one (mul_nonneg hx ht0.le)
      have j2 : |1 - besselJ0 (x * t)| ≤ 2 := by
        have := abs_sub 1 (besselJ0 (x * t))
        rw [abs_one] at this
        linarith
      have a := abs_nonneg (thF4 t / t)
      nlinarith
    · exact Integrable.const_mul (Integrable.abs integrableOn_thF4_div) 2
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
      have ht0 : 0 < t := ht
      have hJ : Tendsto (fun x : ℝ => besselJ0 (x * t)) atTop (nhds 0) :=
        tendsto_besselJ0_atTop.comp (tendsto_id.atTop_mul_const ht0)
      have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      have h := (hc.sub hJ).const_mul (thF4 t / t)
      rw [sub_zero, mul_one] at h
      exact h
  rw [integral_thF4_div] at hD
  refine hD.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [x2_hk_thF2_eq hx]

end Tower.RV6
