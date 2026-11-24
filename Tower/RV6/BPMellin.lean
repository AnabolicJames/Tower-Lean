import Mathlib
import Tower.RV6.BPLam
import Tower.RV6.BPKernel
import Tower.RV6.BPIbp

/-!
# RungBP, step 8 (Mellin side): `j(u) j(s-u) = j(s)[s/(u(s-u)) - Λ(-u) - Λ(u-s)]`

For `0 < u < s ≤ 1` the Mellin transform `M(u) = ∫₀^∞ k_s(1, t) t^{-1-u} dt` is computed twice.

* Tonelli in `(x, t)` on `(1 - J₀(x))(1 - J₀(xt)) x^{-1-s} t^{-1-u} ≥ 0`, the `t`-integral first:
  `M(u) = j(u) j(s - u)` (`mellin_kerS_left`).
* `k_s(1, t) = j(s)(1 + t^s - M_s(1, t))` with `M_s(1, t) = 1 + h_s(t²)` (`angM_one_eq_hS`) and
  `M_s(1, t) = t^s (1 + h_s(t^{-2}))` (`angM_one_eq_hS_inv`); termwise,
  `∫₀¹ h_s(r²) r^{v-1} dr = Λ(v)` (`integral_hS_rpow`) and `∫₁^∞ h_s(t^{-2}) t^{-v-1} dt = Λ(v)`
  (`integral_hS_inv_rpow`): `M(u) = j(s)[(1/(s-u) - Λ(-u)) + (1/u - Λ(u-s))]` (`mellin_kerS_right`).
-/

namespace Tower.RV6

open Real MeasureTheory Set Filter Topology

theorem continuous_angM_one {s : ℝ} (hs : 0 ≤ s) : Continuous (fun t : ℝ => angM s 1 t) := by
  have h : Continuous (Function.uncurry fun (t θ : ℝ) => rhoN 1 t θ ^ s) := by
    have hc : Continuous (fun p : ℝ × ℝ => ((1 : ℝ) : ℂ) + (p.1 : ℂ) * cexpR (2 * π * p.2)) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (continuous_cexpR_two_pi.comp continuous_snd))
    exact (continuous_norm.comp hc).rpow_const (fun _ => Or.inr hs)
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := (volume : Measure ℝ)) h 0 1
  refine h2.congr fun t => ?_
  show ∫ θ in (0 : ℝ)..1, rhoN 1 t θ ^ s = angM s 1 t
  rw [angM, intervalIntegral.integral_of_le zero_le_one]

theorem continuous_hS {s : ℝ} (hs : 0 ≤ s) : Continuous (hS s) :=
  ((continuous_angM_one hs).comp Real.continuous_sqrt).sub continuous_const

theorem angM_one_eq_hS (s : ℝ) {t : ℝ} (ht : 0 ≤ t) : angM s 1 t = 1 + hS s (t ^ 2) := by
  rw [hS, Real.sqrt_sq ht]
  ring

theorem angM_one_eq_hS_inv (s : ℝ) {t : ℝ} (ht : 0 < t) :
    angM s 1 t = t ^ s * (1 + hS s ((t ^ 2)⁻¹)) := by
  rw [angM_symm, angM_homog ht, angM_one_eq_hS s (by positivity : (0 : ℝ) ≤ 1 / t), one_div,
    inv_pow]

theorem integral_rpow_Ioo01 {a : ℝ} (ha : -1 < a) : ∫ r in Ioo (0 : ℝ) 1, r ^ a = 1 / (a + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl ha), Real.one_rpow,
    Real.zero_rpow (show (0 : ℝ) < a + 1 by linarith).ne', sub_zero]

theorem integral_rpow_Ioc01 {a : ℝ} (ha : -1 < a) : ∫ r in Ioc (0 : ℝ) 1, r ^ a = 1 / (a + 1) := by
  rw [integral_Ioc_eq_integral_Ioo, integral_rpow_Ioo01 ha]

theorem integrableOn_rpow_Ioc01 {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun r : ℝ => r ^ a) (Ioc 0 1) :=
  (intervalIntegral.intervalIntegrable_rpow' ha).1

/-- `∫₀¹ h_s(r²) r^{v-1} dr = Λ(v)` for `0 ≤ s ≤ 1`, `-1 ≤ v ≤ 1`. -/
theorem integral_hS_rpow {s v : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hv0 : -1 ≤ v) (hv1 : v ≤ 1) :
    ∫ r in Ioc (0 : ℝ) 1, hS s (r ^ 2) * r ^ (v - 1) = lamS s v := by
  have hs2 : s ≤ 2 := by linarith
  have hexp : ∀ n : ℕ, -1 < 2 * (n : ℝ) + 1 + v := fun n => by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hpt : ∀ r ∈ Ioo (0 : ℝ) 1, hS s (r ^ 2) * r ^ (v - 1)
      = ∑' n : ℕ, bk s (n + 1) ^ 2 * r ^ (2 * (n : ℝ) + 1 + v) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr.1
    have hr1 : r < 1 := hr.2
    rw [hS_eq_tsum hs0 hs2 (sq_nonneg r) (by nlinarith), ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [mul_assoc]
    congr 1
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hr0]
    congr 1
    push_cast
    ring
  have hint : ∀ n : ℕ, Integrable (fun r : ℝ => bk s (n + 1) ^ 2 * r ^ (2 * (n : ℝ) + 1 + v))
      (volume.restrict (Ioo (0 : ℝ) 1)) := fun n =>
    (((integrableOn_rpow_Ioc01 (hexp n)).mono_set Ioo_subset_Ioc_self)).const_mul _
  have hval : ∀ n : ℕ, ∫ r in Ioo (0 : ℝ) 1, bk s (n + 1) ^ 2 * r ^ (2 * (n : ℝ) + 1 + v)
      = bk s (n + 1) ^ 2 / (2 * ((n : ℝ) + 1) + v) := fun n => by
    rw [integral_const_mul, integral_rpow_Ioo01 (hexp n), mul_one_div]
    congr 1
    ring
  have hnorm : ∀ n : ℕ, ∫ r in Ioo (0 : ℝ) 1, ‖bk s (n + 1) ^ 2 * r ^ (2 * (n : ℝ) + 1 + v)‖
      = ∫ r in Ioo (0 : ℝ) 1, bk s (n + 1) ^ 2 * r ^ (2 * (n : ℝ) + 1 + v) := fun n =>
    setIntegral_congr_fun measurableSet_Ioo (fun r hr =>
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hr.1.le _)))
  have hsum : Summable (fun n : ℕ =>
      ∫ r in Ioo (0 : ℝ) 1, ‖bk s (n + 1) ^ 2 * r ^ (2 * (n : ℝ) + 1 + v)‖) :=
    (summable_lam_term hs0 hs2 hv0).congr fun n => ((hnorm n).trans (hval n)).symm
  rw [integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hpt,
    ← integral_tsum_of_summable_integral_norm hint hsum, lamS]
  exact tsum_congr hval

/-- `∫₁^∞ h_s(t^{-2}) t^{-v-1} dt = Λ(v)` for `0 ≤ s ≤ 1`, `-1 ≤ v ≤ 1`. -/
theorem integral_hS_inv_rpow {s v : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hv0 : -1 ≤ v) (hv1 : v ≤ 1) :
    ∫ t in Ioi (1 : ℝ), hS s ((t ^ 2)⁻¹) * t ^ (-v - 1) = lamS s v := by
  have hs2 : s ≤ 2 := by linarith
  have hexp : ∀ n : ℕ, -(2 * (n : ℝ) + 3 + v) < -1 := fun n => by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hpt : ∀ t ∈ Ioi (1 : ℝ), hS s ((t ^ 2)⁻¹) * t ^ (-v - 1)
      = ∑' n : ℕ, bk s (n + 1) ^ 2 * t ^ (-(2 * (n : ℝ) + 3 + v)) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hw1 : (t ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    rw [hS_eq_tsum hs0 hs2 (by positivity) hw1, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [mul_assoc]
    congr 1
    rw [inv_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]
    congr 1
    push_cast
    ring
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => bk s (n + 1) ^ 2 * t ^ (-(2 * (n : ℝ) + 3 + v)))
      (volume.restrict (Ioi (1 : ℝ))) := fun n =>
    (integrableOn_Ioi_rpow_of_lt (hexp n) one_pos).const_mul _
  have hval : ∀ n : ℕ, ∫ t in Ioi (1 : ℝ), bk s (n + 1) ^ 2 * t ^ (-(2 * (n : ℝ) + 3 + v))
      = bk s (n + 1) ^ 2 / (2 * ((n : ℝ) + 1) + v) := fun n => by
    have hn := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h1 : -(2 * (n : ℝ) + 3 + v) + 1 ≠ 0 := (show -(2 * (n : ℝ) + 3 + v) + 1 < 0 by linarith).ne
    have h2 : 2 * ((n : ℝ) + 1) + v ≠ 0 := (show (0 : ℝ) < 2 * ((n : ℝ) + 1) + v by linarith).ne'
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (hexp n) one_pos, Real.one_rpow]
    field_simp
    all_goals ring
  have hnorm : ∀ n : ℕ, ∫ t in Ioi (1 : ℝ), ‖bk s (n + 1) ^ 2 * t ^ (-(2 * (n : ℝ) + 3 + v))‖
      = ∫ t in Ioi (1 : ℝ), bk s (n + 1) ^ 2 * t ^ (-(2 * (n : ℝ) + 3 + v)) := fun n =>
    setIntegral_congr_fun measurableSet_Ioi (fun t ht =>
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_trans zero_le_one (le_of_lt ht)) _)))
  have hsum : Summable (fun n : ℕ =>
      ∫ t in Ioi (1 : ℝ), ‖bk s (n + 1) ^ 2 * t ^ (-(2 * (n : ℝ) + 3 + v))‖) :=
    (summable_lam_term hs0 hs2 hv0).congr fun n => ((hnorm n).trans (hval n)).symm
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    ← integral_tsum_of_summable_integral_norm hint hsum, lamS]
  exact tsum_congr hval

theorem integrableOn_hS_sq {s v : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hv0 : -1 ≤ v) :
    IntegrableOn (fun r : ℝ => hS s (r ^ 2) * r ^ (v - 1)) (Ioc 0 1) := by
  have hs2 : s ≤ 2 := by linarith
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hb : IntegrableOn (fun r : ℝ => s ^ 2 / 2 * r ^ (v + 1)) (Ioo 0 1) :=
    ((integrableOn_rpow_Ioc01 (by linarith : (-1 : ℝ) < v + 1)).mono_set
      Ioo_subset_Ioc_self).const_mul _
  refine Integrable.mono' hb ?_ ?_
  · exact (((continuous_hS hs0).comp (continuous_pow 2)).continuousOn.mul
      (ContinuousOn.rpow_const (continuousOn_id (s := Ioo (0 : ℝ) 1))
        (fun r hr => Or.inl (show (0 : ℝ) < r from hr.1).ne'))).aestronglyMeasurable
      measurableSet_Ioo
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := hr.1
    have hw1 : r ^ 2 < 1 := by nlinarith [hr.2]
    have h0 := hS_nonneg hs0 hs2 (sq_nonneg r) hw1
    have h1 := hS_le hs0 hs2 (sq_nonneg r) hw1
    have hp : 0 < r ^ (v - 1) := Real.rpow_pos_of_pos hr0 _
    have e : r ^ (v + 1) = r ^ 2 * r ^ (v - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr0]
      congr 1
      push_cast
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hp.le), e]
    calc hS s (r ^ 2) * r ^ (v - 1) ≤ s ^ 2 / 2 * r ^ 2 * r ^ (v - 1) :=
          mul_le_mul_of_nonneg_right h1 hp.le
      _ = s ^ 2 / 2 * (r ^ 2 * r ^ (v - 1)) := by ring

theorem integrableOn_hS_inv {s v : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hv1 : v ≤ 1) (hv0 : -1 ≤ v) :
    IntegrableOn (fun t : ℝ => hS s ((t ^ 2)⁻¹) * t ^ (-v - 1)) (Ioi 1) := by
  have hs2 : s ≤ 2 := by linarith
  have hb : IntegrableOn (fun t : ℝ => s ^ 2 / 2 * t ^ (-v - 3)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -v - 3 < -1) one_pos).const_mul _
  refine Integrable.mono' hb ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ (ContinuousOn.rpow_const (continuousOn_id (s := Ioi (1 : ℝ)))
      (fun t ht => Or.inl (show (0 : ℝ) < t from lt_trans one_pos ht).ne'))
    exact (continuous_hS hs0).comp_continuousOn
      ((continuousOn_pow 2).inv₀ (fun t ht =>
        pow_ne_zero 2 (show (0 : ℝ) < t from lt_trans one_pos ht).ne'))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hw1 : (t ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    have h0 := hS_nonneg hs0 hs2 (by positivity) hw1
    have h1 := hS_le hs0 hs2 (by positivity) hw1
    have hp : 0 < t ^ (-v - 1) := Real.rpow_pos_of_pos ht0 _
    have e : t ^ (-v - 3) = (t ^ 2)⁻¹ * t ^ (-v - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]
      congr 1
      push_cast
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hp.le), e]
    calc hS s ((t ^ 2)⁻¹) * t ^ (-v - 1) ≤ s ^ 2 / 2 * (t ^ 2)⁻¹ * t ^ (-v - 1) :=
          mul_le_mul_of_nonneg_right h1 hp.le
      _ = s ^ 2 / 2 * ((t ^ 2)⁻¹ * t ^ (-v - 1)) := by ring

/-- The integrand of the Mellin transform on `(0, ∞)²`. -/
noncomputable def mellG (s u x t : ℝ) : ℝ :=
  (1 - besselJ0 (x * 1)) * (1 - besselJ0 (x * t)) * x ^ (-1 - s) * t ^ (-1 - u)

theorem mellG_nonneg {s u x t : ℝ} (hx : 0 < x) (ht : 0 < t) : 0 ≤ mellG s u x t := by
  have h1 := one_sub_besselJ0_nonneg (show (0 : ℝ) ≤ x * 1 by positivity)
  have h2 := one_sub_besselJ0_nonneg (show (0 : ℝ) ≤ x * t by positivity)
  have h3 := Real.rpow_pos_of_pos hx (-1 - s)
  have h4 := Real.rpow_pos_of_pos ht (-1 - u)
  unfold mellG
  positivity

/-- **`M(u) = j(u) j(s - u)`** for `0 < u < s < 2`. -/
theorem mellin_kerS_left {s u : ℝ} (hu0 : 0 < u) (hus : u < s) (hs2 : s < 2) :
    ∫ t in Ioi (0 : ℝ), kerS s 1 t * t ^ (-1 - u) = jS u * jS (s - u) := by
  have hsu : 0 < s - u := by linarith
  have hmeas : Measurable (Function.uncurry (mellG s u)) := by
    have h1 : Continuous (fun p : ℝ × ℝ =>
        (1 - besselJ0 (p.1 * 1)) * (1 - besselJ0 (p.1 * p.2))) :=
      (continuous_const.sub (continuous_besselJ0.comp (continuous_fst.mul continuous_const))).mul
        (continuous_const.sub (continuous_besselJ0.comp (continuous_fst.mul continuous_snd)))
    exact (h1.measurable.mul (measurable_fst.pow_const _)).mul (measurable_snd.pow_const _)
  have hinner : ∀ x ∈ Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), mellG s u x t
      = jS u * ((1 - besselJ0 (x * 1)) * x ^ (-1 - (s - u))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h := jS_scale hu0 hx0.le
    have e : ∀ t : ℝ, mellG s u x t = ((1 - besselJ0 (x * 1)) * x ^ (-1 - s))
        * ((1 - besselJ0 (t * x)) * t ^ (-1 - u)) := fun t => by
      unfold mellG
      rw [mul_comm x t]
      ring
    simp only [e]
    rw [integral_const_mul, h]
    have e2 : x ^ (-1 - s) * x ^ u = x ^ (-1 - (s - u)) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [← e2]
    ring
  have hintx : ∀ x ∈ Ioi (0 : ℝ), IntegrableOn (mellG s u x) (Ioi 0) := by
    intro x hx
    have h : IntegrableOn (fun t : ℝ => ((1 - besselJ0 (x * 1)) * x ^ (-1 - s))
        * ((1 - besselJ0 (t * x)) * t ^ (-1 - u))) (Ioi 0) :=
      (integrableOn_one_sub_scale hu0 (by linarith) (le_of_lt hx)).const_mul _
    refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
    simp only [mellG]
    rw [mul_comm x t]
    ring
  have hint : Integrable (Function.uncurry (mellG s u))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    constructor
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => hintx x hx)
    · have hR : IntegrableOn (fun x : ℝ => jS u * ((1 - besselJ0 (x * 1)) * x ^ (-1 - (s - u))))
          (Ioi 0) := (integrableOn_one_sub_scale hsu (by linarith) zero_le_one).const_mul _
      refine IntegrableOn.congr_fun hR (fun x hx => ?_) measurableSet_Ioi
      simp only [Function.uncurry_apply_pair]
      rw [← hinner x hx]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht =>
        (Real.norm_of_nonneg (mellG_nonneg hx ht)).symm)
  have hsw := integral_integral_swap hint
  calc ∫ t in Ioi (0 : ℝ), kerS s 1 t * t ^ (-1 - u)
      = ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), mellG s u x t := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        show kerS s 1 t * t ^ (-1 - u) = ∫ x in Ioi (0 : ℝ), mellG s u x t
        rw [kerS, ← integral_mul_const]
        rfl
    _ = ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), mellG s u x t := hsw.symm
    _ = ∫ x in Ioi (0 : ℝ), jS u * ((1 - besselJ0 (x * 1)) * x ^ (-1 - (s - u))) :=
        setIntegral_congr_fun measurableSet_Ioi hinner
    _ = jS u * jS (s - u) := by
        rw [integral_const_mul, jS_scale hsu zero_le_one, Real.one_rpow, one_mul]

/-- **`M(u) = j(s)[(1/(s-u) - Λ(-u)) + (1/u - Λ(u-s))]`** for `0 < u < s ≤ 1`. -/
theorem mellin_kerS_right {s u : ℝ} (hu0 : 0 < u) (hus : u < s) (hs1 : s ≤ 1) :
    ∫ t in Ioi (0 : ℝ), kerS s 1 t * t ^ (-1 - u)
      = jS s * ((1 / (s - u) - lamS s (-u)) + (1 / u - lamS s (u - s))) := by
  have hs0 : 0 < s := by linarith
  have hs2 : s < 2 := by linarith
  -- the two pieces of the integrand
  have hA : EqOn (fun t : ℝ => kerS s 1 t * t ^ (-1 - u))
      (fun t : ℝ => jS s * (t ^ (s - 1 - u) - hS s (t ^ 2) * t ^ (-u - 1))) (Ioc 0 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht.1
    show kerS s 1 t * t ^ (-1 - u) = jS s * (t ^ (s - 1 - u) - hS s (t ^ 2) * t ^ (-u - 1))
    rw [kerS_eq hs0 hs2 zero_le_one ht0.le, Real.one_rpow, angM_one_eq_hS s ht0.le]
    have e1 : t ^ s * t ^ (-1 - u) = t ^ (s - 1 - u) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    have e2 : t ^ (-1 - u) = t ^ (-u - 1) := by
      congr 1
      ring
    rw [← e1, ← e2]
    ring
  have hB : EqOn (fun t : ℝ => kerS s 1 t * t ^ (-1 - u))
      (fun t : ℝ => jS s * (t ^ (-1 - u) - hS s ((t ^ 2)⁻¹) * t ^ (-(u - s) - 1))) (Ioi 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    show kerS s 1 t * t ^ (-1 - u)
      = jS s * (t ^ (-1 - u) - hS s ((t ^ 2)⁻¹) * t ^ (-(u - s) - 1))
    rw [kerS_eq hs0 hs2 zero_le_one ht0.le, Real.one_rpow, angM_one_eq_hS_inv s ht0]
    have e1 : t ^ s * t ^ (-1 - u) = t ^ (-(u - s) - 1) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [← e1]
    ring
  -- integrability of the pieces
  have iA1 : IntegrableOn (fun t : ℝ => t ^ (s - 1 - u)) (Ioc 0 1) :=
    integrableOn_rpow_Ioc01 (by linarith)
  have iA2 : IntegrableOn (fun t : ℝ => hS s (t ^ 2) * t ^ (-u - 1)) (Ioc 0 1) :=
    integrableOn_hS_sq hs0.le hs1 (by linarith)
  have iB1 : IntegrableOn (fun t : ℝ => t ^ (-1 - u)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have iB2 : IntegrableOn (fun t : ℝ => hS s ((t ^ 2)⁻¹) * t ^ (-(u - s) - 1)) (Ioi 1) :=
    integrableOn_hS_inv hs0.le hs1 (by linarith) (by linarith)
  have iA : IntegrableOn (fun t : ℝ => kerS s 1 t * t ^ (-1 - u)) (Ioc 0 1) :=
    IntegrableOn.congr_fun ((iA1.sub iA2).const_mul (jS s)) hA.symm measurableSet_Ioc
  have iB : IntegrableOn (fun t : ℝ => kerS s 1 t * t ^ (-1 - u)) (Ioi 1) :=
    IntegrableOn.congr_fun ((iB1.sub iB2).const_mul (jS s)) hB.symm measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi iA iB,
    setIntegral_congr_fun measurableSet_Ioc hA, setIntegral_congr_fun measurableSet_Ioi hB,
    integral_const_mul, integral_const_mul, integral_sub iA1 iA2, integral_sub iB1 iB2,
    integral_rpow_Ioc01 (by linarith), integral_hS_rpow hs0.le hs1 (by linarith) (by linarith),
    integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
    integral_hS_inv_rpow hs0.le hs1 (by linarith) (by linarith)]
  have h1 : s - 1 - u + 1 = s - u := by ring
  have h2 : -1 - u + 1 = -u := by ring
  rw [h1, h2, ← mul_add]
  congr 1
  rw [neg_div_neg_eq]

/-- **`j(u) j(s - u) = j(s)[s/(u(s - u)) - Λ(-u) - Λ(u - s)]`** for `0 < u < s ≤ 1`. -/
theorem jS_mul_jS {s u : ℝ} (hu0 : 0 < u) (hus : u < s) (hs1 : s ≤ 1) :
    jS u * jS (s - u) = jS s * (s / (u * (s - u)) - lamS s (-u) - lamS s (u - s)) := by
  rw [← mellin_kerS_left hu0 hus (by linarith), mellin_kerS_right hu0 hus hs1]
  have hu : u ≠ 0 := hu0.ne'
  have hsu : s - u ≠ 0 := (show (0 : ℝ) < s - u by linarith).ne'
  congr 1
  have e : 1 / (s - u) + 1 / u = s / (u * (s - u)) := by
    field_simp
    all_goals ring
  linarith [e]

end Tower.RV6
