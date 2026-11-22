import Mathlib
import Tower.RV6.QSeries
import Tower.RV6.PhiKernel
import Tower.RV6.Interchange

/-!
# The partial Eichler integral of `E₄` and its inversion formula

`Tint a = ∫_a^∞ t S₃(t) dt`, `S₃ = qa (sig 3) = ∑ σ₃(n) e^{-2πnt}`.

* `Tint_eq`: `T(a) = a U₁(a)/(2π) + U₂(a)/(4π²)` with `U₁ = ∑ σ₃(n)/n qⁿ`, `U₂ = ∑ σ₃(n)/n² qⁿ`.
* `Tint_inv`: `T(a) + T(1/a) = (a² + a⁻²)/480 + 2T(1) - 1/240` for `a > 0`.

The inversion formula is the statement `K₁ = 0` of the paper in a form that needs no
continuation: for `a ≥ 1` the differences `T(1) - T(a)` and `T(1/a) - T(1)` are integrals over
`[1, a]` and `[1/a, 1]`, the second is carried to `[1, a]` by `t = 1/x`, and
`ψ(t) = t (S₃(t) + 1/240) = t E₄(it)/240` satisfies `ψ(1/x)/x² = ψ(x)` by `E4im_inv`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- `∫_a^∞ e^{-rt} t dt = e^{-ra}(a/r + 1/r²)`. -/
theorem integral_Ioi_exp_mul_id {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in Set.Ioi a, Real.exp (-(r * t)) * t ^ 1
      = Real.exp (-(r * a)) * (a / r + 1 / r ^ 2) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(r * t)) * t ^ 1) (Set.Ioi (0 : ℝ)) :=
    integrable_exp_mul_pow hr 1
  have h0 := integral_exp_mul_pow hr 1
  have hsub := intervalIntegral.integral_Ioi_sub_Ioi hint ha
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt (fun t : ℝ => -(Real.exp (-(r * t)) * (t / r + 1 / r ^ 2)))
        (Real.exp (-(r * x)) * x ^ 1) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(r * t)))
        (Real.exp (-(r * x)) * (-(r * 1))) x :=
      (((hasDerivAt_id' x).const_mul r).neg).exp
    have h2 : HasDerivAt (fun t : ℝ => t / r + 1 / r ^ 2) (1 / r) x :=
      ((hasDerivAt_id' x).div_const r).add_const _
    have h3 := (h1.mul h2).neg
    refine h3.congr_deriv ?_
    have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    linear_combination (Real.exp (-(r * x)) * x + Real.exp (-(r * x)) * r⁻¹) * hrr
  have hcont : Continuous (fun t : ℝ => Real.exp (-(r * t)) * t ^ 1) := by fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 a)
  have e0 : Real.exp (-(r * 0)) = 1 := by rw [mul_zero, neg_zero, Real.exp_zero]
  have ef : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  rw [hftc, h0, e0, ef] at hsub
  linear_combination (-1 : ℝ) * hsub

/-- A series with non-negative coefficients and positive first coefficient is positive. -/
theorem qa_pos {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K)
    (hnn : ∀ n, 0 ≤ C n) (h1 : 0 < C 1) {y : ℝ} (hy : 0 < y) : 0 < qa C y := by
  unfold qa
  exact (summable_qa hC hy).tsum_pos (fun n => mul_nonneg (hnn n) (Real.exp_pos _).le) 1
    (mul_pos h1 (Real.exp_pos _))

/-- `qa C` is continuous on `[ε, ∞)` for `ε > 0`. -/
theorem continuousOn_qa {C : ℕ → ℝ} {B : ℝ} {K : ℕ} (hC : ∀ n, |C n| ≤ B * (n : ℝ) ^ K)
    {ε : ℝ} (hε : 0 < ε) : ContinuousOn (qa C) (Set.Ici ε) := by
  have hu := summable_qa_abs hC hε
  show ContinuousOn (fun x : ℝ => ∑' n : ℕ, C n * Real.exp (-(2 * π * (n : ℝ) * x))) (Set.Ici ε)
  refine continuousOn_tsum (fun n => ?_) hu (fun n x hx => ?_)
  · exact (by fun_prop :
      Continuous fun x : ℝ => C n * Real.exp (-(2 * π * (n : ℝ) * x))).continuousOn
  · have hx' : ε ≤ x := hx
    show ‖C n * Real.exp (-(2 * π * (n : ℝ) * x))‖ ≤ |C n| * Real.exp (-(2 * π * (n : ℝ) * ε))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    have h2 : 0 ≤ 2 * π * (n : ℝ) := by positivity
    have h3 := mul_le_mul_of_nonneg_left hx' h2
    linarith

/-- The partial Eichler integral `T(a) = ∫_a^∞ t S₃(t) dt`. -/
noncomputable def Tint (a : ℝ) : ℝ := ∫ t in Set.Ioi a, t * qa (sig 3) t

theorem sig3_div_nonneg (n : ℕ) : 0 ≤ sig 3 n / (n : ℝ) :=
  div_nonneg (sig_nonneg 3 n) (Nat.cast_nonneg n)

theorem sig3_div_sq_nonneg (n : ℕ) : 0 ≤ sig 3 n / (n : ℝ) ^ 2 :=
  div_nonneg (sig_nonneg 3 n) (pow_nonneg (Nat.cast_nonneg n) 2)

/-- `T(a) = a U₁(a)/(2π) + U₂(a)/(4π²)`. -/
theorem Tint_eq {a : ℝ} (ha : 0 < a) :
    Tint a = a * qa (fun n => sig 3 n / (n : ℝ)) a / (2 * π)
      + qa (fun n => sig 3 n / (n : ℝ) ^ 2) a / (4 * π ^ 2) := by
  have hr : ∀ n : ℕ, (0 : ℝ) < 2 * π * ((n + 1 : ℕ) : ℝ) := fun n => by positivity
  have hF_int : ∀ n : ℕ, Integrable
      (fun t : ℝ => sig 3 (n + 1) * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1))
      (volume.restrict (Set.Ioi a)) :=
    fun n => Integrable.const_mul
      (IntegrableOn.mono_set (integrable_exp_mul_pow (hr n) 1) (Set.Ioi_subset_Ioi ha.le)) _
  have hbase : ∀ n : ℕ,
      ∫ t in Set.Ioi a, Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1
        = Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a))
          * (a / (2 * π * ((n + 1 : ℕ) : ℝ)) + 1 / (2 * π * ((n + 1 : ℕ) : ℝ)) ^ 2) :=
    fun n => integral_Ioi_exp_mul_id (hr n) ha.le
  have hval : ∀ n : ℕ,
      ∫ t in Set.Ioi a, sig 3 (n + 1) * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1)
        = a / (2 * π) * (sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ)
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a)))
          + 1 / (4 * π ^ 2) * (sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a))) := by
    intro n
    rw [integral_const_mul, hbase n]
    ring
  have hnorm : ∀ n : ℕ,
      ∫ t in Set.Ioi a,
          ‖sig 3 (n + 1) * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1)‖
        = a / (2 * π) * (sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ)
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a)))
          + 1 / (4 * π ^ 2) * (sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a))) := by
    intro n
    rw [← hval n]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt (lt_trans ha ht)
    show ‖sig 3 (n + 1) * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1)‖
      = sig 3 (n + 1) * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1)
    rw [Real.norm_of_nonneg
      (mul_nonneg (sig_nonneg 3 _) (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht0 1)))]
  have hU1 : Summable fun n : ℕ => sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ)
      * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a)) :=
    (summable_nat_add_iff 1).mpr (summable_qa bound_sig3_div ha)
  have hU2 : Summable fun n : ℕ => sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2
      * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a)) :=
    (summable_nat_add_iff 1).mpr (summable_qa bound_sig3_div_sq ha)
  have hH := (hU1.hasSum.mul_left (a / (2 * π))).add (hU2.hasSum.mul_left (1 / (4 * π ^ 2)))
  have hsumInt : Summable fun n : ℕ => ∫ t in Set.Ioi a,
      ‖sig 3 (n + 1) * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1)‖ :=
    hH.summable.congr (fun n => (hnorm n).symm)
  have key := hasSum_integral_of_summable_integral_norm hF_int hsumInt
  have hfun : ∀ t ∈ Set.Ioi a, t * qa (sig 3) t
      = ∑' n : ℕ, sig 3 (n + 1) * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans ha ht
    rw [qa_eq_shift (sig_zero 3) (summable_qa (sig_abs_le 3) ht0), ← tsum_mul_left]
    exact tsum_congr (fun n => by ring)
  have e1 : qa (fun n => sig 3 n / (n : ℝ)) a
      = ∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ)
          * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a)) :=
    qa_eq_shift (by simp [sig_zero]) (summable_qa bound_sig3_div ha)
  have e2 : qa (fun n => sig 3 n / (n : ℝ) ^ 2) a
      = ∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2
          * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a)) :=
    qa_eq_shift (by simp [sig_zero]) (summable_qa bound_sig3_div_sq ha)
  unfold Tint
  rw [e1, e2]
  calc ∫ t in Set.Ioi a, t * qa (sig 3) t
      = ∫ t in Set.Ioi a, ∑' n : ℕ,
          sig 3 (n + 1) * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1) :=
        setIntegral_congr_fun measurableSet_Ioi hfun
    _ = ∑' n : ℕ, ∫ t in Set.Ioi a,
          sig 3 (n + 1) * (Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) * t ^ 1) :=
        key.tsum_eq.symm
    _ = ∑' n : ℕ, (a / (2 * π) * (sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ)
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a)))
          + 1 / (4 * π ^ 2) * (sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a)))) :=
        tsum_congr hval
    _ = a / (2 * π) * ∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ)
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a))
          + 1 / (4 * π ^ 2) * ∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a)) :=
        hH.tsum_eq
    _ = a * (∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ)
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a))) / (2 * π)
          + (∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2
              * Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * a))) / (4 * π ^ 2) := by
        ring

theorem Tint_pos {a : ℝ} (ha : 0 < a) : 0 < Tint a := by
  rw [Tint_eq ha]
  have h1 : 0 < qa (fun n => sig 3 n / (n : ℝ)) a :=
    qa_pos bound_sig3_div sig3_div_nonneg (by simp [sig]) ha
  have h2 : 0 < qa (fun n => sig 3 n / (n : ℝ) ^ 2) a :=
    qa_pos bound_sig3_div_sq sig3_div_sq_nonneg (by simp [sig]) ha
  positivity

/-- `t S₃(t)` is integrable on `(b, ∞)` for `b > 0`: its integral there is not zero. -/
theorem integrableOn_Tint {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t * qa (sig 3) t) (Set.Ioi b) := by
  refine Integrable.of_integral_ne_zero ?_
  exact (Tint_pos hb).ne'

/-- `∫_{1/a}^1 g = ∫_1^a g(1/x) x⁻² dx` for `a ≥ 1` and `g` continuous on `[1/a, 1]`. -/
theorem integral_inv_subst {g : ℝ → ℝ} {a : ℝ} (ha : 1 ≤ a)
    (hg : ContinuousOn g (Set.Icc (1 / a) 1)) :
    ∫ t in (1 / a)..1, g t = ∫ x in (1 : ℝ)..a, g x⁻¹ * (x ^ 2)⁻¹ := by
  have hu : Set.uIcc (1 : ℝ) a = Set.Icc 1 a := Set.uIcc_of_le ha
  have hd : ∀ x ∈ Set.uIcc (1 : ℝ) a, HasDerivAt (fun v : ℝ => v⁻¹) (-(x ^ 2)⁻¹) x := by
    intro x hx
    rw [hu] at hx
    exact hasDerivAt_inv (lt_of_lt_of_le one_pos hx.1).ne'
  have hc : ContinuousOn (fun x : ℝ => -(x ^ 2)⁻¹) (Set.uIcc (1 : ℝ) a) := by
    rw [hu]
    refine ((continuous_pow 2).continuousOn.inv₀ (fun x hx => ?_)).neg
    exact pow_ne_zero 2 (lt_of_lt_of_le one_pos hx.1).ne'
  have himg : (fun v : ℝ => v⁻¹) '' Set.uIcc (1 : ℝ) a ⊆ Set.Icc (1 / a) 1 := by
    rw [hu]
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
    constructor
    · rw [one_div]
      exact inv_anti₀ hx0 hx.2
    · exact inv_le_one_of_one_le₀ hx.1
  have h := intervalIntegral.integral_comp_mul_deriv' hd hc (hg.mono himg)
  have h' : ∫ x in (1 : ℝ)..a, (g ∘ fun v : ℝ => v⁻¹) x * -(x ^ 2)⁻¹
      = ∫ x in (1 : ℝ)..(1 / a), g x := by
    have h2 := h
    simp only [inv_one] at h2
    rw [one_div]
    exact h2
  have e3 : ∫ x in (1 : ℝ)..a, g x⁻¹ * (x ^ 2)⁻¹
      = -∫ x in (1 : ℝ)..a, (g ∘ fun v : ℝ => v⁻¹) x * -(x ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    show g x⁻¹ * (x ^ 2)⁻¹ = -((g ∘ fun v : ℝ => v⁻¹) x * -(x ^ 2)⁻¹)
    rw [Function.comp_apply, mul_neg, neg_neg]
  calc ∫ t in (1 / a)..1, g t = -∫ t in (1 : ℝ)..(1 / a), g t :=
        intervalIntegral.integral_symm _ _
    _ = -∫ x in (1 : ℝ)..a, (g ∘ fun v : ℝ => v⁻¹) x * -(x ^ 2)⁻¹ := by rw [h']
    _ = ∫ x in (1 : ℝ)..a, g x⁻¹ * (x ^ 2)⁻¹ := e3.symm

/-- `ψ(t) = t (S₃(t) + 1/240)` satisfies `ψ(1/x)/x² = ψ(x)`. -/
theorem psi_inv {x : ℝ} (hx : 0 < x) :
    (x⁻¹ * qa (sig 3) x⁻¹ + x⁻¹ / 240) * (x ^ 2)⁻¹ = x * qa (sig 3) x + x / 240 := by
  have h := E4im_inv hx
  rw [E4im_eq_qa hx, E4im_eq_qa (by positivity : (0 : ℝ) < 1 / x), one_div] at h
  have hS : qa (sig 3) x⁻¹ = x ^ 4 * qa (sig 3) x + (x ^ 4 - 1) / 240 := by
    linear_combination (1 / 240 : ℝ) * h
  have hx' : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  linear_combination (x⁻¹ ^ 3) * hS
    + ((qa (sig 3) x * x + x / 240) * (x⁻¹ ^ 2 * x ^ 2 + x⁻¹ * x + 1)) * hx'

theorem Tint_inv_of_one_le {a : ℝ} (ha : 1 ≤ a) :
    Tint a + Tint (1 / a) = (a ^ 2 + (1 / a) ^ 2) / 480 + 2 * Tint 1 - 1 / 240 := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hia0 : (0 : ℝ) < 1 / a := by positivity
  have hia1 : 1 / a ≤ 1 := by
    rw [div_le_one ha0]
    exact ha
  have h1 := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_Tint one_pos) ha
  have h2 := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_Tint hia0) hia1
  have hcont : ∀ ε : ℝ, 0 < ε → ContinuousOn (fun t : ℝ => t * qa (sig 3) t) (Set.Ici ε) :=
    fun ε hε => continuous_id.continuousOn.mul (continuousOn_qa (sig_abs_le 3) hε)
  have hψcont : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun t : ℝ => t * qa (sig 3) t + t / 240) (Set.Ici ε) :=
    fun ε hε => (hcont ε hε).add (continuous_id.div_const 240).continuousOn
  have hadd : ∀ b c : ℝ, 0 < b → b ≤ c →
      ∫ x in b..c, (x * qa (sig 3) x + x / 240)
        = ∫ x in b..c, x * qa (sig 3) x + (c ^ 2 - b ^ 2) / 2 / 240 := by
    intro b c hb hbc
    have hsub : Set.uIcc b c ⊆ Set.Ici b := by
      rw [Set.uIcc_of_le hbc]
      exact fun x hx => hx.1
    have i1 : IntervalIntegrable (fun x : ℝ => x * qa (sig 3) x) volume b c :=
      ((hcont b hb).mono hsub).intervalIntegrable
    have i2 : IntervalIntegrable (fun x : ℝ => x / 240) volume b c :=
      (continuous_id.div_const 240).intervalIntegrable b c
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_div, integral_id]
  have hA := hadd 1 a one_pos ha
  have hB := hadd (1 / a) 1 hia0 hia1
  have h4 : ∫ x in (1 / a)..1, (x * qa (sig 3) x + x / 240)
      = ∫ x in (1 : ℝ)..a, (x * qa (sig 3) x + x / 240) := by
    rw [integral_inv_subst ha ((hψcont (1 / a) hia0).mono Set.Icc_subset_Ici_self)]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le ha] at hx
    exact psi_inv (lt_of_lt_of_le one_pos hx.1)
  unfold Tint
  linear_combination (-1 : ℝ) * h1 + h2 + hA - hB + h4

/-- **Inversion formula for the partial Eichler integral.** -/
theorem Tint_inv {a : ℝ} (ha : 0 < a) :
    Tint a + Tint (1 / a) = (a ^ 2 + (1 / a) ^ 2) / 480 + 2 * Tint 1 - 1 / 240 := by
  rcases le_total 1 a with h | h
  · exact Tint_inv_of_one_le h
  · have h' : 1 ≤ 1 / a := by
      rw [le_div_iff₀ ha, one_mul]
      exact h
    have key := Tint_inv_of_one_le h'
    rw [one_div_one_div] at key
    linear_combination key

end Tower.RV6
