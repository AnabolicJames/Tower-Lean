import Mathlib
import Tower.RV6.BesselJ
import Tower.RV6.Laplace
import Tower.RV6.LadderB
import Tower.RV6.HankelDom

/-!
# The Hankel transform at fixed `x`: two integrations by parts

`hk ψ x = ∫₀^∞ J₀(xt) ψ(t) t dt`, so `hjF = hk fB` by definition.  For `x ≥ 0` and `ψ`, `χ` in a
chain `HChain ψ ψ₁` (`ψ, ψ₁ ∈ HDom`, `ψ' = ψ₁/t`, i.e. `ψ₁ = θψ`):

* `hk_ibpA`: `∫ t (ψ₁ + 2ψ) J₀(xt) dt = ∫ t² ψ · x J₁(xt) dt`  (`F = t² ψ J₀(xt)`, `F' = ...`, `∫ F' = 0`);
* `hk_ibpB`: `∫ t² (χ₁ + 2χ) · x J₁(xt) dt = -x² ∫ t³ χ J₀(xt) dt`  (`G = t² χ · (xt) J₁(xt)`, from
  `(s J₁(s))' = s J₀(s)`);
* **`hk_theta2`**: `hk((θ + 2)² φ) = -x² hk(t² φ)` for a chain `φ, φ₁, φ₂`
  (`(θ + 2)² φ = φ₂ + 4φ₁ + 4φ`).

Every integral converges absolutely and every boundary term vanishes by `HankelDom.lean`.
-/

namespace Tower.RV6

open MeasureTheory

/-- The Hankel transform `∫₀^∞ J₀(xt) ψ(t) t dt`. -/
noncomputable def hk (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * ψ t * t

theorem hjF_eq_hk : hjF = hk fB := rfl

/-! ## The two kernels -/

theorem continuousOn_besselJ0_mul (x : ℝ) :
    ContinuousOn (fun t : ℝ => besselJ0 (x * t)) (Set.Ioi 0) := by
  have hm : Continuous (fun t : ℝ => x * t) := continuous_const.mul continuous_id
  have h : Continuous (fun t : ℝ => besselJ0 (x * t)) := continuous_besselJ0.comp hm
  exact h.continuousOn

theorem continuousOn_mul_besselJ1_mul (x : ℝ) :
    ContinuousOn (fun t : ℝ => x * besselJ1 (x * t)) (Set.Ioi 0) := by
  have hm : Continuous (fun t : ℝ => x * t) := continuous_const.mul continuous_id
  have h : Continuous (fun t : ℝ => besselJ1 (x * t)) := continuous_besselJ1.comp hm
  have h2 : ContinuousOn (fun t : ℝ => x * besselJ1 (x * t)) (Set.Ioi 0) :=
    ContinuousOn.mul (f := fun _ : ℝ => x) continuousOn_const h.continuousOn
  exact h2

theorem abs_besselJ0_mul_le {x : ℝ} (hx : 0 ≤ x) :
    ∀ t : ℝ, 0 < t → |besselJ0 (x * t)| ≤ 1 :=
  fun t ht => abs_besselJ0_le_one (mul_nonneg hx ht.le)

theorem abs_mul_besselJ1_mul_le {x : ℝ} (hx : 0 ≤ x) :
    ∀ t : ℝ, 0 < t → |x * besselJ1 (x * t)| ≤ x := by
  intro t ht
  rw [abs_mul, abs_of_nonneg hx]
  exact mul_le_of_le_one_right hx (abs_besselJ1_le_one (mul_nonneg hx ht.le))

/-! ## Linearity -/

theorem integrableOn_hk {φ : ℝ → ℝ} (hφ : HDom φ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => besselJ0 (x * t) * φ t * t) (Set.Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => t ^ 1 * φ t * besselJ0 (x * t)) (Set.Ioi 0) :=
    integrableOn_hdom hφ (continuousOn_besselJ0_mul x) (abs_besselJ0_mul_le hx) (le_refl 1)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show t ^ 1 * φ t * besselJ0 (x * t) = besselJ0 (x * t) * φ t * t
  ring

theorem hk_add {φ ψ : ℝ → ℝ} (hφ : HDom φ) (hψ : HDom ψ) {x : ℝ} (hx : 0 ≤ x) :
    hk (fun t => φ t + ψ t) x = hk φ x + hk ψ x := by
  unfold hk
  rw [← integral_add (integrableOn_hk hφ hx) (integrableOn_hk hψ hx)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  show besselJ0 (x * t) * (φ t + ψ t) * t
    = besselJ0 (x * t) * φ t * t + besselJ0 (x * t) * ψ t * t
  ring

theorem hk_const_mul (c : ℝ) (φ : ℝ → ℝ) (x : ℝ) : hk (fun t => c * φ t) x = c * hk φ x := by
  unfold hk
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  show besselJ0 (x * t) * (c * φ t) * t = c * (besselJ0 (x * t) * φ t * t)
  ring

theorem hk_add_cmul {φ ψ : ℝ → ℝ} (hφ : HDom φ) (hψ : HDom ψ) (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    hk (fun t => φ t + a * ψ t) x = hk φ x + a * hk ψ x := by
  have h := hk_add hφ (hdom_const_mul a hψ) hx
  rw [hk_const_mul] at h
  exact h

theorem hk_congr {φ ψ : ℝ → ℝ} (h : ∀ t : ℝ, φ t = ψ t) (x : ℝ) : hk φ x = hk ψ x := by
  have e : φ = ψ := funext h
  rw [e]

theorem hk_zero (x : ℝ) : hk (fun _ => 0) x = 0 := by
  simp [hk]

/-! ## Chains -/

/-- `φ, φ₁ ∈ HDom` and `φ₁ = θφ = t φ'` on `(0, ∞)`. -/
abbrev HChain (φ φ1 : ℝ → ℝ) : Prop :=
  HDom φ ∧ HDom φ1 ∧ ∀ t : ℝ, 0 < t → HasDerivAt φ (φ1 t / t) t

theorem hchain_add {φ φ1 ψ ψ1 : ℝ → ℝ} (h1 : HChain φ φ1) (h2 : HChain ψ ψ1) :
    HChain (fun t => φ t + ψ t) (fun t => φ1 t + ψ1 t) := by
  obtain ⟨a1, b1, d1⟩ := h1
  obtain ⟨a2, b2, d2⟩ := h2
  refine ⟨hdom_add a1 a2, hdom_add b1 b2, fun t ht => ?_⟩
  have h := (d1 t ht).add (d2 t ht)
  have h' : HasDerivAt (fun t => φ t + ψ t) (φ1 t / t + ψ1 t / t) t := h
  refine h'.congr_deriv ?_
  show φ1 t / t + ψ1 t / t = (φ1 t + ψ1 t) / t
  ring

theorem hchain_const_mul (c : ℝ) {φ φ1 : ℝ → ℝ} (h1 : HChain φ φ1) :
    HChain (fun t => c * φ t) (fun t => c * φ1 t) := by
  obtain ⟨a1, b1, d1⟩ := h1
  refine ⟨hdom_const_mul c a1, hdom_const_mul c b1, fun t ht => ?_⟩
  have h := (d1 t ht).const_mul c
  have h' : HasDerivAt (fun t => c * φ t) (c * (φ1 t / t)) t := h
  refine h'.congr_deriv ?_
  show c * (φ1 t / t) = c * φ1 t / t
  ring

/-- `θ(t² φ) = t² (θφ + 2φ)`. -/
theorem hchain_tsq {φ φ1 : ℝ → ℝ} (h1 : HChain φ φ1) :
    HChain (fun t => t ^ 2 * φ t) (fun t => t ^ 2 * (φ1 t + 2 * φ t)) := by
  obtain ⟨a1, b1, d1⟩ := h1
  refine ⟨hdom_pow_mul 2 a1, hdom_pow_mul 2 (hdom_add b1 (hdom_const_mul 2 a1)),
    fun t ht => ?_⟩
  have h := (hasDerivAt_sqx t).mul (d1 t ht)
  have h' : HasDerivAt (fun t => t ^ 2 * φ t) (2 * t * φ t + t ^ 2 * (φ1 t / t)) t := h
  refine h'.congr_deriv ?_
  show 2 * t * φ t + t ^ 2 * (φ1 t / t) = t ^ 2 * (φ1 t + 2 * φ t) / t
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  linear_combination (-(2 * t * φ t)) * hinv

/-! ## The two integrations by parts -/

/-- `∫ t (ψ₁ + 2ψ) J₀(xt) dt = ∫ t² ψ · x J₁(xt) dt`. -/
theorem hk_ibpA {ψ ψ1 : ℝ → ℝ} (hc : HChain ψ ψ1) {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (x * t)
      = ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * ψ t * (x * besselJ1 (x * t)) := by
  obtain ⟨hψ, hψ1, hd⟩ := hc
  have i1 : IntegrableOn (fun t : ℝ => t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (x * t))
      (Set.Ioi 0) :=
    integrableOn_hdom (hdom_add hψ1 (hdom_const_mul 2 hψ)) (continuousOn_besselJ0_mul x)
      (abs_besselJ0_mul_le hx) (le_refl 1)
  have i2 : IntegrableOn (fun t : ℝ => t ^ 2 * ψ t * (x * besselJ1 (x * t))) (Set.Ioi 0) :=
    integrableOn_hdom hψ (continuousOn_mul_besselJ1_mul x) (abs_mul_besselJ1_mul_le hx)
      (by norm_num)
  have i3 : IntegrableOn (fun t : ℝ => t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (x * t)
      - t ^ 2 * ψ t * (x * besselJ1 (x * t))) (Set.Ioi 0) := Integrable.sub i1 i2
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => t ^ 2 * ψ t * besselJ0 (x * t))
      (t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (x * t) - t ^ 2 * ψ t * (x * besselJ1 (x * t))) t := by
    intro t ht
    have h0 := ((hasDerivAt_sqx t).mul (hd t ht)).mul (hasDerivAt_besselJ0_comp x t)
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 * ψ t * besselJ0 (x * t))
        ((2 * t * ψ t + t ^ 2 * (ψ1 t / t)) * besselJ0 (x * t)
          + t ^ 2 * ψ t * (-(x * besselJ1 (x * t)))) t := h0
    refine h1.congr_deriv ?_
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    linear_combination (t * ψ1 t * besselJ0 (x * t)) * hinv
  have hF0 : (fun t : ℝ => t ^ 2 * ψ t * besselJ0 (x * t)) 0 = 0 := by
    show (0 : ℝ) ^ 2 * ψ 0 * besselJ0 (x * 0) = 0
    ring
  have hlim0 := tendsto_hdom_zero hψ (abs_besselJ0_mul_le hx)
  have hliminf := tendsto_hdom_atTop hψ (abs_besselJ0_mul_le hx)
  have h0 := integral_Ioi_deriv_eq_zero
    (F := fun t : ℝ => t ^ 2 * ψ t * besselJ0 (x * t))
    (F' := fun t : ℝ => t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (x * t)
      - t ^ 2 * ψ t * (x * besselJ1 (x * t))) hF0 hderiv hlim0 hliminf i3
  have h : ∫ t in Set.Ioi (0 : ℝ), (t ^ 1 * (ψ1 t + 2 * ψ t) * besselJ0 (x * t)
      - t ^ 2 * ψ t * (x * besselJ1 (x * t))) = 0 := h0
  rw [integral_sub i1 i2] at h
  linarith

/-- `∫ t² (χ₁ + 2χ) · x J₁(xt) dt = -x² ∫ t³ χ J₀(xt) dt`. -/
theorem hk_ibpB {χ χ1 : ℝ → ℝ} (hc : HChain χ χ1) {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * (χ1 t + 2 * χ t) * (x * besselJ1 (x * t))
      = -(x ^ 2 * ∫ t in Set.Ioi (0 : ℝ), t ^ 3 * χ t * besselJ0 (x * t)) := by
  obtain ⟨hχ, hχ1, hd⟩ := hc
  have i1 : IntegrableOn (fun t : ℝ => t ^ 2 * (χ1 t + 2 * χ t) * (x * besselJ1 (x * t)))
      (Set.Ioi 0) :=
    integrableOn_hdom (hdom_add hχ1 (hdom_const_mul 2 hχ)) (continuousOn_mul_besselJ1_mul x)
      (abs_mul_besselJ1_mul_le hx) (by norm_num)
  have i2 : IntegrableOn (fun t : ℝ => t ^ 3 * χ t * besselJ0 (x * t)) (Set.Ioi 0) :=
    integrableOn_hdom hχ (continuousOn_besselJ0_mul x) (abs_besselJ0_mul_le hx) (by norm_num)
  have i2' : IntegrableOn (fun t : ℝ => x ^ 2 * (t ^ 3 * χ t * besselJ0 (x * t))) (Set.Ioi 0) :=
    Integrable.const_mul i2 (x ^ 2)
  have i3 : IntegrableOn (fun t : ℝ => t ^ 2 * (χ1 t + 2 * χ t) * (x * besselJ1 (x * t))
      + x ^ 2 * (t ^ 3 * χ t * besselJ0 (x * t))) (Set.Ioi 0) := Integrable.add i1 i2'
  have hderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun t : ℝ => t ^ 2 * χ t * (x * t * besselJ1 (x * t)))
        (t ^ 2 * (χ1 t + 2 * χ t) * (x * besselJ1 (x * t))
          + x ^ 2 * (t ^ 3 * χ t * besselJ0 (x * t))) t := by
    intro t ht
    have hq0 := (hasDerivAt_mul_besselJ1 (x * t)).comp t ((hasDerivAt_id' t).const_mul x)
    have hq : HasDerivAt (fun y : ℝ => x * y * besselJ1 (x * y))
        (x * t * besselJ0 (x * t) * (x * 1)) t := hq0
    have h0 := ((hasDerivAt_sqx t).mul (hd t ht)).mul hq
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 * χ t * (x * t * besselJ1 (x * t)))
        ((2 * t * χ t + t ^ 2 * (χ1 t / t)) * (x * t * besselJ1 (x * t))
          + t ^ 2 * χ t * (x * t * besselJ0 (x * t) * (x * 1))) t := h0
    refine h1.congr_deriv ?_
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    linear_combination (t * χ1 t * (x * t * besselJ1 (x * t))) * hinv
  have hF0 : (fun t : ℝ => t ^ 2 * χ t * (x * t * besselJ1 (x * t))) 0 = 0 := by
    show (0 : ℝ) ^ 2 * χ 0 * (x * 0 * besselJ1 (x * 0)) = 0
    ring
  have hT : HDom (fun t : ℝ => t ^ 1 * χ t) := hdom_pow_mul 1 hχ
  have heq : ∀ t : ℝ, t ^ 2 * (t ^ 1 * χ t) * (x * besselJ1 (x * t))
      = t ^ 2 * χ t * (x * t * besselJ1 (x * t)) := fun t => by ring
  have hlim0 := (tendsto_hdom_zero hT (abs_mul_besselJ1_mul_le hx)).congr heq
  have hliminf := (tendsto_hdom_atTop hT (abs_mul_besselJ1_mul_le hx)).congr heq
  have h0 := integral_Ioi_deriv_eq_zero
    (F := fun t : ℝ => t ^ 2 * χ t * (x * t * besselJ1 (x * t)))
    (F' := fun t : ℝ => t ^ 2 * (χ1 t + 2 * χ t) * (x * besselJ1 (x * t))
      + x ^ 2 * (t ^ 3 * χ t * besselJ0 (x * t))) hF0 hderiv hlim0 hliminf i3
  have h : ∫ t in Set.Ioi (0 : ℝ), (t ^ 2 * (χ1 t + 2 * χ t) * (x * besselJ1 (x * t))
      + x ^ 2 * (t ^ 3 * χ t * besselJ0 (x * t))) = 0 := h0
  rw [integral_add i1 i2', integral_const_mul] at h
  linarith

/-- **`hk((θ + 2)² φ) = -x² hk(t² φ)`** for a chain `φ, φ₁ = θφ, φ₂ = θφ₁` in `HDom`. -/
theorem hk_theta2 {φ φ1 φ2 : ℝ → ℝ} (h1 : HChain φ φ1) (h2 : HChain φ1 φ2) {x : ℝ}
    (hx : 0 ≤ x) :
    hk (fun t => φ2 t + 4 * φ1 t + 4 * φ t) x = -(x ^ 2 * hk (fun t => t ^ 2 * φ t) x) := by
  have hψ : HChain (fun t => φ1 t + 2 * φ t) (fun t => φ2 t + 2 * φ1 t) :=
    hchain_add h2 (hchain_const_mul 2 h1)
  have hA : ∫ t in Set.Ioi (0 : ℝ),
        t ^ 1 * (φ2 t + 2 * φ1 t + 2 * (φ1 t + 2 * φ t)) * besselJ0 (x * t)
      = ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * (φ1 t + 2 * φ t) * (x * besselJ1 (x * t)) :=
    hk_ibpA hψ hx
  have hB : ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * (φ1 t + 2 * φ t) * (x * besselJ1 (x * t))
      = -(x ^ 2 * ∫ t in Set.Ioi (0 : ℝ), t ^ 3 * φ t * besselJ0 (x * t)) :=
    hk_ibpB h1 hx
  have e1 : hk (fun t => φ2 t + 4 * φ1 t + 4 * φ t) x
      = ∫ t in Set.Ioi (0 : ℝ),
        t ^ 1 * (φ2 t + 2 * φ1 t + 2 * (φ1 t + 2 * φ t)) * besselJ0 (x * t) := by
    unfold hk
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show besselJ0 (x * t) * (φ2 t + 4 * φ1 t + 4 * φ t) * t
      = t ^ 1 * (φ2 t + 2 * φ1 t + 2 * (φ1 t + 2 * φ t)) * besselJ0 (x * t)
    ring
  have e2 : hk (fun t => t ^ 2 * φ t) x
      = ∫ t in Set.Ioi (0 : ℝ), t ^ 3 * φ t * besselJ0 (x * t) := by
    unfold hk
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show besselJ0 (x * t) * (t ^ 2 * φ t) * t = t ^ 3 * φ t * besselJ0 (x * t)
    ring
  rw [e1, e2, hA, hB]

end Tower.RV6
