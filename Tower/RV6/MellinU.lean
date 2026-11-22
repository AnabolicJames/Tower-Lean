import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselI
import Tower.RV6.BesselK
import Tower.RV6.BesselW
import Tower.RV6.BesselR
import Tower.RV6.BesselJ
import Tower.RV6.LadderA2

/-!
# The Mellin integrands in the variable `u = log t` are integrable

The sub-rungs of `LadderA2.lean` are statements about `mellU h s = ∫ h(e^u) e^{su} du`.  This file
proves, once, the bounds and the integrability they all need.

* `integrable_mul_exp_of_bounds`: if `|g u| ≤ A (2 - u)^b` for `u ≤ 0` and `|g u| ≤ B e^{-αu}` for
  `u > 0`, then `g(u) e^{σu}` is integrable on `ℝ` for `0 < σ < α`
  (`two_sub_pow_le`: `(2 - u)^b ≤ b! δ^{-b} e^{2δ} e^{-δu}` for `u ≤ 0`).
* Small `t`: `K₀(e^u) ≤ 2 - u` and `I₀(e^u) ≤ e` for `u ≤ 0`.
* Large `t`: `I₀ K₀ ≤ 1/t`; for `t ≥ 1`, with `κ = e K₀(1)`: `K₀(t) ≤ κ e^{-t}`, `I₀ K₀ ≤ κ`,
  `I₀^a K₀^{a+d+2} ≤ κ^{a+d+2} e^{-2t}`; and `exp(-2e^u) ≤ (27/8) e^{-3u}`.
* Consequences, for `0 < σ < 3`: `h(e^u) e^{σu}` is integrable on `ℝ` for `h = I₀^a K₀^{a+d+2}`,
  `I₀³ K₀³`, `I₀² I₁ K₀⁵`, `J₀⁶`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## A power of `2 - u` against an exponential -/

/-- `(2 - u)^b ≤ b! δ^{-b} e^{2δ} e^{-δu}` for `u ≤ 0` and `δ > 0`. -/
theorem two_sub_pow_le {δ : ℝ} (hδ : 0 < δ) (b : ℕ) {u : ℝ} (hu : u ≤ 0) :
    (2 - u) ^ b ≤ (b.factorial : ℝ) * (1 / δ) ^ b * Real.exp (2 * δ) * Real.exp (-δ * u) := by
  have h2u : (0 : ℝ) ≤ 2 - u := by linarith
  have hx : 0 ≤ δ * (2 - u) := mul_nonneg hδ.le h2u
  have h1 : (δ * (2 - u)) ^ b / (b.factorial : ℝ) ≤ Real.exp (δ * (2 - u)) :=
    Real.pow_div_factorial_le_exp (x := δ * (2 - u)) hx b
  have hf : (0 : ℝ) < (b.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos b)
  have h2 : (δ * (2 - u)) ^ b ≤ Real.exp (δ * (2 - u)) * (b.factorial : ℝ) :=
    (div_le_iff₀ hf).mp h1
  have he : Real.exp (δ * (2 - u)) = Real.exp (2 * δ) * Real.exp (-δ * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hone : 1 / δ * (δ * (2 - u)) = 2 - u := by
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
  have hd : (1 / δ) ^ b * (δ * (2 - u)) ^ b = (2 - u) ^ b := by
    rw [← mul_pow, hone]
  have hp : (0 : ℝ) ≤ (1 / δ) ^ b := pow_nonneg (one_div_nonneg.mpr hδ.le) b
  have h3 : (1 / δ) ^ b * (δ * (2 - u)) ^ b
      ≤ (1 / δ) ^ b * (Real.exp (δ * (2 - u)) * (b.factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 hp
  rw [hd, he] at h3
  have e : (1 / δ) ^ b * (Real.exp (2 * δ) * Real.exp (-δ * u) * (b.factorial : ℝ))
      = (b.factorial : ℝ) * (1 / δ) ^ b * Real.exp (2 * δ) * Real.exp (-δ * u) := by ring
  rw [e] at h3
  exact h3

/-! ## The general integrability lemma -/

/-- If `|g u| ≤ A (2 - u)^b` for `u ≤ 0` and `|g u| ≤ B e^{-αu}` for `u > 0`, then `g(u) e^{σu}` is
integrable on `ℝ` for `0 < σ < α`. -/
theorem integrable_mul_exp_of_bounds {g : ℝ → ℝ} (hm : AEStronglyMeasurable g volume)
    {A B α σ : ℝ} {b : ℕ} (hA : 0 ≤ A)
    (hlo : ∀ u : ℝ, u ≤ 0 → |g u| ≤ A * (2 - u) ^ b)
    (hhi : ∀ u : ℝ, 0 < u → |g u| ≤ B * Real.exp (-α * u))
    (hσ : 0 < σ) (hσα : σ < α) :
    Integrable (fun u : ℝ => g u * Real.exp (σ * u)) := by
  have hexp : Continuous (fun u : ℝ => Real.exp (σ * u)) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun u : ℝ => g u * Real.exp (σ * u)) volume :=
    hm.mul hexp.aestronglyMeasurable
  have hδ : 0 < σ / 2 := half_pos hσ
  -- the left half-line
  have hbL : Integrable
      (fun u : ℝ => A * ((b.factorial : ℝ) * (1 / (σ / 2)) ^ b * Real.exp (2 * (σ / 2)))
        * Real.exp (σ / 2 * u)) (volume.restrict (Set.Iic (0 : ℝ))) :=
    Integrable.const_mul (integrableOn_exp_mul_Iic hδ 0)
      (A * ((b.factorial : ℝ) * (1 / (σ / 2)) ^ b * Real.exp (2 * (σ / 2))))
  have haeL : ∀ᵐ u ∂(volume.restrict (Set.Iic (0 : ℝ))),
      ‖g u * Real.exp (σ * u)‖
        ≤ A * ((b.factorial : ℝ) * (1 / (σ / 2)) ^ b * Real.exp (2 * (σ / 2)))
          * Real.exp (σ / 2 * u) := by
    refine ae_restrict_of_forall_mem measurableSet_Iic (fun u hu => ?_)
    show ‖g u * Real.exp (σ * u)‖
        ≤ A * ((b.factorial : ℝ) * (1 / (σ / 2)) ^ b * Real.exp (2 * (σ / 2)))
          * Real.exp (σ / 2 * u)
    have hu0 : u ≤ 0 := hu
    have hE : 0 < Real.exp (σ * u) := Real.exp_pos _
    have h1 := hlo u hu0
    have h2 := two_sub_pow_le hδ b hu0
    have h3 : |g u| * Real.exp (σ * u) ≤ A * (2 - u) ^ b * Real.exp (σ * u) :=
      mul_le_mul_of_nonneg_right h1 hE.le
    have h4 : A * (2 - u) ^ b * Real.exp (σ * u)
        ≤ A * ((b.factorial : ℝ) * (1 / (σ / 2)) ^ b * Real.exp (2 * (σ / 2))
            * Real.exp (-(σ / 2) * u)) * Real.exp (σ * u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hA) hE.le
    have he : Real.exp (-(σ / 2) * u) * Real.exp (σ * u) = Real.exp (σ / 2 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h5 : A * ((b.factorial : ℝ) * (1 / (σ / 2)) ^ b * Real.exp (2 * (σ / 2))
            * Real.exp (-(σ / 2) * u)) * Real.exp (σ * u)
        = A * ((b.factorial : ℝ) * (1 / (σ / 2)) ^ b * Real.exp (2 * (σ / 2)))
            * (Real.exp (-(σ / 2) * u) * Real.exp (σ * u)) := by ring
    rw [h5, he] at h4
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE]
    exact le_trans h3 h4
  have hL : IntegrableOn (fun u : ℝ => g u * Real.exp (σ * u)) (Set.Iic (0 : ℝ)) :=
    Integrable.mono' hbL hmeas.restrict haeL
  -- the right half-line
  have hbR : Integrable (fun u : ℝ => B * Real.exp (-(α - σ) * u))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hσα)) B
  have haeR : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖g u * Real.exp (σ * u)‖ ≤ B * Real.exp (-(α - σ) * u) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
    show ‖g u * Real.exp (σ * u)‖ ≤ B * Real.exp (-(α - σ) * u)
    have hu0 : 0 < u := hu
    have hE : 0 < Real.exp (σ * u) := Real.exp_pos _
    have h1 := hhi u hu0
    have h3 : |g u| * Real.exp (σ * u) ≤ B * Real.exp (-α * u) * Real.exp (σ * u) :=
      mul_le_mul_of_nonneg_right h1 hE.le
    have he : Real.exp (-α * u) * Real.exp (σ * u) = Real.exp (-(α - σ) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h5 : B * Real.exp (-α * u) * Real.exp (σ * u)
        = B * (Real.exp (-α * u) * Real.exp (σ * u)) := by ring
    rw [h5, he] at h3
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE]
    exact h3
  have hR : IntegrableOn (fun u : ℝ => g u * Real.exp (σ * u)) (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' hbR hmeas.restrict haeR
  have hU : IntegrableOn (fun u : ℝ => g u * Real.exp (σ * u))
      (Set.Iic (0 : ℝ) ∪ Set.Ioi 0) := IntegrableOn.union hL hR
  rw [Set.Iic_union_Ioi, integrableOn_univ] at hU
  exact hU

/-! ## Small `t` -/

theorem exp_le_one_of_nonpos {u : ℝ} (hu : u ≤ 0) : Real.exp u ≤ 1 := by
  have h := Real.exp_le_exp.mpr hu
  rw [Real.exp_zero] at h
  exact h

theorem one_le_exp_of_pos {u : ℝ} (hu : 0 < u) : 1 ≤ Real.exp u := by
  have h := Real.exp_le_exp.mpr hu.le
  rw [Real.exp_zero] at h
  exact h

/-- `K₀(e^u) ≤ 2 - u` for `u ≤ 0`. -/
theorem besselK0_exp_le_small {u : ℝ} (hu : u ≤ 0) : besselK0 (Real.exp u) ≤ 2 - u := by
  have ht : 0 < Real.exp u := Real.exp_pos u
  have h := besselK0_le_one_add_log ht (exp_le_one_of_nonpos hu)
  have h2 : Real.log (2 / Real.exp u) = Real.log 2 - u := by
    rw [Real.log_div two_ne_zero ht.ne', Real.log_exp]
  have h3 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos two_pos
  rw [h2] at h
  linarith

/-- `I₀(e^u) ≤ e` for `u ≤ 0`. -/
theorem besselI0_exp_le_small {u : ℝ} (hu : u ≤ 0) : besselI0 (Real.exp u) ≤ Real.exp 1 :=
  le_trans (besselI0_le_exp (Real.exp_pos u)) (Real.exp_le_exp.mpr (exp_le_one_of_nonpos hu))

/-- `I₀(e^u)^a K₀(e^u)^b ≤ e^a (2 - u)^b` for `u ≤ 0`. -/
theorem besselIK_exp_abs_le_small (a b : ℕ) {u : ℝ} (hu : u ≤ 0) :
    |besselI0 (Real.exp u) ^ a * besselK0 (Real.exp u) ^ b| ≤ Real.exp 1 ^ a * (2 - u) ^ b := by
  have hI0 : 0 ≤ besselI0 (Real.exp u) := (besselI0_pos _).le
  have hK0 : 0 ≤ besselK0 (Real.exp u) := besselK0_nonneg _
  have h1 : besselI0 (Real.exp u) ^ a ≤ Real.exp 1 ^ a :=
    pow_le_pow_left₀ hI0 (besselI0_exp_le_small hu) a
  have h2 : besselK0 (Real.exp u) ^ b ≤ (2 - u) ^ b :=
    pow_le_pow_left₀ hK0 (besselK0_exp_le_small hu) b
  have hnn : 0 ≤ besselI0 (Real.exp u) ^ a * besselK0 (Real.exp u) ^ b :=
    mul_nonneg (pow_nonneg hI0 a) (pow_nonneg hK0 b)
  rw [abs_of_nonneg hnn]
  exact mul_le_mul h1 h2 (pow_nonneg hK0 b) (pow_nonneg (Real.exp_pos 1).le a)

/-! ## Large `t` -/

/-- `I₀(t) K₀(t) ≤ 1/t` for `t > 0`. -/
theorem besselI0_mul_besselK0_le {t : ℝ} (ht : 0 < t) : besselI0 t * besselK0 t ≤ 1 / t := by
  have hw := wronskian ht
  have h1 : besselI0 t * besselK0 t ≤ besselI0 t * besselK1 t :=
    mul_le_mul_of_nonneg_left (besselK0_le_besselK1 ht) (besselI0_pos t).le
  have h2 : 0 ≤ besselI1 t * besselK0 t :=
    mul_nonneg (besselI1_nonneg ht.le) (besselK0_nonneg t)
  linarith

/-- `K₀(t) ≤ κ e^{-t}` for `t ≥ 1`, `κ = e K₀(1)`. -/
theorem besselK0_le_kappa_exp {t : ℝ} (ht : 1 ≤ t) :
    besselK0 t ≤ Real.exp 1 * besselK0 1 * Real.exp (-t) := by
  have h := besselK0_le_of_one_le ht
  have e : Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have e2 : Real.exp 1 * Real.exp (-t) * besselK0 1
      = Real.exp 1 * besselK0 1 * Real.exp (-t) := by ring
  rw [e, e2] at h
  exact h

/-- `I₀(t) K₀(t) ≤ κ` for `t ≥ 1`. -/
theorem besselI0_mul_besselK0_le_kappa {t : ℝ} (ht : 1 ≤ t) :
    besselI0 t * besselK0 t ≤ Real.exp 1 * besselK0 1 := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hI := besselI0_le_exp ht0
  have hK := besselK0_le_kappa_exp ht
  have h1 : besselI0 t * besselK0 t
      ≤ Real.exp t * (Real.exp 1 * besselK0 1 * Real.exp (-t)) :=
    mul_le_mul hI hK (besselK0_nonneg t) (Real.exp_pos t).le
  have e2 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have e : Real.exp t * (Real.exp 1 * besselK0 1 * Real.exp (-t))
      = Real.exp 1 * besselK0 1 * (Real.exp (-t) * Real.exp t) := by ring
  rw [e, e2, mul_one (Real.exp 1 * besselK0 1)] at h1
  exact h1

/-- For `t ≥ 1`: `I₀(t)^a K₀(t)^{a+d+2} ≤ κ^{a+d+2} e^{-2t}`. -/
theorem besselIK_le_large (a d : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    besselI0 t ^ a * besselK0 t ^ (a + d + 2)
      ≤ (Real.exp 1 * besselK0 1) ^ (a + d + 2) * Real.exp (-(2 * t)) := by
  have hK0 : 0 ≤ besselK0 t := besselK0_nonneg t
  have hI0 : 0 ≤ besselI0 t := (besselI0_pos t).le
  have hκ : 0 ≤ Real.exp 1 * besselK0 1 :=
    mul_nonneg (Real.exp_pos 1).le (besselK0_nonneg 1)
  have hIK := besselI0_mul_besselK0_le_kappa ht
  have hK := besselK0_le_kappa_exp ht
  have hE1 : Real.exp (-t) ≤ 1 := exp_le_one_of_nonpos (by linarith)
  have hKκ : besselK0 t ≤ Real.exp 1 * besselK0 1 := by
    have h := mul_le_mul_of_nonneg_left hE1 hκ
    rw [mul_one (Real.exp 1 * besselK0 1)] at h
    exact le_trans hK h
  have h1 : (besselI0 t * besselK0 t) ^ a ≤ (Real.exp 1 * besselK0 1) ^ a :=
    pow_le_pow_left₀ (mul_nonneg hI0 hK0) hIK a
  have h2 : besselK0 t ^ d ≤ (Real.exp 1 * besselK0 1) ^ d := pow_le_pow_left₀ hK0 hKκ d
  have h3 : besselK0 t ^ 2 ≤ (Real.exp 1 * besselK0 1 * Real.exp (-t)) ^ 2 :=
    pow_le_pow_left₀ hK0 hK 2
  have e3 : (Real.exp 1 * besselK0 1 * Real.exp (-t)) ^ 2
      = (Real.exp 1 * besselK0 1) ^ 2 * Real.exp (-(2 * t)) := by
    have e : Real.exp (-(2 * t)) = Real.exp (-t) * Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    ring
  rw [e3] at h3
  have h12 : (besselI0 t * besselK0 t) ^ a * besselK0 t ^ d
      ≤ (Real.exp 1 * besselK0 1) ^ a * (Real.exp 1 * besselK0 1) ^ d :=
    mul_le_mul h1 h2 (pow_nonneg hK0 d) (pow_nonneg hκ a)
  have h123 : (besselI0 t * besselK0 t) ^ a * besselK0 t ^ d * besselK0 t ^ 2
      ≤ (Real.exp 1 * besselK0 1) ^ a * (Real.exp 1 * besselK0 1) ^ d
        * ((Real.exp 1 * besselK0 1) ^ 2 * Real.exp (-(2 * t))) :=
    mul_le_mul h12 h3 (pow_nonneg hK0 2) (mul_nonneg (pow_nonneg hκ a) (pow_nonneg hκ d))
  have eL : besselI0 t ^ a * besselK0 t ^ (a + d + 2)
      = (besselI0 t * besselK0 t) ^ a * besselK0 t ^ d * besselK0 t ^ 2 := by
    rw [pow_add (besselK0 t) (a + d) 2, pow_add (besselK0 t) a d,
      mul_pow (besselI0 t) (besselK0 t) a]
    ring
  have eR : (Real.exp 1 * besselK0 1) ^ (a + d + 2) * Real.exp (-(2 * t))
      = (Real.exp 1 * besselK0 1) ^ a * (Real.exp 1 * besselK0 1) ^ d
        * ((Real.exp 1 * besselK0 1) ^ 2 * Real.exp (-(2 * t))) := by
    rw [pow_add (Real.exp 1 * besselK0 1) (a + d) 2, pow_add (Real.exp 1 * besselK0 1) a d]
    ring
  rw [eL, eR]
  exact h123

/-- `exp(-2e^u) ≤ (27/8) e^{-3u}`. -/
theorem exp_neg_two_mul_exp_le (u : ℝ) :
    Real.exp (-(2 * Real.exp u)) ≤ 27 / 8 * Real.exp (-3 * u) := by
  have hE : 0 < Real.exp u := Real.exp_pos u
  have h := exp_neg_le_cube (mul_pos two_pos hE)
  have hprod : Real.exp (-3 * u) * (Real.exp u * Real.exp u * Real.exp u) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    have e : -3 * u + (u + u + u) = 0 := by ring
    rw [e, Real.exp_zero]
  have hne : (2 * Real.exp u) ^ 3 ≠ 0 := pow_ne_zero 3 (mul_pos two_pos hE).ne'
  have e : 27 / (2 * Real.exp u) ^ 3 = 27 / 8 * Real.exp (-3 * u) := by
    rw [div_eq_iff hne]
    linear_combination (-27 : ℝ) * hprod
  rw [e] at h
  exact h

/-- `e^{-3u} = (e^{-u})³`. -/
theorem exp_neg_three_mul (u : ℝ) :
    Real.exp (-3 * u) = Real.exp (-u) * Real.exp (-u) * Real.exp (-u) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- `I₀(e^u)^a K₀(e^u)^{a+d+2} ≤ (27/8) κ^{a+d+2} e^{-3u}` for `u > 0`. -/
theorem besselIK_exp_abs_le_large (a d : ℕ) {u : ℝ} (hu : 0 < u) :
    |besselI0 (Real.exp u) ^ a * besselK0 (Real.exp u) ^ (a + d + 2)|
      ≤ 27 / 8 * (Real.exp 1 * besselK0 1) ^ (a + d + 2) * Real.exp (-3 * u) := by
  have h1 := besselIK_le_large a d (one_le_exp_of_pos hu)
  have h2 := exp_neg_two_mul_exp_le u
  have hκ : 0 ≤ (Real.exp 1 * besselK0 1) ^ (a + d + 2) :=
    pow_nonneg (mul_nonneg (Real.exp_pos 1).le (besselK0_nonneg 1)) (a + d + 2)
  have h3 := mul_le_mul_of_nonneg_left h2 hκ
  have e : (Real.exp 1 * besselK0 1) ^ (a + d + 2) * (27 / 8 * Real.exp (-3 * u))
      = 27 / 8 * (Real.exp 1 * besselK0 1) ^ (a + d + 2) * Real.exp (-3 * u) := by ring
  rw [e] at h3
  have hnn : 0 ≤ besselI0 (Real.exp u) ^ a * besselK0 (Real.exp u) ^ (a + d + 2) :=
    mul_nonneg (pow_nonneg (besselI0_pos _).le a) (pow_nonneg (besselK0_nonneg _) (a + d + 2))
  rw [abs_of_nonneg hnn]
  exact le_trans h1 h3

/-- `(I₀ K₀)³(e^u) ≤ e^{-3u}`. -/
theorem besselIK_cube_exp_abs_le_large (u : ℝ) :
    |besselI0 (Real.exp u) ^ 3 * besselK0 (Real.exp u) ^ 3| ≤ 1 * Real.exp (-3 * u) := by
  have hE : 0 < Real.exp u := Real.exp_pos u
  have h := besselI0_mul_besselK0_le hE
  have hnn : 0 ≤ besselI0 (Real.exp u) * besselK0 (Real.exp u) :=
    mul_nonneg (besselI0_pos _).le (besselK0_nonneg _)
  have h3 : (besselI0 (Real.exp u) * besselK0 (Real.exp u)) ^ 3 ≤ (1 / Real.exp u) ^ 3 :=
    pow_le_pow_left₀ hnn h 3
  have e1 : (besselI0 (Real.exp u) * besselK0 (Real.exp u)) ^ 3
      = besselI0 (Real.exp u) ^ 3 * besselK0 (Real.exp u) ^ 3 := by ring
  have e2 : (1 / Real.exp u) ^ 3 = 1 * Real.exp (-3 * u) := by
    rw [exp_neg_three_mul, Real.exp_neg]
    ring
  rw [e1, e2] at h3
  have hnn3 : 0 ≤ besselI0 (Real.exp u) ^ 3 * besselK0 (Real.exp u) ^ 3 :=
    mul_nonneg (pow_nonneg (besselI0_pos _).le 3) (pow_nonneg (besselK0_nonneg _) 3)
  rw [abs_of_nonneg hnn3]
  exact h3

/-! ## The integrand of `R₆,₂` and the sixth power of `J₀` -/

theorem besselP_exp_abs_le_small {u : ℝ} (hu : u ≤ 0) :
    |besselI0 (Real.exp u) ^ 2 * besselI1 (Real.exp u) * besselK0 (Real.exp u) ^ 5|
      ≤ Real.exp 1 ^ 2 * Bser 1 * 9375 * (2 - u) ^ 0 := by
  have ht : 0 < Real.exp u := Real.exp_pos u
  have h := R62_integrand_le_of_le_one ht (exp_le_one_of_nonpos hu)
  rw [abs_of_nonneg (R62_integrand_pos ht).le, pow_zero (2 - u),
    mul_one (Real.exp 1 ^ 2 * Bser 1 * 9375)]
  exact h

theorem besselP_exp_abs_le_large {u : ℝ} (hu : 0 < u) :
    |besselI0 (Real.exp u) ^ 2 * besselI1 (Real.exp u) * besselK0 (Real.exp u) ^ 5|
      ≤ 27 / 8 * (Real.exp 1 * besselK0 1) ^ 4 * Real.exp (-3 * u) := by
  have ht : 0 < Real.exp u := Real.exp_pos u
  have h1 := R62_integrand_le (one_le_exp_of_pos hu)
  have h2 := exp_neg_two_mul_exp_le u
  have hκ : 0 ≤ (Real.exp 1 * besselK0 1) ^ 4 :=
    pow_nonneg (mul_nonneg (Real.exp_pos 1).le (besselK0_nonneg 1)) 4
  have h3 := mul_le_mul_of_nonneg_left h2 hκ
  have e : (Real.exp 1 * besselK0 1) ^ 4 * (27 / 8 * Real.exp (-3 * u))
      = 27 / 8 * (Real.exp 1 * besselK0 1) ^ 4 * Real.exp (-3 * u) := by ring
  rw [e] at h3
  rw [abs_of_nonneg (R62_integrand_pos ht).le]
  exact le_trans h1 h3

theorem besselJ0_pow_six_exp_abs_le_small (u : ℝ) :
    |besselJ0 (Real.exp u) ^ 6| ≤ 1 * (2 - u) ^ 0 := by
  have h := abs_besselJ0_le_one (Real.exp_pos u).le
  rw [abs_pow, pow_zero (2 - u), mul_one (1 : ℝ)]
  exact pow_le_one₀ (abs_nonneg _) h

theorem besselJ0_pow_six_exp_abs_le_large {u : ℝ} (hu : 0 < u) :
    |besselJ0 (Real.exp u) ^ 6| ≤ besselJE 1 ^ 3 * Real.exp (-3 * u) := by
  have h := besselJ0_sq_le (one_le_exp_of_pos hu)
  have h3 : (besselJ0 (Real.exp u) * besselJ0 (Real.exp u)) ^ 3
      ≤ (besselJE 1 / Real.exp u) ^ 3 :=
    pow_le_pow_left₀ (mul_self_nonneg _) h 3
  have e1 : besselJ0 (Real.exp u) ^ 6
      = (besselJ0 (Real.exp u) * besselJ0 (Real.exp u)) ^ 3 := by ring
  have e2 : (besselJE 1 / Real.exp u) ^ 3 = besselJE 1 ^ 3 * Real.exp (-3 * u) := by
    rw [exp_neg_three_mul, Real.exp_neg]
    ring
  rw [e2] at h3
  rw [e1, abs_of_nonneg (pow_nonneg (mul_self_nonneg (besselJ0 (Real.exp u))) 3)]
  exact h3

/-! ## Continuity in `u` -/

theorem continuous_besselK0_exp : Continuous (fun u : ℝ => besselK0 (Real.exp u)) :=
  continuousOn_besselK0.comp_continuous Real.continuous_exp (fun u => Real.exp_pos u)

theorem continuous_besselI0_exp : Continuous (fun u : ℝ => besselI0 (Real.exp u)) :=
  continuous_besselI0.comp Real.continuous_exp

theorem continuous_besselIK_exp (a b : ℕ) :
    Continuous (fun u : ℝ => besselI0 (Real.exp u) ^ a * besselK0 (Real.exp u) ^ b) :=
  (continuous_besselI0_exp.pow a).mul (continuous_besselK0_exp.pow b)

theorem continuous_besselP_exp :
    Continuous (fun u : ℝ =>
      besselI0 (Real.exp u) ^ 2 * besselI1 (Real.exp u) * besselK0 (Real.exp u) ^ 5) :=
  ((continuous_besselI0_exp.pow 2).mul (continuous_besselI1.comp Real.continuous_exp)).mul
    (continuous_besselK0_exp.pow 5)

theorem continuous_besselJ0_pow_six_exp :
    Continuous (fun u : ℝ => besselJ0 (Real.exp u) ^ 6) :=
  (continuous_besselJ0.comp Real.continuous_exp).pow 6

/-! ## Integrability -/

/-- `I₀(e^u)^a K₀(e^u)^{a+d+2} e^{σu}` is integrable on `ℝ` for `0 < σ < 3`. -/
theorem integrable_besselIK_exp (a d : ℕ) {σ : ℝ} (hσ : 0 < σ) (hσ3 : σ < 3) :
    Integrable (fun u : ℝ =>
      besselI0 (Real.exp u) ^ a * besselK0 (Real.exp u) ^ (a + d + 2) * Real.exp (σ * u)) :=
  integrable_mul_exp_of_bounds
    (g := fun u : ℝ => besselI0 (Real.exp u) ^ a * besselK0 (Real.exp u) ^ (a + d + 2))
    (A := Real.exp 1 ^ a) (B := 27 / 8 * (Real.exp 1 * besselK0 1) ^ (a + d + 2)) (α := 3)
    (b := a + d + 2)
    (continuous_besselIK_exp a (a + d + 2)).aestronglyMeasurable
    (pow_nonneg (Real.exp_pos 1).le a)
    (fun _ hu => besselIK_exp_abs_le_small a (a + d + 2) hu)
    (fun _ hu => besselIK_exp_abs_le_large a d hu) hσ hσ3

/-- `I₀(e^u)³ K₀(e^u)³ e^{σu}` is integrable on `ℝ` for `0 < σ < 3`. -/
theorem integrable_besselIK_cube_exp {σ : ℝ} (hσ : 0 < σ) (hσ3 : σ < 3) :
    Integrable (fun u : ℝ =>
      besselI0 (Real.exp u) ^ 3 * besselK0 (Real.exp u) ^ 3 * Real.exp (σ * u)) :=
  integrable_mul_exp_of_bounds
    (g := fun u : ℝ => besselI0 (Real.exp u) ^ 3 * besselK0 (Real.exp u) ^ 3)
    (A := Real.exp 1 ^ 3) (B := 1) (α := 3) (b := 3)
    (continuous_besselIK_exp 3 3).aestronglyMeasurable
    (pow_nonneg (Real.exp_pos 1).le 3)
    (fun _ hu => besselIK_exp_abs_le_small 3 3 hu)
    (fun u _ => besselIK_cube_exp_abs_le_large u) hσ hσ3

/-- `(I₀² I₁ K₀⁵)(e^u) e^{σu}` is integrable on `ℝ` for `0 < σ < 3`. -/
theorem integrable_besselP_exp {σ : ℝ} (hσ : 0 < σ) (hσ3 : σ < 3) :
    Integrable (fun u : ℝ =>
      besselI0 (Real.exp u) ^ 2 * besselI1 (Real.exp u) * besselK0 (Real.exp u) ^ 5
        * Real.exp (σ * u)) :=
  integrable_mul_exp_of_bounds
    (g := fun u : ℝ =>
      besselI0 (Real.exp u) ^ 2 * besselI1 (Real.exp u) * besselK0 (Real.exp u) ^ 5)
    (A := Real.exp 1 ^ 2 * Bser 1 * 9375) (B := 27 / 8 * (Real.exp 1 * besselK0 1) ^ 4) (α := 3)
    (b := 0)
    continuous_besselP_exp.aestronglyMeasurable
    (mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos 1).le 2) (Bser_nonneg zero_le_one))
      (by norm_num))
    (fun _ hu => besselP_exp_abs_le_small hu)
    (fun _ hu => besselP_exp_abs_le_large hu) hσ hσ3

/-- `J₀(e^u)⁶ e^{σu}` is integrable on `ℝ` for `0 < σ < 3`. -/
theorem integrable_besselJ0_pow_six_exp {σ : ℝ} (hσ : 0 < σ) (hσ3 : σ < 3) :
    Integrable (fun u : ℝ => besselJ0 (Real.exp u) ^ 6 * Real.exp (σ * u)) :=
  integrable_mul_exp_of_bounds
    (g := fun u : ℝ => besselJ0 (Real.exp u) ^ 6)
    (A := 1) (B := besselJE 1 ^ 3) (α := 3) (b := 0)
    continuous_besselJ0_pow_six_exp.aestronglyMeasurable
    zero_le_one
    (fun u _ => besselJ0_pow_six_exp_abs_le_small u)
    (fun _ hu => besselJ0_pow_six_exp_abs_le_large hu) hσ hσ3

end Tower.RV6
