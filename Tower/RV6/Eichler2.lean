import Mathlib
import Tower.RV6.Dirichlet
import Tower.RV6.Fricke6
import Tower.RV6.Eichler
import Tower.RV6.Bilin

/-!
# The Eisenstein integral `𝒜₁` in its two forms, and the moments of the Eichler integral

`A1E y = ∫_y^∞ t g₄(it) dt` for the weight-four combination `g4E` of `Fricke6.lean`.

* `g4E_eq_qa`, `ghatE_eq_qa`: `g₄` and its Fricke image as combinations of `S₃ = qa (sig 3)`.
* `A1E_direct`: `𝒜₁(y) = 32 (T(y) - T(2y)/4 - T(3y) + T(6y)/4)`.
* `A1E_fricke`: `𝒜₁(y) = 1/(18y²) - 8 (T(u) - 4T(2u) - T(3u) + 4T(6u))`, `u = 1/(6y)`; this is the
  inversion formula `Tint_inv` at `y, 2y, 3y, 6y`, and it is where the paper's `K₁ = 0` is used.
* `integral_sq_mul_Tint`: `∫₀^∞ x² T(x) dx = ζ(5)/(24π³)`.
* `integral_Tint_fricke`: `∫₀^∞ y⁻⁴ T(d/(6y)) dy = (216/d³) ζ(5)/(24π³)`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## `g₄` and its Fricke image as `q`-series -/

/-- `g₄(it) = 32 (S₃(t) - S₃(2t) - 9 S₃(3t) + 9 S₃(6t))`. -/
theorem g4E_eq_qa {t : ℝ} (ht : 0 < t) :
    g4E t = 32 * (qa (sig 3) t - qa (sig 3) (2 * t) - 9 * qa (sig 3) (3 * t)
      + 9 * qa (sig 3) (6 * t)) := by
  unfold g4E
  rw [E4im_eq_qa ht, E4im_eq_qa (by positivity : (0 : ℝ) < 2 * t),
    E4im_eq_qa (by positivity : (0 : ℝ) < 3 * t), E4im_eq_qa (by positivity : (0 : ℝ) < 6 * t)]
  ring

/-- `ĝ(ix) = 32 (9 S₃(x) - 144 S₃(2x) - 81 S₃(3x) + 1296 S₃(6x))`: no constant term. -/
theorem ghatE_eq_qa {x : ℝ} (hx : 0 < x) :
    ghatE x = 32 * (9 * qa (sig 3) x - 144 * qa (sig 3) (2 * x) - 81 * qa (sig 3) (3 * x)
      + 1296 * qa (sig 3) (6 * x)) := by
  unfold ghatE
  rw [E4im_eq_qa hx, E4im_eq_qa (by positivity : (0 : ℝ) < 2 * x),
    E4im_eq_qa (by positivity : (0 : ℝ) < 3 * x), E4im_eq_qa (by positivity : (0 : ℝ) < 6 * x)]
  ring

/-! ## Scaling of the Eichler integral -/

/-- `∫_y^∞ t S₃(d t) dt = T(d y)/d²`. -/
theorem integral_Ioi_mul_qa_scale {d : ℝ} (hd : 0 < d) (y : ℝ) :
    ∫ t in Set.Ioi y, t * qa (sig 3) (d * t) = Tint (d * y) / d ^ 2 := by
  have h : ∫ t in Set.Ioi y, (d * t) * qa (sig 3) (d * t)
      = d⁻¹ * ∫ t in Set.Ioi (d * y), t * qa (sig 3) t := by
    have h0 := integral_comp_mul_left_Ioi (fun u : ℝ => u * qa (sig 3) u) y hd
    rw [smul_eq_mul] at h0
    exact h0
  have hc : ∫ t in Set.Ioi y, t * qa (sig 3) (d * t)
      = ∫ t in Set.Ioi y, d⁻¹ * ((d * t) * qa (sig 3) (d * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    show t * qa (sig 3) (d * t) = d⁻¹ * ((d * t) * qa (sig 3) (d * t))
    have hdd : d * d⁻¹ = 1 := mul_inv_cancel₀ hd.ne'
    linear_combination (-(t * qa (sig 3) (d * t))) * hdd
  rw [hc, integral_const_mul, h]
  unfold Tint
  ring

theorem integrableOn_mul_qa_scale {d : ℝ} (hd : 0 < d) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => t * qa (sig 3) (d * t)) (Set.Ioi y) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_Ioi_mul_qa_scale hd y]
  exact (div_pos (Tint_pos (mul_pos hd hy)) (pow_pos hd 2)).ne'

/-! ## The two forms of `𝒜₁` -/

/-- `𝒜₁(y) = ∫_y^∞ t g₄(it) dt` for the Eisenstein combination `g4E`. -/
noncomputable def A1E (y : ℝ) : ℝ := ∫ t in Set.Ioi y, t * g4E t

/-- The direct form: `𝒜₁(y) = 32 (T(y) - T(2y)/4 - T(3y) + T(6y)/4)`. -/
theorem A1E_direct {y : ℝ} (hy : 0 < y) :
    A1E y = 32 * (Tint y - Tint (2 * y) / 4 - Tint (3 * y) + Tint (6 * y) / 4) := by
  have hcongr : ∫ t in Set.Ioi y, t * g4E t
      = ∫ t in Set.Ioi y, (32 * (t * qa (sig 3) t) + (-32) * (t * qa (sig 3) (2 * t))
          + (-288) * (t * qa (sig 3) (3 * t)) + 288 * (t * qa (sig 3) (6 * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := lt_trans hy ht
    show t * g4E t = 32 * (t * qa (sig 3) t) + (-32) * (t * qa (sig 3) (2 * t))
          + (-288) * (t * qa (sig 3) (3 * t)) + 288 * (t * qa (sig 3) (6 * t))
    rw [g4E_eq_qa ht0]
    ring
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h6 : (0 : ℝ) < 6 := by norm_num
  have hlin : ∫ t in Set.Ioi y, (32 * (t * qa (sig 3) t) + (-32) * (t * qa (sig 3) (2 * t))
          + (-288) * (t * qa (sig 3) (3 * t)) + 288 * (t * qa (sig 3) (6 * t)))
      = 32 * (∫ t in Set.Ioi y, t * qa (sig 3) t)
        + (-32) * (∫ t in Set.Ioi y, t * qa (sig 3) (2 * t))
        + (-288) * (∫ t in Set.Ioi y, t * qa (sig 3) (3 * t))
        + 288 * (∫ t in Set.Ioi y, t * qa (sig 3) (6 * t)) :=
    integral_lin4 (integrableOn_Tint hy) (integrableOn_mul_qa_scale h2 hy)
      (integrableOn_mul_qa_scale h3 hy) (integrableOn_mul_qa_scale h6 hy) 32 (-32) (-288) 288
  have e1 : ∫ t in Set.Ioi y, t * qa (sig 3) t = Tint y := rfl
  unfold A1E
  rw [hcongr, hlin, e1, integral_Ioi_mul_qa_scale h2 y, integral_Ioi_mul_qa_scale h3 y,
    integral_Ioi_mul_qa_scale h6 y]
  ring

/-- The Fricke form: `𝒜₁(y) = 1/(18y²) - 8 (T(u) - 4T(2u) - T(3u) + 4T(6u))`, `u = 1/(6y)`. -/
theorem A1E_fricke {y : ℝ} (hy : 0 < y) :
    A1E y = 1 / (18 * y ^ 2)
      - 8 * (Tint (1 / (6 * y)) - 4 * Tint (2 / (6 * y)) - Tint (3 / (6 * y))
          + 4 * Tint (6 / (6 * y))) := by
  have hdir := A1E_direct hy
  have i1 := Tint_inv hy
  have i2 := Tint_inv (by positivity : (0 : ℝ) < 2 * y)
  have i3 := Tint_inv (by positivity : (0 : ℝ) < 3 * y)
  have i6 := Tint_inv (by positivity : (0 : ℝ) < 6 * y)
  have a1 : 6 / (6 * y) = 1 / y := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have a2 : 3 / (6 * y) = 1 / (2 * y) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have a3 : 2 / (6 * y) = 1 / (3 * y) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [a1, a2, a3]
  linear_combination hdir + 32 * i1 - 8 * i2 - 32 * i3 + 8 * i6

/-! ## Moments -/

theorem zeta5_pos : 0 < zeta5 := by
  rw [← tsum_inv_pow_five_shift]
  have hs := summable_shift_one_div_pow (p := 5) (by norm_num)
  exact hs.tsum_pos (fun n => by positivity) 0 (by norm_num)

theorem summable_sig3_div_pow5 :
    Summable fun n : ℕ => sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 := by
  by_contra h
  have h0 := tsum_eq_zero_of_not_summable h
  rw [tsum_sig3_div_pow5] at h0
  have hp : 0 < π ^ 2 / 6 * zeta5 := mul_pos (by positivity) zeta5_pos
  exact hp.ne' h0

/-- `∫₀^∞ U₁(x) x³ dx = ζ(5)/(16π²)`, `U₁ = ∑ σ₃(n)/n qⁿ`. -/
theorem integral_U1_cube :
    ∫ x in Set.Ioi (0 : ℝ), qa (fun n => sig 3 n / (n : ℝ)) x * x ^ 3
      = zeta5 / (16 * π ^ 2) := by
  have hs : Summable fun n : ℕ =>
      |sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ)| / ((n + 1 : ℕ) : ℝ) ^ (3 + 1) := by
    refine summable_sig3_div_pow5.congr (fun n => ?_)
    show sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5
      = |sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ)| / ((n + 1 : ℕ) : ℝ) ^ (3 + 1)
    rw [abs_of_nonneg (sig3_div_nonneg (n + 1))]
    ring
  have h := integral_qa (fun n : ℕ => sig 3 n / (n : ℝ)) (by simp [sig_zero]) 3 hs
    (fun y hy => summable_qa bound_sig3_div hy)
  have hsum : ∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (3 + 1)
      = π ^ 2 / 6 * zeta5 := by
    rw [← tsum_sig3_div_pow5]
    refine tsum_congr (fun n => ?_)
    ring
  have hval : ∫ x in Set.Ioi (0 : ℝ), qa (fun n => sig 3 n / (n : ℝ)) x * x ^ 3
      = ((Nat.factorial 3 : ℕ) : ℝ) / (2 * π) ^ (3 + 1) * (π ^ 2 / 6 * zeta5) := by
    rw [← hsum]
    exact h
  have ef : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have hp : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  rw [hval, ef]
  linear_combination (zeta5 / 16 * π⁻¹ ^ 2 * (π * π⁻¹ + 1)) * hp

/-- `∫₀^∞ U₂(x) x² dx = ζ(5)/(24π)`, `U₂ = ∑ σ₃(n)/n² qⁿ`. -/
theorem integral_U2_sq :
    ∫ x in Set.Ioi (0 : ℝ), qa (fun n => sig 3 n / (n : ℝ) ^ 2) x * x ^ 2
      = zeta5 / (24 * π) := by
  have hs : Summable fun n : ℕ =>
      |sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2| / ((n + 1 : ℕ) : ℝ) ^ (2 + 1) := by
    refine summable_sig3_div_pow5.congr (fun n => ?_)
    show sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5
      = |sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2| / ((n + 1 : ℕ) : ℝ) ^ (2 + 1)
    rw [abs_of_nonneg (sig3_div_sq_nonneg (n + 1))]
    ring
  have h := integral_qa (fun n : ℕ => sig 3 n / (n : ℝ) ^ 2) (by simp [sig_zero]) 2 hs
    (fun y hy => summable_qa bound_sig3_div_sq hy)
  have hsum : ∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ (2 + 1)
      = π ^ 2 / 6 * zeta5 := by
    rw [← tsum_sig3_div_pow5]
    refine tsum_congr (fun n => ?_)
    ring
  have hval : ∫ x in Set.Ioi (0 : ℝ), qa (fun n => sig 3 n / (n : ℝ) ^ 2) x * x ^ 2
      = ((Nat.factorial 2 : ℕ) : ℝ) / (2 * π) ^ (2 + 1) * (π ^ 2 / 6 * zeta5) := by
    rw [← hsum]
    exact h
  have ef : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have hp : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  rw [hval, ef]
  linear_combination (zeta5 / 24 * π⁻¹ * (π * π⁻¹ + 1)) * hp

/-- `∫₀^∞ x² T(x) dx = ζ(5)/(24π³)`. -/
theorem integral_sq_mul_Tint :
    ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Tint x = zeta5 / (24 * π ^ 3) := by
  have hz := zeta5_pos
  have i1 : Integrable (fun x : ℝ => qa (fun n => sig 3 n / (n : ℝ)) x * x ^ 3)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_U1_cube]
    exact (div_pos hz (by positivity)).ne'
  have i2 : Integrable (fun x : ℝ => qa (fun n => sig 3 n / (n : ℝ) ^ 2) x * x ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_U2_sq]
    exact (div_pos hz (by positivity)).ne'
  have hcongr : ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Tint x
      = ∫ x in Set.Ioi (0 : ℝ), (1 / (2 * π) * (qa (fun n => sig 3 n / (n : ℝ)) x * x ^ 3)
          + 1 / (4 * π ^ 2) * (qa (fun n => sig 3 n / (n : ℝ) ^ 2) x * x ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    show x ^ 2 * Tint x = 1 / (2 * π) * (qa (fun n => sig 3 n / (n : ℝ)) x * x ^ 3)
          + 1 / (4 * π ^ 2) * (qa (fun n => sig 3 n / (n : ℝ) ^ 2) x * x ^ 2)
    rw [Tint_eq hx0]
    ring
  have e : ∫ x in Set.Ioi (0 : ℝ), (1 / (2 * π) * (qa (fun n => sig 3 n / (n : ℝ)) x * x ^ 3)
          + 1 / (4 * π ^ 2) * (qa (fun n => sig 3 n / (n : ℝ) ^ 2) x * x ^ 2))
      = (∫ x in Set.Ioi (0 : ℝ), 1 / (2 * π) * (qa (fun n => sig 3 n / (n : ℝ)) x * x ^ 3))
        + ∫ x in Set.Ioi (0 : ℝ), 1 / (4 * π ^ 2)
            * (qa (fun n => sig 3 n / (n : ℝ) ^ 2) x * x ^ 2) :=
    integral_add (i1.const_mul _) (i2.const_mul _)
  rw [hcongr, e, integral_const_mul, integral_const_mul, integral_U1_cube, integral_U2_sq]
  ring

/-! ## Inversion on the half-line -/

/-- `∫₀^∞ g(1/x) x⁻² dx = ∫₀^∞ g(y) dy`. -/
theorem integral_Ioi_inv_subst (g : ℝ → ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), g x⁻¹ * (x ^ 2)⁻¹ = ∫ y in Set.Ioi (0 : ℝ), g y := by
  have h := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  have e1 : x ^ (-1 : ℝ) = x⁻¹ := Real.rpow_neg_one x
  have e2 : x ^ ((-1 : ℝ) - 1) = (x ^ 2)⁻¹ := by
    have e : ((-1 : ℝ) - 1) = -(2 : ℝ) := by norm_num
    rw [e, Real.rpow_neg hx0.le, Real.rpow_two]
  have ha : |(-1 : ℝ)| = 1 := by norm_num
  simp only [smul_eq_mul]
  rw [e1, e2, ha]
  ring

/-- `∫₀^∞ y⁻⁴ T(d/(6y)) dy = (216/d³) ζ(5)/(24π³)`. -/
theorem integral_Tint_fricke {d : ℝ} (hd : 0 < d) :
    ∫ y in Set.Ioi (0 : ℝ), Tint (d / (6 * y)) / y ^ 4
      = 216 / d ^ 3 * (zeta5 / (24 * π ^ 3)) := by
  have hd6 : (0 : ℝ) < d / 6 := by positivity
  have hA : ∫ y in Set.Ioi (0 : ℝ), Tint (d / (6 * y)) / y ^ 4
      = ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Tint (d / 6 * x) := by
    have h1 : ∫ x in Set.Ioi (0 : ℝ), (x⁻¹ ^ 2 * Tint (d / 6 * x⁻¹)) * (x ^ 2)⁻¹
        = ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Tint (d / 6 * x) :=
      integral_Ioi_inv_subst (fun x : ℝ => x ^ 2 * Tint (d / 6 * x))
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    show Tint (d / (6 * y)) / y ^ 4 = (y⁻¹ ^ 2 * Tint (d / 6 * y⁻¹)) * (y ^ 2)⁻¹
    have ea : d / 6 * y⁻¹ = d / (6 * y) := by ring
    rw [ea]
    ring
  have hB : ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Tint (d / 6 * x)
      = (d / 6)⁻¹ ^ 3 * ∫ u in Set.Ioi (0 : ℝ), u ^ 2 * Tint u := by
    have h2 : ∫ x in Set.Ioi (0 : ℝ), (d / 6 * x) ^ 2 * Tint (d / 6 * x)
        = (d / 6)⁻¹ * ∫ u in Set.Ioi (0 : ℝ), u ^ 2 * Tint u := by
      have h0 := integral_comp_mul_left_Ioi (fun u : ℝ => u ^ 2 * Tint u) (0 : ℝ) hd6
      rw [mul_zero, smul_eq_mul] at h0
      exact h0
    have hc : ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Tint (d / 6 * x)
        = ∫ x in Set.Ioi (0 : ℝ), (d / 6)⁻¹ ^ 2 * ((d / 6 * x) ^ 2 * Tint (d / 6 * x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      show x ^ 2 * Tint (d / 6 * x) = (d / 6)⁻¹ ^ 2 * ((d / 6 * x) ^ 2 * Tint (d / 6 * x))
      have hcc : d / 6 * (d / 6)⁻¹ = 1 := mul_inv_cancel₀ hd6.ne'
      linear_combination (-(x ^ 2 * Tint (d / 6 * x)) * (d / 6 * (d / 6)⁻¹ + 1)) * hcc
    rw [hc, integral_const_mul, h2]
    ring
  rw [hA, hB, integral_sq_mul_Tint]
  ring

theorem integrable_Tint_fricke {d : ℝ} (hd : 0 < d) :
    Integrable (fun y : ℝ => Tint (d / (6 * y)) / y ^ 4)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_Tint_fricke hd]
  have h1 : 0 < 216 / d ^ 3 * (zeta5 / (24 * π ^ 3)) :=
    mul_pos (by positivity) (div_pos zeta5_pos (by positivity))
  exact h1.ne'

end Tower.RV6
