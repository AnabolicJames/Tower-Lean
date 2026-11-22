import Mathlib
import Tower.RV6.Defs
import Tower.RV6.Fricke6
import Tower.RV6.Eichler2
import Tower.RV6.QCalc
import Tower.RV6.RungC1

/-!
# The inversion formula of `D E₂`, and the substitution `y ↦ 1/(6y)` in an integral

* `DEq_inv`: `D𝔈(i/y) = y³/(24π) - (y³/π) 𝔈(iy) + y⁴ D𝔈(iy) - y²/(8π²)` for `y > 0`, where
  `𝔈 = ∑ σ₁(n) qⁿ` and `D = q d/dq`.  It is the derivative of `E2im_inv`: the two sides of
  `24 𝔈(i/t) + 24 t² 𝔈(it) = t² - 6t/π + 1` are differentiated at `t = y`.
* `DGcal_fricke`: `(D𝔊)(i/(6y)) = (13/(3π)) y³ - (4/π) y³ 𝔉(iy) + 4 y⁴ (D𝔉)(iy)`.
* `fricke_subst`: `∫₀^∞ g(1/(6y)) y⁻² dy = 6 ∫₀^∞ g(x) dx`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-- The inversion formula of `D E₂` on the imaginary axis. -/
theorem DEq_inv {y : ℝ} (hy : 0 < y) :
    qa (fun n => (n : ℝ) * sig 1 n) (1 / y)
      = y ^ 3 / (24 * π) - y ^ 3 / π * qa (sig 1) y
        + y ^ 4 * qa (fun n => (n : ℝ) * sig 1 n) y - y ^ 2 / (8 * π ^ 2) := by
  have hEq : ∀ t : ℝ, 0 < t →
      24 * qa (sig 1) t⁻¹ + 24 * (t * t * qa (sig 1) t) = t * t - 6 / π * t + 1 := by
    intro t ht
    have h := E2im_inv ht
    rw [E2im_eq_qa (by positivity : (0 : ℝ) < 1 / t), E2im_eq_qa ht, one_div] at h
    linear_combination (-1 : ℝ) * h
  have hy0 : y ≠ 0 := hy.ne'
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-(y ^ 2)⁻¹) y := hasDerivAt_inv hy0
  have hq' : HasDerivAt (qa (sig 1)) (-(2 * π) * qa (fun n => (n : ℝ) * sig 1 n) y⁻¹) y⁻¹ :=
    hasDerivAt_qa (sig_abs_le 1) (inv_pos.mpr hy)
  have hA0 := hq'.comp y hinv
  have hA : HasDerivAt (fun t : ℝ => qa (sig 1) t⁻¹)
      (-(2 * π) * qa (fun n => (n : ℝ) * sig 1 n) y⁻¹ * (-(y ^ 2)⁻¹)) y := hA0
  have hq : HasDerivAt (qa (sig 1)) (-(2 * π) * qa (fun n => (n : ℝ) * sig 1 n) y) y :=
    hasDerivAt_qa (sig_abs_le 1) hy
  have hsq0 := (hasDerivAt_id' y).mul (hasDerivAt_id' y)
  have hsq : HasDerivAt (fun t : ℝ => t * t) (1 * y + y * 1) y := hsq0
  have hprod0 := hsq.mul hq
  have hprod : HasDerivAt (fun t : ℝ => t * t * qa (sig 1) t)
      ((1 * y + y * 1) * qa (sig 1) y
        + y * y * (-(2 * π) * qa (fun n => (n : ℝ) * sig 1 n) y)) y := hprod0
  have hc0 := (hA.const_mul 24).add (hprod.const_mul 24)
  have hc : HasDerivAt (fun t : ℝ => 24 * qa (sig 1) t⁻¹ + 24 * (t * t * qa (sig 1) t))
      (24 * (-(2 * π) * qa (fun n => (n : ℝ) * sig 1 n) y⁻¹ * (-(y ^ 2)⁻¹))
        + 24 * ((1 * y + y * 1) * qa (sig 1) y
          + y * y * (-(2 * π) * qa (fun n => (n : ℝ) * sig 1 n) y))) y := hc0
  have hd0 := (hsq.sub ((hasDerivAt_id' y).const_mul (6 / π))).add_const (1 : ℝ)
  have hd : HasDerivAt (fun t : ℝ => t * t - 6 / π * t + 1) (1 * y + y * 1 - 6 / π * 1) y := hd0
  have heq : (fun t : ℝ => 24 * qa (sig 1) t⁻¹ + 24 * (t * t * qa (sig 1) t))
      =ᶠ[nhds y] (fun t : ℝ => t * t - 6 / π * t + 1) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) (fun t ht => hEq t ht)
  have huniq := hc.unique (hd.congr_of_eventuallyEq heq)
  have hp : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0
  rw [one_div]
  linear_combination (y ^ 2 * π⁻¹ / 48) * huniq
    + (-(qa (fun n => (n : ℝ) * sig 1 n) y⁻¹) * y ^ 2 * y⁻¹ ^ 2
        + y ^ 4 * qa (fun n => (n : ℝ) * sig 1 n) y) * hp
    + (-(qa (fun n => (n : ℝ) * sig 1 n) y⁻¹) * (y * y⁻¹ + 1)) * hyy

/-- `((q d/dq) 𝔉)(iy)`, `𝔉 = 𝔈(τ) - 2𝔈(2τ) - 27𝔈(3τ) + 54𝔈(6τ)`. -/
noncomputable def DFcal (y : ℝ) : ℝ :=
  DEcal y - 4 * DEcal (2 * y) - 81 * DEcal (3 * y) + 324 * DEcal (6 * y)

/-- `(D𝔊)(i/(6y)) = (13/(3π)) y³ - (4/π) y³ 𝔉(iy) + 4 y⁴ (D𝔉)(iy)`. -/
theorem DGcal_fricke {y : ℝ} (hy : 0 < y) :
    DGcal (1 / (6 * y)) = 13 / (3 * π) * y ^ 3 - 4 / π * y ^ 3 * Fcal y + 4 * y ^ 4 * DFcal y := by
  have k6 := DEq_inv (y := 6 * y) (by positivity)
  have k3 := DEq_inv (y := 3 * y) (by positivity)
  have k2 := DEq_inv (y := 2 * y) (by positivity)
  have k1 := DEq_inv hy
  have a2 : 2 * (1 / (6 * y)) = 1 / (3 * y) := by
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have a3 : 3 * (1 / (6 * y)) = 1 / (2 * y) := by
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have a6 : 6 * (1 / (6 * y)) = 1 / y := by
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  unfold DGcal Fcal DFcal
  rw [a2, a3, a6]
  simp only [DEcal_eq_qa, Ecal_eq_qa]
  linear_combination k6 - 4 * k3 - k2 + 4 * k1

/-- `∫₀^∞ g(1/(6y)) y⁻² dy = 6 ∫₀^∞ g(x) dx`. -/
theorem fricke_subst (g : ℝ → ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), g (1 / (6 * y)) / y ^ 2 = 6 * ∫ x in Set.Ioi (0 : ℝ), g x := by
  have h1 : ∫ x in Set.Ioi (0 : ℝ), g (1 / 6 * x⁻¹) * (x ^ 2)⁻¹
      = ∫ x in Set.Ioi (0 : ℝ), g (1 / 6 * x) :=
    integral_Ioi_inv_subst (fun x : ℝ => g (1 / 6 * x))
  have h2 : ∫ x in Set.Ioi (0 : ℝ), g (1 / 6 * x) = 6 * ∫ x in Set.Ioi (0 : ℝ), g x := by
    have h0 := integral_comp_mul_left_Ioi g (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 6)
    rw [mul_zero, smul_eq_mul] at h0
    rw [h0]
    norm_num
  rw [← h2, ← h1]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  show g (1 / (6 * y)) / y ^ 2 = g (1 / 6 * y⁻¹) * (y ^ 2)⁻¹
  have e : 1 / 6 * y⁻¹ = 1 / (6 * y) := by ring
  rw [e]
  ring

/-- Scaling of the moment of a series: `∫₀^∞ qa A (d x) x^k dx = d^{-(k+1)} ∫₀^∞ qa A u u^k du`. -/
theorem integral_qa_scale (A : ℕ → ℝ) {d : ℝ} (hd : 0 < d) (k : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), qa A (d * x) * x ^ k
      = d⁻¹ ^ (k + 1) * ∫ u in Set.Ioi (0 : ℝ), qa A u * u ^ k := by
  have h : ∫ x in Set.Ioi (0 : ℝ), qa A (d * x) * (d * x) ^ k
      = d⁻¹ * ∫ u in Set.Ioi (0 : ℝ), qa A u * u ^ k := by
    have h0 := integral_comp_mul_left_Ioi (fun u : ℝ => qa A u * u ^ k) (0 : ℝ) hd
    rw [mul_zero, smul_eq_mul] at h0
    exact h0
  have hc : ∫ x in Set.Ioi (0 : ℝ), qa A (d * x) * x ^ k
      = ∫ x in Set.Ioi (0 : ℝ), d⁻¹ ^ k * (qa A (d * x) * (d * x) ^ k) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    show qa A (d * x) * x ^ k = d⁻¹ ^ k * (qa A (d * x) * (d * x) ^ k)
    have hdd : d⁻¹ * d = 1 := inv_mul_cancel₀ hd.ne'
    have hk : d⁻¹ ^ k * (d * x) ^ k = x ^ k := by
      rw [← mul_pow, ← mul_assoc, hdd, one_mul]
    linear_combination (-(qa A (d * x))) * hk
  rw [hc, integral_const_mul, h]
  ring

end Tower.RV6
