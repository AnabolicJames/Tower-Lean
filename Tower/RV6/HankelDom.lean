import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselI
import Tower.RV6.BesselK
import Tower.RV6.BesselW
import Tower.RV6.BesselR
import Tower.RV6.MellinU

/-!
# The analytic class of the Hankel transform of `f = I₀ K₀³`

The Hankel dual of the fifth-order equation moves `θ = t d/dt` from `θᵏ f` onto `J₀(xt)` by
integration by parts on `(0, ∞)`.  This file gives, with explicit constants, a class of functions for
which every such integral converges absolutely and every boundary term vanishes.

* `besselK1_le_of_one_le`: `K₁(t) ≤ e^{1-t} K₁(1)` for `t ≥ 1`.
* `sqrt_mul_one_add_log_cube_le`: `√t (1 + log(2/t))³ ≤ 343 √2` for `0 < t ≤ 1`.
* `ITy`, `KTy`: the bounds of `I₀`, `t I₁` (`≤ e` on `(0, 1]`, `≤ t eᵗ` on `[1, ∞)`) and of `K₀`, `t K₁`
  (`≤ 1 + log(2/t)` on `(0, 1]`, `≤ κ t e^{-t}` on `[1, ∞)`, `κ = kapK = e (K₀(1) + K₁(1))`).
* `HDom φ`: `φ` continuous on `(0, ∞)`, `√t |φ t| ≤ C` on `(0, 1]` and `|φ t| ≤ C t^N e^{-t}` on
  `[1, ∞)`.  A product of one `ITy` and three `KTy` factors is in `HDom` (`hdom_prod4`); `HDom` is
  closed under sums, constant multiples and multiplication by `tⁿ`.
* `integrableOn_hdom`: `tʲ φ(t) g(t)` is integrable on `(0, ∞)` for `j ≥ 1`, `g` continuous and bounded;
  `tendsto_hdom_zero`, `tendsto_hdom_atTop`: `t² φ(t) g(t) → 0` at `0+` and at `∞`.
* `integral_Ioi_deriv_eq_zero`: `∫₀^∞ F' = 0` if `F(0) = 0` and `F → 0` at both ends.

That `θᵏ f` is in `HDom` for `k ≤ 5` is in `HankelDomF.lean`.
-/

namespace Tower.RV6

open MeasureTheory

/-! ## Two bounds -/

/-- `K₁(t) ≤ e^{1-t} K₁(1)` for `t ≥ 1`. -/
theorem besselK1_le_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    besselK1 t ≤ Real.exp (1 - t) * besselK1 1 := by
  have ht0 : 0 < t := by linarith
  have hpt : ∀ u : ℝ, kf t 1 u ≤ Real.exp (1 - t) * kf 1 1 u := by
    intro u
    show Real.exp (-t * Real.cosh u) * Real.cosh u ^ 1
      ≤ Real.exp (1 - t) * (Real.exp (-1 * Real.cosh u) * Real.cosh u ^ 1)
    have hc := Real.one_le_cosh u
    have hprod : 0 ≤ (t - 1) * (Real.cosh u - 1) :=
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hc)
    have hlin : -t * Real.cosh u ≤ 1 - t + -1 * Real.cosh u := by
      calc -t * Real.cosh u
          = (1 - t + -1 * Real.cosh u) - (t - 1) * (Real.cosh u - 1) := by ring
        _ ≤ 1 - t + -1 * Real.cosh u := sub_le_self _ hprod
    have hE : Real.exp (-t * Real.cosh u)
        ≤ Real.exp (1 - t) * Real.exp (-1 * Real.cosh u) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hlin
    have hcp : 0 ≤ Real.cosh u ^ 1 := pow_nonneg (Real.cosh_pos u).le 1
    calc Real.exp (-t * Real.cosh u) * Real.cosh u ^ 1
        ≤ Real.exp (1 - t) * Real.exp (-1 * Real.cosh u) * Real.cosh u ^ 1 :=
          mul_le_mul_of_nonneg_right hE hcp
      _ = Real.exp (1 - t) * (Real.exp (-1 * Real.cosh u) * Real.cosh u ^ 1) := by ring
  have hint : Integrable (fun u : ℝ => Real.exp (1 - t) * kf 1 1 u)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrable_kf one_pos 1 (by norm_num)).const_mul _
  have h : ∫ u in Set.Ioi (0 : ℝ), kf t 1 u
      ≤ ∫ u in Set.Ioi (0 : ℝ), Real.exp (1 - t) * kf 1 1 u :=
    integral_mono (integrable_kf ht0 1 (by norm_num)) hint hpt
  rw [integral_const_mul] at h
  rw [besselK1_eq t, besselK1_eq 1]
  exact h

/-- `√t (1 + log(2/t))³ ≤ 343 √2` for `0 < t ≤ 1` (`log y ≤ 6 (y^{1/6} - 1)`). -/
theorem sqrt_mul_one_add_log_cube_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.sqrt t * (1 + Real.log (2 / t)) ^ 3 ≤ 343 * Real.sqrt 2 := by
  have hy : 0 < 2 / t := div_pos two_pos ht
  have hy1 : 1 ≤ 2 / t := by
    rw [le_div_iff₀ ht]
    linarith
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = (2 / t) ^ ((1 : ℝ) / 6) := ⟨_, rfl⟩
  have hzpos : 0 < z := by
    rw [hz]
    exact Real.rpow_pos_of_pos hy _
  have hlogz : Real.log z = 1 / 6 * Real.log (2 / t) := by
    rw [hz]
    exact Real.log_rpow hy _
  have hle : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hzpos
  have hL0 : 0 ≤ Real.log (2 / t) := Real.log_nonneg hy1
  have hA : 0 ≤ 1 + Real.log (2 / t) := by linarith
  have hB : 1 + Real.log (2 / t) ≤ 7 * z := by linarith
  have hC : (1 + Real.log (2 / t)) ^ 3 ≤ (7 * z) ^ 3 := pow_le_pow_left₀ hA hB 3
  have hz3 : z ^ 3 = Real.sqrt (2 / t) := by
    rw [Real.sqrt_eq_rpow, hz, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hst : Real.sqrt t * Real.sqrt (2 / t) = Real.sqrt 2 := by
    rw [← Real.sqrt_mul ht.le]
    have e : t * (2 / t) = 2 := by linear_combination 2 * hinv
    rw [e]
  have hsq : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  calc Real.sqrt t * (1 + Real.log (2 / t)) ^ 3 ≤ Real.sqrt t * (7 * z) ^ 3 :=
        mul_le_mul_of_nonneg_left hC hsq
    _ = 343 * (Real.sqrt t * z ^ 3) := by ring
    _ = 343 * Real.sqrt 2 := by rw [hz3, hst]

theorem sinh_le_exp_self (t : ℝ) : Real.sinh t ≤ Real.exp t := by
  rw [Real.sinh_eq]
  have h1 := Real.exp_pos t
  have h2 := Real.exp_pos (-t)
  linarith

/-! ## The classes -/

/-- The constant of the decay of `K₀` and `t K₁` at infinity. -/
noncomputable def kapK : ℝ := Real.exp 1 * (besselK0 1 + besselK1 1)

theorem kapK_nonneg : 0 ≤ kapK := by
  unfold kapK
  have h0 := besselK0_nonneg 1
  have h1 := (besselK1_pos one_pos).le
  exact mul_nonneg (Real.exp_pos 1).le (by linarith)

/-- The bounds of `I₀` and `t I₁`. -/
abbrev ITy (a : ℝ → ℝ) : Prop :=
  ContinuousOn a (Set.Ioi 0) ∧ (∀ t : ℝ, 0 < t → t ≤ 1 → |a t| ≤ Real.exp 1) ∧
    ∀ t : ℝ, 1 ≤ t → |a t| ≤ t * Real.exp t

/-- The bounds of `K₀` and `t K₁`. -/
abbrev KTy (b : ℝ → ℝ) : Prop :=
  ContinuousOn b (Set.Ioi 0) ∧ (∀ t : ℝ, 0 < t → t ≤ 1 → |b t| ≤ 1 + Real.log (2 / t)) ∧
    ∀ t : ℝ, 1 ≤ t → |b t| ≤ kapK * t * Real.exp (-t)

/-- The class of the integrands: `√t |φ t| ≤ C` on `(0, 1]`, `|φ t| ≤ C t^N e^{-t}` on `[1, ∞)`. -/
abbrev HDom (φ : ℝ → ℝ) : Prop :=
  ContinuousOn φ (Set.Ioi 0) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    (∀ t : ℝ, 0 < t → t ≤ 1 → Real.sqrt t * |φ t| ≤ C) ∧
      ∀ t : ℝ, 1 ≤ t → |φ t| ≤ C * t ^ N * Real.exp (-t)

theorem ity_besselI0 : ITy besselI0 := by
  refine ⟨continuous_besselI0.continuousOn, fun t ht ht1 => ?_, fun t ht => ?_⟩
  · rw [abs_of_pos (besselI0_pos t)]
    exact (besselI0_le_exp ht).trans (Real.exp_le_exp.mpr ht1)
  · have ht0 : 0 < t := by linarith
    rw [abs_of_pos (besselI0_pos t)]
    have h1 := besselI0_le_exp ht0
    have h2 : Real.exp t ≤ t * Real.exp t := le_mul_of_one_le_left (Real.exp_pos t).le ht
    linarith

theorem ity_mul_besselI1 : ITy (fun x : ℝ => x * besselI1 x) := by
  have hc : Continuous (fun x : ℝ => x * besselI1 x) := continuous_id.mul continuous_besselI1
  refine ⟨hc.continuousOn, fun t ht ht1 => ?_, fun t ht => ?_⟩
  · show |t * besselI1 t| ≤ Real.exp 1
    have hnn : 0 ≤ t * besselI1 t := mul_nonneg ht.le (besselI1_nonneg ht.le)
    rw [abs_of_nonneg hnn]
    have h1 : besselI1 t ≤ Real.exp t := (besselI1_le_sinh ht.le).trans (sinh_le_exp_self t)
    have h2 : t * besselI1 t ≤ t * Real.exp t := mul_le_mul_of_nonneg_left h1 ht.le
    have h3 : t * Real.exp t ≤ 1 * Real.exp 1 :=
      mul_le_mul ht1 (Real.exp_le_exp.mpr ht1) (Real.exp_pos t).le zero_le_one
    linarith
  · show |t * besselI1 t| ≤ t * Real.exp t
    have ht0 : 0 < t := by linarith
    have hnn : 0 ≤ t * besselI1 t := mul_nonneg ht0.le (besselI1_nonneg ht0.le)
    rw [abs_of_nonneg hnn]
    have h1 : besselI1 t ≤ Real.exp t := (besselI1_le_sinh ht0.le).trans (sinh_le_exp_self t)
    exact mul_le_mul_of_nonneg_left h1 ht0.le

theorem kty_besselK0 : KTy besselK0 := by
  refine ⟨fun t ht => (hasDerivAt_besselK0 (Set.mem_Ioi.mp ht)).continuousAt.continuousWithinAt,
    fun t ht ht1 => ?_, fun t ht => ?_⟩
  · rw [abs_of_nonneg (besselK0_nonneg t)]
    exact besselK0_le_one_add_log ht ht1
  · rw [abs_of_nonneg (besselK0_nonneg t)]
    have h1 := besselK0_le_kappa_exp ht
    have hk1 := (besselK1_pos one_pos).le
    have hK01 := besselK0_nonneg 1
    have he := (Real.exp_pos (-t)).le
    have hE := (Real.exp_pos 1).le
    have h2 : Real.exp 1 * besselK0 1 * Real.exp (-t) ≤ kapK * t * Real.exp (-t) := by
      unfold kapK
      have hA : 0 ≤ Real.exp 1 * (besselK0 1 + besselK1 1) * Real.exp (-t) :=
        mul_nonneg (mul_nonneg hE (by linarith)) he
      have h4 : Real.exp 1 * besselK0 1 ≤ Real.exp 1 * (besselK0 1 + besselK1 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hE
      have h3 : Real.exp 1 * besselK0 1 * Real.exp (-t)
          ≤ Real.exp 1 * (besselK0 1 + besselK1 1) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right h4 he
      have h6 := le_mul_of_one_le_right hA ht
      linarith
    linarith

theorem kty_mul_besselK1 : KTy (fun x : ℝ => x * besselK1 x) := by
  refine ⟨fun t ht => (hasDerivAt_mul_besselK1 (Set.mem_Ioi.mp ht)).continuousAt.continuousWithinAt,
    fun t ht ht1 => ?_, fun t ht => ?_⟩
  · show |t * besselK1 t| ≤ 1 + Real.log (2 / t)
    rw [abs_of_pos (mul_pos ht (besselK1_pos ht))]
    have h1 := mul_besselK1_le_one ht
    have hy1 : 1 ≤ 2 / t := by
      rw [le_div_iff₀ ht]
      linarith
    have h2 := Real.log_nonneg hy1
    linarith
  · show |t * besselK1 t| ≤ kapK * t * Real.exp (-t)
    have ht0 : 0 < t := by linarith
    rw [abs_of_pos (mul_pos ht0 (besselK1_pos ht0))]
    have h1 := besselK1_le_of_one_le ht
    have e : Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) := by
      rw [sub_eq_add_neg, Real.exp_add]
    rw [e] at h1
    have hK01 := besselK0_nonneg 1
    have he := (Real.exp_pos (-t)).le
    have hE := (Real.exp_pos 1).le
    have h2 : besselK1 t ≤ kapK * Real.exp (-t) := by
      unfold kapK
      have h4 : 0 ≤ Real.exp 1 * Real.exp (-t) := mul_nonneg hE he
      have h5 : Real.exp 1 * Real.exp (-t) * besselK1 1
          ≤ Real.exp 1 * Real.exp (-t) * (besselK0 1 + besselK1 1) :=
        mul_le_mul_of_nonneg_left (by linarith) h4
      linarith
    have h6 : t * besselK1 t ≤ t * (kapK * Real.exp (-t)) := mul_le_mul_of_nonneg_left h2 ht0.le
    linarith

/-! ## Closure of `HDom` -/

theorem abs_mul4_le {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) : |a * b * c * d| ≤ A * B * C * D := by
  have hA : 0 ≤ A := (abs_nonneg a).trans ha
  have hB : 0 ≤ B := (abs_nonneg b).trans hb
  have hC : 0 ≤ C := (abs_nonneg c).trans hc
  rw [abs_mul, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul ha hb (abs_nonneg b) hA) hc (abs_nonneg c)
    (mul_nonneg hA hB)) hd (abs_nonneg d) (mul_nonneg (mul_nonneg hA hB) hC)

/-- One `ITy` factor times three `KTy` factors is in `HDom`, with `C = e · 343 √2 + κ³`, `N = 4`. -/
theorem hdom_prod4 {a b c d : ℝ → ℝ} (ha : ITy a) (hb : KTy b) (hc : KTy c) (hd : KTy d) :
    HDom (fun t => a t * b t * c t * d t) := by
  obtain ⟨ca, na, fa⟩ := ha
  obtain ⟨cb, nb, fb⟩ := hb
  obtain ⟨cc, nc, fc⟩ := hc
  obtain ⟨cd, nd, fd⟩ := hd
  have hk := kapK_nonneg
  have hcont : ContinuousOn (fun t => a t * b t * c t * d t) (Set.Ioi 0) :=
    ((ca.mul cb).mul cc).mul cd
  have h1 : 0 ≤ Real.exp 1 * (343 * Real.sqrt 2) :=
    mul_nonneg (Real.exp_pos 1).le (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2))
  have h2 : 0 ≤ kapK ^ 3 := pow_nonneg hk 3
  refine ⟨hcont, Real.exp 1 * (343 * Real.sqrt 2) + kapK ^ 3, by linarith, 4,
    fun t ht ht1 => ?_, fun t ht => ?_⟩
  · show Real.sqrt t * |a t * b t * c t * d t| ≤ Real.exp 1 * (343 * Real.sqrt 2) + kapK ^ 3
    have hB : |a t * b t * c t * d t|
        ≤ Real.exp 1 * (1 + Real.log (2 / t)) * (1 + Real.log (2 / t))
          * (1 + Real.log (2 / t)) :=
      abs_mul4_le (na t ht ht1) (nb t ht ht1) (nc t ht ht1) (nd t ht ht1)
    have hL := sqrt_mul_one_add_log_cube_le ht ht1
    have hs := Real.sqrt_nonneg t
    have h3 : Real.sqrt t * |a t * b t * c t * d t|
        ≤ Real.sqrt t * (Real.exp 1 * (1 + Real.log (2 / t)) * (1 + Real.log (2 / t))
          * (1 + Real.log (2 / t))) := mul_le_mul_of_nonneg_left hB hs
    have h4 : Real.sqrt t * (Real.exp 1 * (1 + Real.log (2 / t)) * (1 + Real.log (2 / t))
          * (1 + Real.log (2 / t)))
        = Real.exp 1 * (Real.sqrt t * (1 + Real.log (2 / t)) ^ 3) := by ring
    have h5 : Real.exp 1 * (Real.sqrt t * (1 + Real.log (2 / t)) ^ 3)
        ≤ Real.exp 1 * (343 * Real.sqrt 2) := mul_le_mul_of_nonneg_left hL (Real.exp_pos 1).le
    linarith
  · show |a t * b t * c t * d t|
      ≤ (Real.exp 1 * (343 * Real.sqrt 2) + kapK ^ 3) * t ^ 4 * Real.exp (-t)
    have ht0 : 0 < t := by linarith
    have hB : |a t * b t * c t * d t|
        ≤ t * Real.exp t * (kapK * t * Real.exp (-t)) * (kapK * t * Real.exp (-t))
          * (kapK * t * Real.exp (-t)) :=
      abs_mul4_le (fa t ht) (fb t ht) (fc t ht) (fd t ht)
    have hEE : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]
      simp
    have he1 : Real.exp (-t) ≤ 1 := exp_le_one_of_nonpos (by linarith)
    have h6 : t * Real.exp t * (kapK * t * Real.exp (-t)) * (kapK * t * Real.exp (-t))
          * (kapK * t * Real.exp (-t))
        = kapK ^ 3 * t ^ 4 * Real.exp (-t) * Real.exp (-t) := by
      linear_combination (kapK ^ 3 * t ^ 4 * Real.exp (-t) * Real.exp (-t)) * hEE
    have hX : 0 ≤ kapK ^ 3 * t ^ 4 * Real.exp (-t) :=
      mul_nonneg (mul_nonneg h2 (pow_nonneg ht0.le 4)) (Real.exp_pos _).le
    have h7 : kapK ^ 3 * t ^ 4 * Real.exp (-t) * Real.exp (-t)
        ≤ kapK ^ 3 * t ^ 4 * Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left he1 hX
    have hY : 0 ≤ t ^ 4 * Real.exp (-t) := mul_nonneg (pow_nonneg ht0.le 4) (Real.exp_pos _).le
    have h8 : 0 ≤ Real.exp 1 * (343 * Real.sqrt 2) * (t ^ 4 * Real.exp (-t)) := mul_nonneg h1 hY
    have h9 : (Real.exp 1 * (343 * Real.sqrt 2) + kapK ^ 3) * t ^ 4 * Real.exp (-t)
        = Real.exp 1 * (343 * Real.sqrt 2) * (t ^ 4 * Real.exp (-t))
          + kapK ^ 3 * t ^ 4 * Real.exp (-t) := by ring
    linarith

theorem hdom_add {φ ψ : ℝ → ℝ} (hφ : HDom φ) (hψ : HDom ψ) : HDom (fun t => φ t + ψ t) := by
  obtain ⟨c1, C1, hC1, N1, n1, f1⟩ := hφ
  obtain ⟨c2, C2, hC2, N2, n2, f2⟩ := hψ
  refine ⟨c1.add c2, C1 + C2, by linarith, N1 + N2, fun t ht ht1 => ?_, fun t ht => ?_⟩
  · show Real.sqrt t * |φ t + ψ t| ≤ C1 + C2
    have h := abs_add_le (φ t) (ψ t)
    have hs := Real.sqrt_nonneg t
    have h1 := n1 t ht ht1
    have h2 := n2 t ht ht1
    have h3 : Real.sqrt t * |φ t + ψ t| ≤ Real.sqrt t * (|φ t| + |ψ t|) :=
      mul_le_mul_of_nonneg_left h hs
    linarith
  · show |φ t + ψ t| ≤ (C1 + C2) * t ^ (N1 + N2) * Real.exp (-t)
    have h := abs_add_le (φ t) (ψ t)
    have h1 := f1 t ht
    have h2 := f2 t ht
    have hp1 : t ^ N1 ≤ t ^ (N1 + N2) := pow_le_pow_right₀ ht (Nat.le_add_right N1 N2)
    have hp2 : t ^ N2 ≤ t ^ (N1 + N2) := pow_le_pow_right₀ ht (Nat.le_add_left N2 N1)
    have he := (Real.exp_pos (-t)).le
    have h3 : C1 * t ^ N1 * Real.exp (-t) ≤ C1 * t ^ (N1 + N2) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 hC1) he
    have h4 : C2 * t ^ N2 * Real.exp (-t) ≤ C2 * t ^ (N1 + N2) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hC2) he
    have h5 : (C1 + C2) * t ^ (N1 + N2) * Real.exp (-t)
        = C1 * t ^ (N1 + N2) * Real.exp (-t) + C2 * t ^ (N1 + N2) * Real.exp (-t) := by ring
    linarith

theorem hdom_const_mul (c : ℝ) {φ : ℝ → ℝ} (hφ : HDom φ) : HDom (fun t => c * φ t) := by
  obtain ⟨c1, C1, hC1, N1, n1, f1⟩ := hφ
  have hc : ContinuousOn (fun t : ℝ => c * φ t) (Set.Ioi 0) :=
    ContinuousOn.mul (f := fun _ : ℝ => c) continuousOn_const c1
  refine ⟨hc, |c| * C1, mul_nonneg (abs_nonneg c) hC1, N1, fun t ht ht1 => ?_, fun t ht => ?_⟩
  · show Real.sqrt t * |c * φ t| ≤ |c| * C1
    rw [abs_mul]
    have h1 := n1 t ht ht1
    have h2 : |c| * (Real.sqrt t * |φ t|) ≤ |c| * C1 :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    linarith
  · show |c * φ t| ≤ |c| * C1 * t ^ N1 * Real.exp (-t)
    rw [abs_mul]
    have h1 := f1 t ht
    have h2 : |c| * |φ t| ≤ |c| * (C1 * t ^ N1 * Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    linarith

theorem hdom_pow_mul (n : ℕ) {φ : ℝ → ℝ} (hφ : HDom φ) : HDom (fun t => t ^ n * φ t) := by
  obtain ⟨c1, C1, hC1, N1, n1, f1⟩ := hφ
  have hc : ContinuousOn (fun t : ℝ => t ^ n * φ t) (Set.Ioi 0) :=
    ContinuousOn.mul (f := fun t : ℝ => t ^ n) (continuous_pow n).continuousOn c1
  refine ⟨hc, C1, hC1, n + N1, fun t ht ht1 => ?_, fun t ht => ?_⟩
  · show Real.sqrt t * |t ^ n * φ t| ≤ C1
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le n)]
    have hp : t ^ n ≤ 1 := pow_le_one₀ ht.le ht1
    have h1 := n1 t ht ht1
    have hX : 0 ≤ Real.sqrt t * |φ t| := mul_nonneg (Real.sqrt_nonneg t) (abs_nonneg _)
    have h2 : t ^ n * (Real.sqrt t * |φ t|) ≤ 1 * (Real.sqrt t * |φ t|) :=
      mul_le_mul_of_nonneg_right hp hX
    linarith
  · show |t ^ n * φ t| ≤ C1 * t ^ (n + N1) * Real.exp (-t)
    have ht0 : 0 ≤ t := by linarith
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 n)]
    have h1 := f1 t ht
    have h2 : t ^ n * |φ t| ≤ t ^ n * (C1 * t ^ N1 * Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg ht0 n)
    have e : C1 * t ^ (n + N1) * Real.exp (-t) = t ^ n * (C1 * t ^ N1 * Real.exp (-t)) := by
      rw [pow_add]
      ring
    linarith

/-! ## Integrability and the boundary terms -/

/-- `tⁿ e^{-t} ≤ 2ⁿ n! e^{-t/2}` for `t ≥ 0`. -/
theorem pow_mul_exp_neg_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ n * Real.exp (-t) ≤ 2 ^ n * (n.factorial : ℝ) * Real.exp (-(1 / 2) * t) := by
  have h := Real.pow_div_factorial_le_exp (t / 2) (by linarith) n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h2 : (t / 2) ^ n ≤ Real.exp (t / 2) * (n.factorial : ℝ) := (div_le_iff₀ hf).mp h
  have e1 : t ^ n = 2 ^ n * (t / 2) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  have e2 : Real.exp (t / 2) * Real.exp (-t) = Real.exp (-(1 / 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE := (Real.exp_pos (-t)).le
  have h3 : 2 ^ n * (t / 2) ^ n * Real.exp (-t)
      ≤ 2 ^ n * (Real.exp (t / 2) * (n.factorial : ℝ)) * Real.exp (-t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (pow_nonneg (by norm_num) n)) hE
  calc t ^ n * Real.exp (-t) = 2 ^ n * (t / 2) ^ n * Real.exp (-t) := by rw [e1]
    _ ≤ 2 ^ n * (Real.exp (t / 2) * (n.factorial : ℝ)) * Real.exp (-t) := h3
    _ = 2 ^ n * (n.factorial : ℝ) * (Real.exp (t / 2) * Real.exp (-t)) := by ring
    _ = 2 ^ n * (n.factorial : ℝ) * Real.exp (-(1 / 2) * t) := by rw [e2]

/-- `tʲ φ(t) g(t)` is integrable on `(0, ∞)` for `φ ∈ HDom`, `g` continuous and bounded, `j ≥ 1`. -/
theorem integrableOn_hdom {φ g : ℝ → ℝ} (hφ : HDom φ) (hg : ContinuousOn g (Set.Ioi 0))
    {G : ℝ} (hG : ∀ t : ℝ, 0 < t → |g t| ≤ G) {j : ℕ} (hj : 1 ≤ j) :
    IntegrableOn (fun t : ℝ => t ^ j * φ t * g t) (Set.Ioi 0) := by
  obtain ⟨hc, C, hC0, N, hn, hf⟩ := hφ
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 1 one_pos)
  have hcont : ContinuousOn (fun t : ℝ => t ^ j * φ t * g t) (Set.Ioi 0) :=
    (ContinuousOn.mul (f := fun t : ℝ => t ^ j) (continuous_pow j).continuousOn hc).mul hg
  have i1 : IntegrableOn (fun t : ℝ => t ^ j * φ t * g t) (Set.Ioc 0 1) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => t ^ j * φ t * g t)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖t ^ j * φ t * g t‖ ≤ C * G := by
      refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
      rw [Real.norm_eq_abs]
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0.le j)]
      have hpj : t ^ j ≤ t := by
        calc t ^ j ≤ t ^ 1 := pow_le_pow_of_le_one ht0.le ht1 hj
          _ = t := pow_one t
      have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
      have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
      have hs0 := Real.sqrt_nonneg t
      have hss1 : Real.sqrt t * Real.sqrt t ≤ Real.sqrt t * 1 :=
        mul_le_mul_of_nonneg_left hs1 hs0
      have hts : t ^ j ≤ Real.sqrt t := by linarith
      have hA : t ^ j * |φ t| ≤ Real.sqrt t * |φ t| :=
        mul_le_mul_of_nonneg_right hts (abs_nonneg _)
      have hA2 : t ^ j * |φ t| ≤ C := hA.trans (hn t ht0 ht1)
      exact mul_le_mul hA2 (hG t ht0) (abs_nonneg _) hC0
    have hi : IntegrableOn (fun _ : ℝ => C * G) (Set.Ioc (0 : ℝ) 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    exact Integrable.mono' hi hm hb
  have i2 : IntegrableOn (fun t : ℝ => t ^ j * φ t * g t) (Set.Ioi 1) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => t ^ j * φ t * g t)
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ‖t ^ j * φ t * g t‖
          ≤ C * G * (2 ^ (j + N) * ((j + N).factorial : ℝ)) * Real.exp (-(1 / 2) * t) := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
      rw [Real.norm_eq_abs]
      have ht1 : 1 ≤ t := (Set.mem_Ioi.mp ht).le
      have ht0 : 0 < t := by linarith
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0.le j)]
      have h1 := hf t ht1
      have h2 := hG t ht0
      have hP := pow_mul_exp_neg_le (j + N) ht0.le
      have hA : t ^ j * |φ t| ≤ t ^ j * (C * t ^ N * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg ht0.le j)
      have hB : t ^ j * |φ t| * |g t| ≤ t ^ j * (C * t ^ N * Real.exp (-t)) * G :=
        mul_le_mul hA h2 (abs_nonneg _) (mul_nonneg (pow_nonneg ht0.le j)
          (mul_nonneg (mul_nonneg hC0 (pow_nonneg ht0.le N)) (Real.exp_pos _).le))
      have e : t ^ j * (C * t ^ N * Real.exp (-t)) * G
          = C * G * (t ^ (j + N) * Real.exp (-t)) := by
        rw [pow_add]
        ring
      have hCG : 0 ≤ C * G := mul_nonneg hC0 hG0
      have hD : C * G * (t ^ (j + N) * Real.exp (-t))
          ≤ C * G * (2 ^ (j + N) * ((j + N).factorial : ℝ) * Real.exp (-(1 / 2) * t)) :=
        mul_le_mul_of_nonneg_left hP hCG
      have e2 : C * G * (2 ^ (j + N) * ((j + N).factorial : ℝ) * Real.exp (-(1 / 2) * t))
          = C * G * (2 ^ (j + N) * ((j + N).factorial : ℝ)) * Real.exp (-(1 / 2) * t) := by
        ring
      linarith
    have hi0 : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2) * t)) (Set.Ioi 1) :=
      exp_neg_integrableOn_Ioi 1 (by norm_num)
    have hi : IntegrableOn (fun t : ℝ => C * G * (2 ^ (j + N) * ((j + N).factorial : ℝ))
        * Real.exp (-(1 / 2) * t)) (Set.Ioi 1) :=
      Integrable.const_mul hi0 (C * G * (2 ^ (j + N) * ((j + N).factorial : ℝ)))
    exact Integrable.mono' hi hm hb
  have h := i1.union i2
  rw [Set.Ioc_union_Ioi_eq_Ioi zero_le_one] at h
  exact h

/-- `t² φ(t) g(t) → 0` as `t → 0+`. -/
theorem tendsto_hdom_zero {φ g : ℝ → ℝ} (hφ : HDom φ) {G : ℝ}
    (hG : ∀ t : ℝ, 0 < t → |g t| ≤ G) :
    Filter.Tendsto (fun t : ℝ => t ^ 2 * φ t * g t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨_, C, hC0, _, hn, _⟩ := hφ
  have hlim : Filter.Tendsto (fun t : ℝ => C * G * t) (nhds 0) (nhds (C * G * 0)) :=
    Filter.tendsto_id.const_mul (C * G)
  rw [mul_zero] at hlim
  have hlim2 : Filter.Tendsto (fun t : ℝ => C * G * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hlim.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim2
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hmem] with t ht
  show ‖t ^ 2 * φ t * g t‖ ≤ C * G * t
  rw [Real.norm_eq_abs]
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2.le
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0.le 2)]
  have h1 := hn t ht0 ht1
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hs0 := Real.sqrt_nonneg t
  have e : t ^ 2 * |φ t| = t * Real.sqrt t * (Real.sqrt t * |φ t|) := by
    have e0 : t ^ 2 = t * (Real.sqrt t * Real.sqrt t) := by
      rw [hss]
      ring
    rw [e0]
    ring
  have hA : t * Real.sqrt t * (Real.sqrt t * |φ t|) ≤ t * Real.sqrt t * C :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg ht0.le hs0)
  have hB : t * Real.sqrt t * C ≤ t * 1 * C :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs1 ht0.le) hC0
  have hX : t ^ 2 * |φ t| ≤ C * t := by linarith
  have hY : t ^ 2 * |φ t| * |g t| ≤ C * t * G :=
    mul_le_mul hX (hG t ht0) (abs_nonneg _) (mul_nonneg hC0 ht0.le)
  linarith

/-- `t² φ(t) g(t) → 0` as `t → ∞`. -/
theorem tendsto_hdom_atTop {φ g : ℝ → ℝ} (hφ : HDom φ) {G : ℝ}
    (hG : ∀ t : ℝ, 0 < t → |g t| ≤ G) :
    Filter.Tendsto (fun t : ℝ => t ^ 2 * φ t * g t) Filter.atTop (nhds 0) := by
  obtain ⟨_, C, hC0, N, _, hf⟩ := hφ
  have hlim : Filter.Tendsto (fun t : ℝ => C * G * (t ^ (N + 2) * Real.exp (-t)))
      Filter.atTop (nhds (C * G * 0)) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (N + 2)).const_mul (C * G)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ((Filter.eventually_ge_atTop (1 : ℝ)).mono (fun t ht => ?_)) hlim
  show ‖t ^ 2 * φ t * g t‖ ≤ C * G * (t ^ (N + 2) * Real.exp (-t))
  rw [Real.norm_eq_abs]
  have ht0 : 0 < t := by linarith
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0.le 2)]
  have h1 := hf t ht
  have h2 := hG t ht0
  have hA : t ^ 2 * |φ t| ≤ t ^ 2 * (C * t ^ N * Real.exp (-t)) :=
    mul_le_mul_of_nonneg_left h1 (pow_nonneg ht0.le 2)
  have hB : t ^ 2 * |φ t| * |g t| ≤ t ^ 2 * (C * t ^ N * Real.exp (-t)) * G :=
    mul_le_mul hA h2 (abs_nonneg _) (mul_nonneg (pow_nonneg ht0.le 2)
      (mul_nonneg (mul_nonneg hC0 (pow_nonneg ht0.le N)) (Real.exp_pos _).le))
  have e : t ^ 2 * (C * t ^ N * Real.exp (-t)) * G = C * G * (t ^ (N + 2) * Real.exp (-t)) := by
    rw [pow_add]
    ring
  linarith

/-- `∫₀^∞ F' = 0` when `F(0) = 0`, `F' = dF/dt` on `(0, ∞)` is integrable, and `F → 0` at `0+`
and at `∞`. -/
theorem integral_Ioi_deriv_eq_zero {F F' : ℝ → ℝ} (hF0 : F 0 = 0)
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt F (F' t) t)
    (h0 : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hinf : Filter.Tendsto F Filter.atTop (nhds 0)) (hint : IntegrableOn F' (Set.Ioi 0)) :
    ∫ t in Set.Ioi (0 : ℝ), F' t = 0 := by
  have hc : ContinuousWithinAt F (Set.Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    show Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0))
    rw [hF0]
    exact h0
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc
    (fun x hx => hd x (Set.mem_Ioi.mp hx)) hint hinf
  rw [h, hF0, sub_zero]

end Tower.RV6
