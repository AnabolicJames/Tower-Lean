import Mathlib
import Tower.RV6.Defs
import Tower.RV6.BesselJ
import Tower.RV6.LadderA2

/-!
# Sub-rung A2T: the trigonometric cancellation of the poles

`rungA2T : RungA2T`:

`(1440/π⁵) sin(πs/2)/s⁶ - (720/π⁴) cos(πs/2)/s⁵ - (120/π³) sin(πs/2)/s⁴ - 1/s → 0` as `s → 0+`.

With `N(x) = 45 sin x - 45 x cos x - 15 x² sin x - x⁵` the expression is `(32/π⁵) N(πs/2)/s⁶`
(`trigT_eq`).  `N' = 5x N₁` with `N₁(x) = 3 sin x - 3 x cos x - x³`, `N₁' = 3x (sin x - x)`, and
`x - x³/6 ≤ sin x ≤ x` for `x ≥ 0` (Mathlib).  A function that vanishes at `0` and has a
nonpositive derivative on `(0, ∞)` is `≤ 0` on `[0, ∞)`; applied four times this gives
`-x⁵/10 ≤ N₁(x) ≤ 0` and `-x⁷/14 ≤ N(x) ≤ 0`, hence `-(π²/56) s ≤ expression ≤ 0`.

Powers are written as products (`x * x * x`), so that every derivative is a chain of
`HasDerivAt.mul` and no numeral is cast.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## A sign lemma -/

/-- A function with `f 0 = 0` and a nonpositive derivative on `(0, ∞)` is `≤ 0` on `[0, ∞)`. -/
theorem nonpos_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} (hd : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hn : ∀ x : ℝ, 0 < x → f' x ≤ 0) (h0 : f 0 = 0) {x : ℝ} (hx : 0 ≤ x) : f x ≤ 0 := by
  have hc : ContinuousOn f (Set.Ici (0 : ℝ)) :=
    (continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)).continuousOn
  have h : f x ≤ f 0 :=
    antitone_of_hasDerivAt_nonpos (f' := f') hc (fun y _ => hd y) hn (le_refl (0 : ℝ)) hx
  rw [h0] at h
  exact h

/-! ## Derivatives of monomials written as products -/

theorem hasDerivAt_id_pow2 (x : ℝ) : HasDerivAt (fun y : ℝ => y * y) (2 * x) x := by
  have h : HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x :=
    (hasDerivAt_id' x).mul (hasDerivAt_id' x)
  exact h.congr_deriv (by ring)

theorem hasDerivAt_id_pow3 (x : ℝ) : HasDerivAt (fun y : ℝ => y * y * y) (3 * (x * x)) x := by
  have h : HasDerivAt (fun y : ℝ => y * y * y) (2 * x * x + x * x * 1) x :=
    (hasDerivAt_id_pow2 x).mul (hasDerivAt_id' x)
  exact h.congr_deriv (by ring)

theorem hasDerivAt_id_pow4 (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * y * y * y) (4 * (x * x * x)) x := by
  have h : HasDerivAt (fun y : ℝ => y * y * y * y) (3 * (x * x) * x + x * x * x * 1) x :=
    (hasDerivAt_id_pow3 x).mul (hasDerivAt_id' x)
  exact h.congr_deriv (by ring)

theorem hasDerivAt_id_pow5 (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * y * y * y * y) (5 * (x * x * x * x)) x := by
  have h : HasDerivAt (fun y : ℝ => y * y * y * y * y)
      (4 * (x * x * x) * x + x * x * x * x * 1) x :=
    (hasDerivAt_id_pow4 x).mul (hasDerivAt_id' x)
  exact h.congr_deriv (by ring)

theorem hasDerivAt_id_pow6 (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * y * y * y * y * y) (6 * (x * x * x * x * x)) x := by
  have h : HasDerivAt (fun y : ℝ => y * y * y * y * y * y)
      (5 * (x * x * x * x) * x + x * x * x * x * x * 1) x :=
    (hasDerivAt_id_pow5 x).mul (hasDerivAt_id' x)
  exact h.congr_deriv (by ring)

theorem hasDerivAt_id_pow7 (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * y * y * y * y * y * y) (7 * (x * x * x * x * x * x)) x := by
  have h : HasDerivAt (fun y : ℝ => y * y * y * y * y * y * y)
      (6 * (x * x * x * x * x) * x + x * x * x * x * x * x * 1) x :=
    (hasDerivAt_id_pow6 x).mul (hasDerivAt_id' x)
  exact h.congr_deriv (by ring)

/-! ## The two auxiliary functions -/

/-- `N₁(x) = 3 sin x - 3 x cos x - x³`. -/
noncomputable def trigN1 (x : ℝ) : ℝ := 3 * Real.sin x - 3 * x * Real.cos x - x * x * x

/-- `N(x) = 45 sin x - 45 x cos x - 15 x² sin x - x⁵`. -/
noncomputable def trigN (x : ℝ) : ℝ :=
  45 * Real.sin x - 45 * x * Real.cos x - 15 * (x * x) * Real.sin x - x * x * x * x * x

/-- `N₁' = 3x (sin x - x)`. -/
theorem hasDerivAt_trigN1 (x : ℝ) : HasDerivAt trigN1 (3 * x * (Real.sin x - x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 3 * Real.sin y) (3 * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul 3
  have h2 : HasDerivAt (fun y : ℝ => 3 * y * Real.cos y)
      (3 * 1 * Real.cos x + 3 * x * -Real.sin x) x :=
    ((hasDerivAt_id' x).const_mul 3).mul (Real.hasDerivAt_cos x)
  have h : HasDerivAt (fun y : ℝ => 3 * Real.sin y - 3 * y * Real.cos y - y * y * y)
      (3 * Real.cos x - (3 * 1 * Real.cos x + 3 * x * -Real.sin x) - 3 * (x * x)) x :=
    (h1.sub h2).sub (hasDerivAt_id_pow3 x)
  have hfun : trigN1 = fun y : ℝ => 3 * Real.sin y - 3 * y * Real.cos y - y * y * y := rfl
  rw [hfun]
  exact h.congr_deriv (by ring)

theorem trigN1_zero : trigN1 0 = 0 := by
  show 3 * Real.sin 0 - 3 * 0 * Real.cos 0 - 0 * 0 * 0 = (0 : ℝ)
  rw [Real.sin_zero]
  ring

/-- `N₁(x) ≤ 0` for `x ≥ 0`. -/
theorem trigN1_nonpos {x : ℝ} (hx : 0 ≤ x) : trigN1 x ≤ 0 := by
  have hn : ∀ y : ℝ, 0 < y → 3 * y * (Real.sin y - y) ≤ 0 := by
    intro y hy
    have h1 : Real.sin y - y ≤ 0 := by linarith [Real.sin_le hy.le]
    have h2 : (0 : ℝ) ≤ 3 * y := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos h2 h1
  exact nonpos_of_hasDerivAt_nonpos (f := trigN1) (f' := fun y : ℝ => 3 * y * (Real.sin y - y))
    hasDerivAt_trigN1 hn trigN1_zero hx

theorem hasDerivAt_trigN1_aux (x : ℝ) :
    HasDerivAt (fun y : ℝ => -trigN1 y - y * y * y * y * y / 10)
      (-(3 * x * (Real.sin x - x + x * x * x / 6))) x := by
  have h : HasDerivAt (fun y : ℝ => -trigN1 y - y * y * y * y * y / 10)
      (-(3 * x * (Real.sin x - x)) - 5 * (x * x * x * x) / 10) x :=
    (hasDerivAt_trigN1 x).neg.sub ((hasDerivAt_id_pow5 x).div_const 10)
  exact h.congr_deriv (by ring)

/-- `-x⁵/10 ≤ N₁(x)` for `x ≥ 0`. -/
theorem trigN1_lower {x : ℝ} (hx : 0 ≤ x) : -(x * x * x * x * x / 10) ≤ trigN1 x := by
  have hn : ∀ y : ℝ, 0 < y → -(3 * y * (Real.sin y - y + y * y * y / 6)) ≤ 0 := by
    intro y hy
    have hs : y - y ^ 3 / 6 ≤ Real.sin y := Real.sin_ge_sub_cube hy.le
    have e : y ^ 3 = y * y * y := by ring
    rw [e] at hs
    have h1 : 0 ≤ Real.sin y - y + y * y * y / 6 := by linarith
    have h2 : (0 : ℝ) ≤ 3 * y := by linarith
    have h3 : 0 ≤ 3 * y * (Real.sin y - y + y * y * y / 6) := mul_nonneg h2 h1
    linarith
  have h0 : -trigN1 0 - 0 * 0 * 0 * 0 * 0 / 10 = (0 : ℝ) := by
    rw [trigN1_zero]
    ring
  have h : -trigN1 x - x * x * x * x * x / 10 ≤ 0 :=
    nonpos_of_hasDerivAt_nonpos (f := fun y : ℝ => -trigN1 y - y * y * y * y * y / 10)
      (f' := fun y : ℝ => -(3 * y * (Real.sin y - y + y * y * y / 6)))
      hasDerivAt_trigN1_aux hn h0 hx
  linarith

/-- `N' = 5x N₁`. -/
theorem hasDerivAt_trigN (x : ℝ) : HasDerivAt trigN (5 * x * trigN1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => 45 * Real.sin y) (45 * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul 45
  have h2 : HasDerivAt (fun y : ℝ => 45 * y * Real.cos y)
      (45 * 1 * Real.cos x + 45 * x * -Real.sin x) x :=
    ((hasDerivAt_id' x).const_mul 45).mul (Real.hasDerivAt_cos x)
  have h3 : HasDerivAt (fun y : ℝ => 15 * (y * y) * Real.sin y)
      (15 * (2 * x) * Real.sin x + 15 * (x * x) * Real.cos x) x :=
    ((hasDerivAt_id_pow2 x).const_mul 15).mul (Real.hasDerivAt_sin x)
  have h : HasDerivAt
      (fun y : ℝ => 45 * Real.sin y - 45 * y * Real.cos y - 15 * (y * y) * Real.sin y
        - y * y * y * y * y)
      (45 * Real.cos x - (45 * 1 * Real.cos x + 45 * x * -Real.sin x)
        - (15 * (2 * x) * Real.sin x + 15 * (x * x) * Real.cos x)
        - 5 * (x * x * x * x)) x :=
    ((h1.sub h2).sub h3).sub (hasDerivAt_id_pow5 x)
  have hfun : trigN = fun y : ℝ => 45 * Real.sin y - 45 * y * Real.cos y
      - 15 * (y * y) * Real.sin y - y * y * y * y * y := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  show 45 * Real.cos x - (45 * 1 * Real.cos x + 45 * x * -Real.sin x)
      - (15 * (2 * x) * Real.sin x + 15 * (x * x) * Real.cos x) - 5 * (x * x * x * x)
    = 5 * x * (3 * Real.sin x - 3 * x * Real.cos x - x * x * x)
  ring

theorem trigN_zero : trigN 0 = 0 := by
  show 45 * Real.sin 0 - 45 * 0 * Real.cos 0 - 15 * (0 * 0) * Real.sin 0 - 0 * 0 * 0 * 0 * 0
    = (0 : ℝ)
  rw [Real.sin_zero]
  ring

/-- `N(x) ≤ 0` for `x ≥ 0`. -/
theorem trigN_nonpos {x : ℝ} (hx : 0 ≤ x) : trigN x ≤ 0 := by
  have hn : ∀ y : ℝ, 0 < y → 5 * y * trigN1 y ≤ 0 := by
    intro y hy
    have h2 : (0 : ℝ) ≤ 5 * y := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos h2 (trigN1_nonpos hy.le)
  exact nonpos_of_hasDerivAt_nonpos (f := trigN) (f' := fun y : ℝ => 5 * y * trigN1 y)
    hasDerivAt_trigN hn trigN_zero hx

theorem hasDerivAt_trigN_aux (x : ℝ) :
    HasDerivAt (fun y : ℝ => -trigN y - y * y * y * y * y * y * y / 14)
      (-(5 * x * (trigN1 x + x * x * x * x * x / 10))) x := by
  have h : HasDerivAt (fun y : ℝ => -trigN y - y * y * y * y * y * y * y / 14)
      (-(5 * x * trigN1 x) - 7 * (x * x * x * x * x * x) / 14) x :=
    (hasDerivAt_trigN x).neg.sub ((hasDerivAt_id_pow7 x).div_const 14)
  exact h.congr_deriv (by ring)

/-- `-x⁷/14 ≤ N(x)` for `x ≥ 0`. -/
theorem trigN_lower {x : ℝ} (hx : 0 ≤ x) : -(x * x * x * x * x * x * x / 14) ≤ trigN x := by
  have hn : ∀ y : ℝ, 0 < y → -(5 * y * (trigN1 y + y * y * y * y * y / 10)) ≤ 0 := by
    intro y hy
    have h1 : 0 ≤ trigN1 y + y * y * y * y * y / 10 := by linarith [trigN1_lower hy.le]
    have h2 : (0 : ℝ) ≤ 5 * y := by linarith
    have h3 : 0 ≤ 5 * y * (trigN1 y + y * y * y * y * y / 10) := mul_nonneg h2 h1
    linarith
  have h0 : -trigN 0 - 0 * 0 * 0 * 0 * 0 * 0 * 0 / 14 = (0 : ℝ) := by
    rw [trigN_zero]
    ring
  have h : -trigN x - x * x * x * x * x * x * x / 14 ≤ 0 :=
    nonpos_of_hasDerivAt_nonpos (f := fun y : ℝ => -trigN y - y * y * y * y * y * y * y / 14)
      (f' := fun y : ℝ => -(5 * y * (trigN1 y + y * y * y * y * y / 10)))
      hasDerivAt_trigN_aux hn h0 hx
  linarith

/-! ## The expression of the sub-rung -/

/-- For `s ≠ 0` the expression of `RungA2T` is `(32/π⁵) N(πs/2)/s⁶`. -/
theorem trigT_eq {s x : ℝ} (hs : s ≠ 0) (hx : x = π * s / 2) :
    1440 / π ^ 5 * Real.sin (π * s / 2) / s ^ 6 - 720 / π ^ 4 * Real.cos (π * s / 2) / s ^ 5
        - 120 / π ^ 3 * Real.sin (π * s / 2) / s ^ 4 - 1 / s
      = 32 * π⁻¹ ^ 5 * s⁻¹ ^ 6 * trigN x := by
  subst hx
  have hp : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  have hs' : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  unfold trigN
  linear_combination
    (720 * π⁻¹ ^ 4 * s⁻¹ ^ 5 * Real.cos (π * s / 2) * (s * s⁻¹)
        + 120 * π⁻¹ ^ 3 * s⁻¹ ^ 4 * Real.sin (π * s / 2) * (π * π⁻¹ + 1) * (s * s⁻¹) ^ 2
        + s⁻¹ * ((π * π⁻¹) ^ 4 + (π * π⁻¹) ^ 3 + (π * π⁻¹) ^ 2 + π * π⁻¹ + 1) * (s * s⁻¹) ^ 5)
      * hp
    + (720 * π⁻¹ ^ 4 * s⁻¹ ^ 5 * Real.cos (π * s / 2)
        + 120 * π⁻¹ ^ 3 * s⁻¹ ^ 4 * Real.sin (π * s / 2) * (s * s⁻¹ + 1)
        + s⁻¹ * ((s * s⁻¹) ^ 4 + (s * s⁻¹) ^ 3 + (s * s⁻¹) ^ 2 + s * s⁻¹ + 1)) * hs'

/-- The lower bound `-(x⁷/14)` for `N`, carried to the expression: it is `-(π²/56) s`. -/
theorem trigT_lower_eq {s x : ℝ} (hs : s ≠ 0) (hx : x = π * s / 2) :
    32 * π⁻¹ ^ 5 * s⁻¹ ^ 6 * (-(x * x * x * x * x * x * x / 14)) = -(π ^ 2 / 56 * s) := by
  subst hx
  have hp : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  have hs' : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  linear_combination
    (-(π ^ 2 / 56 * s) * ((π * π⁻¹) ^ 4 + (π * π⁻¹) ^ 3 + (π * π⁻¹) ^ 2 + π * π⁻¹ + 1)
        * (s * s⁻¹) ^ 6) * hp
    - (π ^ 2 / 56 * s) * ((s * s⁻¹) ^ 5 + (s * s⁻¹) ^ 4 + (s * s⁻¹) ^ 3 + (s * s⁻¹) ^ 2
        + s * s⁻¹ + 1) * hs'

/-- For `s > 0` the expression of `RungA2T` lies in `[-(π²/56) s, 0]`. -/
theorem trigT_abs_le {s : ℝ} (hs : 0 < s) :
    ‖1440 / π ^ 5 * Real.sin (π * s / 2) / s ^ 6 - 720 / π ^ 4 * Real.cos (π * s / 2) / s ^ 5
        - 120 / π ^ 3 * Real.sin (π * s / 2) / s ^ 4 - 1 / s‖ ≤ π ^ 2 / 56 * s := by
  have hx : 0 ≤ π * s / 2 := div_nonneg (mul_nonneg Real.pi_pos.le hs.le) zero_le_two
  have hN0 : trigN (π * s / 2) ≤ 0 := trigN_nonpos hx
  have hN1 := trigN_lower hx
  have h32 : (0 : ℝ) ≤ 32 := by norm_num
  have hc : 0 ≤ 32 * π⁻¹ ^ 5 * s⁻¹ ^ 6 :=
    mul_nonneg (mul_nonneg h32 (pow_nonneg (inv_nonneg.mpr Real.pi_pos.le) 5))
      (pow_nonneg (inv_nonneg.mpr hs.le) 6)
  have hT := trigT_eq (x := π * s / 2) hs.ne' rfl
  have hup : 32 * π⁻¹ ^ 5 * s⁻¹ ^ 6 * trigN (π * s / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc hN0
  have hlo := mul_le_mul_of_nonneg_left hN1 hc
  rw [trigT_lower_eq (x := π * s / 2) hs.ne' rfl] at hlo
  have h56 : (0 : ℝ) ≤ 56 := by norm_num
  have hpos : 0 ≤ π ^ 2 / 56 * s := mul_nonneg (div_nonneg (sq_nonneg π) h56) hs.le
  rw [hT, Real.norm_eq_abs]
  exact abs_le.mpr ⟨hlo, le_trans hup hpos⟩

/-! ## The sub-rung -/

/-- **Sub-rung A2T**: the poles cancel. -/
theorem rungA2T : RungA2T := by
  unfold RungA2T
  have hlim : Filter.Tendsto (fun s : ℝ => π ^ 2 / 56 * s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
    have h : Filter.Tendsto (fun s : ℝ => π ^ 2 / 56 * s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (π ^ 2 / 56 * 0)) := tendsto_id_nhdsGT_zero.const_mul (π ^ 2 / 56)
    rw [mul_zero] at h
    exact h
  have hmem : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hmem] with s hs
  exact trigT_abs_le hs

/-- **The six-step theorem from the four remaining sub-rungs of A2 and Rung B.** -/
theorem rv6_of_A2RNMP_B (hR : RungA2R) (hN : RungA2N) (hM : RungA2M) (hP : RungA2P)
    (hB : RungB) : mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_A2sub_B hR hN hM hP rungA2T hB

end Tower.RV6
