import Mathlib
import Tower.RV6.XMod

/-!
# Sub-rung BM reduced to Zhou's two parametrisations and one limit

With the change of variable `x = xm(y)` of `XMod.lean` (a decreasing `C¹` bijection of `(0, ∞)`
with `xm' = -(π/4) Pax xm`), Zhou's parametrisations of the two Bessel transforms

* `ZhouF : hjF (xm y) = (π²/16) Zax y`,   `ZhouG : ajG (xm y) = (π²/2) A1 y`   (`y > 0`)

turn the pairing into a modular integral (`pairS_eq_JS`, exact, for every real `s`):

`pairS s = (π⁵/16) ∫₀^∞ g₄(y) 𝒜₁(y) xm(y)^{-s} dy`,

because `(π/4) Pax · Zax · xm² = (π/4) Pax · 64 Uax = 2π g₄` (`xm_sq`, `g4_eq_UP`).  The pole is a
Gamma integral (`integral_exp_div_pow_six`, `pole_eq`):

`72/s⁵ = (π⁵/16) ∫₀^∞ e^{-πs/(6y)} / (162 y⁶) dy`.

So `RungBM` follows from `ZhouF`, `ZhouG` and the limit `LimBM` (`rungBM_of_zhou`), and the
six-step theorem from `RungBP` and these three (`rv6_of_zhou`).  **`ZhouF`, `ZhouG`, `LimBM` are
hypotheses here.**
-/

namespace Tower.RV6

open Real MeasureTheory

/-- Zhou's parametrisation of the Hankel transform of `I₀K₀³`. -/
def ZhouF : Prop := ∀ y : ℝ, 0 < y → hjF (xm y) = π ^ 2 / 16 * Zax y

/-- Zhou's parametrisation of the cumulative Hankel transform of `I₀²K₀²`. -/
def ZhouG : Prop := ∀ y : ℝ, 0 < y → ajG (xm y) = π ^ 2 / 2 * A1 y

/-- `∫₀^∞ g₄(y) 𝒜₁(y) x(y)^{-s} dy`. -/
noncomputable def JS (s : ℝ) : ℝ := ∫ y in Set.Ioi (0 : ℝ), g4 y * A1 y * xm y ^ (-s)

/-- `∫₀^∞ e^{-πs/(6y)} / (162 y⁶) dy`. -/
noncomputable def poleS (s : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6)

/-- The limit left on the modular side: `JS s - poleS s → D₀₁` as `s → 0+`. -/
def LimBM : Prop :=
  Filter.Tendsto (fun s : ℝ => JS s - poleS s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds D01)

/-- **The pairing as a modular integral** (exact, for every `s`). -/
theorem pairS_eq_JS (hF : ZhouF) (hG : ZhouG) (s : ℝ) : pairS s = π ^ 5 / 16 * JS s := by
  have hderiv : ∀ y ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt xm (-(π / 4) * Pax y * xm y) (Set.Ioi 0) y :=
    fun y hy => (hasDerivAt_xm (Set.mem_Ioi.mp hy)).hasDerivWithinAt
  have hcv := integral_image_eq_integral_abs_deriv_smul
    (f' := fun y : ℝ => -(π / 4) * Pax y * xm y) measurableSet_Ioi hderiv strictAntiOn_xm.injOn
    (fun x : ℝ => hjF x * ajG x * x ^ (1 - s))
  rw [image_xm] at hcv
  simp only [smul_eq_mul] at hcv
  have hcv' : ∫ x in Set.Ioi (0 : ℝ), hjF x * ajG x * x ^ (1 - s)
      = ∫ y in Set.Ioi (0 : ℝ),
          |-(π / 4) * Pax y * xm y| * (hjF (xm y) * ajG (xm y) * xm y ^ (1 - s)) := hcv
  unfold pairS JS
  rw [hcv', ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  have hy0 : 0 < y := Set.mem_Ioi.mp hy
  show |-(π / 4) * Pax y * xm y| * (hjF (xm y) * ajG (xm y) * xm y ^ (1 - s))
    = π ^ 5 / 16 * (g4 y * A1 y * xm y ^ (-s))
  have hneg : -(π / 4) * Pax y * xm y < 0 := by
    have hp := mul_pos (mul_pos Real.pi_pos (Pax_pos hy0)) (xm_pos y)
    nlinarith
  have hx2 : xm y ^ 2 * Zax y = 64 * Uax y := by
    rw [xm_sq hy0]
    exact div_mul_cancel₀ _ (Zax_pos hy0).ne'
  have hr : xm y ^ (1 - s) = xm y * xm y ^ (-s) := by
    rw [show (1 : ℝ) - s = 1 + -s by ring, Real.rpow_add (xm_pos y), Real.rpow_one]
  rw [abs_of_neg hneg, hF y hy0, hG y hy0, hr, g4_eq_UP hy0]
  linear_combination (π ^ 5 / 128 * Pax y * A1 y * xm y ^ (-s)) * hx2

/-! ## The pole -/

theorem image_inv_Ioi_zero : (fun u : ℝ => u⁻¹) '' Set.Ioi 0 = Set.Ioi 0 := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Set.mem_Ioi.mpr (inv_pos.mpr (Set.mem_Ioi.mp hu))
  · intro hv
    refine ⟨v⁻¹, Set.mem_Ioi.mpr (inv_pos.mpr (Set.mem_Ioi.mp hv)), ?_⟩
    show v⁻¹⁻¹ = v
    exact inv_inv v

/-- `∫₀^∞ e^{-a/y} / y⁶ dy = 24/a⁵` (`y = 1/u`, then `∫₀^∞ u⁴ e^{-au} du = 4!/a⁵`). -/
theorem integral_exp_div_pow_six {a : ℝ} (ha : 0 < a) :
    ∫ y in Set.Ioi (0 : ℝ), Real.exp (-(a / y)) / y ^ 6 = 24 / a ^ 5 := by
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => u⁻¹) (-(u ^ 2)⁻¹) (Set.Ioi 0) u :=
    fun u hu => (hasDerivAt_inv (Set.mem_Ioi.mp hu).ne').hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => u⁻¹) (Set.Ioi 0) := fun u _ v _ h => inv_injective h
  have hcv := integral_image_eq_integral_abs_deriv_smul
    (f' := fun u : ℝ => -(u ^ 2)⁻¹) measurableSet_Ioi hderiv hinj
    (fun y : ℝ => Real.exp (-(a / y)) / y ^ 6)
  rw [image_inv_Ioi_zero] at hcv
  simp only [smul_eq_mul] at hcv
  have hcv' : ∫ y in Set.Ioi (0 : ℝ), Real.exp (-(a / y)) / y ^ 6
      = ∫ u in Set.Ioi (0 : ℝ), |-(u ^ 2)⁻¹| * (Real.exp (-(a / u⁻¹)) / u⁻¹ ^ 6) := hcv
  have hm := integral_exp_mul_pow ha 4
  have e : (24 : ℝ) / a ^ 5 = ((4 : ℕ).factorial : ℝ) / a ^ (4 + 1) := by
    norm_num [Nat.factorial]
  rw [hcv', e, ← hm]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu0 : 0 < u := Set.mem_Ioi.mp hu
  show |-(u ^ 2)⁻¹| * (Real.exp (-(a / u⁻¹)) / u⁻¹ ^ 6) = Real.exp (-(a * u)) * u ^ 4
  have h1 : a / u⁻¹ = a * u := div_inv_eq_mul a u
  have hinv : u ^ 2 * (u ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_pos hu0 2).ne'
  rw [abs_neg, abs_of_pos (inv_pos.mpr (pow_pos hu0 2)), h1, inv_pow, div_inv_eq_mul]
  linear_combination (Real.exp (-(a * u)) * u ^ 4) * hinv

/-- `72/s⁵ = (π⁵/16) ∫₀^∞ e^{-πs/(6y)} / (162 y⁶) dy` for `s > 0`. -/
theorem pole_eq {s : ℝ} (hs : 0 < s) : 72 / s ^ 5 = π ^ 5 / 16 * poleS s := by
  have ha : 0 < π * s / 6 := div_pos (mul_pos Real.pi_pos hs) (by norm_num)
  have h := integral_exp_div_pow_six ha
  have hc : poleS s
      = 1 / 162 * ∫ y in Set.Ioi (0 : ℝ), Real.exp (-(π * s / 6 / y)) / y ^ 6 := by
    unfold poleS
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    show Real.exp (-(π * s / (6 * y))) / (162 * y ^ 6)
      = 1 / 162 * (Real.exp (-(π * s / 6 / y)) / y ^ 6)
    have e : π * s / (6 * y) = π * s / 6 / y := by rw [div_div]
    rw [e]
    ring
  rw [hc, h]
  have hp5 : π ^ 5 * (π ^ 5)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 5 Real.pi_ne_zero)
  linear_combination (-(72 : ℝ) * (s ^ 5)⁻¹) * hp5

/-! ## The reduction -/

/-- **`RungBM` from Zhou's parametrisations and the limit `LimBM`.** -/
theorem rungBM_of_zhou (hF : ZhouF) (hG : ZhouG) (hL : LimBM) : RungBM := by
  unfold RungBM
  unfold LimBM at hL
  have h2 : Filter.Tendsto (fun s : ℝ => π ^ 5 / 16 * (JS s - poleS s))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (π ^ 5 / 16 * D01)) := hL.const_mul (π ^ 5 / 16)
  refine h2.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  have hs0 : 0 < s := Set.mem_Ioi.mp hs
  show π ^ 5 / 16 * (JS s - poleS s) = pairS s - 72 / s ^ 5
  rw [pairS_eq_JS hF hG s, pole_eq hs0]
  ring

/-- **The six-step theorem from `RungBP`, Zhou's two parametrisations and `LimBM`.** -/
theorem rv6_of_zhou (hP : RungBP) (hF : ZhouF) (hG : ZhouG) (hL : LimBM) :
    mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_PM hP (rungBM_of_zhou hF hG hL)

end Tower.RV6
