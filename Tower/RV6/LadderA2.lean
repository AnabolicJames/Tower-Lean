import Mathlib
import Tower.RV6.Defs
import Tower.RV6.Ladder
import Tower.RV6.KZero
import Tower.RV6.RungA1

/-!
# Rung A2 cut into sub-rungs

`RungA2 : walkSide = 30 / π ^ 4 * R62` is derived here from five named propositions about a real
parameter `s > 0`.  **A sub-rung is a hypothesis.**  Nothing in this file proves a sub-rung; what is
proved is `rungA2_of_subrungs`: the five together imply `RungA2`.  Each sub-rung was checked
numerically from the definitions before being stated.

Notation: `mellU h s = ∫ h(e^u) e^{su} du` is the Mellin transform `∫₀^∞ h(t) t^{s-1} dt` in the
variable `u = log t`;  `N = mellN`, `M_{a,b} = mellM a b`, `P = mellP`;  `a₀ = a0 = log 2 + eulerW`.

| sub-rung | statement |
|---|---|
| `RungA2R` | for `0 < s < 1`: `N(s) = (12/π⁵) sin(πs/2) M₁,₅(s) - (30/π⁴) cos(πs/2) M₂,₄(s) - (20/π³) sin(πs/2) M₃,₃(s)` |
| `RungA2N` | `N(s) - 1/s → eulerW - (walkSide - log 2)` as `s → 0+` |
| `RungA2M` | `e^{-a₀ s} M_{a,b}(s) - b!/s^{b+1}` is bounded on `0 < s ≤ 1` for `(a,b) = (1,5), (3,3), (3,5)` |
| `RungA2P` | for `0 < s ≤ 1`: `M₂,₄(s) = (8/5) P(s) + (s/5) M₃,₅(s)`; and `(8/5) P(s) → R62` as `s → 0+` |
| `RungA2T` | `(1440/π⁵) sin(πs/2)/s⁶ - (720/π⁴) cos(πs/2)/s⁵ - (120/π³) sin(πs/2)/s⁴ - 1/s → 0` as `s → 0+` |

The argument: multiply `RungA2R` by `e^{-a₀ s}` and subtract `1/s`.  The left side is
`e^{-a₀ s}(N(s) - 1/s) + (e^{-a₀ s} - 1)/s → eulerW - (walkSide - log 2) - a₀ = -walkSide`.  On the
right the poles cancel (`RungA2T`), the bounded remainders are multiplied by `sin(πs/2)` or by `s`,
and what is left tends to `-(30/π⁴) R62`.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## Definitions -/

/-- The Mellin transform `∫₀^∞ h(t) t^{s-1} dt`, written in the variable `u = log t`. -/
noncomputable def mellU (h : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u : ℝ, h (Real.exp u) * Real.exp (s * u)

/-- `a₀ = log 2 + eulerW`:  `K₀(t) = a₀ - log t + O(t)` as `t → 0` (`abs_besselK0_add_log_le`). -/
noncomputable def a0 : ℝ := Real.log 2 + eulerW

/-- `N(s) = ∫₀^∞ J₀(t)⁶ t^{s-1} dt`. -/
noncomputable def mellN (s : ℝ) : ℝ := mellU (fun t => besselJ0 t ^ 6) s

/-- `M_{a,b}(s) = ∫₀^∞ I₀(t)^a K₀(t)^b t^{s-1} dt`. -/
noncomputable def mellM (a b : ℕ) (s : ℝ) : ℝ :=
  mellU (fun t => besselI0 t ^ a * besselK0 t ^ b) s

/-- `P(s) = ∫₀^∞ I₀(t)² I₁(t) K₀(t)⁵ t^s dt`. -/
noncomputable def mellP (s : ℝ) : ℝ :=
  mellU (fun t => besselI0 t ^ 2 * besselI1 t * besselK0 t ^ 5) (s + 1)

/-! ## The sub-rungs -/

/-- **Sub-rung A2R** (rotation of the contour to the imaginary axis). -/
def RungA2R : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    mellN s = 12 / π ^ 5 * Real.sin (π * s / 2) * mellM 1 5 s
      - 30 / π ^ 4 * Real.cos (π * s / 2) * mellM 2 4 s
      - 20 / π ^ 3 * Real.sin (π * s / 2) * mellM 3 3 s

/-- **Sub-rung A2N** (the walk side near `s = 0`). -/
def RungA2N : Prop :=
  Filter.Tendsto (fun s : ℝ => mellN s - 1 / s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds (eulerW - (walkSide - Real.log 2)))

/-- **Sub-rung A2M** (the poles of the Bessel moments at `s = 0`). -/
def RungA2M : Prop :=
  (∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 →
      |Real.exp (-a0 * s) * mellM 1 5 s - 120 / s ^ 6| ≤ C) ∧
  (∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 →
      |Real.exp (-a0 * s) * mellM 3 3 s - 6 / s ^ 4| ≤ C) ∧
  (∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 →
      |Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6| ≤ C)

/-- **Sub-rung A2P** (integration by parts with the Wronskian `I₀ K₁ + I₁ K₀ = 1/t`). -/
def RungA2P : Prop :=
  (∀ s : ℝ, 0 < s → s ≤ 1 → mellM 2 4 s = 8 / 5 * mellP s + s / 5 * mellM 3 5 s) ∧
  Filter.Tendsto (fun s : ℝ => 8 / 5 * mellP s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds R62)

/-- **Sub-rung A2T** (the trigonometric cancellation of the poles). -/
def RungA2T : Prop :=
  Filter.Tendsto
    (fun s : ℝ => 1440 / π ^ 5 * Real.sin (π * s / 2) / s ^ 6
      - 720 / π ^ 4 * Real.cos (π * s / 2) / s ^ 5
      - 120 / π ^ 3 * Real.sin (π * s / 2) / s ^ 4 - 1 / s)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)

/-! ## Elementary limits at `0+` -/

/-- `e^{-a s} → 1` as `s → 0+`. -/
theorem tendsto_exp_neg_mul_zero (a : ℝ) :
    Filter.Tendsto (fun s : ℝ => Real.exp (-a * s)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 1) := by
  have hc : Continuous (fun s : ℝ => Real.exp (-a * s)) := by fun_prop
  have ht : Filter.Tendsto (fun s : ℝ => Real.exp (-a * s)) (nhds 0)
      (nhds (Real.exp (-a * 0))) := hc.tendsto 0
  rw [mul_zero, Real.exp_zero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- `(e^{-a s} - 1)/s → -a` as `s → 0+`. -/
theorem tendsto_exp_neg_mul_slope (a : ℝ) :
    Filter.Tendsto (fun s : ℝ => (Real.exp (-a * s) - 1) / s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-a)) := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-a * y)) (Real.exp (-a * 0) * (-a * 1)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_mul (-a)).exp
  have he : Real.exp (-a * 0) * (-a * 1) = -a := by
    rw [mul_zero, Real.exp_zero]
    ring
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-a * y)) (-a) 0 := h1.congr_deriv he
  have h3 : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (Real.exp (-a * (0 + t)) - Real.exp (-a * 0)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-a)) := h2.tendsto_slope_zero_right
  have hfun : (fun t : ℝ => t⁻¹ • (Real.exp (-a * (0 + t)) - Real.exp (-a * 0)))
      = fun s : ℝ => (Real.exp (-a * s) - 1) / s := by
    funext t
    show t⁻¹ • (Real.exp (-a * (0 + t)) - Real.exp (-a * 0)) = (Real.exp (-a * t) - 1) / t
    rw [zero_add, mul_zero, Real.exp_zero, smul_eq_mul]
    ring
  rw [hfun] at h3
  exact h3

/-- `sin(πs/2) → 0` as `s → 0+`. -/
theorem tendsto_sin_half_pi :
    Filter.Tendsto (fun s : ℝ => Real.sin (π * s / 2)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
  have hc : Continuous (fun s : ℝ => Real.sin (π * s / 2)) := by fun_prop
  have ht : Filter.Tendsto (fun s : ℝ => Real.sin (π * s / 2)) (nhds 0)
      (nhds (Real.sin (π * 0 / 2))) := hc.tendsto 0
  rw [mul_zero, zero_div, Real.sin_zero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- `cos(πs/2) → 1` as `s → 0+`. -/
theorem tendsto_cos_half_pi :
    Filter.Tendsto (fun s : ℝ => Real.cos (π * s / 2)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 1) := by
  have hc : Continuous (fun s : ℝ => Real.cos (π * s / 2)) := by fun_prop
  have ht : Filter.Tendsto (fun s : ℝ => Real.cos (π * s / 2)) (nhds 0)
      (nhds (Real.cos (π * 0 / 2))) := hc.tendsto 0
  rw [mul_zero, zero_div, Real.cos_zero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- `s → 0` as `s → 0+`. -/
theorem tendsto_id_nhdsGT_zero :
    Filter.Tendsto (fun s : ℝ => s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h : Filter.Tendsto (fun s : ℝ => s) (nhds 0) (nhds 0) := Filter.tendsto_id
  exact h.mono_left nhdsWithin_le_nhds

/-- A function tending to `0` at `0+` times a function bounded on `(0, 1]` tends to `0`. -/
theorem tendsto_mul_bounded_zero {f g : ℝ → ℝ} {C : ℝ}
    (hf : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hg : ∀ s : ℝ, 0 < s → s ≤ 1 → |g s| ≤ C) :
    Filter.Tendsto (fun s : ℝ => f s * g s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖f s * g s‖ ≤ |f s| * C := by
    filter_upwards [hmem] with s hs
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg s hs.1 hs.2.le) (abs_nonneg (f s))
  have h1 : Filter.Tendsto (fun s : ℝ => |f s|) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds |(0 : ℝ)|) := hf.abs
  have h2 : Filter.Tendsto (fun s : ℝ => |f s| * C) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (|(0 : ℝ)| * C)) := h1.mul_const C
  have h0 : |(0 : ℝ)| * C = 0 := by rw [abs_zero, zero_mul]
  rw [h0] at h2
  exact squeeze_zero_norm' hev h2

/-! ## The rotation formula with the poles split off -/

/-- For `0 < s < 1`: the rotation formula multiplied by `e^{-a₀ s}`, less `1/s`, regrouped as the
trigonometric expression of `RungA2T` plus terms each of which has a limit at `0+`. -/
theorem subrung_identity (hR : RungA2R) (hP : RungA2P) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.exp (-a0 * s) * (mellN s - 1 / s) + (Real.exp (-a0 * s) - 1) / s
      = (1440 / π ^ 5 * Real.sin (π * s / 2) / s ^ 6
          - 720 / π ^ 4 * Real.cos (π * s / 2) / s ^ 5
          - 120 / π ^ 3 * Real.sin (π * s / 2) / s ^ 4 - 1 / s)
        + 12 / π ^ 5 * (Real.sin (π * s / 2) * (Real.exp (-a0 * s) * mellM 1 5 s - 120 / s ^ 6))
        - 30 / π ^ 4 * (Real.cos (π * s / 2) * (Real.exp (-a0 * s) * (8 / 5 * mellP s)))
        - 6 / π ^ 4
            * (Real.cos (π * s / 2) * (s * (Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6)))
        - 20 / π ^ 3 * (Real.sin (π * s / 2) * (Real.exp (-a0 * s) * mellM 3 3 s - 6 / s ^ 4)) := by
  unfold RungA2R at hR
  unfold RungA2P at hP
  have h1 := hR s hs0 hs1
  have h2 := hP.1 s hs0 hs1.le
  have hs : s * s⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hs0)
  linear_combination Real.exp (-a0 * s) * h1
    - 30 * π⁻¹ ^ 4 * Real.cos (π * s / 2) * Real.exp (-a0 * s) * h2
    - 720 * π⁻¹ ^ 4 * Real.cos (π * s / 2) * s⁻¹ ^ 5 * hs

/-! ## The sub-rungs imply Rung A2 -/

/-- **Rung A2 from its five sub-rungs.** -/
theorem rungA2_of_subrungs (hR : RungA2R) (hN : RungA2N) (hM : RungA2M) (hP : RungA2P)
    (hT : RungA2T) : RungA2 := by
  have hPl : Filter.Tendsto (fun s : ℝ => 8 / 5 * mellP s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds R62) := by
    unfold RungA2P at hP
    exact hP.2
  unfold RungA2N at hN
  unfold RungA2T at hT
  unfold RungA2M at hM
  obtain ⟨⟨C15, h15⟩, ⟨C33, h33⟩, ⟨C35, h35⟩⟩ := hM
  have hE := tendsto_exp_neg_mul_zero a0
  -- the left side
  have hL1 : Filter.Tendsto (fun s : ℝ => Real.exp (-a0 * s) * (mellN s - 1 / s))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 * (eulerW - (walkSide - Real.log 2)))) :=
    hE.mul hN
  have hL : Filter.Tendsto
      (fun s : ℝ => Real.exp (-a0 * s) * (mellN s - 1 / s) + (Real.exp (-a0 * s) - 1) / s)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (1 * (eulerW - (walkSide - Real.log 2)) + -a0)) :=
    hL1.add (tendsto_exp_neg_mul_slope a0)
  -- the terms of the right side
  have hR1 : Filter.Tendsto
      (fun s : ℝ => Real.sin (π * s / 2) * (Real.exp (-a0 * s) * mellM 1 5 s - 120 / s ^ 6))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_mul_bounded_zero (f := fun s : ℝ => Real.sin (π * s / 2))
      (g := fun s : ℝ => Real.exp (-a0 * s) * mellM 1 5 s - 120 / s ^ 6) tendsto_sin_half_pi h15
  have hR2 : Filter.Tendsto
      (fun s : ℝ => Real.cos (π * s / 2) * (Real.exp (-a0 * s) * (8 / 5 * mellP s)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 * (1 * R62))) :=
    tendsto_cos_half_pi.mul (hE.mul hPl)
  have hR3 : Filter.Tendsto
      (fun s : ℝ => s * (Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_mul_bounded_zero (f := fun s : ℝ => s)
      (g := fun s : ℝ => Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6) tendsto_id_nhdsGT_zero h35
  have hR3' : Filter.Tendsto
      (fun s : ℝ =>
        Real.cos (π * s / 2) * (s * (Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 * 0)) :=
    tendsto_cos_half_pi.mul hR3
  have hR4 : Filter.Tendsto
      (fun s : ℝ => Real.sin (π * s / 2) * (Real.exp (-a0 * s) * mellM 3 3 s - 6 / s ^ 4))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_mul_bounded_zero (f := fun s : ℝ => Real.sin (π * s / 2))
      (g := fun s : ℝ => Real.exp (-a0 * s) * mellM 3 3 s - 6 / s ^ 4) tendsto_sin_half_pi h33
  -- the right side
  have hRt : Filter.Tendsto
      (fun s : ℝ =>
        (1440 / π ^ 5 * Real.sin (π * s / 2) / s ^ 6
          - 720 / π ^ 4 * Real.cos (π * s / 2) / s ^ 5
          - 120 / π ^ 3 * Real.sin (π * s / 2) / s ^ 4 - 1 / s)
        + 12 / π ^ 5 * (Real.sin (π * s / 2) * (Real.exp (-a0 * s) * mellM 1 5 s - 120 / s ^ 6))
        - 30 / π ^ 4 * (Real.cos (π * s / 2) * (Real.exp (-a0 * s) * (8 / 5 * mellP s)))
        - 6 / π ^ 4
            * (Real.cos (π * s / 2) * (s * (Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6)))
        - 20 / π ^ 3 * (Real.sin (π * s / 2) * (Real.exp (-a0 * s) * mellM 3 3 s - 6 / s ^ 4)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (0 + 12 / π ^ 5 * 0 - 30 / π ^ 4 * (1 * (1 * R62)) - 6 / π ^ 4 * (1 * 0)
        - 20 / π ^ 3 * 0)) :=
    (((hT.add (hR1.const_mul (12 / π ^ 5))).sub (hR2.const_mul (30 / π ^ 4))).sub
      (hR3'.const_mul (6 / π ^ 4))).sub (hR4.const_mul (20 / π ^ 3))
  -- the two sides agree on `(0, 1)`
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  have hev : Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun s : ℝ => Real.exp (-a0 * s) * (mellN s - 1 / s) + (Real.exp (-a0 * s) - 1) / s)
      (fun s : ℝ =>
        (1440 / π ^ 5 * Real.sin (π * s / 2) / s ^ 6
          - 720 / π ^ 4 * Real.cos (π * s / 2) / s ^ 5
          - 120 / π ^ 3 * Real.sin (π * s / 2) / s ^ 4 - 1 / s)
        + 12 / π ^ 5 * (Real.sin (π * s / 2) * (Real.exp (-a0 * s) * mellM 1 5 s - 120 / s ^ 6))
        - 30 / π ^ 4 * (Real.cos (π * s / 2) * (Real.exp (-a0 * s) * (8 / 5 * mellP s)))
        - 6 / π ^ 4
            * (Real.cos (π * s / 2) * (s * (Real.exp (-a0 * s) * mellM 3 5 s - 120 / s ^ 6)))
        - 20 / π ^ 3
            * (Real.sin (π * s / 2) * (Real.exp (-a0 * s) * mellM 3 3 s - 6 / s ^ 4))) := by
    filter_upwards [hmem] with s hs
    exact subrung_identity hR hP hs.1 hs.2
  have hEq : 1 * (eulerW - (walkSide - Real.log 2)) + -a0
      = 0 + 12 / π ^ 5 * 0 - 30 / π ^ 4 * (1 * (1 * R62)) - 6 / π ^ 4 * (1 * 0)
        - 20 / π ^ 3 * 0 :=
    tendsto_nhds_unique (Filter.Tendsto.congr' hev hL) hRt
  unfold a0 at hEq
  unfold RungA2
  linear_combination (-1 : ℝ) * hEq

/-- **The six-step theorem from the five sub-rungs of A2 and Rung B.** -/
theorem rv6_of_A2sub_B (hR : RungA2R) (hN : RungA2N) (hM : RungA2M) (hP : RungA2P)
    (hT : RungA2T) (hB : RungB) : mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_A2_B (rungA2_of_subrungs hR hN hM hP hT) hB

end Tower.RV6
