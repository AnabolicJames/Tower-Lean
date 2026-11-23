import Mathlib
import Tower.RV6.QTail

/-!
# `Zax` and `Uax` are exponentials of explicit `q`-series

With `qb y = ∑ (σ₁(n)/n) e^{-2πny}` (this is `-∑ log(1 - qⁿ)`, but no logarithm or product
is used here) put

* `lgZ y = -4 qb(y) + 2 qb(2y) - 4 qb(3y) + 2 qb(6y)`,
* `lgU y = -2πy + 2 qb(y) - 4 qb(2y) + 2 qb(3y) - 4 qb(6y)`.

Then for `y > 0`

* `Zax_eq_exp : Zax y = exp (lgZ y)`  and  `Uax_eq_exp : Uax y = exp (lgU y)`,

which are the eta quotients `η(τ)⁴η(3τ)⁴/(η(2τ)²η(6τ)²)` and
`η(2τ)⁴η(6τ)⁴/(η(τ)²η(3τ)²)` at `τ = iy`.  In particular `Zax_pos`, `Uax_pos`.

Proof.  `lgZ' = -2π Eax` and `lgU' = -2π (Eax + Pax/4)` (`hasDerivAt_lgZ`, `hasDerivAt_lgU`;
termwise differentiation of `qb` and linear algebra).  By `hasDerivAt_Zax`, `hasDerivAt_Uax` of
`ModAxis.lean` the functions `Zax · exp(-lgZ)` and `Uax · exp(-lgU)` have derivative `0` on
`(0, ∞)`, and they tend to `1` at `+∞` (`tendsto_Zax_atTop`, `tendsto_exp_mul_Uax_atTop`: the
coefficient of `q` in `Uax` is `σ₁(1) = 1`).
-/

namespace Tower.RV6

open Real

/-! ## The series `∑ (σ₁(n)/n) qⁿ` -/

/-- `σ₁(n)/n` (and `0` at `n = 0`). -/
noncomputable def sigq (n : ℕ) : ℝ := sig 1 n / (n : ℝ)

theorem sigq_zero : sigq 0 = 0 := by
  unfold sigq
  rw [Nat.cast_zero, div_zero]

theorem nat_mul_sigq (n : ℕ) : (n : ℝ) * sigq n = sig 1 n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, sigq_zero, sig_zero, Nat.cast_zero, mul_zero]
  · have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
    have hinv : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hne
    unfold sigq
    rw [div_eq_mul_inv]
    linear_combination (sig 1 n) * hinv

theorem sigq_abs_le (n : ℕ) : |sigq n| ≤ 1 * (n : ℝ) ^ (1 + 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, sigq_zero, abs_zero, Nat.cast_zero]
    exact mul_nonneg zero_le_one (pow_nonneg (le_refl 0) _)
  · have hn : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.succ_le_of_lt h)
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn
    unfold sigq
    rw [abs_div, abs_of_pos hn0]
    exact le_trans (div_le_self (abs_nonneg _) hn) (sig_abs_le 1 n)

theorem polyBdd_sigq : PolyBdd sigq :=
  ⟨1, 1 + 1, zero_le_one, Nat.le_add_left 1 1, sigq_abs_le⟩

/-- `qb y = ∑ (σ₁(n)/n) e^{-2πny}`. -/
noncomputable def qb (y : ℝ) : ℝ := qa sigq y

/-- `d/dy qb(y) = -(π/12)(1 - E₂(iy))`. -/
theorem hasDerivAt_qb {y : ℝ} (hy : 0 < y) :
    HasDerivAt qb (-(π / 12) * (1 - E2im y)) y := by
  have h := polyBdd_hasDerivAt polyBdd_sigq hy
  have e0 : qa (fun n : ℕ => (n : ℝ) * sigq n) y = qa (sig 1) y :=
    congrArg (fun C : ℕ → ℝ => qa C y) (funext nat_mul_sigq)
  have e : -(2 * π) * qa (fun n : ℕ => (n : ℝ) * sigq n) y
      = -(π / 12) * (1 - E2im y) := by
    rw [e0, E2im_eq_qa hy]
    ring
  have h2 : HasDerivAt qb (-(2 * π) * qa (fun n : ℕ => (n : ℝ) * sigq n) y) y := h
  exact h2.congr_deriv e

/-- The derivative of `qb (d y)` in `y`. -/
noncomputable def dQ (d y : ℝ) : ℝ := -(π * d / 12) * (1 - E2im (d * y))

theorem hasDerivAt_qb_mul (d : ℝ) (hd : 0 < d) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => qb (d * t)) (dQ d y) y := by
  have h0 := hasDerivAt_qb (mul_pos hd hy)
  have hlin : HasDerivAt (fun t : ℝ => d * t) (d * 1) y := (hasDerivAt_id' y).const_mul d
  have hc := HasDerivAt.comp y h0 hlin
  have e : -(π / 12) * (1 - E2im (d * y)) * (d * 1)
      = -(π * d / 12) * (1 - E2im (d * y)) := by ring
  have hc2 := hc.congr_deriv e
  exact hc2

/-! ## The two exponents -/

/-- `log Z(iy)`. -/
noncomputable def lgZ (y : ℝ) : ℝ :=
  -4 * qb y + 2 * qb (2 * y) + -4 * qb (3 * y) + 2 * qb (6 * y)

/-- `log U(iy) + 2πy`. -/
noncomputable def lgUr (y : ℝ) : ℝ :=
  2 * qb y + -4 * qb (2 * y) + 2 * qb (3 * y) + -4 * qb (6 * y)

/-- `log U(iy)`. -/
noncomputable def lgU (y : ℝ) : ℝ := -(2 * π * y) + lgUr y

/-- `lgZ' = -2π Eax`. -/
theorem hasDerivAt_lgZ {y : ℝ} (hy : 0 < y) : HasDerivAt lgZ (-(2 * π) * Eax y) y := by
  have h1 := hasDerivAt_qb hy
  have h2 := hasDerivAt_qb_mul 2 (by norm_num) hy
  have h3 := hasDerivAt_qb_mul 3 (by norm_num) hy
  have h6 := hasDerivAt_qb_mul 6 (by norm_num) hy
  have k0 := hasDerivAt_lin4 (-4) 2 (-4) 2 h1 h2 h3 h6
  have k : HasDerivAt lgZ
      (-4 * (-(π / 12) * (1 - E2im y)) + 2 * dQ 2 y + -4 * dQ 3 y + 2 * dQ 6 y) y := k0
  have e : -4 * (-(π / 12) * (1 - E2im y)) + 2 * dQ 2 y + -4 * dQ 3 y + 2 * dQ 6 y
      = -(2 * π) * Eax y := by
    unfold dQ Eax
    ring
  exact k.congr_deriv e

/-- `lgU' = -2π (Eax + Pax/4)`. -/
theorem hasDerivAt_lgU {y : ℝ} (hy : 0 < y) :
    HasDerivAt lgU (-(2 * π) * (Eax y + Pax y / 4)) y := by
  have h1 := hasDerivAt_qb hy
  have h2 := hasDerivAt_qb_mul 2 (by norm_num) hy
  have h3 := hasDerivAt_qb_mul 3 (by norm_num) hy
  have h6 := hasDerivAt_qb_mul 6 (by norm_num) hy
  have k0 := hasDerivAt_lin4 2 (-4) 2 (-4) h1 h2 h3 h6
  have kr : HasDerivAt lgUr
      (2 * (-(π / 12) * (1 - E2im y)) + -4 * dQ 2 y + 2 * dQ 3 y + -4 * dQ 6 y) y := k0
  have klin : HasDerivAt (fun t : ℝ => -(2 * π * t)) (-(2 * π * 1)) y :=
    ((hasDerivAt_id' y).const_mul (2 * π)).neg
  have ks : HasDerivAt (fun t : ℝ => -(2 * π * t) + lgUr t)
      (-(2 * π * 1)
        + (2 * (-(π / 12) * (1 - E2im y)) + -4 * dQ 2 y + 2 * dQ 3 y + -4 * dQ 6 y)) y :=
    klin.add kr
  have k : HasDerivAt lgU
      (-(2 * π * 1)
        + (2 * (-(π / 12) * (1 - E2im y)) + -4 * dQ 2 y + 2 * dQ 3 y + -4 * dQ 6 y)) y := ks
  have e : -(2 * π * 1)
        + (2 * (-(π / 12) * (1 - E2im y)) + -4 * dQ 2 y + 2 * dQ 3 y + -4 * dQ 6 y)
      = -(2 * π) * (Eax y + Pax y / 4) := by
    unfold dQ Eax Pax
    ring
  exact k.congr_deriv e

/-! ## Limits at the cusp `y → +∞` -/

theorem sig1_zero_or (n : ℕ) : sig 1 n = 0 ∨ (1 : ℝ) ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · left
    rw [h]
    exact sig_zero 1
  · right
    exact Nat.one_le_cast.mpr (Nat.succ_le_of_lt h)

theorem tendsto_qa_sig1 : Filter.Tendsto (qa (sig 1)) Filter.atTop (nhds 0) :=
  tendsto_qa_atTop (sig_abs_le 1) (sig_zero 1)

/-- `E₂(iy) → 1` as `y → +∞`. -/
theorem tendsto_E2im_atTop : Filter.Tendsto E2im Filter.atTop (nhds 1) := by
  have h24 : Filter.Tendsto (fun y : ℝ => 24 * qa (sig 1) y) Filter.atTop (nhds (24 * 0)) :=
    tendsto_qa_sig1.const_mul 24
  have hc1 : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have hs : Filter.Tendsto (fun y : ℝ => 1 - 24 * qa (sig 1) y) Filter.atTop
      (nhds (1 - 24 * 0)) := hc1.sub h24
  have e : (1 : ℝ) - 24 * 0 = 1 := by norm_num
  rw [e] at hs
  have hev : Filter.EventuallyEq Filter.atTop (fun y : ℝ => 1 - 24 * qa (sig 1) y) E2im :=
    (Filter.eventually_gt_atTop (0 : ℝ)).mono (fun y hy => (E2im_eq_qa hy).symm)
  exact Filter.Tendsto.congr' hev hs

/-- `Zax → 1` as `y → +∞`. -/
theorem tendsto_Zax_atTop : Filter.Tendsto Zax Filter.atTop (nhds 1) := by
  have h1 := tendsto_E2im_atTop
  have h2 := tendsto_comp_mul_atTop tendsto_E2im_atTop 2 (by norm_num)
  have h3 := tendsto_comp_mul_atTop tendsto_E2im_atTop 3 (by norm_num)
  have h6 := tendsto_comp_mul_atTop tendsto_E2im_atTop 6 (by norm_num)
  have k1 : Filter.Tendsto (fun y : ℝ => E2im y - 4 * E2im (2 * y)) Filter.atTop
      (nhds (1 - 4 * 1)) := h1.sub (h2.const_mul 4)
  have k2 : Filter.Tendsto (fun y : ℝ => E2im y - 4 * E2im (2 * y) - 3 * E2im (3 * y))
      Filter.atTop (nhds (1 - 4 * 1 - 3 * 1)) := k1.sub (h3.const_mul 3)
  have k3 : Filter.Tendsto
      (fun y : ℝ => E2im y - 4 * E2im (2 * y) - 3 * E2im (3 * y) + 12 * E2im (6 * y))
      Filter.atTop (nhds (1 - 4 * 1 - 3 * 1 + 12 * 1)) := k2.add (h6.const_mul 12)
  have k4 : Filter.Tendsto
      (fun y : ℝ => (E2im y - 4 * E2im (2 * y) - 3 * E2im (3 * y) + 12 * E2im (6 * y)) / 6)
      Filter.atTop (nhds ((1 - 4 * 1 - 3 * 1 + 12 * 1) / 6)) := k3.div_const 6
  have e : ((1 : ℝ) - 4 * 1 - 3 * 1 + 12 * 1) / 6 = 1 := by norm_num
  rw [e] at k4
  exact k4

theorem tendsto_qb_atTop : Filter.Tendsto qb Filter.atTop (nhds 0) := by
  have h := tendsto_qa_atTop sigq_abs_le sigq_zero
  exact h

theorem tendsto_lgZ_atTop : Filter.Tendsto lgZ Filter.atTop (nhds 0) := by
  have h1 := tendsto_qb_atTop
  have h2 := tendsto_comp_mul_atTop tendsto_qb_atTop 2 (by norm_num)
  have h3 := tendsto_comp_mul_atTop tendsto_qb_atTop 3 (by norm_num)
  have h6 := tendsto_comp_mul_atTop tendsto_qb_atTop 6 (by norm_num)
  have k := tendsto_lin4_zero (-4) 2 (-4) 2 h1 h2 h3 h6
  exact k

theorem tendsto_lgUr_atTop : Filter.Tendsto lgUr Filter.atTop (nhds 0) := by
  have h1 := tendsto_qb_atTop
  have h2 := tendsto_comp_mul_atTop tendsto_qb_atTop 2 (by norm_num)
  have h3 := tendsto_comp_mul_atTop tendsto_qb_atTop 3 (by norm_num)
  have h6 := tendsto_comp_mul_atTop tendsto_qb_atTop 6 (by norm_num)
  have k := tendsto_lin4_zero 2 (-4) 2 (-4) h1 h2 h3 h6
  exact k

/-! ## The coefficient of `q` in `Uax` -/

/-- `σ₁(n)` with the term `n = 1` removed. -/
noncomputable def sigT (n : ℕ) : ℝ := if n = 1 then 0 else sig 1 n

/-- The sequence `1` at `n = 1` and `0` elsewhere. -/
noncomputable def dl1 (n : ℕ) : ℝ := if n = 1 then 1 else 0

theorem sigT_abs_le (n : ℕ) : |sigT n| ≤ 1 * (n : ℝ) ^ (1 + 1) := by
  unfold sigT
  by_cases h : n = 1
  · rw [if_pos h, abs_zero]
    exact mul_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg n) _)
  · rw [if_neg h]
    exact sig_abs_le 1 n

theorem dl1_abs_le (n : ℕ) : |dl1 n| ≤ 1 * (n : ℝ) ^ 1 := by
  unfold dl1
  by_cases h : n = 1
  · rw [if_pos h, h]
    norm_num
  · rw [if_neg h, abs_zero]
    exact mul_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg n) _)

theorem sigT_zero_or (n : ℕ) : sigT n = 0 ∨ (2 : ℝ) ≤ (n : ℝ) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · left
    unfold sigT
    by_cases h1 : n = 1
    · rw [if_pos h1]
    · rw [if_neg h1]
      have h0 : n = 0 := by omega
      rw [h0]
      exact sig_zero 1
  · right
    exact_mod_cast h

theorem sig1_eq_dl1_add (n : ℕ) : sig 1 n = dl1 n + sigT n := by
  unfold dl1 sigT
  by_cases h : n = 1
  · rw [if_pos h, if_pos h, add_zero, h]
    exact sig1_vals.2.1
  · rw [if_neg h, if_neg h, zero_add]

theorem qa_dl1 (y : ℝ) : qa dl1 y = Real.exp (-(2 * π * y)) := by
  have h : ∀ b : ℕ, b ≠ 1 → dl1 b * Real.exp (-(2 * π * (b : ℝ) * y)) = 0 := by
    intro b hb
    unfold dl1
    rw [if_neg hb, zero_mul]
  have h1 : dl1 1 = 1 := by
    unfold dl1
    simp
  unfold qa
  rw [tsum_eq_single 1 h, h1, one_mul, Nat.cast_one, mul_one]

/-- `∑ σ₁(n) qⁿ = q + ∑_{n ≥ 2} σ₁(n) qⁿ`. -/
theorem qa_sig1_split {y : ℝ} (hy : 0 < y) :
    qa (sig 1) y = Real.exp (-(2 * π * y)) + qa sigT y := by
  have hs1 := summable_qa dl1_abs_le hy
  have hs2 := summable_qa sigT_abs_le hy
  have h := qa_add hs1 hs2
  have e0 : qa (fun n : ℕ => dl1 n + sigT n) y = qa (sig 1) y :=
    congrArg (fun C : ℕ → ℝ => qa C y) (funext (fun n => (sig1_eq_dl1_add n).symm))
  rw [e0, qa_dl1] at h
  exact h

theorem exp_mul_Uax_eq {y : ℝ} (hy : 0 < y) :
    Real.exp (2 * π * y) * Uax y
      = 1 + Real.exp (2 * π * y) * qa sigT y - Real.exp (2 * π * y) * qa (sig 1) (2 * y)
        - 3 * (Real.exp (2 * π * y) * qa (sig 1) (3 * y))
        + 3 * (Real.exp (2 * π * y) * qa (sig 1) (6 * y)) := by
  have h2 : (0 : ℝ) < 2 * y := mul_pos (by norm_num) hy
  have h3 : (0 : ℝ) < 3 * y := mul_pos (by norm_num) hy
  have h6 : (0 : ℝ) < 6 * y := mul_pos (by norm_num) hy
  have hee : Real.exp (2 * π * y) * Real.exp (-(2 * π * y)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold Uax
  rw [E2im_eq_qa hy, E2im_eq_qa h2, E2im_eq_qa h3, E2im_eq_qa h6, qa_sig1_split hy]
  linear_combination hee

/-- `e^{2πy} Uax(y) → 1` as `y → +∞`: the expansion of `Uax` starts with `q`. -/
theorem tendsto_exp_mul_Uax_atTop :
    Filter.Tendsto (fun y : ℝ => Real.exp (2 * π * y) * Uax y) Filter.atTop (nhds 1) := by
  have hT0 := tendsto_exp_mul_qa_atTop sigT_abs_le 2 1 sigT_zero_or (le_refl 1) (by norm_num)
  have hT : Filter.Tendsto (fun y : ℝ => Real.exp (2 * π * y) * qa sigT y) Filter.atTop
      (nhds 0) := by
    refine hT0.congr (fun y => ?_)
    show Real.exp (2 * π * y) * qa sigT (1 * y) = Real.exp (2 * π * y) * qa sigT y
    rw [one_mul]
  have h2 := tendsto_exp_mul_qa_atTop (sig_abs_le 1) 1 2 sig1_zero_or (by norm_num)
    (by norm_num)
  have h3 := tendsto_exp_mul_qa_atTop (sig_abs_le 1) 1 3 sig1_zero_or (by norm_num)
    (by norm_num)
  have h6 := tendsto_exp_mul_qa_atTop (sig_abs_le 1) 1 6 sig1_zero_or (by norm_num)
    (by norm_num)
  have hc1 : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have k1 : Filter.Tendsto (fun y : ℝ => 1 + Real.exp (2 * π * y) * qa sigT y) Filter.atTop
      (nhds (1 + 0)) := hc1.add hT
  have k2 : Filter.Tendsto
      (fun y : ℝ => 1 + Real.exp (2 * π * y) * qa sigT y
        - Real.exp (2 * π * y) * qa (sig 1) (2 * y))
      Filter.atTop (nhds (1 + 0 - 0)) := k1.sub h2
  have k3 : Filter.Tendsto
      (fun y : ℝ => 1 + Real.exp (2 * π * y) * qa sigT y
        - Real.exp (2 * π * y) * qa (sig 1) (2 * y)
        - 3 * (Real.exp (2 * π * y) * qa (sig 1) (3 * y)))
      Filter.atTop (nhds (1 + 0 - 0 - 3 * 0)) := k2.sub (h3.const_mul 3)
  have k4 : Filter.Tendsto
      (fun y : ℝ => 1 + Real.exp (2 * π * y) * qa sigT y
        - Real.exp (2 * π * y) * qa (sig 1) (2 * y)
        - 3 * (Real.exp (2 * π * y) * qa (sig 1) (3 * y))
        + 3 * (Real.exp (2 * π * y) * qa (sig 1) (6 * y)))
      Filter.atTop (nhds (1 + 0 - 0 - 3 * 0 + 3 * 0)) := k3.add (h6.const_mul 3)
  have e0 : (1 : ℝ) + 0 - 0 - 3 * 0 + 3 * 0 = 1 := by norm_num
  rw [e0] at k4
  have hev : Filter.EventuallyEq Filter.atTop
      (fun y : ℝ => 1 + Real.exp (2 * π * y) * qa sigT y
        - Real.exp (2 * π * y) * qa (sig 1) (2 * y)
        - 3 * (Real.exp (2 * π * y) * qa (sig 1) (3 * y))
        + 3 * (Real.exp (2 * π * y) * qa (sig 1) (6 * y)))
      (fun y : ℝ => Real.exp (2 * π * y) * Uax y) :=
    (Filter.eventually_gt_atTop (0 : ℝ)).mono (fun y hy => (exp_mul_Uax_eq hy).symm)
  exact Filter.Tendsto.congr' hev k4

/-! ## The two functions with derivative zero -/

theorem Zax_mul_exp_deriv {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => Zax t * Real.exp (-lgZ t)) 0 y := by
  have hZ := hasDerivAt_Zax hy
  have hL := hasDerivAt_lgZ hy
  have hE0 := (hL.neg).exp
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-lgZ t))
      (Real.exp (-lgZ y) * -(-(2 * π) * Eax y)) y := hE0
  have hF0 := hZ.mul hE
  have hF : HasDerivAt (fun t : ℝ => Zax t * Real.exp (-lgZ t))
      (-(2 * π) * (Zax y * Eax y) * Real.exp (-lgZ y)
        + Zax y * (Real.exp (-lgZ y) * -(-(2 * π) * Eax y))) y := hF0
  have e : -(2 * π) * (Zax y * Eax y) * Real.exp (-lgZ y)
        + Zax y * (Real.exp (-lgZ y) * -(-(2 * π) * Eax y)) = 0 := by ring
  exact hF.congr_deriv e

theorem Uax_mul_exp_deriv {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => Uax t * Real.exp (-lgU t)) 0 y := by
  have hU := hasDerivAt_Uax hy
  have hL := hasDerivAt_lgU hy
  have hE0 := (hL.neg).exp
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-lgU t))
      (Real.exp (-lgU y) * -(-(2 * π) * (Eax y + Pax y / 4))) y := hE0
  have hF0 := hU.mul hE
  have hF : HasDerivAt (fun t : ℝ => Uax t * Real.exp (-lgU t))
      (-(2 * π) * (Uax y * (Eax y + Pax y / 4)) * Real.exp (-lgU y)
        + Uax y * (Real.exp (-lgU y) * -(-(2 * π) * (Eax y + Pax y / 4)))) y := hF0
  have e : -(2 * π) * (Uax y * (Eax y + Pax y / 4)) * Real.exp (-lgU y)
        + Uax y * (Real.exp (-lgU y) * -(-(2 * π) * (Eax y + Pax y / 4))) = 0 := by ring
  exact hF.congr_deriv e

/-! ## The exponential forms -/

/-- **`Zax` is the exponential of an explicit `q`-series.** -/
theorem Zax_eq_exp {y : ℝ} (hy : 0 < y) : Zax y = Real.exp (lgZ y) := by
  have hl : Filter.Tendsto (fun t : ℝ => Zax t * Real.exp (-lgZ t)) Filter.atTop
      (nhds 1) := by
    have hn : Filter.Tendsto (fun t : ℝ => -lgZ t) Filter.atTop (nhds (-0)) :=
      tendsto_lgZ_atTop.neg
    have hx0 := (Real.continuous_exp.tendsto (-0)).comp hn
    have hx : Filter.Tendsto (fun t : ℝ => Real.exp (-lgZ t)) Filter.atTop
        (nhds (Real.exp (-0))) := hx0
    have hm : Filter.Tendsto (fun t : ℝ => Zax t * Real.exp (-lgZ t)) Filter.atTop
        (nhds (1 * Real.exp (-0))) := tendsto_Zax_atTop.mul hx
    have e : (1 : ℝ) * Real.exp (-0) = 1 := by rw [neg_zero, Real.exp_zero, mul_one]
    rw [e] at hm
    exact hm
  have h1 := eq_one_of_deriv_zero_of_tendsto (fun t ht => Zax_mul_exp_deriv ht) hl hy
  have h1' : Zax y * Real.exp (-lgZ y) = 1 := h1
  have h2 : Real.exp (-lgZ y) * Real.exp (lgZ y) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination (Real.exp (lgZ y)) * h1' - Zax y * h2

/-- **`Uax` is the exponential of an explicit `q`-series.** -/
theorem Uax_eq_exp {y : ℝ} (hy : 0 < y) : Uax y = Real.exp (lgU y) := by
  have hl : Filter.Tendsto (fun t : ℝ => Uax t * Real.exp (-lgU t)) Filter.atTop
      (nhds 1) := by
    have hn : Filter.Tendsto (fun t : ℝ => -lgUr t) Filter.atTop (nhds (-0)) :=
      tendsto_lgUr_atTop.neg
    have hx0 := (Real.continuous_exp.tendsto (-0)).comp hn
    have hx : Filter.Tendsto (fun t : ℝ => Real.exp (-lgUr t)) Filter.atTop
        (nhds (Real.exp (-0))) := hx0
    have hm : Filter.Tendsto
        (fun t : ℝ => Real.exp (2 * π * t) * Uax t * Real.exp (-lgUr t)) Filter.atTop
        (nhds (1 * Real.exp (-0))) := tendsto_exp_mul_Uax_atTop.mul hx
    have e : (1 : ℝ) * Real.exp (-0) = 1 := by rw [neg_zero, Real.exp_zero, mul_one]
    rw [e] at hm
    refine hm.congr (fun t => ?_)
    show Real.exp (2 * π * t) * Uax t * Real.exp (-lgUr t) = Uax t * Real.exp (-lgU t)
    have e1 : -lgU t = 2 * π * t + -lgUr t := by
      unfold lgU
      ring
    rw [e1, Real.exp_add]
    ring
  have h1 := eq_one_of_deriv_zero_of_tendsto (fun t ht => Uax_mul_exp_deriv ht) hl hy
  have h1' : Uax y * Real.exp (-lgU y) = 1 := h1
  have h2 : Real.exp (-lgU y) * Real.exp (lgU y) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination (Real.exp (lgU y)) * h1' - Uax y * h2

theorem Zax_pos {y : ℝ} (hy : 0 < y) : 0 < Zax y := by
  rw [Zax_eq_exp hy]
  exact Real.exp_pos _

theorem Uax_pos {y : ℝ} (hy : 0 < y) : 0 < Uax y := by
  rw [Uax_eq_exp hy]
  exact Real.exp_pos _

end Tower.RV6
