import Mathlib
import Tower.RV6.ModAxis

/-!
# A tail bound for `q`-series on the imaginary axis, and limits at the cusp `y → +∞`

For a sequence `D` of polynomial growth, `qa D y = ∑ D(n) e^{-2πny}` (`QSeries.lean`).

* `qa_abs_le_tail`: if every `n` has `D n = 0` or `c ≤ n`, then for `y ≥ 1`
  `|qa D y| ≤ e^{-2πc(y-1)} ∑ |D n| e^{-2πn}`.  Termwise this is `(n - c)(y - 1) ≥ 0`.
* `tendsto_qa_atTop`: if `D 0 = 0` then `qa D y → 0` as `y → +∞`.
* `tendsto_exp_mul_qa_atTop`: if `d ≥ 1` and `c d > 1` then `e^{2πy} qa D (d y) → 0`.
  With `c = 2`, `d = 1` this isolates the coefficient of `q`; with `c = 1`, `d ≥ 2` it says that
  a dilated series is `o(q)`.

Also two small tools for linear combinations of four functions (`hasDerivAt_lin4`,
`tendsto_lin4_zero`) and for a dilation of the variable (`tendsto_comp_mul_atTop`).
-/

namespace Tower.RV6

open Real

/-- **Tail bound.**  If every `n` has `D n = 0` or `c ≤ n`, then for `y ≥ 1`
`|∑ D(n) e^{-2πny}| ≤ e^{-2πc(y-1)} ∑ |D(n)| e^{-2πn}`. -/
theorem qa_abs_le_tail {D : ℕ → ℝ} {B : ℝ} {K : ℕ}
    (hD : ∀ n : ℕ, |D n| ≤ B * (n : ℝ) ^ K) (c : ℝ) (hc : ∀ n : ℕ, D n = 0 ∨ c ≤ (n : ℝ))
    {y : ℝ} (hy : 1 ≤ y) :
    |qa D y| ≤ Real.exp (-(2 * π * c * (y - 1)))
      * ∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * 1)) := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  have hs1 : Summable fun n : ℕ => |D n| * Real.exp (-(2 * π * (n : ℝ) * 1)) :=
    summable_qa_abs hD one_pos
  have hsy : Summable fun n : ℕ => |D n| * Real.exp (-(2 * π * (n : ℝ) * y)) :=
    summable_qa_abs hD hy0
  have hA : ∀ n : ℕ, |D n * Real.exp (-(2 * π * (n : ℝ) * y))|
      = |D n| * Real.exp (-(2 * π * (n : ℝ) * y)) := by
    intro n
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have habs : Summable fun n : ℕ => |D n * Real.exp (-(2 * π * (n : ℝ) * y))| :=
    hsy.congr (fun n => (hA n).symm)
  have hterm : ∀ n : ℕ, |D n * Real.exp (-(2 * π * (n : ℝ) * y))|
      ≤ Real.exp (-(2 * π * c * (y - 1))) * (|D n| * Real.exp (-(2 * π * (n : ℝ) * 1))) := by
    intro n
    rw [hA n]
    rcases hc n with h0 | hcn
    · have e1 : |D n| = 0 := by rw [h0, abs_zero]
      refine le_of_eq ?_
      rw [e1, zero_mul, zero_mul, mul_zero]
    · have hE : Real.exp (-(2 * π * (n : ℝ) * y))
          ≤ Real.exp (-(2 * π * c * (y - 1))) * Real.exp (-(2 * π * (n : ℝ) * 1)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h2pi : (0 : ℝ) ≤ 2 * π := mul_nonneg (by norm_num) Real.pi_pos.le
        have hprod : 0 ≤ 2 * π * (((n : ℝ) - c) * (y - 1)) :=
          mul_nonneg h2pi (mul_nonneg (sub_nonneg.mpr hcn) (sub_nonneg.mpr hy))
        have key : -(2 * π * c * (y - 1)) + -(2 * π * (n : ℝ) * 1) - -(2 * π * (n : ℝ) * y)
            = 2 * π * (((n : ℝ) - c) * (y - 1)) := by ring
        linarith
      calc |D n| * Real.exp (-(2 * π * (n : ℝ) * y))
          ≤ |D n| * (Real.exp (-(2 * π * c * (y - 1)))
              * Real.exp (-(2 * π * (n : ℝ) * 1))) :=
            mul_le_mul_of_nonneg_left hE (abs_nonneg _)
        _ = Real.exp (-(2 * π * c * (y - 1)))
              * (|D n| * Real.exp (-(2 * π * (n : ℝ) * 1))) := by ring
  calc |qa D y| = |∑' n : ℕ, D n * Real.exp (-(2 * π * (n : ℝ) * y))| := rfl
    _ ≤ ∑' n : ℕ, |D n * Real.exp (-(2 * π * (n : ℝ) * y))| := abs_tsum_le_tsum_abs habs
    _ ≤ ∑' n : ℕ, Real.exp (-(2 * π * c * (y - 1)))
          * (|D n| * Real.exp (-(2 * π * (n : ℝ) * 1))) :=
        Summable.tsum_le_tsum hterm habs (hs1.mul_left _)
    _ = Real.exp (-(2 * π * c * (y - 1)))
          * ∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * 1)) := tsum_mul_left

/-- A real function bounded by `M e^{-ky}` (`k > 0`) from some point on tends to `0`. -/
theorem tendsto_zero_of_abs_le_exp {F : ℝ → ℝ} {M k : ℝ} (hk : 0 < k) (y0 : ℝ)
    (hb : ∀ y : ℝ, y0 ≤ y → |F y| ≤ M * Real.exp (-(k * y))) :
    Filter.Tendsto F Filter.atTop (nhds 0) := by
  have hlim0 : Filter.Tendsto (fun y : ℝ => k * y) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hk Filter.tendsto_id
  have hlim1' := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlim0
  have hlim1 : Filter.Tendsto (fun y : ℝ => Real.exp (-(k * y))) Filter.atTop (nhds 0) :=
    hlim1'
  have hlim2 : Filter.Tendsto (fun y : ℝ => M * Real.exp (-(k * y))) Filter.atTop
      (nhds (M * 0)) := hlim1.const_mul M
  rw [mul_zero] at hlim2
  refine squeeze_zero_norm' ((Filter.eventually_ge_atTop y0).mono (fun y hy => ?_)) hlim2
  show ‖F y‖ ≤ M * Real.exp (-(k * y))
  rw [Real.norm_eq_abs]
  exact hb y hy

/-- A `q`-series without constant term tends to `0` at the cusp. -/
theorem tendsto_qa_atTop {D : ℕ → ℝ} {B : ℝ} {K : ℕ}
    (hD : ∀ n : ℕ, |D n| ≤ B * (n : ℝ) ^ K) (h0 : D 0 = 0) :
    Filter.Tendsto (qa D) Filter.atTop (nhds 0) := by
  have hc : ∀ n : ℕ, D n = 0 ∨ (1 : ℝ) ≤ (n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · left
      rw [h, h0]
    · right
      exact Nat.one_le_cast.mpr (Nat.succ_le_of_lt h)
  refine tendsto_zero_of_abs_le_exp
    (M := Real.exp (2 * π) * ∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * 1)))
    (k := 2 * π) (mul_pos (by norm_num) Real.pi_pos) 1 (fun y hy => ?_)
  show |qa D y| ≤ Real.exp (2 * π) * (∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * 1)))
    * Real.exp (-(2 * π * y))
  have h := qa_abs_le_tail hD 1 hc hy
  have e : Real.exp (-(2 * π * 1 * (y - 1))) = Real.exp (2 * π) * Real.exp (-(2 * π * y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e] at h
  exact le_trans h (le_of_eq (by ring))

/-- If `D n = 0` or `c ≤ n` for every `n`, `d ≥ 1` and `c d > 1`, then
`e^{2πy} ∑ D(n) e^{-2πn d y} → 0` as `y → +∞`. -/
theorem tendsto_exp_mul_qa_atTop {D : ℕ → ℝ} {B : ℝ} {K : ℕ}
    (hD : ∀ n : ℕ, |D n| ≤ B * (n : ℝ) ^ K) (c d : ℝ)
    (hc : ∀ n : ℕ, D n = 0 ∨ c ≤ (n : ℝ)) (hd : 1 ≤ d) (hcd : 1 < c * d) :
    Filter.Tendsto (fun y : ℝ => Real.exp (2 * π * y) * qa D (d * y)) Filter.atTop
      (nhds 0) := by
  have hk : 0 < 2 * π * (c * d - 1) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (sub_pos.mpr hcd)
  refine tendsto_zero_of_abs_le_exp
    (M := Real.exp (2 * π * c) * ∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * 1)))
    (k := 2 * π * (c * d - 1)) hk 1 (fun y hy => ?_)
  show |Real.exp (2 * π * y) * qa D (d * y)|
    ≤ Real.exp (2 * π * c) * (∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * 1)))
      * Real.exp (-(2 * π * (c * d - 1) * y))
  have hdy : 1 ≤ d * y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hy)]
  have h := qa_abs_le_tail hD c hc hdy
  have e : Real.exp (2 * π * y) * Real.exp (-(2 * π * c * (d * y - 1)))
      = Real.exp (2 * π * c) * Real.exp (-(2 * π * (c * d - 1) * y)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have alg : ∀ S : ℝ, Real.exp (2 * π * y) * (Real.exp (-(2 * π * c * (d * y - 1))) * S)
      = Real.exp (2 * π * c) * S * Real.exp (-(2 * π * (c * d - 1) * y)) := by
    intro S
    linear_combination S * e
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (2 * π * y) * |qa D (d * y)|
      ≤ Real.exp (2 * π * y) * (Real.exp (-(2 * π * c * (d * y - 1)))
          * ∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * 1))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp (2 * π * c) * (∑' n : ℕ, |D n| * Real.exp (-(2 * π * (n : ℝ) * 1)))
          * Real.exp (-(2 * π * (c * d - 1) * y)) := alg _

/-! ## Small tools -/

/-- A limit at `+∞` is not changed by a dilation of the variable. -/
theorem tendsto_comp_mul_atTop {F : ℝ → ℝ} {a : ℝ}
    (h : Filter.Tendsto F Filter.atTop (nhds a)) (d : ℝ) (hd : 0 < d) :
    Filter.Tendsto (fun y : ℝ => F (d * y)) Filter.atTop (nhds a) := by
  have hlim : Filter.Tendsto (fun y : ℝ => d * y) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hd Filter.tendsto_id
  have hc := h.comp hlim
  exact hc

/-- The derivative of a linear combination of four functions. -/
theorem hasDerivAt_lin4 {f1 f2 f3 f4 : ℝ → ℝ} {d1 d2 d3 d4 y : ℝ} (c1 c2 c3 c4 : ℝ)
    (h1 : HasDerivAt f1 d1 y) (h2 : HasDerivAt f2 d2 y) (h3 : HasDerivAt f3 d3 y)
    (h4 : HasDerivAt f4 d4 y) :
    HasDerivAt (fun t : ℝ => c1 * f1 t + c2 * f2 t + c3 * f3 t + c4 * f4 t)
      (c1 * d1 + c2 * d2 + c3 * d3 + c4 * d4) y := by
  have k1 : HasDerivAt (fun t : ℝ => c1 * f1 t) (c1 * d1) y := h1.const_mul c1
  have k2 : HasDerivAt (fun t : ℝ => c1 * f1 t + c2 * f2 t) (c1 * d1 + c2 * d2) y :=
    k1.add (h2.const_mul c2)
  have k3 : HasDerivAt (fun t : ℝ => c1 * f1 t + c2 * f2 t + c3 * f3 t)
      (c1 * d1 + c2 * d2 + c3 * d3) y := k2.add (h3.const_mul c3)
  have k4 : HasDerivAt (fun t : ℝ => c1 * f1 t + c2 * f2 t + c3 * f3 t + c4 * f4 t)
      (c1 * d1 + c2 * d2 + c3 * d3 + c4 * d4) y := k3.add (h4.const_mul c4)
  exact k4

/-- A linear combination of four functions tending to `0` tends to `0`. -/
theorem tendsto_lin4_zero {l : Filter ℝ} {f1 f2 f3 f4 : ℝ → ℝ} (c1 c2 c3 c4 : ℝ)
    (h1 : Filter.Tendsto f1 l (nhds 0)) (h2 : Filter.Tendsto f2 l (nhds 0))
    (h3 : Filter.Tendsto f3 l (nhds 0)) (h4 : Filter.Tendsto f4 l (nhds 0)) :
    Filter.Tendsto (fun y : ℝ => c1 * f1 y + c2 * f2 y + c3 * f3 y + c4 * f4 y) l
      (nhds 0) := by
  have k1 : Filter.Tendsto (fun y : ℝ => c1 * f1 y) l (nhds (c1 * 0)) := h1.const_mul c1
  have k2 : Filter.Tendsto (fun y : ℝ => c1 * f1 y + c2 * f2 y) l
      (nhds (c1 * 0 + c2 * 0)) := k1.add (h2.const_mul c2)
  have k3 : Filter.Tendsto (fun y : ℝ => c1 * f1 y + c2 * f2 y + c3 * f3 y) l
      (nhds (c1 * 0 + c2 * 0 + c3 * 0)) := k2.add (h3.const_mul c3)
  have k4 : Filter.Tendsto (fun y : ℝ => c1 * f1 y + c2 * f2 y + c3 * f3 y + c4 * f4 y) l
      (nhds (c1 * 0 + c2 * 0 + c3 * 0 + c4 * 0)) := k3.add (h4.const_mul c4)
  have e : c1 * 0 + c2 * 0 + c3 * 0 + c4 * 0 = (0 : ℝ) := by ring
  rw [e] at k4
  exact k4

/-- A function with derivative `0` on `(0, ∞)` takes the same value at any two points. -/
theorem eq_of_hasDerivAt_zero {F : ℝ → ℝ} (h : ∀ y : ℝ, 0 < y → HasDerivAt F 0 y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : F b = F a := by
  have hcont : ContinuousOn F (Set.Icc a b) := fun x hx =>
    (h x (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt F 0 (Set.Ici x) x := fun x hx =>
    (h x (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hcont hderiv b (Set.right_mem_Icc.mpr hab)

/-- A function with derivative `0` on `(0, ∞)` and limit `1` at `+∞` is `1`. -/
theorem eq_one_of_deriv_zero_of_tendsto {F : ℝ → ℝ}
    (h : ∀ y : ℝ, 0 < y → HasDerivAt F 0 y)
    (hlim : Filter.Tendsto F Filter.atTop (nhds 1)) {y : ℝ} (hy : 0 < y) : F y = 1 := by
  have hev : Filter.EventuallyEq Filter.atTop F (fun _ : ℝ => F y) :=
    (Filter.eventually_ge_atTop y).mono (fun t ht => eq_of_hasDerivAt_zero h hy ht)
  have hc : Filter.Tendsto (fun _ : ℝ => F y) Filter.atTop (nhds 1) :=
    Filter.Tendsto.congr' hev hlim
  exact (tendsto_nhds_unique hc tendsto_const_nhds).symm

end Tower.RV6
