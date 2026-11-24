import Mathlib
import Tower.RV6.AJODEG
import Tower.RV6.CuspBesselF

/-!
# `c = 0`: the dual equation of `ajG` is `uG = 0`

With `u = bG t = (e + B₁)(1 + log(2/t))`, `B₁ = Bser 1`, on `(0, 1]`:

* `abs_pB_small`: `|pB₀| ≤ u²`, `|pB₁| ≤ 2u²`, `|pB₂| ≤ 4t²u²`, `|pB₃| ≤ 12t²u²`, `|pB₄| ≤ 48t²u²`,
  `|pB₅| ≤ 208t²u²`;
* `abs_thG4_small`, `abs_thG5_small`: `|θ⁴g| ≤ 384 t²u⁴`, `|θ⁵g| ≤ 2336 t²u⁴`; with `t u⁴ ≤ kG0`
  (`mul_bG_pow4_le`), `θ⁴g → 0` at `0+` (`tendsto_thG4_zero`) and `θ⁵g/t` is integrable;
* **`AJ_thG4_eq`**: `AJ(θ⁴g)(x) = ∫₀^∞ J₀(xt) θ⁵g(t)/t dt` (one integration by parts), so
  `AJ(θ⁴g)(x) → 0` as `x → ∞` (`tendsto_AJ_thG4`, dominated convergence);
* `abs_AJ_le`: `|AJ ψ x| ≤ x ∫|ψ|`;
* **`uG_zero`**: the constant of `uG_eq` is `0` (`uG_c_zero`), so `uG = 0` on `(0, ∞)`.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

/-! ## Near `0` -/

/-- `u(t) = (e + B₁)(1 + log(2/t))`. -/
noncomputable def bG (t : ℝ) : ℝ := (Real.exp 1 + Bser 1) * (1 + Real.log (2 / t))

theorem Bser_one_nonneg : 0 ≤ Bser 1 := by
  have h1 := besselI1_le_mul (t := 1) zero_le_one le_rfl
  have h2 := besselI1_nonneg (t := (1 : ℝ)) zero_le_one
  linarith

theorem one_le_log_term {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ 1 + Real.log (2 / t) := by
  have h : 0 ≤ Real.log (2 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  linarith

theorem one_le_bG {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ bG t := by
  have hL := one_le_log_term ht ht1
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hb := Bser_one_nonneg
  have hM : (1 : ℝ) ≤ Real.exp 1 + Bser 1 := by linarith
  have h := mul_le_mul hM hL zero_le_one (by linarith)
  unfold bG
  linarith

theorem near0_prim {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |besselI0 t| ≤ bG t ∧ |t * besselI1 t| ≤ t ^ 2 * bG t ∧ |besselK0 t| ≤ bG t ∧
      |t * besselK1 t| ≤ bG t := by
  have hL := one_le_log_term ht ht1
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hb := Bser_one_nonneg
  have hu1 : Real.exp 1 + Bser 1 ≤ bG t := by
    have h := mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ Real.exp 1 + Bser 1)
    unfold bG
    linarith
  have hu2 : 1 + Real.log (2 / t) ≤ bG t := by
    have h := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ Real.exp 1 + Bser 1)
      (by linarith : (0 : ℝ) ≤ 1 + Real.log (2 / t))
    unfold bG
    linarith
  have hI0 : |besselI0 t| ≤ Real.exp 1 := ity_besselI0.2.1 t ht ht1
  have hK0 : |besselK0 t| ≤ 1 + Real.log (2 / t) := kty_besselK0.2.1 t ht ht1
  have hk1 : Real.exp (-t) ≤ t * besselK1 t := exp_neg_le_mul_besselK1 ht
  have hk2 : t * besselK1 t ≤ 1 := mul_besselK1_le_one ht
  have hk0 : 0 < t * besselK1 t := lt_of_lt_of_le (Real.exp_pos _) hk1
  have hi1 : besselI1 t ≤ t * Bser 1 := besselI1_le_mul ht.le ht1
  have hi0 : 0 ≤ besselI1 t := besselI1_nonneg ht.le
  have hti : t * besselI1 t ≤ t * (t * Bser 1) := mul_le_mul_of_nonneg_left hi1 ht.le
  have hbu : Bser 1 ≤ bG t := by linarith
  have hsu : t ^ 2 * Bser 1 ≤ t ^ 2 * bG t := mul_le_mul_of_nonneg_left hbu (sq_nonneg t)
  refine ⟨by linarith, ?_, by linarith, ?_⟩
  · rw [abs_of_nonneg (mul_nonneg ht.le hi0)]
    linarith
  · rw [abs_of_pos hk0]
    linarith

theorem abs_pB_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |pB0 t| ≤ bG t ^ 2 ∧ |pB1 t| ≤ 2 * bG t ^ 2 ∧ |pB2 t| ≤ 4 * (t ^ 2 * bG t ^ 2) ∧
      |pB3 t| ≤ 12 * (t ^ 2 * bG t ^ 2) ∧ |pB4 t| ≤ 48 * (t ^ 2 * bG t ^ 2) ∧
      |pB5 t| ≤ 208 * (t ^ 2 * bG t ^ 2) := by
  obtain ⟨hI0, hI1, hK0, hK1⟩ := near0_prim ht ht1
  have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hs1 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht1
  have hu2 : 0 ≤ bG t ^ 2 := sq_nonneg _
  have hsu : t ^ 2 * bG t ^ 2 ≤ bG t ^ 2 := mul_le_of_le_one_left hu2 hs1
  have hssu : t ^ 2 * (t ^ 2 * bG t ^ 2) ≤ t ^ 2 * bG t ^ 2 :=
    mul_le_of_le_one_left (mul_nonneg hs0 hu2) hs1
  have ht2 : |t ^ 2| ≤ t ^ 2 := le_of_eq (abs_of_nonneg hs0)
  have p0 : |pB0 t| ≤ bG t ^ 2 := by
    have h := abs_mul_leG hI0 hK0
    unfold pB0
    linarith
  have p1 : |pB1 t| ≤ 2 * bG t ^ 2 := by
    have a1 := abs_mul_leG hI1 hK0
    have a2 := abs_mul_leG hI0 hK1
    have a := abs_add_le (t * besselI1 t * besselK0 t) (-(besselI0 t * (t * besselK1 t)))
    rw [abs_neg, ← sub_eq_add_neg] at a
    unfold pB1
    linarith
  have p2 : |pB2 t| ≤ 4 * (t ^ 2 * bG t ^ 2) := by
    have b1 : |t ^ 2 * besselI0 t * besselK0 t| ≤ t ^ 2 * bG t * bG t :=
      abs_mul_leG (abs_mul_leG ht2 hI0) hK0
    have b2 : |t * besselI1 t * (t * besselK1 t)| ≤ t ^ 2 * bG t * bG t := abs_mul_leG hI1 hK1
    have c1 : |(2 : ℝ) * (t ^ 2 * besselI0 t * besselK0 t)| ≤ 2 * (t ^ 2 * bG t * bG t) :=
      abs_cmul_leG (by norm_num) b1
    have c2 : |(2 : ℝ) * (t * besselI1 t * (t * besselK1 t))| ≤ 2 * (t ^ 2 * bG t * bG t) :=
      abs_cmul_leG (by norm_num) b2
    have a := abs_add_le ((2 : ℝ) * (t ^ 2 * besselI0 t * besselK0 t))
      (-((2 : ℝ) * (t * besselI1 t * (t * besselK1 t))))
    rw [abs_neg, ← sub_eq_add_neg] at a
    unfold pB2
    linarith
  have p01 : |pB0 t + pB1 t| ≤ 3 * bG t ^ 2 := by
    have a := abs_add_le (pB0 t) (pB1 t)
    linarith
  have p12 : |pB1 t + pB2 t| ≤ 6 * bG t ^ 2 := by
    have a := abs_add_le (pB1 t) (pB2 t)
    linarith
  have p3 : |pB3 t| ≤ 12 * (t ^ 2 * bG t ^ 2) := by
    have e : pB3 t = (4 : ℝ) * (t ^ 2 * (pB0 t + pB1 t)) := by
      unfold pB3
      ring
    have c := abs_cmul_leG (c := (4 : ℝ)) (C := 4) (by norm_num) (abs_mul_leG ht2 p01)
    rw [e]
    linarith
  have p23 : |pB2 t + pB3 t| ≤ 16 * (t ^ 2 * bG t ^ 2) := by
    have a := abs_add_le (pB2 t) (pB3 t)
    linarith
  have p4 : |pB4 t| ≤ 48 * (t ^ 2 * bG t ^ 2) := by
    have e : pB4 t = (8 : ℝ) * (t ^ 2 * (pB0 t + pB1 t)) + (4 : ℝ) * (t ^ 2 * (pB1 t + pB2 t)) := by
      unfold pB4
      ring
    have h1 := abs_cmul_leG (c := (8 : ℝ)) (C := 8) (by norm_num) (abs_mul_leG ht2 p01)
    have h2 := abs_cmul_leG (c := (4 : ℝ)) (C := 4) (by norm_num) (abs_mul_leG ht2 p12)
    have a := abs_add_le ((8 : ℝ) * (t ^ 2 * (pB0 t + pB1 t))) ((4 : ℝ) * (t ^ 2 * (pB1 t + pB2 t)))
    rw [e]
    linarith
  have p5 : |pB5 t| ≤ 208 * (t ^ 2 * bG t ^ 2) := by
    have e : pB5 t = (16 : ℝ) * (t ^ 2 * (pB0 t + pB1 t)) + (16 : ℝ) * (t ^ 2 * (pB1 t + pB2 t))
        + (4 : ℝ) * (t ^ 2 * (pB2 t + pB3 t)) := by
      unfold pB5
      ring
    have h1 := abs_cmul_leG (c := (16 : ℝ)) (C := 16) (by norm_num) (abs_mul_leG ht2 p01)
    have h2 := abs_cmul_leG (c := (16 : ℝ)) (C := 16) (by norm_num) (abs_mul_leG ht2 p12)
    have h3 := abs_cmul_leG (c := (4 : ℝ)) (C := 4) (by norm_num) (abs_mul_leG ht2 p23)
    have a1 := abs_add_le ((16 : ℝ) * (t ^ 2 * (pB0 t + pB1 t))) ((16 : ℝ) * (t ^ 2 * (pB1 t + pB2 t)))
    have a2 := abs_add_le ((16 : ℝ) * (t ^ 2 * (pB0 t + pB1 t)) + (16 : ℝ) * (t ^ 2 * (pB1 t + pB2 t)))
      ((4 : ℝ) * (t ^ 2 * (pB2 t + pB3 t)))
    rw [e]
    linarith
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem abs_thG4_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |thG4 t| ≤ 384 * (t ^ 2 * bG t ^ 4) := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := abs_pB_small ht ht1
  have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hs1 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht1
  have hu4 : 0 ≤ bG t ^ 4 := pow_nonneg (by linarith [one_le_bG ht ht1]) 4
  have hss : t ^ 2 * (t ^ 2 * bG t ^ 4) ≤ t ^ 2 * bG t ^ 4 :=
    mul_le_of_le_one_left (mul_nonneg hs0 hu4) hs1
  have q1 := abs_cmul_leG (c := (2 : ℝ)) (C := 2) (by norm_num) (abs_mul_leG p0 p4)
  have q2 := abs_cmul_leG (c := (6 : ℝ)) (C := 6) (by norm_num) (abs_mul_leG p2 p2)
  have q3 := abs_cmul_leG (c := (8 : ℝ)) (C := 8) (by norm_num) (abs_mul_leG p1 p3)
  have a1 := abs_add_le ((2 : ℝ) * (pB0 t * pB4 t)) ((6 : ℝ) * (pB2 t * pB2 t))
  have a2 := abs_add_le ((2 : ℝ) * (pB0 t * pB4 t) + (6 : ℝ) * (pB2 t * pB2 t))
    ((8 : ℝ) * (pB1 t * pB3 t))
  rw [thG4_eq_P]
  linarith

theorem abs_thG5_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |thG5 t| ≤ 2336 * (t ^ 2 * bG t ^ 4) := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := abs_pB_small ht ht1
  have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hs1 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht1
  have hu4 : 0 ≤ bG t ^ 4 := pow_nonneg (by linarith [one_le_bG ht ht1]) 4
  have hss : t ^ 2 * (t ^ 2 * bG t ^ 4) ≤ t ^ 2 * bG t ^ 4 :=
    mul_le_of_le_one_left (mul_nonneg hs0 hu4) hs1
  have q1 := abs_cmul_leG (c := (2 : ℝ)) (C := 2) (by norm_num) (abs_mul_leG p0 p5)
  have q2 := abs_cmul_leG (c := (10 : ℝ)) (C := 10) (by norm_num) (abs_mul_leG p1 p4)
  have q3 := abs_cmul_leG (c := (20 : ℝ)) (C := 20) (by norm_num) (abs_mul_leG p2 p3)
  have a1 := abs_add_le ((2 : ℝ) * (pB0 t * pB5 t)) ((10 : ℝ) * (pB1 t * pB4 t))
  have a2 := abs_add_le ((2 : ℝ) * (pB0 t * pB5 t) + (10 : ℝ) * (pB1 t * pB4 t))
    ((20 : ℝ) * (pB2 t * pB3 t))
  rw [thG5_eq_P]
  linarith

/-- The constant of `t u⁴ ≤ kG0`. -/
noncomputable def kG0 : ℝ := (Real.exp 1 + Bser 1) ^ 4 * (343 * Real.sqrt 2) ^ 2

theorem mul_bG_pow4_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : t * bG t ^ 4 ≤ kG0 := by
  have hc := sqrt_mul_one_add_log_cube_le ht ht1
  have hL := one_le_log_term ht ht1
  have hs := Real.sqrt_nonneg t
  have h23 : (1 + Real.log (2 / t)) ^ 2 ≤ (1 + Real.log (2 / t)) ^ 3 :=
    pow_le_pow_right₀ hL (by norm_num : 2 ≤ 3)
  have hL2 : Real.sqrt t * (1 + Real.log (2 / t)) ^ 2 ≤ 343 * Real.sqrt 2 :=
    le_trans (mul_le_mul_of_nonneg_left h23 hs) hc
  have hA : 0 ≤ Real.sqrt t * (1 + Real.log (2 / t)) ^ 2 := mul_nonneg hs (sq_nonneg _)
  have hB : (Real.sqrt t * (1 + Real.log (2 / t)) ^ 2) ^ 2 ≤ (343 * Real.sqrt 2) ^ 2 :=
    pow_le_pow_left₀ hA hL2 2
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hM : 0 ≤ (Real.exp 1 + Bser 1) ^ 4 :=
    pow_nonneg (by linarith [Real.exp_pos 1, Bser_one_nonneg]) 4
  have e : t * bG t ^ 4
      = (Real.exp 1 + Bser 1) ^ 4 * (Real.sqrt t * (1 + Real.log (2 / t)) ^ 2) ^ 2 := by
    rw [mul_pow (Real.sqrt t) ((1 + Real.log (2 / t)) ^ 2) 2, hsq]
    unfold bG
    ring
  rw [e]
  unfold kG0
  exact mul_le_mul_of_nonneg_left hB hM

theorem abs_thG4_le_mul {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : |thG4 t| ≤ 384 * kG0 * t := by
  have h := abs_thG4_small ht ht1
  have k := mul_le_mul_of_nonneg_left (mul_bG_pow4_le ht ht1) ht.le
  linarith

theorem abs_thG5_div_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : |thG5 t / t| ≤ 2336 * kG0 := by
  have h := abs_thG5_small ht ht1
  have k := mul_le_mul_of_nonneg_left (mul_bG_pow4_le ht ht1) ht.le
  have h2 : |thG5 t| ≤ 2336 * kG0 * t := by linarith
  rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
  exact h2

/-! ## The limits of `θ⁴g` and the integrability of `θ⁵g/t` -/

theorem tendsto_thG4_zero : Tendsto thG4 (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hb : Tendsto (fun t : ℝ => 384 * kG0 * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun t : ℝ => 384 * kG0 * t) (nhds 0) (nhds (384 * kG0 * 0)) :=
      (by fun_prop : Continuous (fun t : ℝ => 384 * kG0 * t)).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (one_pos : (0 : ℝ) < 1))]
    with t ht ht1
  have ht0 : (0 : ℝ) < t := ht
  have ht1' : t < 1 := ht1
  rw [Real.norm_eq_abs]
  exact abs_thG4_le_mul ht0 ht1'.le

theorem tendsto_thG4_atTop : Tendsto thG4 atTop (nhds 0) := by
  have hb : Tendsto (fun t : ℝ => (27328 : ℝ) / t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have h := abs_tsq_thG4_le ht0
  rw [abs_mul, abs_of_nonneg (sq_nonneg t)] at h
  have a : |thG4 t| * t ≤ |thG4 t| * t ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
  rw [Real.norm_eq_abs, le_div_iff₀ ht0]
  linarith

theorem continuousOn_thG5_div : ContinuousOn (fun t : ℝ => thG5 t / t) (Set.Ioi 0) :=
  continuousOn_thG5.div continuousOn_id (fun t ht => ne_of_gt ht)

theorem integrableOn_thG5_div : IntegrableOn (fun t : ℝ => thG5 t / t) (Set.Ioi 0) := by
  refine integrableOn_Ioi_of_bounds continuousOn_thG5_div (A := 2336 * kG0) (B := 514528)
    (fun t ht ht1 => ?_) (fun t ht => ?_)
  · have h := abs_thG5_div_le ht ht1
    have hs1 : Real.sqrt t ≤ 1 := by
      have h' := Real.sqrt_le_sqrt ht1
      rwa [Real.sqrt_one] at h'
    have hm : Real.sqrt t * |thG5 t / t| ≤ 1 * (2336 * kG0) :=
      mul_le_mul hs1 h (abs_nonneg _) zero_le_one
    exact abs_le_of_sqrt_mul_le ht (by linarith)
  · have ht0 : (0 : ℝ) < t := by linarith
    have h := abs_tsq_thG5_le ht0
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)] at h
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
    have e : t ^ 2 * |thG5 t / t| = t * |thG5 t| := by
      rw [abs_div, abs_of_pos ht0, div_eq_mul_inv]
      linear_combination (t * |thG5 t|) * hinv
    have a : t * |thG5 t| ≤ t ^ 2 * |thG5 t| :=
      mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
    exact abs_le_of_sq_mul_le ht0 (by linarith)

/-! ## `AJ(θ⁴g) = ∫ J₀(xt) θ⁵g/t` and its limit -/

theorem AJ_thG4_eq {x : ℝ} (hx : 0 < x) :
    AJ thG4 x = ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * (thG5 t / t) := by
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => besselJ0 (x * t) * thG4 t)
      ((-x) * (besselJ1 (x * t) * thG4 t) + besselJ0 (x * t) * (thG5 t / t)) t := by
    intro t ht
    have d1 : HasDerivAt (fun t : ℝ => besselJ0 (x * t)) (-besselJ1 (x * t) * (x * 1)) t :=
      (hasDerivAt_besselJ0 (x * t)).comp t ((hasDerivAt_id' t).const_mul x)
    have h := d1.mul (hasDerivAt_thG4 ht)
    exact h.congr_deriv (by ring)
  have hz0 : Tendsto (fun t : ℝ => |thG4 t|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := tendsto_thG4_zero.abs
    rw [abs_zero] at h
    exact h
  have h0 : Tendsto (fun t : ℝ => besselJ0 (x * t) * thG4 t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hz0
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have j := abs_besselJ0_le_one (mul_nonneg hx.le ht0.le)
    rw [Real.norm_eq_abs, abs_mul]
    calc |besselJ0 (x * t)| * |thG4 t| ≤ 1 * |thG4 t| :=
          mul_le_mul_of_nonneg_right j (abs_nonneg _)
      _ = |thG4 t| := one_mul _
  have hzi : Tendsto (fun t : ℝ => |thG4 t|) atTop (nhds 0) := by
    have h := tendsto_thG4_atTop.abs
    rw [abs_zero] at h
    exact h
  have hinf : Tendsto (fun t : ℝ => besselJ0 (x * t) * thG4 t) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hzi
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have j := abs_besselJ0_le_one (mul_nonneg hx.le ht.le)
    rw [Real.norm_eq_abs, abs_mul]
    calc |besselJ0 (x * t)| * |thG4 t| ≤ 1 * |thG4 t| :=
          mul_le_mul_of_nonneg_right j (abs_nonneg _)
      _ = |thG4 t| := one_mul _
  have i1 : Integrable (fun t : ℝ => (-x) * (besselJ1 (x * t) * thG4 t))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrable_J1_mul_of_pdom pdom_thG4 hx).const_mul (-x)
  have i2 : Integrable (fun t : ℝ => besselJ0 (x * t) * (thG5 t / t))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => besselJ0 (x * t) * (thG5 t / t))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      ((continuousOn_besselJ0_mul x).mul continuousOn_thG5_div).aestronglyMeasurable
        measurableSet_Ioi
    refine (Integrable.abs integrableOn_thG5_div).mono' hm
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := ht
    have j := abs_besselJ0_le_one (mul_nonneg hx.le ht0.le)
    show ‖besselJ0 (x * t) * (thG5 t / t)‖ ≤ |thG5 t / t|
    rw [Real.norm_eq_abs, abs_mul]
    calc |besselJ0 (x * t)| * |thG5 t / t| ≤ 1 * |thG5 t / t| :=
          mul_le_mul_of_nonneg_right j (abs_nonneg _)
      _ = |thG5 t / t| := one_mul _
  have hint : IntegrableOn
      (fun t : ℝ => (-x) * (besselJ1 (x * t) * thG4 t) + besselJ0 (x * t) * (thG5 t / t))
      (Set.Ioi 0) := i1.add i2
  have hz := integral_Ioi_deriv_eq_neg hd h0 hinf hint
  have a1 : (∫ t in Set.Ioi (0 : ℝ),
        ((-x) * (besselJ1 (x * t) * thG4 t) + besselJ0 (x * t) * (thG5 t / t)))
      = (∫ t in Set.Ioi (0 : ℝ), (-x) * (besselJ1 (x * t) * thG4 t))
        + ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * (thG5 t / t) := integral_add i1 i2
  have a2 : (∫ t in Set.Ioi (0 : ℝ), (-x) * (besselJ1 (x * t) * thG4 t))
      = (-x) * ∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * thG4 t := integral_const_mul _ _
  show x * (∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * thG4 t) = _
  linarith

/-- **`AJ(θ⁴g)(x) → 0`** as `x → ∞`. -/
theorem tendsto_AJ_thG4 : Tendsto (AJ thG4) atTop (nhds 0) := by
  have hD : Tendsto (fun x : ℝ => ∫ t in Set.Ioi (0 : ℝ), besselJ0 (x * t) * (thG5 t / t)) atTop
      (nhds (∫ t in Set.Ioi (0 : ℝ), (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => |thG5 t / t|) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall (fun x => ?_)
      have hc : ContinuousOn (fun t : ℝ => besselJ0 (x * t) * (thG5 t / t)) (Set.Ioi 0) :=
        (continuousOn_besselJ0_mul x).mul continuousOn_thG5_div
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
      have ht0 : (0 : ℝ) < t := ht
      have j := abs_besselJ0_le_one (mul_nonneg hx ht0.le)
      show ‖besselJ0 (x * t) * (thG5 t / t)‖ ≤ |thG5 t / t|
      rw [Real.norm_eq_abs, abs_mul]
      calc |besselJ0 (x * t)| * |thG5 t / t| ≤ 1 * |thG5 t / t| :=
            mul_le_mul_of_nonneg_right j (abs_nonneg _)
        _ = |thG5 t / t| := one_mul _
    · exact Integrable.abs integrableOn_thG5_div
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
      have ht0 : (0 : ℝ) < t := ht
      have hJ : Tendsto (fun x : ℝ => besselJ0 (x * t)) atTop (nhds 0) :=
        tendsto_besselJ0_atTop.comp (tendsto_id.atTop_mul_const ht0)
      have h := hJ.mul_const (thG5 t / t)
      rw [zero_mul] at h
      exact h
  rw [integral_zero] at hD
  refine hD.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [AJ_thG4_eq hx]

/-! ## `c = 0` -/

theorem abs_AJ_le {ψ : ℝ → ℝ} (hψ : PDom ψ) {x : ℝ} (hx : 0 < x) :
    |AJ ψ x| ≤ x * ∫ t in Set.Ioi (0 : ℝ), |ψ t| := by
  have hi : Integrable (fun t : ℝ => |ψ t|) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.abs (pdom_integrableOn hψ)
  have hb : ‖∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * ψ t‖ ≤ ∫ t in Set.Ioi (0 : ℝ), |ψ t| := by
    refine norm_integral_le_of_norm_le hi
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := ht
    have hJ := abs_besselJ1_le_one (mul_nonneg hx.le ht0.le)
    show ‖besselJ1 (x * t) * ψ t‖ ≤ |ψ t|
    rw [Real.norm_eq_abs, abs_mul]
    calc |besselJ1 (x * t)| * |ψ t| ≤ 1 * |ψ t| := mul_le_mul_of_nonneg_right hJ (abs_nonneg _)
      _ = |ψ t| := one_mul _
  rw [Real.norm_eq_abs] at hb
  show |x * ∫ t in Set.Ioi (0 : ℝ), besselJ1 (x * t) * ψ t| ≤ x * ∫ t in Set.Ioi (0 : ℝ), |ψ t|
  rw [abs_mul, abs_of_pos hx]
  exact mul_le_mul_of_nonneg_left hb hx.le

/-- `∫₀^∞ |θ g|`. -/
noncomputable def NG1 : ℝ := ∫ t in Set.Ioi (0 : ℝ), |thG1 t|

/-- `∫₀^∞ |θ² g|`. -/
noncomputable def NG2 : ℝ := ∫ t in Set.Ioi (0 : ℝ), |thG2 t|

/-- `∫₀^∞ |θ³ g|`. -/
noncomputable def NG3 : ℝ := ∫ t in Set.Ioi (0 : ℝ), |thG3 t|

/-- `∫₀^∞ |θ⁴ g|`. -/
noncomputable def NG4 : ℝ := ∫ t in Set.Ioi (0 : ℝ), |thG4 t|

/-- The constant of `|c - A₄(x)| ≤ KG/x`. -/
noncomputable def KG : ℝ :=
  4 * (5 * NG4 + 15 * NG3 + 18 * NG2 + 8 * NG1) + 64 * (NG4 + 6 * NG3 + 12 * NG2 + 8 * NG1)

theorem abs_c_sub_le {c : ℝ} (hc : ∀ x : ℝ, 0 < x → uG x = c * x ^ 2) {x : ℝ} (hx1 : 1 ≤ x) :
    |c - AJ thG4 x| ≤ KG / x := by
  have hx : 0 < x := by linarith
  have b1 : |AJ thG1 x| ≤ x * NG1 := abs_AJ_le pdom_thG1 hx
  have b2 : |AJ thG2 x| ≤ x * NG2 := abs_AJ_le pdom_thG2 hx
  have b3 : |AJ thG3 x| ≤ x * NG3 := abs_AJ_le pdom_thG3 hx
  have b4 : |AJ thG4 x| ≤ x * NG4 := abs_AJ_le pdom_thG4 hx
  obtain ⟨l1, u1⟩ := abs_le.mp b1
  obtain ⟨l2, u2⟩ := abs_le.mp b2
  obtain ⟨l3, u3⟩ := abs_le.mp b3
  obtain ⟨l4, u4⟩ := abs_le.mp b4
  have h := hc x hx
  unfold uG at h
  have hS1 : |5 * AJ thG4 x + 15 * AJ thG3 x + 18 * AJ thG2 x + 8 * AJ thG1 x|
      ≤ x * (5 * NG4 + 15 * NG3 + 18 * NG2 + 8 * NG1) := by
    rw [abs_le]
    constructor <;> linarith
  have hS2 : |AJ thG4 x + 6 * AJ thG3 x + 12 * AJ thG2 x + 8 * AJ thG1 x|
      ≤ x * (NG4 + 6 * NG3 + 12 * NG2 + 8 * NG1) := by
    rw [abs_le]
    constructor <;> linarith
  have hx2 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
  have hq : |(AJ thG4 x + 6 * AJ thG3 x + 12 * AJ thG2 x + 8 * AJ thG1 x) / x ^ 2|
      ≤ |AJ thG4 x + 6 * AJ thG3 x + 12 * AJ thG2 x + 8 * AJ thG1 x| := by
    rw [abs_div, abs_of_pos (pow_pos hx 2)]
    exact div_le_self (abs_nonneg _) hx2
  have t1 := abs_cmul_leG (c := (4 : ℝ)) (C := 4) (by norm_num) hS1
  have t2 := abs_cmul_leG (c := (64 : ℝ)) (C := 64) (by norm_num) (hq.trans hS2)
  have e : (c - AJ thG4 x) * x ^ 2
      = 4 * (5 * AJ thG4 x + 15 * AJ thG3 x + 18 * AJ thG2 x + 8 * AJ thG1 x)
        + 64 * ((AJ thG4 x + 6 * AJ thG3 x + 12 * AJ thG2 x + 8 * AJ thG1 x) / x ^ 2) := by
    linear_combination (-1 : ℝ) * h
  have tri := abs_add_le (4 * (5 * AJ thG4 x + 15 * AJ thG3 x + 18 * AJ thG2 x + 8 * AJ thG1 x))
    (64 * ((AJ thG4 x + 6 * AJ thG3 x + 12 * AJ thG2 x + 8 * AJ thG1 x) / x ^ 2))
  have h3 : |(c - AJ thG4 x) * x ^ 2| ≤ x * KG := by
    rw [e]
    unfold KG
    linarith
  rw [abs_mul, abs_of_nonneg (sq_nonneg x)] at h3
  have h4 : |c - AJ thG4 x| * x * x ≤ KG * x := by linarith
  have h5 : |c - AJ thG4 x| * x ≤ KG := le_of_mul_le_mul_right h4 hx
  rw [le_div_iff₀ hx]
  exact h5

/-- The constant of `uG_eq` is `0`. -/
theorem uG_c_zero {c : ℝ} (hc : ∀ x : ℝ, 0 < x → uG x = c * x ^ 2) : c = 0 := by
  have hK : Tendsto (fun x : ℝ => KG / x) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h1 : Tendsto (fun x : ℝ => c - AJ thG4 x) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx1
    rw [Real.norm_eq_abs]
    exact abs_c_sub_le hc hx1
  have h2 : Tendsto (fun x : ℝ => c - AJ thG4 x) atTop (nhds (c - 0)) :=
    tendsto_const_nhds.sub tendsto_AJ_thG4
  rw [sub_zero] at h2
  exact tendsto_nhds_unique h2 h1

/-- **The dual equation of `ajG`**: `x²A₄ + 4(5A₄ + 15A₃ + 18A₂ + 8A₁) + 64x⁻²(A₄ + 6A₃ + 12A₂ + 8A₁) = 0`
on `(0, ∞)`, `A_k = AJ(θᵏ g)`. -/
theorem uG_zero {x : ℝ} (hx : 0 < x) : uG x = 0 := by
  obtain ⟨c, hc⟩ := uG_eq
  rw [hc x hx, uG_c_zero hc, zero_mul]

end Tower.RV6
