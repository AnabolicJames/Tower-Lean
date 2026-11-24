import Mathlib
import Tower.RV6.BPEuler
import Tower.RV6.BPRclosed

/-!
# RungBP, step 5: `log Q(s)` as a series

For `0 ≤ u < 1` put `φ_k(u) = log((k + 1 + u)/(k + 1 - u)) - 2u/(k + 1)` (`phiK`).

* `|log((1 + x)/(1 - x)) - 2x| ≤ 2|x|³/(1 - |x|)` (two uses of Mathlib's
  `abs_log_sub_add_sum_range_le`), so `|φ_k(u)| ≤ 2u³/((1 - u)(k + 1)³)` and, for `k ≥ 1`,
  `|φ_k(u)| ≤ 4u³/(k + 1)³`.
* Euler's limit (`Real.GammaSeq_tendsto_Gamma`) and `H_n - log n → γ` give
  `Γ(1 - u)/Γ(1 + u) = exp(∑_k φ_k(u) + 2uγ)` (`gamma_ratio_eq_exp`).
* With `a₀ = log 2 - γ` (`a0_eq_gamma`) and `s j(s) = 2^{-s} Γ(1 - s/2)/Γ(1 + s/2)` (`jS_closed`):
  `Q(s) = e^{a₀ s} s j(s) = exp(ℓ(s))`, `ℓ(s) = ∑_k φ_k(s/2)` (`expQ_eq`).
-/

namespace Tower.RV6

open Real Set Filter Topology

/-- `φ_k(u) = log((k + 1 + u)/(k + 1 - u)) - 2u/(k + 1)`. -/
noncomputable def phiK (u : ℝ) (k : ℕ) : ℝ :=
  Real.log (((k : ℝ) + 1 + u) / ((k : ℝ) + 1 - u)) - 2 * u / ((k : ℝ) + 1)

theorem abs_log_ratio_sub_le {x : ℝ} (hx : |x| < 1) :
    |Real.log ((1 + x) / (1 - x)) - 2 * x| ≤ 2 * (|x| ^ 3 / (1 - |x|)) := by
  have h1 : |(∑ i ∈ Finset.range 2, x ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - x)|
      ≤ |x| ^ 3 / (1 - |x|) := Real.abs_log_sub_add_sum_range_le hx 2
  have h2 : |(∑ i ∈ Finset.range 2, (-x) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -x)|
      ≤ |-x| ^ 3 / (1 - |-x|) := Real.abs_log_sub_add_sum_range_le (by rwa [abs_neg]) 2
  have e1 : (∑ i ∈ Finset.range 2, x ^ (i + 1) / ((i : ℝ) + 1)) = x + x ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one]
    ring
  have e2 : (∑ i ∈ Finset.range 2, (-x) ^ (i + 1) / ((i : ℝ) + 1)) = -x + x ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one]
    ring
  rw [e1] at h1
  rw [e2, abs_neg, sub_neg_eq_add] at h2
  have hx1 : 0 < 1 - x := by
    have := le_abs_self x
    linarith
  have hx2 : 0 < 1 + x := by
    have := neg_abs_le x
    linarith
  rw [Real.log_div hx2.ne' hx1.ne']
  have e : Real.log (1 + x) - Real.log (1 - x) - 2 * x
      = (-x + x ^ 2 / 2 + Real.log (1 + x)) - (x + x ^ 2 / 2 + Real.log (1 - x)) := by ring
  rw [e]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem phiK_eq (u : ℝ) (k : ℕ) :
    phiK u k = Real.log ((1 + u / ((k : ℝ) + 1)) / (1 - u / ((k : ℝ) + 1)))
      - 2 * (u / ((k : ℝ) + 1)) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [phiK, one_add_div hk, one_sub_div hk, div_div_div_cancel_right₀ hk, mul_div_assoc]

theorem abs_phiK_le_gen {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (k : ℕ) :
    |phiK u k| ≤ 2 * u ^ 3 / ((1 - u) * ((k : ℝ) + 1) ^ 3) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  rw [phiK_eq]
  have hx0 : 0 ≤ u / ((k : ℝ) + 1) := div_nonneg hu0 hk0.le
  have hxu : u / ((k : ℝ) + 1) ≤ u := div_le_self hu0 hk1
  have h := abs_log_ratio_sub_le (x := u / ((k : ℝ) + 1)) (by rw [abs_of_nonneg hx0]; linarith)
  rw [abs_of_nonneg hx0] at h
  refine h.trans ?_
  have h3 : (u / ((k : ℝ) + 1)) ^ 3 / (1 - u / ((k : ℝ) + 1))
      ≤ (u / ((k : ℝ) + 1)) ^ 3 / (1 - u) :=
    div_le_div_of_nonneg_left (pow_nonneg hx0 3) (by linarith) (by linarith)
  calc 2 * ((u / ((k : ℝ) + 1)) ^ 3 / (1 - u / ((k : ℝ) + 1)))
      ≤ 2 * ((u / ((k : ℝ) + 1)) ^ 3 / (1 - u)) := by linarith
    _ = 2 * u ^ 3 / ((1 - u) * ((k : ℝ) + 1) ^ 3) := by ring

/-- For `k ≥ 1`: `|φ_k(u)| ≤ 4u³/(k + 1)³`. -/
theorem abs_phiK_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {k : ℕ} (hk : 1 ≤ k) :
    |phiK u k| ≤ 4 * u ^ 3 / ((k : ℝ) + 1) ^ 3 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  rw [phiK_eq]
  have hx0 : 0 ≤ u / ((k : ℝ) + 1) := div_nonneg hu0 hk0.le
  have hxh : u / ((k : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ hk0]
    linarith
  have h := abs_log_ratio_sub_le (x := u / ((k : ℝ) + 1)) (by rw [abs_of_nonneg hx0]; linarith)
  rw [abs_of_nonneg hx0] at h
  refine h.trans ?_
  have h3 : (u / ((k : ℝ) + 1)) ^ 3 / (1 - u / ((k : ℝ) + 1))
      ≤ (u / ((k : ℝ) + 1)) ^ 3 / (1 / 2) :=
    div_le_div_of_nonneg_left (pow_nonneg hx0 3) (by norm_num) (by linarith)
  calc 2 * ((u / ((k : ℝ) + 1)) ^ 3 / (1 - u / ((k : ℝ) + 1)))
      ≤ 2 * ((u / ((k : ℝ) + 1)) ^ 3 / (1 / 2)) := by linarith
    _ = 4 * u ^ 3 / ((k : ℝ) + 1) ^ 3 := by ring

theorem summable_inv_succ_cube : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 3) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 3))
  refine h.congr fun k => ?_
  simp only [Nat.cast_add, Nat.cast_one]

theorem summable_phiK {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : Summable (phiK u) := by
  refine Summable.of_norm_bounded (summable_inv_succ_cube.mul_left (2 * u ^ 3 / (1 - u)))
    fun k => ?_
  rw [Real.norm_eq_abs]
  refine (abs_phiK_le_gen hu0 hu1 k).trans (le_of_eq ?_)
  show 2 * u ^ 3 / ((1 - u) * ((k : ℝ) + 1) ^ 3) = 2 * u ^ 3 / (1 - u) * (1 / ((k : ℝ) + 1) ^ 3)
  ring

theorem div_aux_gamma {A B F P Q : ℝ} (hF : F ≠ 0) :
    (A * F / P) / (B * F / Q) = Q / P * (A / B) := by
  rw [div_div_div_eq, div_mul_div_comm, show A * F * Q = Q * A * F by ring,
    show P * (B * F) = P * B * F by ring, mul_div_mul_right _ _ hF]

theorem harmonic_cast_eq (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one,
    one_div]

/-- The ratio of Euler's sequences at `1 - u` and `1 + u`. -/
theorem gammaSeq_ratio {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {n : ℕ} (hn : 1 ≤ n) :
    Real.GammaSeq (1 - u) n / Real.GammaSeq (1 + u) n
      = Real.exp (∑ k ∈ Finset.range (n + 1), phiK u k
          + 2 * u * ((harmonic (n + 1) : ℝ) - Real.log n)) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hF : ((n.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hpos : ∀ k : ℕ, 0 < (k : ℝ) + 1 - u := fun k => by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hpos' : ∀ k : ℕ, 0 < (k : ℝ) + 1 + u := fun k => by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have h2 : ∑ k ∈ Finset.range (n + 1), 2 * u / ((k : ℝ) + 1)
      = 2 * u * ∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hexp : ∑ k ∈ Finset.range (n + 1), phiK u k
        + 2 * u * ((harmonic (n + 1) : ℝ) - Real.log n)
      = ∑ k ∈ Finset.range (n + 1), Real.log (((k : ℝ) + 1 + u) / ((k : ℝ) + 1 - u))
        + Real.log n * ((1 - u) - (1 + u)) := by
    simp only [phiK]
    rw [Finset.sum_sub_distrib, h2, harmonic_cast_eq]
    ring
  have hprod : ∏ k ∈ Finset.range (n + 1),
        Real.exp (Real.log (((k : ℝ) + 1 + u) / ((k : ℝ) + 1 - u)))
      = ∏ k ∈ Finset.range (n + 1), (((k : ℝ) + 1 + u) / ((k : ℝ) + 1 - u)) :=
    Finset.prod_congr rfl fun k _ => Real.exp_log (div_pos (hpos' k) (hpos k))
  have hQe : ∏ j ∈ Finset.range (n + 1), (1 + u + (j : ℝ))
      = ∏ k ∈ Finset.range (n + 1), ((k : ℝ) + 1 + u) :=
    Finset.prod_congr rfl fun j _ => by ring
  have hPe : ∏ j ∈ Finset.range (n + 1), (1 - u + (j : ℝ))
      = ∏ k ∈ Finset.range (n + 1), ((k : ℝ) + 1 - u) :=
    Finset.prod_congr rfl fun j _ => by ring
  rw [hexp, Real.exp_add, Real.exp_sum, hprod, Finset.prod_div_distrib,
    ← Real.rpow_def_of_pos hn0, Real.rpow_sub hn0]
  simp only [Real.GammaSeq]
  rw [div_aux_gamma hF, hQe, hPe]

/-- `Γ(1 - u)/Γ(1 + u) = exp(∑_k φ_k(u) + 2uγ)` for `0 ≤ u < 1`. -/
theorem gamma_ratio_eq_exp {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.Gamma (1 - u) / Real.Gamma (1 + u)
      = Real.exp (∑' k, phiK u k + 2 * u * Real.eulerMascheroniConstant) := by
  have hlimL : Tendsto (fun n : ℕ => Real.GammaSeq (1 - u) n / Real.GammaSeq (1 + u) n) atTop
      (𝓝 (Real.Gamma (1 - u) / Real.Gamma (1 + u))) :=
    (Real.GammaSeq_tendsto_Gamma _).div (Real.GammaSeq_tendsto_Gamma _)
      (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hS : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), phiK u k) atTop
      (𝓝 (∑' k, phiK u k)) :=
    (summable_phiK hu0 hu1).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hH : Tendsto (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log n) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    have h := Real.tendsto_harmonic_sub_log.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [add_zero] at h
    refine h.congr fun n => ?_
    simp only [harmonic_succ]
    push_cast
    ring
  have hR := (Real.continuous_exp.tendsto _).comp (hS.add (hH.const_mul (2 * u)))
  refine tendsto_nhds_unique hlimL (hR.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (gammaSeq_ratio hu0 hu1 hn).symm

theorem log_gamma_ratio {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.log (Real.Gamma (1 - u) / Real.Gamma (1 + u))
      = ∑' k, phiK u k + 2 * u * Real.eulerMascheroniConstant := by
  rw [gamma_ratio_eq_exp hu0 hu1, Real.log_exp]

/-- `ℓ(s) = ∑_k φ_k(s/2)`. -/
noncomputable def ellQ (s : ℝ) : ℝ := ∑' k, phiK (s / 2) k

/-- `Q(s) = e^{a₀ s} s j(s) = exp(ℓ(s))` for `0 < s < 2`. -/
theorem expQ_eq {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    Real.exp (a0 * s) * (s * jS s) = Real.exp (ellQ s) := by
  rw [jS_closed hs0 hs2, mul_div_assoc,
    gamma_ratio_eq_exp (u := s / 2) (by linarith) (by linarith),
    Real.rpow_def_of_pos two_pos, a0_eq_gamma, ← Real.exp_add, ← Real.exp_add, ellQ]
  congr 1
  ring

end Tower.RV6
