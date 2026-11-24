import Mathlib
import Tower.RV6.BPPhi
import Tower.RV6.BPHs

/-!
# RungBP, step 8 (series side): `Λ(v)`, `T₁`, `E(s)` and `E(s)/s⁴ → ζ(5)/32`

With `K = n + 1` and `b_K = binom(s/2, K)` (`bk`):

* `Λ(v) = ∑ b_K²/(2K + v)` (`lamS`), `T₁ = ∑ b_K²/(4K²)` (`t1S`), `E(s) = Λ(-s) - Λ(0) - s T₁` (`eS`);
  `b_K² ≤ s²/(4K²)`, so the series converge for `v ≥ -1` and `Λ` is continuous on `[-1, ∞)`.
* `E(s) = ∑ s² b_K²/(4K²(2K - s))` (`eS_eq_tsum`).
* `(b_K/s)² → 1/(4K²)` (`tendsto_bk_div_sq`), hence `E(s)/s⁴ → ∑ 1/(32K⁵) = zN 5/32`
  (`tendsto_eS_div`, dominated convergence for series).
-/

namespace Tower.RV6

open Real Set Filter Topology

/-- `Λ(v) = ∑_{n ≥ 0} b_{n+1}²/(2(n + 1) + v)`. -/
noncomputable def lamS (s v : ℝ) : ℝ := ∑' n : ℕ, bk s (n + 1) ^ 2 / (2 * ((n : ℝ) + 1) + v)

/-- `T₁ = ∑_{n ≥ 0} b_{n+1}²/(4(n + 1)²)`. -/
noncomputable def t1S (s : ℝ) : ℝ := ∑' n : ℕ, bk s (n + 1) ^ 2 / (4 * ((n : ℝ) + 1) ^ 2)

/-- `E(s) = Λ(-s) - Λ(0) - s T₁`. -/
noncomputable def eS (s : ℝ) : ℝ := lamS s (-s) - lamS s 0 - s * t1S s

theorem bk_sq_le {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) (n : ℕ) :
    bk s (n + 1) ^ 2 ≤ s ^ 2 / 4 * (1 / ((n : ℝ) + 1) ^ 2) := by
  have h := abs_bk_le h0 h2 (Nat.succ_le_succ (Nat.zero_le n))
  push_cast at h
  have h2' := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at h2'
  calc bk s (n + 1) ^ 2 ≤ (s / 2 / ((n : ℝ) + 1)) ^ 2 := h2'
    _ = s ^ 2 / 4 * (1 / ((n : ℝ) + 1) ^ 2) := by
      rw [div_pow, div_pow]
      ring

theorem lam_term_le {s v : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) (hv : -1 ≤ v) (n : ℕ) :
    0 ≤ bk s (n + 1) ^ 2 / (2 * ((n : ℝ) + 1) + v)
      ∧ bk s (n + 1) ^ 2 / (2 * ((n : ℝ) + 1) + v) ≤ s ^ 2 / 4 * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : 1 ≤ 2 * ((n : ℝ) + 1) + v := by linarith
  exact ⟨div_nonneg (sq_nonneg _) (by linarith),
    (div_le_self (sq_nonneg _) hd).trans (bk_sq_le h0 h2 n)⟩

theorem summable_lam_term {s v : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) (hv : -1 ≤ v) :
    Summable (fun n : ℕ => bk s (n + 1) ^ 2 / (2 * ((n : ℝ) + 1) + v)) :=
  Summable.of_nonneg_of_le (fun n => (lam_term_le h0 h2 hv n).1)
    (fun n => (lam_term_le h0 h2 hv n).2) ((summable_zN le_rfl).mul_left (s ^ 2 / 4))

theorem summable_t1_term {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) :
    Summable (fun n : ℕ => bk s (n + 1) ^ 2 / (4 * ((n : ℝ) + 1) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (sq_nonneg _) (by positivity))
    (fun n => ?_) ((summable_zN le_rfl).mul_left (s ^ 2 / 4))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : 1 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith
  exact (div_le_self (sq_nonneg _) hd).trans (bk_sq_le h0 h2 n)

theorem continuousOn_lamS {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) : ContinuousOn (lamS s) (Ici (-1)) := by
  refine continuousOn_tsum (u := fun n : ℕ => s ^ 2 / 4 * (1 / ((n : ℝ) + 1) ^ 2))
    (fun n => ?_) ((summable_zN le_rfl).mul_left (s ^ 2 / 4)) (fun n v hv => ?_)
  · refine continuousOn_const.div (continuousOn_const.add continuousOn_id) (fun v hv => ?_)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hv' : (-1 : ℝ) ≤ v := hv
    exact (show (0 : ℝ) < 2 * ((n : ℝ) + 1) + id v by simp only [id]; linarith).ne'
  · have h := lam_term_le h0 h2 (show (-1 : ℝ) ≤ v from hv) n
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2

theorem e_term_eq {K s x : ℝ} (hK : 0 < K) (hs : s < 2 * K) :
    x / (2 * K + -s) - x / (2 * K + 0) - s * (x / (4 * K ^ 2))
      = s ^ 2 * x / (4 * K ^ 2 * (2 * K - s)) := by
  have h1 : 2 * K + -s ≠ 0 := (show (0 : ℝ) < 2 * K + -s by linarith).ne'
  have h2 : 2 * K - s ≠ 0 := (show (0 : ℝ) < 2 * K - s by linarith).ne'
  have h3 : K ≠ 0 := hK.ne'
  rw [add_zero]
  field_simp
  ring

/-- `E(s) = ∑ s² b_K²/(4K²(2K - s))` for `0 ≤ s ≤ 1`. -/
theorem eS_eq_tsum {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    eS s = ∑' n : ℕ, s ^ 2 * bk s (n + 1) ^ 2 / (4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - s)) := by
  have h2 : s ≤ 2 := by linarith
  have hA := summable_lam_term (v := -s) h0 h2 (by linarith)
  have hB := summable_lam_term (v := 0) h0 h2 (by norm_num)
  have hC := (summable_t1_term h0 h2).mul_left s
  rw [eS, lamS, lamS, t1S, ← tsum_mul_left, ← hA.tsum_sub hB, ← (hA.sub hB).tsum_sub hC]
  refine tsum_congr fun n => ?_
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact e_term_eq hK (by linarith)

/-- `(b_{n+1}/s)² → 1/(4(n + 1)²)` as `s → 0+`. -/
theorem tendsto_bk_div_sq (n : ℕ) :
    Tendsto (fun s : ℝ => (bk s (n + 1) / s) ^ 2) (𝓝[>] 0) (𝓝 (1 / (4 * ((n : ℝ) + 1) ^ 2))) := by
  induction n with
  | zero =>
    have h : (fun _ : ℝ => (1 : ℝ) / (4 * (((0 : ℕ) : ℝ) + 1) ^ 2))
        =ᶠ[𝓝[>] 0] fun s : ℝ => (bk s (0 + 1) / s) ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : s ≠ 0 := (show (0 : ℝ) < s from hs).ne'
      rw [zero_add, bk_one, div_right_comm, div_self hs0, Nat.cast_zero]
      norm_num
    exact tendsto_const_nhds.congr' h
  | succ n ih =>
    have hc := ((by fun_prop : Continuous (fun s : ℝ => ((s / 2 - ((n : ℝ) + 1)) / ((n : ℝ) + 2)) ^ 2)).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have h := ih.mul hc
    have hval : 1 / (4 * ((n : ℝ) + 1) ^ 2) * (((0 : ℝ) / 2 - ((n : ℝ) + 1)) / ((n : ℝ) + 2)) ^ 2
        = 1 / (4 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2) := by
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
      have h3 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      all_goals ring
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [bk_succ s (n + 1)]
    push_cast
    ring

/-- **`E(s)/s⁴ → ζ(5)/32`** (as `zN 5/32`). -/
theorem tendsto_eS_div : Tendsto (fun s : ℝ => eS s / s ^ 4) (𝓝[>] 0) (𝓝 (zN 5 / 32)) := by
  have hF : (fun s : ℝ => ∑' n : ℕ, (bk s (n + 1) / s) ^ 2
        / (4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - s)))
      =ᶠ[𝓝[>] 0] fun s : ℝ => eS s / s ^ 4 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
    rw [eS_eq_tsum hs.1.le hs.2.le, ← tsum_div_const]
    refine tsum_congr fun n => ?_
    have hs0 : s ≠ 0 := hs.1.ne'
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hD : 4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - s) ≠ 0 :=
      (mul_pos (by positivity) (show (0 : ℝ) < 2 * ((n : ℝ) + 1) - s by linarith [hs.2])).ne'
    field_simp
    all_goals ring
  have hbound : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ n : ℕ,
      ‖(bk s (n + 1) / s) ^ 2 / (4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - s))‖
        ≤ 1 / 16 * (1 / ((n : ℝ) + 1) ^ 5) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hb := bk_sq_le hs.1.le (by linarith [hs.2]) n
    have hq : (bk s (n + 1) / s) ^ 2 ≤ 1 / 4 * (1 / ((n : ℝ) + 1) ^ 2) := by
      rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 2)]
      calc bk s (n + 1) ^ 2 ≤ s ^ 2 / 4 * (1 / ((n : ℝ) + 1) ^ 2) := hb
        _ = 1 / 4 * (1 / ((n : ℝ) + 1) ^ 2) * s ^ 2 := by ring
    have hD : 4 * ((n : ℝ) + 1) ^ 3 ≤ 4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - s) := by
      have := hs.2
      nlinarith [mul_nonneg (sq_nonneg ((n : ℝ) + 1)) (show (0 : ℝ) ≤ (n : ℝ) + 1 - s by linarith)]
    have hD0 : (0 : ℝ) < 4 * ((n : ℝ) + 1) ^ 3 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hD0.le.trans hD))]
    calc (bk s (n + 1) / s) ^ 2 / (4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - s))
        ≤ (1 / 4 * (1 / ((n : ℝ) + 1) ^ 2)) / (4 * ((n : ℝ) + 1) ^ 3) :=
          div_le_div₀ (by positivity) hq hD0 hD
      _ = 1 / 16 * (1 / ((n : ℝ) + 1) ^ 5) := by
          have hK' : (n : ℝ) + 1 ≠ 0 := hK.ne'
          field_simp
          all_goals ring
  have hab : ∀ n : ℕ, Tendsto (fun s : ℝ => (bk s (n + 1) / s) ^ 2
        / (4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - s))) (𝓝[>] 0)
      (𝓝 (1 / (4 * ((n : ℝ) + 1) ^ 2) / (4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - 0)))) := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine (tendsto_bk_div_sq n).div (((by fun_prop : Continuous (fun s : ℝ =>
      4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - s))).tendsto 0).mono_left nhdsWithin_le_nhds) ?_
    have : (0 : ℝ) < 4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - 0) := by
      rw [sub_zero]
      positivity
    exact this.ne'
  have hlim := tendsto_tsum_of_dominated_convergence
    ((summable_zN (by norm_num : 2 ≤ 5)).mul_left (1 / 16)) hab hbound
  have hval : ∑' n : ℕ, 1 / (4 * ((n : ℝ) + 1) ^ 2) / (4 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) - 0))
      = zN 5 / 32 := by
    rw [zN, ← tsum_div_const]
    refine tsum_congr fun n => ?_
    have hK : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    all_goals ring
  rw [hval] at hlim
  exact hlim.congr' hF

end Tower.RV6
