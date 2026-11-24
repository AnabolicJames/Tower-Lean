import Mathlib
import Tower.RV6.BPModel
import Tower.RV6.BPIbp
import Tower.RV6.LadderB
import Tower.RV6.DomG
import Tower.RV6.HankelDomF

/-!
# RungBP, step 4: `pairS(s) = j(s) ∫_τ F₂(τ) ∫_t G(t) [min(τ,t)^s - k_H(τ,t)]`

`F₂ = θ²f/τ`, `G = -θg/t`.  `k_H = min^s - (τ^s + t^s - M_s(τ,t))` (`kerH`), so `k_s = j(s)(min^s - k_H)`;
for `0 < t ≤ τ`, `k_H = τ^s h_s((t/τ)²) ≥ 0`.

* `min(τ,t)^s ≤ τ^{s/2} t^{s/2}` and `E(t) ≤ (1 + 1/δ)(2/t)^δ`, so `|F₂| τ^{s/2}` and `|G| t^{s/2}` are integrable on
  `(0, ∞)` (wave 59's log bounds near `0`, the exponential and `t⁻²` bounds beyond `1`).
* Fubini in `(x, (τ, t))`, the `x`-integral last: `pairS(s) = ∫_{(τ,t)} F₂ G k_s` (`pairS_eq_fubini`).
-/

namespace Tower.RV6

open Real MeasureTheory Set Filter Topology

/-- `k_H(τ, t) = min(τ,t)^s - (τ^s + t^s - M_s(τ, t))`. -/
noncomputable def kerH (s τ t : ℝ) : ℝ := min τ t ^ s - (τ ^ s + t ^ s - angM s τ t)

theorem hS_nonneg_le_one {s w : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ hS s w := by
  rcases hw1.lt_or_eq with h | h
  · exact hS_nonneg hs0 hs2 hw0 h
  · subst h
    have hlim : Tendsto (hS s) (𝓝[<] 1) (𝓝 (hS s 1)) :=
      ((continuous_hS hs0).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with w hw
    exact hS_nonneg hs0 hs2 hw.1.le hw.2

theorem kerH_eq_le {s τ t : ℝ} (ht : 0 < t) (htτ : t ≤ τ) :
    kerH s τ t = τ ^ s * hS s ((t / τ) ^ 2) := by
  have hτ : 0 < τ := lt_of_lt_of_le ht htτ
  rw [kerH, min_eq_right htτ, angM_homog hτ, angM_one_eq_hS s (div_nonneg ht.le hτ.le)]
  ring

theorem kerH_symm (s τ t : ℝ) : kerH s τ t = kerH s t τ := by
  rw [kerH, kerH, min_comm, angM_symm]
  ring

theorem kerH_nonneg {s τ t : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hτ : 0 < τ) (ht : 0 < t) :
    0 ≤ kerH s τ t := by
  rcases le_total t τ with h | h
  · rw [kerH_eq_le ht h]
    exact mul_nonneg (Real.rpow_nonneg hτ.le _) (hS_nonneg_le_one hs0 hs2 (sq_nonneg _)
      (pow_le_one₀ (div_nonneg ht.le hτ.le) ((div_le_one hτ).2 h)))
  · rw [kerH_symm, kerH_eq_le hτ h]
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (hS_nonneg_le_one hs0 hs2 (sq_nonneg _)
      (pow_le_one₀ (div_nonneg hτ.le ht.le) ((div_le_one ht).2 h)))

theorem kerS_nonneg {s τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) : 0 ≤ kerS s τ t := by
  unfold kerS
  refine setIntegral_nonneg measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  exact mul_nonneg (mul_nonneg (one_sub_besselJ0_nonneg (mul_nonneg hx0.le hτ))
    (one_sub_besselJ0_nonneg (mul_nonneg hx0.le ht))) (Real.rpow_nonneg hx0.le _)

theorem kerS_eq_kerH {s τ t : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    kerS s τ t = jS s * (min τ t ^ s - kerH s τ t) := by
  rw [kerS_eq hs0 hs2 hτ ht, kerH]
  ring

theorem min_rpow_le {s τ t : ℝ} (hs : 0 < s) (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    min τ t ^ s ≤ τ ^ (s / 2) * t ^ (s / 2) := by
  have hm0 : 0 ≤ min τ t := le_min hτ ht
  have hm2 : min τ t * min τ t ≤ τ * t :=
    mul_le_mul (min_le_left _ _) (min_le_right _ _) hm0 hτ
  calc min τ t ^ s = min τ t ^ (s / 2) * min τ t ^ (s / 2) := by
        rw [← Real.rpow_add' hm0 (show s / 2 + s / 2 ≠ 0 from ne_of_gt (by linarith))]
        congr 1
        ring
    _ = (min τ t * min τ t) ^ (s / 2) := (Real.mul_rpow hm0 hm0).symm
    _ ≤ (τ * t) ^ (s / 2) := Real.rpow_le_rpow (mul_nonneg hm0 hm0) hm2 (by linarith)
    _ = τ ^ (s / 2) * t ^ (s / 2) := Real.mul_rpow hτ ht

theorem min_rpow_sub_kerH_nonneg {s τ t : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hτ : 0 < τ)
    (ht : 0 < t) : 0 ≤ min τ t ^ s - kerH s τ t := by
  have h := kerS_nonneg (s := s) hτ.le ht.le
  rw [kerS_eq_kerH hs0 hs2 hτ.le ht.le] at h
  exact (mul_nonneg_iff_of_pos_left (jS_pos hs0 hs2)).1 h

theorem Eb_le_rpow {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) (ht1 : t ≤ 1) :
    Eb t ≤ (1 + 1 / δ) * (2 / t) ^ δ := by
  have hy : 1 ≤ 2 / t := by
    rw [le_div_iff₀ ht]
    linarith
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 2 / t) hδ
  have h2 : 1 ≤ (2 / t) ^ δ := Real.one_le_rpow hy hδ.le
  unfold Eb
  have e : (1 + 1 / δ) * (2 / t) ^ δ = (2 / t) ^ δ + (2 / t) ^ δ / δ := by ring
  rw [e]
  linarith

theorem continuousOn_Eb : ContinuousOn Eb (Ioi 0) := by
  show ContinuousOn (fun t : ℝ => 1 + Real.log (2 / t)) (Ioi 0)
  refine continuousOn_const.add (ContinuousOn.log ?_ ?_)
  · exact continuousOn_const.div continuousOn_id (fun t ht => (show (0 : ℝ) < t from ht).ne')
  · intro t ht
    exact div_ne_zero two_ne_zero (show (0 : ℝ) < t from ht).ne'

theorem integrableOn_Eb_pow_rpow {k : ℕ} {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun t : ℝ => Eb t ^ k * t ^ a) (Ioc 0 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set δ : ℝ := (a + 1) / (2 * ((k : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  have hδk : δ * (k : ℝ) ≤ (a + 1) / 2 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hb : IntegrableOn (fun t : ℝ => ((1 + 1 / δ) ^ k * 2 ^ (δ * (k : ℝ))) * t ^ (a - δ * k))
      (Ioc 0 1) := (integrableOn_rpow_Ioc01 (by linarith)).const_mul _
  refine Integrable.mono' hb ?_ (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact ((continuousOn_Eb.mono Ioc_subset_Ioi_self).pow k).mul
      (ContinuousOn.rpow_const (continuousOn_id (s := Ioc (0 : ℝ) 1))
        (fun t ht => Or.inl (show (0 : ℝ) < t from ht.1).ne'))
  · have ht0 : (0 : ℝ) < t := ht.1
    have hE1 := one_le_Eb ht0 ht.2
    have hE := Eb_le_rpow hδ ht0 ht.2
    have hp : 0 < t ^ a := Real.rpow_pos_of_pos ht0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (by linarith) k) hp.le)]
    have h1 : Eb t ^ k ≤ ((1 + 1 / δ) * (2 / t) ^ δ) ^ k := pow_le_pow_left₀ (by linarith) hE k
    have h2 : ((1 + 1 / δ) * (2 / t) ^ δ) ^ k * t ^ a
        = ((1 + 1 / δ) ^ k * 2 ^ (δ * (k : ℝ))) * t ^ (a - δ * k) := by
      rw [mul_pow, ← Real.rpow_natCast ((2 / t) ^ δ) k,
        ← Real.rpow_mul (div_nonneg zero_le_two ht0.le), Real.div_rpow zero_le_two ht0.le,
        Real.rpow_sub ht0]
      ring
    calc Eb t ^ k * t ^ a ≤ ((1 + 1 / δ) * (2 / t) ^ δ) ^ k * t ^ a :=
          mul_le_mul_of_nonneg_right h1 hp.le
      _ = _ := h2

/-- `∫₀^∞ |F₂(τ)| τ^{s/2} dτ < ∞` for `s > 0`. -/
theorem integrableOn_F2_rpow {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun τ : ℝ => |thF2 τ / τ| * τ ^ (s / 2)) (Ioi 0) := by
  have hc : ContinuousOn (fun τ : ℝ => |thF2 τ / τ| * τ ^ (s / 2)) (Ioi 0) :=
    ((hdom_thF2.1.div continuousOn_id (fun τ hτ => (show (0 : ℝ) < τ from hτ).ne')).abs).mul
      (ContinuousOn.rpow_const (continuousOn_id (s := Ioi (0 : ℝ)))
        (fun τ hτ => Or.inl (show (0 : ℝ) < τ from hτ).ne'))
  obtain ⟨C1, hC1⟩ := abs_thF2_le_log
  obtain ⟨_, C2, hC2, N, _, hN⟩ := hdom_thF2
  have i1 : IntegrableOn (fun τ : ℝ => |thF2 τ / τ| * τ ^ (s / 2)) (Ioc 0 1) := by
    refine Integrable.mono' ((integrableOn_Eb_pow_rpow (k := 3) (a := s / 2 - 1)
      (by linarith)).const_mul |C1|) ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc) (ae_restrict_of_forall_mem measurableSet_Ioc (fun τ hτ => ?_))
    have hτ0 : (0 : ℝ) < τ := hτ.1
    have hE1 := one_le_Eb hτ0 hτ.2
    have h1 := hC1 τ hτ0 hτ.2
    have hp : 0 < τ ^ (s / 2 - 1) := Real.rpow_pos_of_pos hτ0 _
    have e : |thF2 τ / τ| * τ ^ (s / 2) = |thF2 τ| * τ ^ (s / 2 - 1) := by
      rw [abs_div, abs_of_pos hτ0, Real.rpow_sub hτ0, Real.rpow_one]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hτ0.le _)), e]
    have hC : C1 * Eb τ ^ 3 ≤ |C1| * Eb τ ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self C1) (pow_nonneg (by linarith) 3)
    calc |thF2 τ| * τ ^ (s / 2 - 1) ≤ |C1| * Eb τ ^ 3 * τ ^ (s / 2 - 1) :=
          mul_le_mul_of_nonneg_right (h1.trans hC) hp.le
      _ = |C1| * (Eb τ ^ 3 * τ ^ (s / 2 - 1)) := by ring
  have i2 : IntegrableOn (fun τ : ℝ => |thF2 τ / τ| * τ ^ (s / 2)) (Ioi 1) := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hg := (Real.GammaIntegral_convergent (by linarith : (0 : ℝ) < (N : ℝ) + s / 2)).mono_set
      (Ioi_subset_Ioi zero_le_one)
    refine Integrable.mono' (hg.const_mul C2) ((hc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi (fun τ hτ => ?_))
    have hτ1 : (1 : ℝ) < τ := hτ
    have hτ0 : (0 : ℝ) < τ := by linarith
    have h1 := hN τ hτ1.le
    have e : |thF2 τ / τ| * τ ^ (s / 2) = |thF2 τ| * τ ^ (s / 2 - 1) := by
      rw [abs_div, abs_of_pos hτ0, Real.rpow_sub hτ0, Real.rpow_one]
      ring
    have e2 : τ ^ N * τ ^ (s / 2 - 1) = τ ^ ((N : ℝ) + s / 2 - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hτ0]
      congr 1
      ring
    have hp : 0 < τ ^ (s / 2 - 1) := Real.rpow_pos_of_pos hτ0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hτ0.le _)), e]
    calc |thF2 τ| * τ ^ (s / 2 - 1) ≤ C2 * τ ^ N * Real.exp (-τ) * τ ^ (s / 2 - 1) :=
          mul_le_mul_of_nonneg_right h1 hp.le
      _ = C2 * (Real.exp (-τ) * τ ^ ((N : ℝ) + s / 2 - 1)) := by
          rw [← e2]
          ring
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact i1.union i2

/-- `∫₀^∞ |G(t)| t^{s/2} dt < ∞` for `0 < s < 4`. -/
theorem integrableOn_G_rpow {s : ℝ} (hs : 0 < s) (hs4 : s < 4) :
    IntegrableOn (fun t : ℝ => |-thG1 t / t| * t ^ (s / 2)) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => |-thG1 t / t| * t ^ (s / 2)) (Ioi 0) :=
    ((continuousOn_thG1.neg.div continuousOn_id (fun t ht => (show (0 : ℝ) < t from ht).ne')).abs).mul
      (ContinuousOn.rpow_const (continuousOn_id (s := Ioi (0 : ℝ)))
        (fun t ht => Or.inl (show (0 : ℝ) < t from ht).ne'))
  obtain ⟨C1, hC1⟩ := abs_thG1_le_log
  have i1 : IntegrableOn (fun t : ℝ => |-thG1 t / t| * t ^ (s / 2)) (Ioc 0 1) := by
    refine Integrable.mono' ((integrableOn_Eb_pow_rpow (k := 2) (a := s / 2 - 1)
      (by linarith)).const_mul |C1|) ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc) (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := ht.1
    have hE1 := one_le_Eb ht0 ht.2
    have h1 := hC1 t ht0 ht.2
    have hp : 0 < t ^ (s / 2 - 1) := Real.rpow_pos_of_pos ht0 _
    have e : |-thG1 t / t| * t ^ (s / 2) = |thG1 t| * t ^ (s / 2 - 1) := by
      rw [abs_div, abs_neg, abs_of_pos ht0, Real.rpow_sub ht0, Real.rpow_one]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht0.le _)), e]
    have hC : C1 * Eb t ^ 2 ≤ |C1| * Eb t ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self C1) (sq_nonneg _)
    calc |thG1 t| * t ^ (s / 2 - 1) ≤ |C1| * Eb t ^ 2 * t ^ (s / 2 - 1) :=
          mul_le_mul_of_nonneg_right (h1.trans hC) hp.le
      _ = |C1| * (Eb t ^ 2 * t ^ (s / 2 - 1)) := by ring
  have i2 : IntegrableOn (fun t : ℝ => |-thG1 t / t| * t ^ (s / 2)) (Ioi 1) := by
    have hg : IntegrableOn (fun t : ℝ => 16 * t ^ (s / 2 - 3)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    refine Integrable.mono' hg ((hc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have h1 := abs_tsq_thG1_le ht0
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)] at h1
    have hp : 0 < t ^ (s / 2 - 3) := Real.rpow_pos_of_pos ht0 _
    have e : |-thG1 t / t| * t ^ (s / 2) = (t ^ 2 * |thG1 t|) * t ^ (s / 2 - 3) := by
      rw [abs_div, abs_neg, abs_of_pos ht0, Real.rpow_sub ht0]
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
      all_goals ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht0.le _)), e]
    exact mul_le_mul_of_nonneg_right h1 hp.le
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact i1.union i2

theorem kerS_le_rpow {s τ t : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hτ : 0 < τ) (ht : 0 < t) :
    kerS s τ t ≤ jS s * (τ ^ (s / 2) * t ^ (s / 2)) := by
  rw [kerS_eq_kerH hs0 hs2 hτ.le ht.le]
  have h1 := kerH_nonneg hs0.le hs2.le hτ ht
  have h2 := min_rpow_le hs0 hτ.le ht.le
  exact mul_le_mul_of_nonneg_left (by linarith) (jS_pos hs0 hs2).le

theorem integrableOn_kerS_integrand {s τ t : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hτ : 0 ≤ τ)
    (ht : 0 ≤ t) :
    IntegrableOn (fun x : ℝ => (1 - besselJ0 (x * τ)) * (1 - besselJ0 (x * t)) * x ^ (-1 - s))
      (Ioi 0) := by
  have h := (integrableOn_one_sub_scale hs0 hs2 hτ).const_mul 2
  refine Integrable.mono' h ?_ (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((continuous_const.sub (continuous_besselJ0.comp (continuous_mul_const τ))).mul
      (continuous_const.sub (continuous_besselJ0.comp (continuous_mul_const t)))).continuousOn.mul
      (ContinuousOn.rpow_const (continuousOn_id (s := Ioi (0 : ℝ)))
        (fun x hx => Or.inl (show (0 : ℝ) < x from hx).ne'))
  · have hx0 : (0 : ℝ) < x := hx
    have a1 := one_sub_besselJ0_nonneg (mul_nonneg hx0.le hτ)
    have a2 := one_sub_besselJ0_nonneg (mul_nonneg hx0.le ht)
    have a3 : 1 - besselJ0 (x * t) ≤ 2 := by
      have := (abs_le.mp (abs_besselJ0_le_one (mul_nonneg hx0.le ht))).1
      linarith
    have hp := Real.rpow_pos_of_pos hx0 (-1 - s)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg a1 a2) hp.le)]
    calc (1 - besselJ0 (x * τ)) * (1 - besselJ0 (x * t)) * x ^ (-1 - s)
        ≤ (1 - besselJ0 (x * τ)) * 2 * x ^ (-1 - s) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a3 a1) hp.le
      _ = 2 * ((1 - besselJ0 (x * τ)) * x ^ (-1 - s)) := by ring

/-- The integrand of `pairS` on `(0, ∞) × (0, ∞)²`. -/
noncomputable def fubPhi (s x : ℝ) (p : ℝ × ℝ) : ℝ :=
  thF2 p.1 / p.1 * (1 - besselJ0 (x * p.1)) * (-thG1 p.2 / p.2 * (1 - besselJ0 (x * p.2)))
    * x ^ (-1 - s)

/-- **Fubini for the pairing**: `pairS(s) = j(s) ∫_τ F₂(τ) ∫_t G(t) (min(τ,t)^s - k_H(τ,t))`, `0 < s ≤ 1`. -/
theorem pairS_eq_fubini {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    pairS s = jS s * ∫ τ in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      thF2 τ / τ * (-thG1 t / t) * (min τ t ^ s - kerH s τ t) := by
  have hs2 : s < 2 := by linarith
  have hν : ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
      = ((volume : Measure ℝ).prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    Measure.prod_restrict _ _
  have hS : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))), p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    rw [hν]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  -- the product majorant
  have hP : Integrable (fun p : ℝ × ℝ => (|thF2 p.1 / p.1| * p.1 ^ (s / 2))
      * (|-thG1 p.2 / p.2| * p.2 ^ (s / 2)))
      (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
        ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))) :=
    Integrable.mul_prod (integrableOn_F2_rpow hs0) (integrableOn_G_rpow hs0 (by linarith))
  -- step 1: the x-integrand as a product integral
  have h1 : ∀ x ∈ Ioi (0 : ℝ), hjF x * ajG x * x ^ (1 - s)
      = ∫ p, fubPhi s x p ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
          ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have e1 : x ^ (1 - s) = x ^ 2 * x ^ (-1 - s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
      congr 1
      push_cast
      ring
    rw [e1, show hjF x * ajG x * (x ^ 2 * x ^ (-1 - s)) = (x ^ 2 * hjF x) * ajG x * x ^ (-1 - s) by ring,
      x2_hjF_eq hx0, ajG_eq_one_sub hx0, ← integral_prod_mul, ← integral_mul_const]
    rfl
  -- step 2: measurability on the triple product
  have hmeas : AEStronglyMeasurable (Function.uncurry (fubPhi s))
      (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
        (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
          ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))))) := by
    rw [hν, Measure.prod_restrict]
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi))
    have cF : ContinuousOn (fun τ : ℝ => thF2 τ / τ) (Ioi 0) :=
      hdom_thF2.1.div continuousOn_id (fun τ hτ => (show (0 : ℝ) < τ from hτ).ne')
    have cG : ContinuousOn (fun t : ℝ => -thG1 t / t) (Ioi 0) :=
      continuousOn_thG1.neg.div continuousOn_id (fun t ht => (show (0 : ℝ) < t from ht).ne')
    have m1 : MapsTo (fun q : ℝ × (ℝ × ℝ) => q.2.1) (Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
        (Ioi 0) := fun q hq => hq.2.1
    have m2 : MapsTo (fun q : ℝ × (ℝ × ℝ) => q.2.2) (Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
        (Ioi 0) := fun q hq => hq.2.2
    have cF' := cF.comp (continuous_snd.fst).continuousOn m1
    have cG' := cG.comp (continuous_snd.snd).continuousOn m2
    have cJ1 : Continuous (fun q : ℝ × (ℝ × ℝ) => 1 - besselJ0 (q.1 * q.2.1)) :=
      continuous_const.sub (continuous_besselJ0.comp (continuous_fst.mul continuous_snd.fst))
    have cJ2 : Continuous (fun q : ℝ × (ℝ × ℝ) => 1 - besselJ0 (q.1 * q.2.2)) :=
      continuous_const.sub (continuous_besselJ0.comp (continuous_fst.mul continuous_snd.snd))
    have cR : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => q.1 ^ (-1 - s))
        (Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :=
      ContinuousOn.rpow_const continuous_fst.continuousOn
        (fun q hq => Or.inl (show (0 : ℝ) < q.1 from hq.1).ne')
    exact ((cF'.mul cJ1.continuousOn).mul (cG'.mul cJ2.continuousOn)).mul cR
  -- step 3: integrability on the triple product
  have hnorm : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
      ∫ x in Ioi (0 : ℝ), ‖fubPhi s x p‖ = |thF2 p.1 / p.1| * |-thG1 p.2 / p.2| * kerS s p.1 p.2 := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    have hp2 : (0 : ℝ) < p.2 := hp.2
    rw [kerS, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    have a1 := one_sub_besselJ0_nonneg (mul_nonneg hx0.le hp1.le)
    have a2 := one_sub_besselJ0_nonneg (mul_nonneg hx0.le hp2.le)
    have hr := Real.rpow_pos_of_pos hx0 (-1 - s)
    simp only [fubPhi, Real.norm_eq_abs, abs_mul, abs_of_nonneg a1, abs_of_nonneg a2,
      abs_of_pos hr]
    ring
  have hint : Integrable (Function.uncurry (fubPhi s))
      (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
        (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
          ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · filter_upwards [hS] with p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      have hp2 : (0 : ℝ) < p.2 := hp.2
      have h := (integrableOn_kerS_integrand hs0 hs2 hp1.le hp2.le).const_mul
        (thF2 p.1 / p.1 * (-thG1 p.2 / p.2))
      refine Integrable.congr h (Eventually.of_forall fun x => ?_)
      simp only [Function.uncurry_apply_pair, fubPhi]
      ring
    · refine Integrable.mono' (hP.const_mul (jS s)) hmeas.prod_swap.norm.integral_prod_right' ?_
      filter_upwards [hS] with p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      have hp2 : (0 : ℝ) < p.2 := hp.2
      simp only [Function.uncurry_apply_pair]
      rw [hnorm p hp, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (kerS_nonneg hp1.le hp2.le))]
      have hk := kerS_le_rpow hs0 hs2 hp1 hp2
      have hF := abs_nonneg (thF2 p.1 / p.1)
      have hG := abs_nonneg (-thG1 p.2 / p.2)
      calc |thF2 p.1 / p.1| * |-thG1 p.2 / p.2| * kerS s p.1 p.2
          ≤ |thF2 p.1 / p.1| * |-thG1 p.2 / p.2| * (jS s * (p.1 ^ (s / 2) * p.2 ^ (s / 2))) :=
            mul_le_mul_of_nonneg_left hk (mul_nonneg hF hG)
        _ = jS s * ((|thF2 p.1 / p.1| * p.1 ^ (s / 2)) * (|-thG1 p.2 / p.2| * p.2 ^ (s / 2))) := by
            ring
  -- step 4: the inner integral
  have h4 : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))),
      ∫ x in Ioi (0 : ℝ), fubPhi s x p
        = jS s * (thF2 p.1 / p.1 * (-thG1 p.2 / p.2) * (min p.1 p.2 ^ s - kerH s p.1 p.2)) := by
    filter_upwards [hS] with p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    have hp2 : (0 : ℝ) < p.2 := hp.2
    have e : ∀ x : ℝ, fubPhi s x p = (thF2 p.1 / p.1 * (-thG1 p.2 / p.2))
        * ((1 - besselJ0 (x * p.1)) * (1 - besselJ0 (x * p.2)) * x ^ (-1 - s)) := fun x => by
      simp only [fubPhi]
      ring
    simp only [e]
    rw [integral_const_mul, ← kerS, kerS_eq_kerH hs0 hs2 hp1.le hp2.le]
    ring
  have hint2 : Integrable (fun p : ℝ × ℝ =>
      jS s * (thF2 p.1 / p.1 * (-thG1 p.2 / p.2) * (min p.1 p.2 ^ s - kerH s p.1 p.2)))
      (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
        ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))) :=
    hint.integral_prod_right.congr h4
  calc pairS s = ∫ x in Ioi (0 : ℝ), hjF x * ajG x * x ^ (1 - s) := rfl
    _ = ∫ x in Ioi (0 : ℝ), ∫ p, fubPhi s x p ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
          ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))) :=
        setIntegral_congr_fun measurableSet_Ioi h1
    _ = ∫ p, (∫ x in Ioi (0 : ℝ), fubPhi s x p) ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
          ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))) := integral_integral_swap hint
    _ = ∫ p, jS s * (thF2 p.1 / p.1 * (-thG1 p.2 / p.2) * (min p.1 p.2 ^ s - kerH s p.1 p.2))
          ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
            ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))) := integral_congr_ae h4
    _ = ∫ τ in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
          jS s * (thF2 τ / τ * (-thG1 t / t) * (min τ t ^ s - kerH s τ t)) :=
        integral_prod _ hint2
    _ = jS s * ∫ τ in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
          thF2 τ / τ * (-thG1 t / t) * (min τ t ^ s - kerH s τ t) := by
        simp only [integral_const_mul]

end Tower.RV6
