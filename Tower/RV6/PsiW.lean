import Mathlib
import Tower.RV6.Defs
import Tower.RV6.Psi
import Tower.RV6.QSeries
import Tower.RV6.Dirichlet
import Tower.RV6.Fricke6
import Tower.RV6.Interchange
import Tower.RV6.Eichler2
import Tower.RV6.RungC1
import Tower.RV6.QCalc
import Tower.RV6.DEInv

/-!
# The weight-four form `Ψ^W`, its Mellin transform, and the moments of `𝔉`

`𝔉 = 𝔈(τ) - 2𝔈(2τ) - 27𝔈(3τ) + 54𝔈(6τ) = ∑ Fc(n) qⁿ`, and

`psiW(n) = -(11/54) σ₃(n) - (22/27) σ₃(n/2) + (63/2) σ₃(n/3) + 126 σ₃(n/6)
            + (65/54) Fc(n) - (5/9) ∑_{i+j=n} Fc(i) Fc(j)`.

* `Fcal_eq_qa`, `Fcal_sq_eq_qa`, `DFcal_eq_qa`, `Fcal_mul_DFcal_eq_qa`: `𝔉`, `𝔉²`, `D𝔉`, `𝔉·D𝔉`
  on the imaginary axis as `q`-series.
* `M2F_eq`: `∫₀^∞ 𝔉(iy) y² dy = 0`;  `L5F_eq`: `∫₀^∞ 𝔉(iy) y⁴ dy = ζ(5)/(144π)`;
  `M5F_eq`: `∫₀^∞ 𝔉 D𝔉 y⁵ dy = (5/(4π)) ∫₀^∞ 𝔉² y⁴ dy`; with the integrability of each integrand.
* **`lambdaPsiW5_eq`** (rung D″): `∫₀^∞ Ψ^W(iy) y⁴ dy = (3/(4π⁵)) ∑ psiW(n)/n⁵`.
* `lambdaPsiW5_split`: `∫₀^∞ Ψ^W(iy) y⁴ dy = -ζ(5)/(96π³) + (65/54) L₅(𝔉) - (5/9) L₅(𝔉²)`.

Nothing is regularised: every integral is over `(0, ∞)` and converges absolutely, because
`𝔉(iy) = -1/(24y²) + 13/12 + O(e^{-c/y})` as `y → 0`.  In Lean the integrability comes from the
termwise majorant (`integrable_qa_pow`) or from the non-vanishing of the integral.
-/

namespace Tower.RV6

open Real MeasureTheory

/-! ## The coefficients -/

/-- Coefficients of `𝔉 = 𝔈(τ) - 2𝔈(2τ) - 27𝔈(3τ) + 54𝔈(6τ)`. -/
noncomputable def Fc (n : ℕ) : ℝ :=
  1 * sig 1 n + (-2) * (if 2 ∣ n then sig 1 (n / 2) else 0)
    + (-27) * (if 3 ∣ n then sig 1 (n / 3) else 0) + 54 * (if 6 ∣ n then sig 1 (n / 6) else 0)

/-- The `σ₃` part of `psiW`. -/
noncomputable def sW (n : ℕ) : ℝ :=
  (-(11 / 54)) * sig 3 n + (-(22 / 27)) * (if 2 ∣ n then sig 3 (n / 2) else 0)
    + 63 / 2 * (if 3 ∣ n then sig 3 (n / 3) else 0) + 126 * (if 6 ∣ n then sig 3 (n / 6) else 0)

/-- Coefficients of the weight-four form `Ψ^W`. -/
noncomputable def psiW (n : ℕ) : ℝ := sW n + 65 / 54 * Fc n + (-(5 / 9)) * conv Fc Fc n

/-- Coefficients of `D𝔈`: `n σ₁(n)`. -/
noncomputable def nsig (n : ℕ) : ℝ := (n : ℝ) * sig 1 n

/-- Coefficients of `𝔉 · D𝔉`: `(n/2) ∑_{i+j=n} Fc(i) Fc(j)`. -/
noncomputable def hcv (n : ℕ) : ℝ := (n : ℝ) / 2 * conv Fc Fc n

/-! ## Bounds -/

theorem Fc_abs_le (n : ℕ) : |Fc n| ≤ 84 * sig 1 n := by
  have h2 := sigDiv_le 1 2 n
  have h3 := sigDiv_le 1 3 n
  have h6 := sigDiv_le 1 6 n
  have p2 := sigDiv_nonneg 1 2 n
  have p3 := sigDiv_nonneg 1 3 n
  have p6 := sigDiv_nonneg 1 6 n
  have p1 := sig_nonneg 1 n
  have e : Fc n = 1 * sig 1 n + (-2) * sigDiv 1 2 n + (-27) * sigDiv 1 3 n
      + 54 * sigDiv 1 6 n := rfl
  rw [e, abs_le]
  constructor <;> linarith

theorem sW_abs_le (n : ℕ) : |sW n| ≤ 159 * sig 3 n := by
  have h2 := sigDiv_le 3 2 n
  have h3 := sigDiv_le 3 3 n
  have h6 := sigDiv_le 3 6 n
  have p2 := sigDiv_nonneg 3 2 n
  have p3 := sigDiv_nonneg 3 3 n
  have p6 := sigDiv_nonneg 3 6 n
  have p1 := sig_nonneg 3 n
  have e : sW n = (-(11 / 54)) * sig 3 n + (-(22 / 27)) * sigDiv 3 2 n + 63 / 2 * sigDiv 3 3 n
      + 126 * sigDiv 3 6 n := rfl
  rw [e, abs_le]
  constructor <;> linarith

theorem Fc_poly (n : ℕ) : |Fc n| ≤ 84 * (n : ℝ) ^ 2 := by
  have h := Fc_abs_le n
  have h1 : sig 1 n ≤ (n : ℝ) ^ 2 := sig_le_pow 1 n
  linarith

theorem sW_poly (n : ℕ) : |sW n| ≤ 159 * (n : ℝ) ^ 4 := by
  have h := sW_abs_le n
  have h1 : sig 3 n ≤ (n : ℝ) ^ 4 := sig_le_pow 3 n
  linarith

theorem Fc_zero : Fc 0 = 0 := by
  have h := Fc_abs_le 0
  rw [sig_zero, mul_zero] at h
  exact abs_nonpos_iff.mp h

theorem sW_zero : sW 0 = 0 := by
  have h := sW_abs_le 0
  rw [sig_zero, mul_zero] at h
  exact abs_nonpos_iff.mp h

theorem DFc_poly (n : ℕ) : |(n : ℝ) * Fc n| ≤ 84 * (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [abs_mul, abs_of_nonneg hn0]
  calc (n : ℝ) * |Fc n| ≤ (n : ℝ) * (84 * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (Fc_poly n) hn0
    _ = 84 * (n : ℝ) ^ 3 := by ring

theorem nsig_abs_le (n : ℕ) : |nsig n| ≤ 1 * (n : ℝ) ^ 3 := bound_mul_sig1 n

theorem convF_poly (n : ℕ) : |conv Fc Fc n| ≤ 14112 * (n : ℝ) ^ 5 := by
  have h : |conv Fc Fc n| ≤ 2 * (84 * 84) * (n : ℝ) ^ (2 + 2 + 1) :=
    conv_poly_bound Fc_zero Fc_poly Fc_poly n
  have e : (2 : ℝ) * (84 * 84) * (n : ℝ) ^ (2 + 2 + 1) = 14112 * (n : ℝ) ^ 5 := by norm_num
  rw [e] at h
  exact h

theorem convF_zero : conv Fc Fc 0 = 0 := by
  have h := convF_poly 0
  rw [Nat.cast_zero, zero_pow (by norm_num), mul_zero] at h
  exact abs_nonpos_iff.mp h

theorem hcv_poly (n : ℕ) : |hcv n| ≤ 7056 * (n : ℝ) ^ 6 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  unfold hcv
  rw [abs_mul, abs_of_nonneg hn0]
  calc (n : ℝ) / 2 * |conv Fc Fc n| ≤ (n : ℝ) / 2 * (14112 * (n : ℝ) ^ 5) :=
        mul_le_mul_of_nonneg_left (convF_poly n) hn0
    _ = 7056 * (n : ℝ) ^ 6 := by ring

theorem hcv_zero : hcv 0 = 0 := by
  unfold hcv
  rw [convF_zero, mul_zero]

theorem psiW_poly (n : ℕ) : |psiW n| ≤ 8200 * (n : ℝ) ^ 5 := by
  have hC := abs_le.mp (sW_poly n)
  have hF := abs_le.mp (Fc_poly n)
  have hc := abs_le.mp (convF_poly n)
  have h24 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 5 ∧ (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      exact ⟨pow_le_pow_right₀ hn1 (by norm_num), pow_le_pow_right₀ hn1 (by norm_num)⟩
  have h5 : (0 : ℝ) ≤ (n : ℝ) ^ 5 := pow_nonneg (Nat.cast_nonneg n) 5
  unfold psiW
  rw [abs_le]
  constructor <;> linarith [hC.1, hC.2, hF.1, hF.2, hc.1, hc.2, h24.1, h24.2]

theorem psiW_zero : psiW 0 = 0 := by
  have h := psiW_poly 0
  rw [Nat.cast_zero, zero_pow (by norm_num), mul_zero] at h
  exact abs_nonpos_iff.mp h

/-- The convolution square of `Fc` at `n = x⁴`: `|(Fc ∗ Fc)(n)| ≤ 225792 x¹⁴`. -/
theorem convF_abs_le (n : ℕ) (x : ℝ) (hx1 : 1 ≤ x) (hxn : (n : ℝ) = x ^ 4)
    (hxr : (n : ℝ) ^ ((1 : ℝ) / 4) = x) : |conv Fc Fc n| ≤ 225792 * x ^ 14 := by
  have hx0 : 0 ≤ x := by linarith
  have hM : ∀ i ≤ n, sig 1 i ≤ 4 * x ^ 5 := by
    intro i hi
    have h := sig_one_le_of_le hi
    rw [hxr, hxn] at h
    calc sig 1 i ≤ x ^ 4 * (4 * x) := h
      _ = 4 * x ^ 5 := by ring
  have hF : ∀ i ≤ n, |Fc i| ≤ 336 * x ^ 5 := by
    intro i hi
    calc |Fc i| ≤ 84 * sig 1 i := Fc_abs_le i
      _ ≤ 84 * (4 * x ^ 5) := by linarith [hM i hi]
      _ = 336 * x ^ 5 := by ring
  have hS := conv_abs_le_gen Fc Fc n (336 * x ^ 5) (336 * x ^ 5) hF hF
  have hn4 : (n : ℝ) + 1 ≤ 2 * x ^ 4 := by
    have h1 : (1 : ℝ) ≤ x ^ 4 := one_le_pow₀ hx1
    linarith
  calc |conv Fc Fc n| ≤ ((n : ℝ) + 1) * (336 * x ^ 5 * (336 * x ^ 5)) := hS
    _ ≤ 2 * x ^ 4 * (336 * x ^ 5 * (336 * x ^ 5)) :=
        mul_le_mul_of_nonneg_right hn4 (by positivity)
    _ = 225792 * x ^ 14 := by ring

theorem psiW_abs_le (n : ℕ) (x : ℝ) (hx1 : 1 ≤ x) (hxn : (n : ℝ) = x ^ 4)
    (hxr : (n : ℝ) ^ ((1 : ℝ) / 4) = x) : |psiW n| ≤ 130000 * x ^ 14 := by
  have hx0 : 0 ≤ x := by linarith
  have hs1 : sig 1 n ≤ 4 * x ^ 5 := by
    have h := sig_one_le_of_le (le_refl n)
    rw [hxr, hxn] at h
    calc sig 1 n ≤ x ^ 4 * (4 * x) := h
      _ = 4 * x ^ 5 := by ring
  have hs3 : sig 3 n ≤ 4 * x ^ 13 := by
    have h := sig_three_le n
    rw [hxn] at h
    calc sig 3 n ≤ (x ^ 4) ^ 2 * sig 1 n := h
      _ ≤ (x ^ 4) ^ 2 * (4 * x ^ 5) := mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = 4 * x ^ 13 := by ring
  have hc := abs_le.mp (convF_abs_le n x hx1 hxn hxr)
  have hF := abs_le.mp (Fc_abs_le n)
  have hC := abs_le.mp (sW_abs_le n)
  have a1 := sig_nonneg 1 n
  have a3 := sig_nonneg 3 n
  have hx13 : x ^ 13 ≤ x ^ 14 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx5 : x ^ 5 ≤ x ^ 14 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx14 : 0 ≤ x ^ 14 := by positivity
  unfold psiW
  rw [abs_le]
  constructor <;> linarith [hc.1, hc.2, hF.1, hF.2, hC.1, hC.2]

/-- A sequence with `|a(n)| ≤ C x¹⁴` for `n = x⁴` has `∑ |a(n)|/n⁵ < ∞`. -/
theorem summable_of_x14 (a : ℕ → ℝ) (C : ℝ)
    (h : ∀ (n : ℕ) (x : ℝ), 1 ≤ x → (n : ℝ) = x ^ 4 → (n : ℝ) ^ ((1 : ℝ) / 4) = x →
      |a n| ≤ C * x ^ 14) :
    Summable fun n : ℕ => |a (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ 5 := by
  have hp : Summable fun n : ℕ => C * (((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
    ((summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2))).mul_left C
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hp
  obtain ⟨x, hx1, hxn, hx6, hxr⟩ := exists_root (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have hb := h (n + 1) x hx1 hxn hxr
  have hx0 : 0 < x := by linarith
  show |a (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ 5 ≤ C * (((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹
  rw [hx6, hxn, div_le_iff₀ (by positivity)]
  have e : (x ^ 6)⁻¹ * (x ^ 4) ^ 5 = x ^ 14 := by
    have h20 : (x ^ 4) ^ 5 = x ^ 6 * x ^ 14 := by ring
    rw [h20, inv_mul_cancel_left₀ (pow_ne_zero 6 hx0.ne')]
  calc |a (n + 1)| ≤ C * x ^ 14 := hb
    _ = C * (x ^ 6)⁻¹ * (x ^ 4) ^ 5 := by rw [mul_assoc, e]

theorem summable_convF :
    Summable fun n : ℕ => |conv Fc Fc (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ 5 :=
  summable_of_x14 (conv Fc Fc) 225792 convF_abs_le

theorem summable_psiW : Summable fun n : ℕ => |psiW (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ 5 :=
  summable_of_x14 psiW 130000 psiW_abs_le

theorem summable_hcv :
    Summable fun n : ℕ => |hcv (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (5 + 1) := by
  have h := summable_convF.mul_left (1 / 2 : ℝ)
  refine h.congr (fun n => ?_)
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hn0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / 2 := by positivity
  have hNN : ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  show 1 / 2 * (|conv Fc Fc (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ 5)
    = |hcv (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (5 + 1)
  unfold hcv
  rw [abs_mul, abs_of_nonneg hn0]
  linear_combination (-(1 / 2 * |conv Fc Fc (n + 1)| * ((n + 1 : ℕ) : ℝ)⁻¹ ^ 5)) * hNN

/-! ## `𝔉`, `𝔉²`, `D𝔉`, `𝔉 · D𝔉` as `q`-series -/

theorem Fcal_eq_qa {y : ℝ} (hy : 0 < y) : Fcal y = qa Fc y := by
  have h := qa_comb4 (A := sig 1) zero_le_one (sig_abs_le 1) 1 (-2) (-27) 54 hy
  have e : qa Fc y = qa (fun n => 1 * sig 1 n + (-2) * (if 2 ∣ n then sig 1 (n / 2) else 0)
      + (-27) * (if 3 ∣ n then sig 1 (n / 3) else 0)
      + 54 * (if 6 ∣ n then sig 1 (n / 6) else 0)) y := rfl
  rw [e, h]
  unfold Fcal
  simp only [Ecal_eq_qa]
  ring

theorem Fcal_sq_eq_qa {y : ℝ} (hy : 0 < y) : Fcal y ^ 2 = qa (conv Fc Fc) y := by
  rw [Fcal_eq_qa hy, sq]
  exact qa_conv Fc_poly Fc_poly hy

/-- The coefficients of `D𝔉` are `n Fc(n)`. -/
theorem DFc_eq (n : ℕ) :
    1 * nsig n + (-4) * (if 2 ∣ n then nsig (n / 2) else 0)
        + (-81) * (if 3 ∣ n then nsig (n / 3) else 0) + 324 * (if 6 ∣ n then nsig (n / 6) else 0)
      = (n : ℝ) * Fc n := by
  have e2 : (if 2 ∣ n then nsig (n / 2) else 0)
      = (n : ℝ) / 2 * (if 2 ∣ n then sig 1 (n / 2) else 0) := by
    split_ifs with h
    · unfold nsig
      rw [Nat.cast_div h (by norm_num : ((2 : ℕ) : ℝ) ≠ 0), Nat.cast_ofNat]
    · rw [mul_zero]
  have e3 : (if 3 ∣ n then nsig (n / 3) else 0)
      = (n : ℝ) / 3 * (if 3 ∣ n then sig 1 (n / 3) else 0) := by
    split_ifs with h
    · unfold nsig
      rw [Nat.cast_div h (by norm_num : ((3 : ℕ) : ℝ) ≠ 0), Nat.cast_ofNat]
    · rw [mul_zero]
  have e6 : (if 6 ∣ n then nsig (n / 6) else 0)
      = (n : ℝ) / 6 * (if 6 ∣ n then sig 1 (n / 6) else 0) := by
    split_ifs with h
    · unfold nsig
      rw [Nat.cast_div h (by norm_num : ((6 : ℕ) : ℝ) ≠ 0), Nat.cast_ofNat]
    · rw [mul_zero]
  rw [e2, e3, e6]
  unfold nsig Fc
  ring

theorem DFcal_eq_qa {y : ℝ} (hy : 0 < y) : DFcal y = qa (fun n : ℕ => (n : ℝ) * Fc n) y := by
  have h := qa_comb4 (A := nsig) zero_le_one nsig_abs_le 1 (-4) (-81) 324 hy
  have hf : (fun n : ℕ => 1 * nsig n + (-4) * (if 2 ∣ n then nsig (n / 2) else 0)
      + (-81) * (if 3 ∣ n then nsig (n / 3) else 0)
      + 324 * (if 6 ∣ n then nsig (n / 6) else 0))
      = (fun n : ℕ => (n : ℝ) * Fc n) := funext DFc_eq
  rw [hf] at h
  have e : ∀ t : ℝ, DEcal t = qa nsig t := DEcal_eq_qa
  rw [h]
  unfold DFcal
  simp only [e]
  ring

theorem Fcal_mul_DFcal_eq_qa {y : ℝ} (hy : 0 < y) : Fcal y * DFcal y = qa hcv y := by
  rw [Fcal_eq_qa hy, DFcal_eq_qa hy, qa_conv Fc_poly DFc_poly hy]
  have hf : conv Fc (fun j : ℕ => (j : ℝ) * Fc j) = hcv := funext (conv_mul_index Fc)
  rw [hf]

/-! ## The moments of `𝔈` and of `S₃` -/

theorem summable_sig1_div_pow5 :
    Summable fun n : ℕ => sig 1 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 := by
  by_contra h
  have h0 := tsum_eq_zero_of_not_summable h
  rw [tsum_sig1_div_pow5] at h0
  have hp : 0 < π ^ 4 / 90 * zeta5 := mul_pos (by positivity) zeta5_pos
  exact hp.ne' h0

theorem tsum_sig1_div_pow3_pos : 0 < ∑' n : ℕ, sig 1 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3 := by
  rw [tsum_sig_div_pow 1 2 3 rfl le_rfl]
  have h3 := (summable_shift_one_div_pow (p := 3) (by norm_num)).tsum_pos
    (fun n => by positivity) 0 (by norm_num)
  have h2 := (summable_shift_one_div_pow (p := 2) (by norm_num)).tsum_pos
    (fun n => by positivity) 0 (by norm_num)
  exact mul_pos h3 h2

theorem summable_sig1_div_pow3 :
    Summable fun n : ℕ => sig 1 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3 := by
  by_contra h
  have h0 := tsum_eq_zero_of_not_summable h
  have hp := tsum_sig1_div_pow3_pos
  rw [h0] at hp
  exact lt_irrefl 0 hp

/-- `∫₀^∞ 𝔈(iu) u⁴ du = ζ(5)/(120π)`. -/
theorem integral_E_pow4 :
    ∫ u in Set.Ioi (0 : ℝ), qa (sig 1) u * u ^ 4 = zeta5 / (120 * π) := by
  have hs : Summable fun n : ℕ => |sig 1 (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (4 + 1) := by
    refine summable_sig1_div_pow5.congr (fun n => ?_)
    show sig 1 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 = |sig 1 (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ 5
    rw [abs_of_nonneg (sig_nonneg 1 (n + 1))]
  have h := integral_qa (sig 1) (sig_zero 1) 4 hs (fun y hy => summable_qa (sig_abs_le 1) hy)
  have hsum : ∑' n : ℕ, sig 1 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (4 + 1) = π ^ 4 / 90 * zeta5 :=
    tsum_sig1_div_pow5
  have ef : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hp : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  rw [h, hsum, ef]
  linear_combination
    (zeta5 / 120 * π⁻¹ * ((π * π⁻¹) ^ 3 + (π * π⁻¹) ^ 2 + π * π⁻¹ + 1)) * hp

/-- `∫₀^∞ 𝔈(iu) u² du > 0`. -/
theorem integral_E_pow2_pos : 0 < ∫ u in Set.Ioi (0 : ℝ), qa (sig 1) u * u ^ 2 := by
  have hs : Summable fun n : ℕ => |sig 1 (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (2 + 1) := by
    refine summable_sig1_div_pow3.congr (fun n => ?_)
    show sig 1 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3 = |sig 1 (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ 3
    rw [abs_of_nonneg (sig_nonneg 1 (n + 1))]
  have h := integral_qa (sig 1) (sig_zero 1) 2 hs (fun y hy => summable_qa (sig_abs_le 1) hy)
  have hsum : 0 < ∑' n : ℕ, sig 1 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (2 + 1) :=
    tsum_sig1_div_pow3_pos
  rw [h]
  exact mul_pos (div_pos (by first | positivity | exact_mod_cast Nat.factorial_pos 2)
    (by positivity)) hsum

/-- `∫₀^∞ S₃(iu) u⁴ du = ζ(5)/(8π³)`, `S₃ = ∑ σ₃(n) qⁿ`. -/
theorem integral_S3_pow4 :
    ∫ u in Set.Ioi (0 : ℝ), qa (sig 3) u * u ^ 4 = zeta5 / (8 * π ^ 3) := by
  have hs : Summable fun n : ℕ => |sig 3 (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (4 + 1) := by
    refine summable_sig3_div_pow5.congr (fun n => ?_)
    show sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 = |sig 3 (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ 5
    rw [abs_of_nonneg (sig_nonneg 3 (n + 1))]
  have h := integral_qa (sig 3) (sig_zero 3) 4 hs (fun y hy => summable_qa (sig_abs_le 3) hy)
  have hsum : ∑' n : ℕ, sig 3 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (4 + 1) = π ^ 2 / 6 * zeta5 :=
    tsum_sig3_div_pow5
  have ef : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hp : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  rw [h, hsum, ef]
  linear_combination (zeta5 / 8 * π⁻¹ ^ 3 * (π * π⁻¹ + 1)) * hp

theorem integrable_E_scale_pow4 {d : ℝ} (hd : 0 < d) :
    Integrable (fun x : ℝ => qa (sig 1) (d * x) * x ^ 4)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_qa_scale (sig 1) hd 4, integral_E_pow4]
  have h1 : 0 < d⁻¹ ^ (4 + 1) * (zeta5 / (120 * π)) :=
    mul_pos (pow_pos (inv_pos.mpr hd) _) (div_pos zeta5_pos (by positivity))
  exact h1.ne'

theorem integrable_E_scale_pow2 {d : ℝ} (hd : 0 < d) :
    Integrable (fun x : ℝ => qa (sig 1) (d * x) * x ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_qa_scale (sig 1) hd 2]
  exact (mul_pos (pow_pos (inv_pos.mpr hd) _) integral_E_pow2_pos).ne'

theorem integrable_S3_scale_pow4 {d : ℝ} (hd : 0 < d) :
    Integrable (fun x : ℝ => qa (sig 3) (d * x) * x ^ 4)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_qa_scale (sig 3) hd 4, integral_S3_pow4]
  have h1 : 0 < d⁻¹ ^ (4 + 1) * (zeta5 / (8 * π ^ 3)) :=
    mul_pos (pow_pos (inv_pos.mpr hd) _) (div_pos zeta5_pos (by positivity))
  exact h1.ne'

/-! ## The moments of `𝔉` -/

/-- `L₅(𝔉) = ∫₀^∞ 𝔉(iy) y⁴ dy`. -/
noncomputable def L5F : ℝ := ∫ y in Set.Ioi (0 : ℝ), Fcal y * y ^ 4

/-- `L₅(𝔉²) = ∫₀^∞ 𝔉(iy)² y⁴ dy`. -/
noncomputable def L5F2 : ℝ := ∫ y in Set.Ioi (0 : ℝ), Fcal y ^ 2 * y ^ 4

/-- `∫₀^∞ 𝔉(iy) y² dy`. -/
noncomputable def M2F : ℝ := ∫ y in Set.Ioi (0 : ℝ), Fcal y * y ^ 2

/-- `∫₀^∞ 𝔉(iy) (D𝔉)(iy) y⁵ dy`. -/
noncomputable def M5F : ℝ := ∫ y in Set.Ioi (0 : ℝ), Fcal y * DFcal y * y ^ 5

theorem Fcal_mul_pow (y : ℝ) (m : ℕ) :
    Fcal y * y ^ m = ∑ k ∈ Finset.range 4, cF k * (qa (sig 1) (dv k * y) * y ^ m) := by
  rw [Fcal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- The moment of order `m` of `𝔉` through the moments of `𝔈` at `y, 2y, 3y, 6y`. -/
theorem lin_F_pow (m : ℕ)
    (hint : ∀ k ∈ Finset.range 4, Integrable (fun y : ℝ => qa (sig 1) (dv k * y) * y ^ m)
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    Integrable (fun y : ℝ => Fcal y * y ^ m) (volume.restrict (Set.Ioi (0 : ℝ)))
      ∧ ∫ y in Set.Ioi (0 : ℝ), Fcal y * y ^ m
        = ∑ k ∈ Finset.range 4,
            cF k * ((dv k)⁻¹ ^ (m + 1) * ∫ u in Set.Ioi (0 : ℝ), qa (sig 1) u * u ^ m) := by
  have h : Integrable
        (fun y : ℝ => ∑ k ∈ Finset.range 4, cF k * (qa (sig 1) (dv k * y) * y ^ m))
        (volume.restrict (Set.Ioi (0 : ℝ)))
      ∧ ∫ y in Set.Ioi (0 : ℝ), ∑ k ∈ Finset.range 4, cF k * (qa (sig 1) (dv k * y) * y ^ m)
        = ∑ k ∈ Finset.range 4, cF k * ∫ y in Set.Ioi (0 : ℝ), qa (sig 1) (dv k * y) * y ^ m :=
    integral_lin_gen (Finset.range 4) (fun (k : ℕ) (y : ℝ) => qa (sig 1) (dv k * y) * y ^ m) cF
      hint
  have hfun : (fun y : ℝ => Fcal y * y ^ m)
      = fun y : ℝ => ∑ k ∈ Finset.range 4, cF k * (qa (sig 1) (dv k * y) * y ^ m) :=
    funext (fun y => Fcal_mul_pow y m)
  rw [hfun]
  refine ⟨h.1, ?_⟩
  rw [h.2]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_qa_scale (sig 1) (dv_pos k) m]

theorem integrable_F_pow4 :
    Integrable (fun y : ℝ => Fcal y * y ^ 4) (volume.restrict (Set.Ioi (0 : ℝ))) :=
  (lin_F_pow 4 (fun k _ => integrable_E_scale_pow4 (dv_pos k))).1

theorem integrable_F_pow2 :
    Integrable (fun y : ℝ => Fcal y * y ^ 2) (volume.restrict (Set.Ioi (0 : ℝ))) :=
  (lin_F_pow 2 (fun k _ => integrable_E_scale_pow2 (dv_pos k))).1

/-- `L₅(𝔉) = ζ(5)/(144π)`. -/
theorem L5F_eq : L5F = zeta5 / (144 * π) := by
  have h := (lin_F_pow 4 (fun k _ => integrable_E_scale_pow4 (dv_pos k))).2
  unfold L5F
  rw [h, integral_E_pow4, sum_range_four, dv_zero, dv_one, dv_two, dv_three, cF_zero, cF_one,
    cF_two, cF_three]
  ring

/-- `∫₀^∞ 𝔉(iy) y² dy = 0`. -/
theorem M2F_eq : M2F = 0 := by
  have h := (lin_F_pow 2 (fun k _ => integrable_E_scale_pow2 (dv_pos k))).2
  unfold M2F
  rw [h, sum_range_four, dv_zero, dv_one, dv_two, dv_three, cF_zero, cF_one, cF_two, cF_three]
  ring

theorem integrable_Fsq :
    Integrable (fun y : ℝ => Fcal y ^ 2 * y ^ 4) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h : IntegrableOn (fun y : ℝ => qa (conv Fc Fc) y * y ^ 4) (Set.Ioi (0 : ℝ)) :=
    integrable_qa_pow convF_poly convF_zero 4 summable_convF
  have h2 : IntegrableOn (fun y : ℝ => Fcal y ^ 2 * y ^ 4) (Set.Ioi (0 : ℝ)) := by
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := hy
    show qa (conv Fc Fc) y * y ^ 4 = Fcal y ^ 2 * y ^ 4
    rw [Fcal_sq_eq_qa hy0]
  exact h2

theorem integrable_FDF :
    Integrable (fun y : ℝ => Fcal y * DFcal y * y ^ 5) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h : IntegrableOn (fun y : ℝ => qa hcv y * y ^ 5) (Set.Ioi (0 : ℝ)) :=
    integrable_qa_pow hcv_poly hcv_zero 5 summable_hcv
  have h2 : IntegrableOn (fun y : ℝ => Fcal y * DFcal y * y ^ 5) (Set.Ioi (0 : ℝ)) := by
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := hy
    show qa hcv y * y ^ 5 = Fcal y * DFcal y * y ^ 5
    rw [Fcal_mul_DFcal_eq_qa hy0]
  exact h2

/-- `∫₀^∞ 𝔉 D𝔉 y⁵ dy = (5/(4π)) L₅(𝔉²)`: the coefficients of `𝔉 · D𝔉` are `(n/2)(Fc ∗ Fc)(n)`. -/
theorem M5F_eq : M5F = 5 / (4 * π) * L5F2 := by
  have h5 := integral_qa hcv hcv_zero 5 summable_hcv (fun y hy => summable_qa hcv_poly hy)
  have hs4 : Summable fun n : ℕ => |conv Fc Fc (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (4 + 1) :=
    summable_convF
  have h4 := integral_qa (conv Fc Fc) convF_zero 4 hs4 (fun y hy => summable_qa convF_poly hy)
  have e5 : ∫ y in Set.Ioi (0 : ℝ), Fcal y * DFcal y * y ^ 5
      = ∫ y in Set.Ioi (0 : ℝ), qa hcv y * y ^ 5 := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    show Fcal y * DFcal y * y ^ 5 = qa hcv y * y ^ 5
    rw [Fcal_mul_DFcal_eq_qa hy0]
  have e4 : ∫ y in Set.Ioi (0 : ℝ), Fcal y ^ 2 * y ^ 4
      = ∫ y in Set.Ioi (0 : ℝ), qa (conv Fc Fc) y * y ^ 4 := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    show Fcal y ^ 2 * y ^ 4 = qa (conv Fc Fc) y * y ^ 4
    rw [Fcal_sq_eq_qa hy0]
  have hS : ∑' n : ℕ, hcv (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (5 + 1)
      = 1 / 2 * ∑' n : ℕ, conv Fc Fc (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (4 + 1) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hNN : ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    show hcv (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (5 + 1)
      = 1 / 2 * (conv Fc Fc (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (4 + 1))
    unfold hcv
    linear_combination (1 / 2 * conv Fc Fc (n + 1) * ((n + 1 : ℕ) : ℝ)⁻¹ ^ 5) * hNN
  have ef5 : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by norm_num [Nat.factorial]
  have ef4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hM : M5F = 120 / (2 * π) ^ (5 + 1)
      * ∑' n : ℕ, hcv (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (5 + 1) := by
    unfold M5F
    rw [e5, h5, ef5]
  have hL : L5F2 = 24 / (2 * π) ^ (4 + 1)
      * ∑' n : ℕ, conv Fc Fc (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (4 + 1) := by
    unfold L5F2
    rw [e4, h4, ef4]
  linear_combination hM - (5 / 4 * π⁻¹) * hL + (15 / 8 * π⁻¹ ^ 6) * hS

/-! ## `Ψ^W`: rung D″ and the split of its Mellin transform -/

/-- `Λ(Ψ^W, 5) = ∫₀^∞ Ψ^W(iy) y⁴ dy`. -/
noncomputable def LambdaPsiW5 : ℝ := ∫ y in Set.Ioi (0 : ℝ), qa psiW y * y ^ 4

/-- `L(Ψ^W, 5) = ∑ psiW(n)/n⁵`. -/
noncomputable def LPsiW5 : ℝ := ∑' n : ℕ, psiW n / (n : ℝ) ^ 5

theorem lPsiW5_eq_shift : LPsiW5 = ∑' n : ℕ, psiW (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 := by
  unfold LPsiW5
  have hsh : Summable fun n : ℕ => psiW (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 5 := by
    refine Summable.of_norm_bounded summable_psiW (fun n => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 5)]
  have hs : Summable fun n : ℕ => psiW n / (n : ℝ) ^ 5 := (summable_nat_add_iff 1).mp hsh
  rw [hs.tsum_eq_zero_add]
  simp

/-- **Rung D″.**  `Λ(Ψ^W, 5) = (3/(4π⁵)) L(Ψ^W, 5)`. -/
theorem lambdaPsiW5_eq : LambdaPsiW5 = 3 / (4 * π ^ 5) * LPsiW5 := by
  have hs : Summable fun n : ℕ => |psiW (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (4 + 1) := summable_psiW
  have h := integral_qa psiW psiW_zero 4 hs (fun y hy => summable_qa psiW_poly hy)
  have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hsum : ∑' n : ℕ, psiW (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (4 + 1) = LPsiW5 :=
    lPsiW5_eq_shift.symm
  unfold LambdaPsiW5
  rw [h, hsum, h4]
  ring

/-- Linearity of a series in its coefficients, in the shape of `psiW`. -/
theorem qa_lin3 {A B C : ℕ → ℝ} {y : ℝ}
    (hA : Summable fun n : ℕ => A n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hB : Summable fun n : ℕ => B n * Real.exp (-(2 * π * (n : ℝ) * y)))
    (hC : Summable fun n : ℕ => C n * Real.exp (-(2 * π * (n : ℝ) * y))) (b c : ℝ) :
    qa (fun n => A n + b * B n + c * C n) y = qa A y + b * qa B y + c * qa C y := by
  have H := (hA.hasSum.add (hB.hasSum.mul_left b)).add (hC.hasSum.mul_left c)
  unfold qa
  calc ∑' n : ℕ, (A n + b * B n + c * C n) * Real.exp (-(2 * π * (n : ℝ) * y))
      = ∑' n : ℕ, (A n * Real.exp (-(2 * π * (n : ℝ) * y))
          + b * (B n * Real.exp (-(2 * π * (n : ℝ) * y)))
          + c * (C n * Real.exp (-(2 * π * (n : ℝ) * y)))) :=
        tsum_congr (fun n => by ring)
    _ = _ := H.tsum_eq

/-- Coefficients of the `σ₃` part of `psiW`, over the divisors `1, 2, 3, 6`. -/
noncomputable def cW (k : ℕ) : ℝ :=
  if k = 0 then -(11 / 54) else if k = 1 then -(22 / 27) else if k = 2 then 63 / 2
  else if k = 3 then 126 else 0

theorem cW_zero : cW 0 = -(11 / 54) := by norm_num [cW]
theorem cW_one : cW 1 = -(22 / 27) := by norm_num [cW]
theorem cW_two : cW 2 = 63 / 2 := by norm_num [cW]
theorem cW_three : cW 3 = 126 := by norm_num [cW]

theorem qa_sW {y : ℝ} (hy : 0 < y) :
    qa sW y = (-(11 / 54)) * qa (sig 3) y + (-(22 / 27)) * qa (sig 3) (2 * y)
      + 63 / 2 * qa (sig 3) (3 * y) + 126 * qa (sig 3) (6 * y) := by
  have h := qa_comb4 (A := sig 3) zero_le_one (sig_abs_le 3) (-(11 / 54)) (-(22 / 27)) (63 / 2)
    126 hy
  exact h

theorem qa_sW_sum {y : ℝ} (hy : 0 < y) :
    qa sW y = ∑ k ∈ Finset.range 4, cW k * qa (sig 3) (dv k * y) := by
  have e : ∑ k ∈ Finset.range 4, cW k * qa (sig 3) (dv k * y)
      = (-(11 / 54)) * qa (sig 3) (1 * y) + (-(22 / 27)) * qa (sig 3) (2 * y)
        + 63 / 2 * qa (sig 3) (3 * y) + 126 * qa (sig 3) (6 * y) := by
    rw [sum_range_four, dv_zero, dv_one, dv_two, dv_three, cW_zero, cW_one, cW_two, cW_three]
  rw [e, one_mul]
  exact qa_sW hy

theorem qa_psiW {y : ℝ} (hy : 0 < y) :
    qa psiW y = qa sW y + 65 / 54 * Fcal y + (-(5 / 9)) * Fcal y ^ 2 := by
  have h := qa_lin3 (summable_qa sW_poly hy) (summable_qa Fc_poly hy) (summable_qa convF_poly hy)
    (65 / 54) (-(5 / 9))
  have e : qa psiW y = qa (fun n => sW n + 65 / 54 * Fc n + (-(5 / 9)) * conv Fc Fc n) y := rfl
  rw [e, h, Fcal_sq_eq_qa hy, Fcal_eq_qa hy]

/-- `Λ(Ψ^W, 5) = -ζ(5)/(96π³) + (65/54) L₅(𝔉) - (5/9) L₅(𝔉²)`. -/
theorem lambdaPsiW5_split :
    LambdaPsiW5 = -zeta5 / (96 * π ^ 3) + 65 / 54 * L5F - 5 / 9 * L5F2 := by
  have hS : Integrable
        (fun y : ℝ => ∑ k ∈ Finset.range 4, cW k * (qa (sig 3) (dv k * y) * y ^ 4))
        (volume.restrict (Set.Ioi (0 : ℝ)))
      ∧ ∫ y in Set.Ioi (0 : ℝ), ∑ k ∈ Finset.range 4, cW k * (qa (sig 3) (dv k * y) * y ^ 4)
        = ∑ k ∈ Finset.range 4, cW k * ∫ y in Set.Ioi (0 : ℝ), qa (sig 3) (dv k * y) * y ^ 4 :=
    integral_lin_gen (Finset.range 4) (fun (k : ℕ) (y : ℝ) => qa (sig 3) (dv k * y) * y ^ 4) cW
      (fun k _ => integrable_S3_scale_pow4 (dv_pos k))
  have hk : ∀ k : ℕ, ∫ y in Set.Ioi (0 : ℝ), qa (sig 3) (dv k * y) * y ^ 4
      = (dv k)⁻¹ ^ (4 + 1) * (zeta5 / (8 * π ^ 3)) := by
    intro k
    rw [integral_qa_scale (sig 3) (dv_pos k) 4, integral_S3_pow4]
  have hSval : ∫ y in Set.Ioi (0 : ℝ),
        ∑ k ∈ Finset.range 4, cW k * (qa (sig 3) (dv k * y) * y ^ 4)
      = -zeta5 / (96 * π ^ 3) := by
    rw [hS.2, sum_range_four, hk 0, hk 1, hk 2, hk 3, dv_zero, dv_one, dv_two, dv_three, cW_zero,
      cW_one, cW_two, cW_three]
    ring
  have hcongr : ∫ y in Set.Ioi (0 : ℝ), qa psiW y * y ^ 4
      = ∫ y in Set.Ioi (0 : ℝ),
          (1 * (∑ k ∈ Finset.range 4, cW k * (qa (sig 3) (dv k * y) * y ^ 4))
            + 65 / 54 * (Fcal y * y ^ 4) + (-(5 / 9)) * (Fcal y ^ 2 * y ^ 4)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    have hsum : ∑ k ∈ Finset.range 4, cW k * (qa (sig 3) (dv k * y) * y ^ 4)
        = (∑ k ∈ Finset.range 4, cW k * qa (sig 3) (dv k * y)) * y ^ 4 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    show qa psiW y * y ^ 4
      = 1 * (∑ k ∈ Finset.range 4, cW k * (qa (sig 3) (dv k * y) * y ^ 4))
        + 65 / 54 * (Fcal y * y ^ 4) + (-(5 / 9)) * (Fcal y ^ 2 * y ^ 4)
    rw [hsum, qa_psiW hy0, qa_sW_sum hy0]
    ring
  have hlin := integral_lin3 hS.1 integrable_F_pow4 integrable_Fsq (1 : ℝ) (65 / 54) (-(5 / 9))
  unfold LambdaPsiW5
  rw [hcongr, hlin, hSval]
  unfold L5F L5F2
  ring

end Tower.RV6
