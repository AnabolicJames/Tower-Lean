import Mathlib
import Tower.RV6.Psi
import Tower.RV6.QSeries
import Tower.RV6.Ser

/-!
# The Eisenstein series of level six as power series: nine relations

`e2_d, e4_d, e6_d` are `E₂, E₄, E₆` at `q^d` for `d ∣ 6`, as formal power series (`E₆` is defined
as `E₂ E₄ - 3 θE₄`).  Under Ramanujan's identities (`Ram6`, a hypothesis in this file) nine
polynomial relations hold among them: one quadratic relation among the four `e2_d`, and each
`e4_d`, `e6_d` is a polynomial in the `e2`'s.

The proof does not use modular forms.  The nine differences `R` satisfy `24 θR = M R` with a
matrix `M` of polynomials (`clos1 … clos9`, each a polynomial identity); the matrix at `X = 0`
has characteristic polynomial `n⁶ (n-2)(n-3)(n-6)` (`lin9`); and `R` vanishes modulo `X⁷`
(`dvd7_Rf1 …`), by explicit truncations.  Hence `R = 0` (`rel_all_zero`).

This file is written by `tools/gen_level6.py` from certificates computed in exact arithmetic;
every identity is checked here by `ring`.
-/

namespace Tower.RV6

open PowerSeries

set_option maxHeartbeats 1600000

local notation "T" => (PowerSeries.X : PowerSeries ℝ)

theorem two_ne : (2 : ℕ) ≠ 0 := by norm_num
theorem three_ne : (3 : ℕ) ≠ 0 := by norm_num
theorem six_ne : (6 : ℕ) ≠ 0 := by norm_num

/-! ## The series -/

/-- `∑ σ₁(n) Xⁿ`. -/
noncomputable def S1 : PowerSeries ℝ := PowerSeries.mk (sig 1)
/-- `∑ σ₃(n) Xⁿ`. -/
noncomputable def S3 : PowerSeries ℝ := PowerSeries.mk (sig 3)
/-- `E₂ = 1 - 24 ∑ σ₁(n) Xⁿ`. -/
noncomputable def xE : PowerSeries ℝ := 1 - 24 * S1
/-- `E₄ = 1 + 240 ∑ σ₃(n) Xⁿ`. -/
noncomputable def uE : PowerSeries ℝ := 1 + 240 * S3
/-- `E₆`, defined as `E₂ E₄ - 3 θE₄`. -/
noncomputable def vE : PowerSeries ℝ := xE * uE - 3 * theta uE
noncomputable def e2_1 : PowerSeries ℝ := xE
noncomputable def e2_2 : PowerSeries ℝ := PowerSeries.expand 2 two_ne xE
noncomputable def e2_3 : PowerSeries ℝ := PowerSeries.expand 3 three_ne xE
noncomputable def e2_6 : PowerSeries ℝ := PowerSeries.expand 6 six_ne xE
noncomputable def e4_1 : PowerSeries ℝ := uE
noncomputable def e4_2 : PowerSeries ℝ := PowerSeries.expand 2 two_ne uE
noncomputable def e4_3 : PowerSeries ℝ := PowerSeries.expand 3 three_ne uE
noncomputable def e4_6 : PowerSeries ℝ := PowerSeries.expand 6 six_ne uE
noncomputable def e6_1 : PowerSeries ℝ := vE
noncomputable def e6_2 : PowerSeries ℝ := PowerSeries.expand 2 two_ne vE
noncomputable def e6_3 : PowerSeries ℝ := PowerSeries.expand 3 three_ne vE
noncomputable def e6_6 : PowerSeries ℝ := PowerSeries.expand 6 six_ne vE

/-- Ramanujan's identities at `q, q², q³, q⁶`, in integer form. -/
def Ram6 : Prop :=
  (12 * theta e2_1 = 1 * (e2_1 * e2_1 - e4_1))
    ∧ (12 * theta e2_2 = 2 * (e2_2 * e2_2 - e4_2))
    ∧ (12 * theta e2_3 = 3 * (e2_3 * e2_3 - e4_3))
    ∧ (12 * theta e2_6 = 6 * (e2_6 * e2_6 - e4_6))
    ∧ (3 * theta e4_1 = 1 * (e2_1 * e4_1 - e6_1))
    ∧ (3 * theta e4_2 = 2 * (e2_2 * e4_2 - e6_2))
    ∧ (3 * theta e4_3 = 3 * (e2_3 * e4_3 - e6_3))
    ∧ (3 * theta e4_6 = 6 * (e2_6 * e4_6 - e6_6))
    ∧ (2 * theta e6_1 = 1 * (e2_1 * e6_1 - e4_1 * e4_1))
    ∧ (2 * theta e6_2 = 2 * (e2_2 * e6_2 - e4_2 * e4_2))
    ∧ (2 * theta e6_3 = 3 * (e2_3 * e6_3 - e4_3 * e4_3))
    ∧ (2 * theta e6_6 = 6 * (e2_6 * e6_6 - e4_6 * e4_6))

theorem ode4_base : 3 * theta uE = xE * uE - vE := by
  unfold vE
  ring

theorem ode2_expand (d : ℕ) (hd : d ≠ 0) (h : 12 * theta xE = xE * xE - uE) :
    12 * theta (PowerSeries.expand d hd xE)
      = (d : PowerSeries ℝ) * (PowerSeries.expand d hd xE * PowerSeries.expand d hd xE - PowerSeries.expand d hd uE) := by
  have h' := congrArg (fun t => PowerSeries.expand d hd t) h
  simp only [map_mul, map_sub, map_ofNat] at h'
  rw [theta_expand]
  linear_combination (d : PowerSeries ℝ) * h'

theorem ode4_expand (d : ℕ) (hd : d ≠ 0) (h : 3 * theta uE = xE * uE - vE) :
    3 * theta (PowerSeries.expand d hd uE)
      = (d : PowerSeries ℝ) * (PowerSeries.expand d hd xE * PowerSeries.expand d hd uE - PowerSeries.expand d hd vE) := by
  have h' := congrArg (fun t => PowerSeries.expand d hd t) h
  simp only [map_mul, map_sub, map_ofNat] at h'
  rw [theta_expand]
  linear_combination (d : PowerSeries ℝ) * h'

theorem ode6_expand (d : ℕ) (hd : d ≠ 0) (h : 2 * theta vE = xE * vE - uE * uE) :
    2 * theta (PowerSeries.expand d hd vE)
      = (d : PowerSeries ℝ) * (PowerSeries.expand d hd xE * PowerSeries.expand d hd vE - PowerSeries.expand d hd uE * PowerSeries.expand d hd uE) := by
  have h' := congrArg (fun t => PowerSeries.expand d hd t) h
  simp only [map_mul, map_sub, map_ofNat] at h'
  rw [theta_expand]
  linear_combination (d : PowerSeries ℝ) * h'

/-- Ramanujan's identities at `q` give them at `q², q³, q⁶`. -/
theorem ram6_of_base (h2 : 12 * theta xE = xE * xE - uE) (h6 : 2 * theta vE = xE * vE - uE * uE) :
    Ram6 := by
  have h4 := ode4_base
  have a2_2 := ode2_expand 2 two_ne h2
  simp only [Nat.cast_ofNat] at a2_2
  have a4_2 := ode4_expand 2 two_ne h4
  simp only [Nat.cast_ofNat] at a4_2
  have a6_2 := ode6_expand 2 two_ne h6
  simp only [Nat.cast_ofNat] at a6_2
  have a2_3 := ode2_expand 3 three_ne h2
  simp only [Nat.cast_ofNat] at a2_3
  have a4_3 := ode4_expand 3 three_ne h4
  simp only [Nat.cast_ofNat] at a4_3
  have a6_3 := ode6_expand 3 three_ne h6
  simp only [Nat.cast_ofNat] at a6_3
  have a2_6 := ode2_expand 6 six_ne h2
  simp only [Nat.cast_ofNat] at a2_6
  have a4_6 := ode4_expand 6 six_ne h4
  simp only [Nat.cast_ofNat] at a4_6
  have a6_6 := ode6_expand 6 six_ne h6
  simp only [Nat.cast_ofNat] at a6_6
  unfold Ram6
  refine ⟨?_, a2_2, a2_3, a2_6, ?_, a4_2, a4_3, a4_6, ?_, a6_2, a6_3, a6_6⟩
  · show 12 * theta xE = 1 * (xE * xE - uE)
    linear_combination h2
  · show 3 * theta uE = 1 * (xE * uE - vE)
    linear_combination h4
  · show 2 * theta vE = 1 * (xE * vE - uE * uE)
    linear_combination h6

/-! ## Constant terms -/

theorem constantCoeff_theta (φ : PowerSeries ℝ) : PowerSeries.constantCoeff (theta φ) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_theta, Nat.cast_zero, zero_mul]

theorem cc_xE : PowerSeries.constantCoeff xE = 1 := by
  simp only [xE, S1, map_sub, map_mul, map_one, map_ofNat, PowerSeries.constantCoeff_mk, sig_zero]
  norm_num

theorem cc_uE : PowerSeries.constantCoeff uE = 1 := by
  simp only [uE, S3, map_add, map_mul, map_one, map_ofNat, PowerSeries.constantCoeff_mk, sig_zero]
  norm_num

theorem cc_vE : PowerSeries.constantCoeff vE = 1 := by
  simp only [vE, map_sub, map_mul, map_ofNat, cc_xE, cc_uE, constantCoeff_theta]
  norm_num

theorem cc_e2_1 : PowerSeries.constantCoeff e2_1 = 1 := cc_xE
theorem cc_e2_2 : PowerSeries.constantCoeff e2_2 = 1 := by
  unfold e2_2
  rw [PowerSeries.constantCoeff_expand, cc_xE]
theorem cc_e2_3 : PowerSeries.constantCoeff e2_3 = 1 := by
  unfold e2_3
  rw [PowerSeries.constantCoeff_expand, cc_xE]
theorem cc_e2_6 : PowerSeries.constantCoeff e2_6 = 1 := by
  unfold e2_6
  rw [PowerSeries.constantCoeff_expand, cc_xE]
theorem cc_e4_1 : PowerSeries.constantCoeff e4_1 = 1 := cc_uE
theorem cc_e4_2 : PowerSeries.constantCoeff e4_2 = 1 := by
  unfold e4_2
  rw [PowerSeries.constantCoeff_expand, cc_uE]
theorem cc_e4_3 : PowerSeries.constantCoeff e4_3 = 1 := by
  unfold e4_3
  rw [PowerSeries.constantCoeff_expand, cc_uE]
theorem cc_e4_6 : PowerSeries.constantCoeff e4_6 = 1 := by
  unfold e4_6
  rw [PowerSeries.constantCoeff_expand, cc_uE]
theorem cc_e6_1 : PowerSeries.constantCoeff e6_1 = 1 := cc_vE
theorem cc_e6_2 : PowerSeries.constantCoeff e6_2 = 1 := by
  unfold e6_2
  rw [PowerSeries.constantCoeff_expand, cc_vE]
theorem cc_e6_3 : PowerSeries.constantCoeff e6_3 = 1 := by
  unfold e6_3
  rw [PowerSeries.constantCoeff_expand, cc_vE]
theorem cc_e6_6 : PowerSeries.constantCoeff e6_6 = 1 := by
  unfold e6_6
  rw [PowerSeries.constantCoeff_expand, cc_vE]

/-! ## Truncations at `X⁷` -/

noncomputable def q1 : PowerSeries ℝ := P7 0 1 3 4 7 6 12
noncomputable def q3 : PowerSeries ℝ := P7 0 1 9 28 73 126 252
noncomputable def tq3 : PowerSeries ℝ := P7 0 1 18 84 292 630 1512
noncomputable def pxE : PowerSeries ℝ := P7 1 (-24) (-72) (-96) (-168) (-144) (-288)
noncomputable def puE : PowerSeries ℝ := P7 1 240 2160 6720 17520 30240 60480
noncomputable def pvE : PowerSeries ℝ := P7 1 (-504) (-16632) (-122976) (-532728) (-1575504) (-4058208)
noncomputable def pe2_1 : PowerSeries ℝ := P7 1 (-24) (-72) (-96) (-168) (-144) (-288)
noncomputable def pe2_2 : PowerSeries ℝ := P7 1 0 (-24) 0 (-72) 0 (-96)
noncomputable def pe2_3 : PowerSeries ℝ := P7 1 0 0 (-24) 0 0 (-72)
noncomputable def pe2_6 : PowerSeries ℝ := P7 1 0 0 0 0 0 (-24)
noncomputable def pe4_1 : PowerSeries ℝ := P7 1 240 2160 6720 17520 30240 60480
noncomputable def pe4_2 : PowerSeries ℝ := P7 1 0 240 0 2160 0 6720
noncomputable def pe4_3 : PowerSeries ℝ := P7 1 0 0 240 0 0 2160
noncomputable def pe4_6 : PowerSeries ℝ := P7 1 0 0 0 0 0 240
noncomputable def pe6_1 : PowerSeries ℝ := P7 1 (-504) (-16632) (-122976) (-532728) (-1575504) (-4058208)
noncomputable def pe6_2 : PowerSeries ℝ := P7 1 0 (-504) 0 (-16632) 0 (-122976)
noncomputable def pe6_3 : PowerSeries ℝ := P7 1 0 0 (-504) 0 0 (-16632)
noncomputable def pe6_6 : PowerSeries ℝ := P7 1 0 0 0 0 0 (-504)

theorem dvd_S1 : T ^ 7 ∣ S1 - q1 := by
  exact dvd7_sub_P7 S1 0 1 3 4 7 6 12
    ((PowerSeries.coeff_mk 0 (sig 1)).trans sig1_vals.1)
    ((PowerSeries.coeff_mk 1 (sig 1)).trans sig1_vals.2.1)
    ((PowerSeries.coeff_mk 2 (sig 1)).trans sig1_vals.2.2.1)
    ((PowerSeries.coeff_mk 3 (sig 1)).trans sig1_vals.2.2.2.1)
    ((PowerSeries.coeff_mk 4 (sig 1)).trans sig1_vals.2.2.2.2.1)
    ((PowerSeries.coeff_mk 5 (sig 1)).trans sig1_vals.2.2.2.2.2.1)
    ((PowerSeries.coeff_mk 6 (sig 1)).trans sig1_vals.2.2.2.2.2.2)

theorem dvd_S3 : T ^ 7 ∣ S3 - q3 := by
  exact dvd7_sub_P7 S3 0 1 9 28 73 126 252
    ((PowerSeries.coeff_mk 0 (sig 3)).trans sig3_vals.1)
    ((PowerSeries.coeff_mk 1 (sig 3)).trans sig3_vals.2.1)
    ((PowerSeries.coeff_mk 2 (sig 3)).trans sig3_vals.2.2.1)
    ((PowerSeries.coeff_mk 3 (sig 3)).trans sig3_vals.2.2.2.1)
    ((PowerSeries.coeff_mk 4 (sig 3)).trans sig3_vals.2.2.2.2.1)
    ((PowerSeries.coeff_mk 5 (sig 3)).trans sig3_vals.2.2.2.2.2.1)
    ((PowerSeries.coeff_mk 6 (sig 3)).trans sig3_vals.2.2.2.2.2.2)

theorem dvd_tS3 : T ^ 7 ∣ theta S3 - tq3 := by
  have c : ∀ k : ℕ, PowerSeries.coeff k (theta S3) = (k : ℝ) * sig 3 k := fun k => by
    rw [coeff_theta]
    exact congrArg (fun t => (k : ℝ) * t) (PowerSeries.coeff_mk k (sig 3))
  refine dvd7_sub_P7 (theta S3) 0 1 18 84 292 630 1512 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [c 0, sig3_vals.1]; norm_num
  · rw [c 1, sig3_vals.2.1]; norm_num
  · rw [c 2, sig3_vals.2.2.1]; norm_num
  · rw [c 3, sig3_vals.2.2.2.1]; norm_num
  · rw [c 4, sig3_vals.2.2.2.2.1]; norm_num
  · rw [c 5, sig3_vals.2.2.2.2.2.1]; norm_num
  · rw [c 6, sig3_vals.2.2.2.2.2.2]; norm_num

theorem dvd_xE : T ^ 7 ∣ xE - pxE := by
  have e : xE - pxE = (-24) * (S1 - q1) := by
    simp only [xE, pxE, q1, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [e]
  exact Dvd.dvd.mul_left dvd_S1 _

theorem dvd_uE : T ^ 7 ∣ uE - puE := by
  have e : uE - puE = 240 * (S3 - q3) := by
    simp only [uE, puE, q3, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [e]
  exact Dvd.dvd.mul_left dvd_S3 _

theorem theta_uE : theta uE = 240 * theta S3 := by
  unfold uE
  rw [theta_add, theta_one, theta_mul, theta_ofNat]
  ring

theorem pi7_vE : pi7 vE = pi7 pvE := by
  have hx := pi7_eq_of_dvd dvd_xE
  have hu := pi7_eq_of_dvd dvd_uE
  have ht := pi7_eq_of_dvd dvd_tS3
  have e : pxE * puE - 3 * (240 * tq3) = pvE + T ^ 7 * ((-6819840) + (-11790720) * T ^ 1 + (-15344640) * T ^ 2 + (-19560960) * T ^ 3 + (-17418240) * T ^ 4 + (-17418240) * T ^ 5) := by
    simp only [pxE, puE, tq3, pvE, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  have e1 : pi7 vE = pi7 (pxE * puE - 3 * (240 * tq3)) := by
    simp only [vE, theta_uE, map_sub, map_mul, map_ofNat, hx, hu, ht]
  rw [e1, e, map_add, pi7_X_pow_mul, add_zero]

theorem dvd_vE : T ^ 7 ∣ vE - pvE := by
  apply dvd7_of_pi7_eq_zero
  rw [map_sub, pi7_vE, sub_self]

theorem pi7_e2_1 : pi7 e2_1 = pi7 pe2_1 := by
  have e : pe2_1 = pxE := rfl
  rw [e]
  exact pi7_eq_of_dvd dvd_xE

theorem pi7_e2_2 : pi7 e2_2 = pi7 pe2_2 := by
  have h1 : pi7 e2_2 = pi7 (PowerSeries.expand 2 two_ne pxE) :=
    pi7_eq_of_dvd (dvd7_expand 2 two_ne dvd_xE)
  have e : PowerSeries.expand 2 two_ne pxE = pe2_2 + T ^ 7 * ((-168) * T ^ 1 + (-144) * T ^ 3 + (-288) * T ^ 5) := by
    simp only [pxE, pe2_2, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
      map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]

theorem pi7_e2_3 : pi7 e2_3 = pi7 pe2_3 := by
  have h1 : pi7 e2_3 = pi7 (PowerSeries.expand 3 three_ne pxE) :=
    pi7_eq_of_dvd (dvd7_expand 3 three_ne dvd_xE)
  have e : PowerSeries.expand 3 three_ne pxE = pe2_3 + T ^ 7 * ((-96) * T ^ 2 + (-168) * T ^ 5 + (-144) * T ^ 8 + (-288) * T ^ 11) := by
    simp only [pxE, pe2_3, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
      map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]

theorem pi7_e2_6 : pi7 e2_6 = pi7 pe2_6 := by
  have h1 : pi7 e2_6 = pi7 (PowerSeries.expand 6 six_ne pxE) :=
    pi7_eq_of_dvd (dvd7_expand 6 six_ne dvd_xE)
  have e : PowerSeries.expand 6 six_ne pxE = pe2_6 + T ^ 7 * ((-72) * T ^ 5 + (-96) * T ^ 11 + (-168) * T ^ 17 + (-144) * T ^ 23 + (-288) * T ^ 29) := by
    simp only [pxE, pe2_6, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
      map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]

theorem pi7_e4_1 : pi7 e4_1 = pi7 pe4_1 := by
  have e : pe4_1 = puE := rfl
  rw [e]
  exact pi7_eq_of_dvd dvd_uE

theorem pi7_e4_2 : pi7 e4_2 = pi7 pe4_2 := by
  have h1 : pi7 e4_2 = pi7 (PowerSeries.expand 2 two_ne puE) :=
    pi7_eq_of_dvd (dvd7_expand 2 two_ne dvd_uE)
  have e : PowerSeries.expand 2 two_ne puE = pe4_2 + T ^ 7 * (17520 * T ^ 1 + 30240 * T ^ 3 + 60480 * T ^ 5) := by
    simp only [puE, pe4_2, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
      map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]

theorem pi7_e4_3 : pi7 e4_3 = pi7 pe4_3 := by
  have h1 : pi7 e4_3 = pi7 (PowerSeries.expand 3 three_ne puE) :=
    pi7_eq_of_dvd (dvd7_expand 3 three_ne dvd_uE)
  have e : PowerSeries.expand 3 three_ne puE = pe4_3 + T ^ 7 * (6720 * T ^ 2 + 17520 * T ^ 5 + 30240 * T ^ 8 + 60480 * T ^ 11) := by
    simp only [puE, pe4_3, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
      map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]

theorem pi7_e4_6 : pi7 e4_6 = pi7 pe4_6 := by
  have h1 : pi7 e4_6 = pi7 (PowerSeries.expand 6 six_ne puE) :=
    pi7_eq_of_dvd (dvd7_expand 6 six_ne dvd_uE)
  have e : PowerSeries.expand 6 six_ne puE = pe4_6 + T ^ 7 * (2160 * T ^ 5 + 6720 * T ^ 11 + 17520 * T ^ 17 + 30240 * T ^ 23 + 60480 * T ^ 29) := by
    simp only [puE, pe4_6, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
      map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]

theorem pi7_e6_1 : pi7 e6_1 = pi7 pe6_1 := by
  have e : pe6_1 = pvE := rfl
  rw [e]
  exact pi7_eq_of_dvd dvd_vE

theorem pi7_e6_2 : pi7 e6_2 = pi7 pe6_2 := by
  have h1 : pi7 e6_2 = pi7 (PowerSeries.expand 2 two_ne pvE) :=
    pi7_eq_of_dvd (dvd7_expand 2 two_ne dvd_vE)
  have e : PowerSeries.expand 2 two_ne pvE = pe6_2 + T ^ 7 * ((-532728) * T ^ 1 + (-1575504) * T ^ 3 + (-4058208) * T ^ 5) := by
    simp only [pvE, pe6_2, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
      map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]

theorem pi7_e6_3 : pi7 e6_3 = pi7 pe6_3 := by
  have h1 : pi7 e6_3 = pi7 (PowerSeries.expand 3 three_ne pvE) :=
    pi7_eq_of_dvd (dvd7_expand 3 three_ne dvd_vE)
  have e : PowerSeries.expand 3 three_ne pvE = pe6_3 + T ^ 7 * ((-122976) * T ^ 2 + (-532728) * T ^ 5 + (-1575504) * T ^ 8 + (-4058208) * T ^ 11) := by
    simp only [pvE, pe6_3, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
      map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]

theorem pi7_e6_6 : pi7 e6_6 = pi7 pe6_6 := by
  have h1 : pi7 e6_6 = pi7 (PowerSeries.expand 6 six_ne pvE) :=
    pi7_eq_of_dvd (dvd7_expand 6 six_ne dvd_vE)
  have e : PowerSeries.expand 6 six_ne pvE = pe6_6 + T ^ 7 * ((-16632) * T ^ 5 + (-122976) * T ^ 11 + (-532728) * T ^ 17 + (-1575504) * T ^ 23
          + (-4058208) * T ^ 29) := by
    simp only [pvE, pe6_6, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
      map_ofNat, map_neg, map_one, map_zero]
    ring
  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]

/-! ## The nine relations -/

/-- `E₄(q) - U₁` as a polynomial in the twelve series. -/
noncomputable def Rf1 (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (-17) * (x1 * x2) + 24 * (x1 * x3) + 3 * (x1 * x6) + 7 * (x2 * x2) + (-3) * (x2 * x3)
    + 66 * (x2 * x6) + 27 * (x3 * x3) + (-243) * (x3 * x6) + 135 * (x6 * x6) + u1

/-- `4 E₄(q²) - U₂` as a polynomial in the twelve series. -/
noncomputable def Rf2 (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (-3) * (x1 * x2) + 6 * (x1 * x3) + (-3) * (x1 * x6) + (-7) * (x2 * x2) + 3 * (x2 * x3)
    + 54 * (x2 * x6) + 18 * (x3 * x3) + (-117) * (x3 * x6) + 45 * (x6 * x6) + 4 * (u2)

/-- `3 E₄(q³) - U₃` as a polynomial in the twelve series. -/
noncomputable def Rf3 (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (-1) * (x1 * x2) + 2 * (x1 * x3) + (-1) * (x1 * x6) + (x2 * x2) + (x2 * x3) + (-2) * (x2 * x6)
    + (-9) * (x3 * x3) + 21 * (x3 * x6) + (-15) * (x6 * x6) + 3 * (u3)

/-- `12 E₄(q⁶) - U₆` as a polynomial in the twelve series. -/
noncomputable def Rf4 (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (x1 * x2) + (-2) * (x1 * x3) + (x1 * x6) + (-1) * (x2 * x2) + (-1) * (x2 * x3) + 2 * (x2 * x6)
    + (-6) * (x3 * x3) + 39 * (x3 * x6) + (-45) * (x6 * x6) + 12 * (u6)

/-- `E₆(q) - V₁` as a polynomial in the twelve series. -/
noncomputable def Rf5 (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (-189) * (x1 * x2 * x2) + 489 * (x1 * x2 * x3) + 156 * (x1 * x2 * x6) + (-243) * (x1 * x3 * x3)
    + (-495) * (x1 * x3 * x6) + 261 * (x1 * x6 * x6) + 98 * (x2 * x2 * x2) + (-174) * (x2 * x2 * x3)
    + 600 * (x2 * x2 * x6) + 225 * (x2 * x3 * x3) + (-2790) * (x2 * x3 * x6) + 522 * (x2 * x6 * x6)
    + (-432) * (x3 * x3 * x3) + 3375 * (x3 * x3 * x6) + (-1080) * (x3 * x6 * x6)
    + (-324) * (x6 * x6 * x6) + v1

/-- `8 E₆(q²) - V₂` as a polynomial in the twelve series. -/
noncomputable def Rf6 (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (-21) * (x1 * x2 * x2) + 69 * (x1 * x2 * x3) + (-12) * (x1 * x2 * x6) + (-54) * (x1 * x3 * x3)
    + 9 * (x1 * x3 * x6) + 9 * (x1 * x6 * x6) + (-14) * (x2 * x2 * x2) + (-6) * (x2 * x2 * x3)
    + 264 * (x2 * x2 * x6) + 99 * (x2 * x3 * x3) + (-774) * (x2 * x3 * x6) + 18 * (x2 * x6 * x6)
    + (-54) * (x3 * x3 * x3) + 351 * (x3 * x3 * x6) + 432 * (x3 * x6 * x6) + (-324) * (x6 * x6 * x6)
    + 8 * (v2)

/-- `E₆(q³) - V₃` as a polynomial in the twelve series. -/
noncomputable def Rf7 (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (-1) * (x1 * x2 * x3) + 2 * (x1 * x2 * x6) + 2 * (x1 * x3 * x3) + (-5) * (x1 * x3 * x6)
    + 2 * (x1 * x6 * x6) + (x2 * x2 * x3) + (-2) * (x2 * x2 * x6) + (x2 * x3 * x3)
    + (-4) * (x2 * x3 * x6) + 4 * (x2 * x6 * x6) + (-5) * (x3 * x3 * x3) + 15 * (x3 * x3 * x6)
    + (-9) * (x3 * x6 * x6) + (-2) * (x6 * x6 * x6) + v3

/-- `8 E₆(q⁶) - V₆` as a polynomial in the twelve series. -/
noncomputable def Rf8 (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (-1) * (x1 * x2 * x3) + 2 * (x1 * x2 * x6) + 2 * (x1 * x3 * x3) + (-5) * (x1 * x3 * x6)
    + 2 * (x1 * x6 * x6) + (x2 * x2 * x3) + (-2) * (x2 * x2 * x6) + (x2 * x3 * x3)
    + (-4) * (x2 * x3 * x6) + 4 * (x2 * x6 * x6) + 2 * (x3 * x3 * x3) + (-27) * (x3 * x3 * x6)
    + 75 * (x3 * x6 * x6) + (-58) * (x6 * x6 * x6) + 8 * (v6)

/-- the quadratic relation `ρ` as a polynomial in the twelve series. -/
noncomputable def Rf9 (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (x1 * x1) + (-8) * (x1 * x2) + 6 * (x1 * x3) + 4 * (x2 * x2) + 24 * (x2 * x6) + 9 * (x3 * x3)
    + (-72) * (x3 * x6) + 36 * (x6 * x6)

theorem dvd7_Rf1 : T ^ 7 ∣ Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have key : pi7 (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = pi7 (Rf1 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6) := by
    simp only [Rf1, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pi7_e2_1, pi7_e2_2, pi7_e2_3, pi7_e2_6, pi7_e4_1, pi7_e4_2, pi7_e4_3, pi7_e4_6, pi7_e6_1, pi7_e6_2, pi7_e6_3, pi7_e6_6]
  have hR : Rf1 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6 = T ^ 7 * ((-80640) + (-126720) * T ^ 1 + (-47808) * T ^ 2 + (-129024) * T ^ 3 + 24192 * T ^ 4
        + 42048 * T ^ 5) := by
    simp only [Rf1, pe2_1, pe2_2, pe2_3, pe2_6, pe4_1, pe4_2, pe4_3, pe4_6, pe6_1, pe6_2, pe6_3, pe6_6, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  apply dvd7_of_pi7_eq_zero
  rw [key, hR]
  exact pi7_X_pow_mul _

theorem dvd7_Rf2 : T ^ 7 ∣ Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have key : pi7 (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = pi7 (Rf2 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6) := by
    simp only [Rf2, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pi7_e2_1, pi7_e2_2, pi7_e2_3, pi7_e2_6, pi7_e4_1, pi7_e4_2, pi7_e4_3, pi7_e4_6, pi7_e6_1, pi7_e6_2, pi7_e6_3, pi7_e6_6]
  have hR : Rf2 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6 = T ^ 7 * ((-63360) * T ^ 1 + 19008 * T ^ 2 + (-38016) * T ^ 3 + 10368 * T ^ 4 + 18432 * T ^ 5) := by
    simp only [Rf2, pe2_1, pe2_2, pe2_3, pe2_6, pe4_1, pe4_2, pe4_3, pe4_6, pe6_1, pe6_2, pe6_3, pe6_6, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  apply dvd7_of_pi7_eq_zero
  rw [key, hR]
  exact pi7_X_pow_mul _

theorem dvd7_Rf3 : T ^ 7 ∣ Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have key : pi7 (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = pi7 (Rf3 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6) := by
    simp only [Rf3, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pi7_e2_1, pi7_e2_2, pi7_e2_3, pi7_e2_6, pi7_e4_1, pi7_e4_2, pi7_e4_3, pi7_e4_6, pi7_e6_1, pi7_e6_2, pi7_e6_3, pi7_e6_6]
  have hR : Rf3 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6 = T ^ 7 * ((-10944) * T ^ 2 + (-1152) * T ^ 3 + 3456 * T ^ 4 + (-576) * T ^ 5) := by
    simp only [Rf3, pe2_1, pe2_2, pe2_3, pe2_6, pe4_1, pe4_2, pe4_3, pe4_6, pe6_1, pe6_2, pe6_3, pe6_6, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  apply dvd7_of_pi7_eq_zero
  rw [key, hR]
  exact pi7_X_pow_mul _

theorem dvd7_Rf4 : T ^ 7 ∣ Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have key : pi7 (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = pi7 (Rf4 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6) := by
    simp only [Rf4, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pi7_e2_1, pi7_e2_2, pi7_e2_3, pi7_e2_6, pi7_e4_1, pi7_e4_2, pi7_e4_3, pi7_e4_6, pi7_e6_1, pi7_e6_2, pi7_e6_3, pi7_e6_6]
  have hR : Rf4 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6 = T ^ 7 * ((-6336) * T ^ 2 + 1152 * T ^ 3 + (-3456) * T ^ 4 + (-8064) * T ^ 5) := by
    simp only [Rf4, pe2_1, pe2_2, pe2_3, pe2_6, pe4_1, pe4_2, pe4_3, pe4_6, pe6_1, pe6_2, pe6_3, pe6_6, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  apply dvd7_of_pi7_eq_zero
  rw [key, hR]
  exact pi7_X_pow_mul _

theorem dvd7_Rf5 : T ^ 7 ∣ Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have key : pi7 (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = pi7 (Rf5 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6) := by
    simp only [Rf5, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pi7_e2_1, pi7_e2_2, pi7_e2_3, pi7_e2_6, pi7_e4_1, pi7_e4_2, pi7_e4_3, pi7_e4_6, pi7_e6_1, pi7_e6_2, pi7_e6_3, pi7_e6_6]
  have hR : Rf5 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6 = T ^ 7 * (8467200 + 16934400 * T ^ 1 + 27701568 * T ^ 2 + 45474048 * T ^ 3 + 34349184 * T ^ 4
        + 100142784 * T ^ 5 + (-13519872) * T ^ 6 + 79750656 * T ^ 7 + (-16920576) * T ^ 8
        + (-40227840) * T ^ 9 + (-4727808) * T ^ 10 + (-815616) * T ^ 11) := by
    simp only [Rf5, pe2_1, pe2_2, pe2_3, pe2_6, pe4_1, pe4_2, pe4_3, pe4_6, pe6_1, pe6_2, pe6_3, pe6_6, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  apply dvd7_of_pi7_eq_zero
  rw [key, hR]
  exact pi7_X_pow_mul _

theorem dvd7_Rf6 : T ^ 7 ∣ Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have key : pi7 (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = pi7 (Rf6 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6) := by
    simp only [Rf6, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pi7_e2_1, pi7_e2_2, pi7_e2_3, pi7_e2_6, pi7_e4_1, pi7_e4_2, pi7_e4_3, pi7_e4_6, pi7_e6_1, pi7_e6_2, pi7_e6_3, pi7_e6_6]
  have hR : Rf6 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6 = T ^ 7 * (4233600 * T ^ 1 + (-95040) * T ^ 2 + 10903680 * T ^ 3 + (-3245184) * T ^ 4 + 22208256 * T ^ 5
        + (-12068352) * T ^ 6 + 14432256 * T ^ 7 + (-3566592) * T ^ 8 + (-8004096) * T ^ 9
        + 497664 * T ^ 10 + 152064 * T ^ 11) := by
    simp only [Rf6, pe2_1, pe2_2, pe2_3, pe2_6, pe4_1, pe4_2, pe4_3, pe4_6, pe6_1, pe6_2, pe6_3, pe6_6, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  apply dvd7_of_pi7_eq_zero
  rw [key, hR]
  exact pi7_X_pow_mul _

theorem dvd7_Rf7 : T ^ 7 ∣ Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have key : pi7 (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = pi7 (Rf7 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6) := by
    simp only [Rf7, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pi7_e2_1, pi7_e2_2, pi7_e2_3, pi7_e2_6, pi7_e4_1, pi7_e4_2, pi7_e4_3, pi7_e4_6, pi7_e6_1, pi7_e6_2, pi7_e6_3, pi7_e6_6]
  have hR : Rf7 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6 = T ^ 7 * (114624 * T ^ 2 + 1152 * T ^ 3 + (-3456) * T ^ 4 + 245952 * T ^ 5 + 27648 * T ^ 6
        + (-82944) * T ^ 7 + 110592 * T ^ 8 + 27648 * T ^ 9 + (-82944) * T ^ 10 + (-41472) * T ^ 11) := by
    simp only [Rf7, pe2_1, pe2_2, pe2_3, pe2_6, pe4_1, pe4_2, pe4_3, pe4_6, pe6_1, pe6_2, pe6_3, pe6_6, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  apply dvd7_of_pi7_eq_zero
  rw [key, hR]
  exact pi7_X_pow_mul _

theorem dvd7_Rf8 : T ^ 7 ∣ Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have key : pi7 (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = pi7 (Rf8 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6) := by
    simp only [Rf8, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pi7_e2_1, pi7_e2_2, pi7_e2_3, pi7_e2_6, pi7_e4_1, pi7_e4_2, pi7_e4_3, pi7_e4_6, pi7_e6_1, pi7_e6_2, pi7_e6_3, pi7_e6_6]
  have hR : Rf8 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6 = T ^ 7 * ((-6336) * T ^ 2 + 1152 * T ^ 3 + (-3456) * T ^ 4 + (-56448) * T ^ 5 + 27648 * T ^ 6
        + (-82944) * T ^ 7 + (-179712) * T ^ 8 + 27648 * T ^ 9 + (-82944) * T ^ 10 + (-138240) * T ^ 11) := by
    simp only [Rf8, pe2_1, pe2_2, pe2_3, pe2_6, pe4_1, pe4_2, pe4_3, pe4_6, pe6_1, pe6_2, pe6_3, pe6_6, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  apply dvd7_of_pi7_eq_zero
  rw [key, hR]
  exact pi7_X_pow_mul _

theorem dvd7_Rf9 : T ^ 7 ∣ Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 := by
  have key : pi7 (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = pi7 (Rf9 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6) := by
    simp only [Rf9, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pi7_e2_1, pi7_e2_2, pi7_e2_3, pi7_e2_6, pi7_e4_1, pi7_e4_2, pi7_e4_3, pi7_e4_6, pi7_e6_1, pi7_e6_2, pi7_e6_3, pi7_e6_6]
  have hR : Rf9 pe2_1 pe2_2 pe2_3 pe2_6 pe4_1 pe4_2 pe4_3 pe4_6 pe6_1 pe6_2 pe6_3 pe6_6 = T ^ 7 * ((-5184) * T ^ 1 + 19584 * T ^ 2 + (-8064) * T ^ 3 + 34560 * T ^ 4 + 21312 * T ^ 5) := by
    simp only [Rf9, pe2_1, pe2_2, pe2_3, pe2_6, pe4_1, pe4_2, pe4_3, pe4_6, pe6_1, pe6_2, pe6_3, pe6_6, P7, map_ofNat, map_neg, map_one, map_zero]
    ring
  apply dvd7_of_pi7_eq_zero
  rw [key, hR]
  exact pi7_X_pow_mul _

/-! ## The closed system `24 θR = M R` -/

theorem clos1 (h : Ram6) :
    24 * theta (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = (8 * (e2_1) + 34 * (e2_2) + (-48) * (e2_3)
        + (-6) * (e2_6)) * (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (17 * (e2_1) + (-14) * (e2_2) + 3 * (e2_3)
        + (-66) * (e2_6)) * (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-48) * (e2_1) + 6 * (e2_2) + (-108) * (e2_3)
        + 486 * (e2_6)) * (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-3) * (e2_1) + (-66) * (e2_2) + 243 * (e2_3)
        + (-270) * (e2_6)) * (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-8)) * (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) + (108 * (e2_2)
        + (-156) * (e2_3)
        + (-12) * (e2_6)) * (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-17) * (e2_2) + 24 * (e2_3) + 3 * (e2_6)) * theta e2_1 + ((-17) * (e2_1) + 14 * (e2_2)
        + (-3) * (e2_3) + 66 * (e2_6)) * theta e2_2 + (24 * (e2_1) + (-3) * (e2_2) + 54 * (e2_3)
        + (-243) * (e2_6)) * theta e2_3 + (3 * (e2_1) + 66 * (e2_2) + (-243) * (e2_3)
        + 270 * (e2_6)) * theta e2_6 + (1) * theta e4_1 := by
    simp only [Rf1, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ ⊢
  linear_combination 24 * hθ + (2 * ((-17) * (e2_2) + 24 * (e2_3) + 3 * (e2_6))) * h1 + (2 * ((-17) * (e2_1)
    + 14 * (e2_2) + (-3) * (e2_3) + 66 * (e2_6))) * h2 + (2 * (24 * (e2_1) + (-3) * (e2_2)
    + 54 * (e2_3) + (-243) * (e2_6))) * h3 + (2 * (3 * (e2_1) + 66 * (e2_2) + (-243) * (e2_3)
    + 270 * (e2_6))) * h4 + (8 * (1)) * h5

theorem clos2 (h : Ram6) :
    24 * theta (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = (6 * (e2_2) + (-12) * (e2_3)
        + 6 * (e2_6)) * (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) + (3 * (e2_1)
        + 30 * (e2_2) + (-3) * (e2_3)
        + (-54) * (e2_6)) * (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-12) * (e2_1) + (-6) * (e2_2) + (-72) * (e2_3)
        + 234 * (e2_6)) * (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (3 * (e2_1) + (-54) * (e2_2) + 117 * (e2_3)
        + (-90) * (e2_6)) * (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-8)) * (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) + ((-12) * (e2_2)
        + 24 * (e2_3)
        + (-12) * (e2_6)) * (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-3) * (e2_2) + 6 * (e2_3) + (-3) * (e2_6)) * theta e2_1 + ((-3) * (e2_1) + (-14) * (e2_2)
        + 3 * (e2_3) + 54 * (e2_6)) * theta e2_2 + (6 * (e2_1) + 3 * (e2_2) + 36 * (e2_3)
        + (-117) * (e2_6)) * theta e2_3 + ((-3) * (e2_1) + 54 * (e2_2) + (-117) * (e2_3)
        + 90 * (e2_6)) * theta e2_6 + (4) * theta e4_2 := by
    simp only [Rf2, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ ⊢
  linear_combination 24 * hθ + (2 * ((-3) * (e2_2) + 6 * (e2_3) + (-3) * (e2_6))) * h1 + (2 * ((-3) * (e2_1)
    + (-14) * (e2_2) + 3 * (e2_3) + 54 * (e2_6))) * h2 + (2 * (6 * (e2_1) + 3 * (e2_2) + 36 * (e2_3)
    + (-117) * (e2_6))) * h3 + (2 * ((-3) * (e2_1) + 54 * (e2_2) + (-117) * (e2_3)
    + 90 * (e2_6))) * h4 + (8 * (4)) * h6

theorem clos3 (h : Ram6) :
    24 * theta (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = (2 * (e2_2) + (-4) * (e2_3)
        + 2 * (e2_6)) * (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) + (e2_1
        + (-2) * (e2_2) + (-1) * (e2_3)
        + 2 * (e2_6)) * (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-4) * (e2_1) + (-2) * (e2_2) + 60 * (e2_3)
        + (-42) * (e2_6)) * (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) + (e2_1
        + 2 * (e2_2) + (-21) * (e2_3)
        + 30 * (e2_6)) * (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-72)) * (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) + ((-4) * (e2_2)
        + 8 * (e2_3)
        + (-4) * (e2_6)) * (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-1) * (e2_2) + 2 * (e2_3) + (-1) * (e2_6)) * theta e2_1 + ((-1) * (e2_1) + 2 * (e2_2) + e2_3
        + (-2) * (e2_6)) * theta e2_2 + (2 * (e2_1) + e2_2 + (-18) * (e2_3) + 21 * (e2_6)) * theta e2_3
        + ((-1) * (e2_1) + (-2) * (e2_2) + 21 * (e2_3) + (-30) * (e2_6)) * theta e2_6 + (3) * theta e4_3 := by
    simp only [Rf3, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ ⊢
  linear_combination 24 * hθ + (2 * ((-1) * (e2_2) + 2 * (e2_3) + (-1) * (e2_6))) * h1 + (2 * ((-1) * (e2_1)
    + 2 * (e2_2) + e2_3 + (-2) * (e2_6))) * h2 + (2 * (2 * (e2_1) + e2_2 + (-18) * (e2_3)
    + 21 * (e2_6))) * h3 + (2 * ((-1) * (e2_1) + (-2) * (e2_2) + 21 * (e2_3) + (-30) * (e2_6))) * h4
    + (8 * (3)) * h7

theorem clos4 (h : Ram6) :
    24 * theta (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-2) * (e2_2) + 4 * (e2_3)
        + (-2) * (e2_6)) * (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-1) * (e2_1) + 2 * (e2_2) + e2_3
        + (-2) * (e2_6)) * (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (4 * (e2_1) + 2 * (e2_2) + 24 * (e2_3)
        + (-78) * (e2_6)) * (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-1) * (e2_1) + (-2) * (e2_2) + (-39) * (e2_3)
        + 138 * (e2_6)) * (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-72)) * (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) + (4 * (e2_2)
        + (-8) * (e2_3)
        + 4 * (e2_6)) * (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = (e2_2 + (-2) * (e2_3) + e2_6) * theta e2_1 + (e2_1 + (-2) * (e2_2) + (-1) * (e2_3)
        + 2 * (e2_6)) * theta e2_2 + ((-2) * (e2_1) + (-1) * (e2_2) + (-12) * (e2_3)
        + 39 * (e2_6)) * theta e2_3 + (e2_1 + 2 * (e2_2) + 39 * (e2_3) + (-90) * (e2_6)) * theta e2_6
        + (12) * theta e4_6 := by
    simp only [Rf4, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ ⊢
  linear_combination 24 * hθ + (2 * (e2_2 + (-2) * (e2_3) + e2_6)) * h1 + (2 * (e2_1 + (-2) * (e2_2) + (-1) * (e2_3)
    + 2 * (e2_6))) * h2 + (2 * ((-2) * (e2_1) + (-1) * (e2_2) + (-12) * (e2_3) + 39 * (e2_6))) * h3
    + (2 * (e2_1 + 2 * (e2_2) + 39 * (e2_3) + (-90) * (e2_6))) * h4 + (8 * (12)) * h8

theorem clos5 (h : Ram6) :
    24 * theta (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-204) * (e2_1 * e2_2) + 288 * (e2_1 * e2_3) + 36 * (e2_1 * e2_6) + 462 * (e2_2 * e2_2)
        + (-1014) * (e2_2 * e2_3) + 480 * (e2_2 * e2_6) + 810 * (e2_3 * e2_3) + (-1926) * (e2_3 * e2_6)
        + 1098 * (e2_6 * e2_6)
        + (-12) * (e4_1)) * (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (378 * (e2_1 * e2_2) + (-489) * (e2_1 * e2_3) + (-156) * (e2_1 * e2_6)
        + (-294) * (e2_2 * e2_2) + 348 * (e2_2 * e2_3) + (-1200) * (e2_2 * e2_6)
        + (-225) * (e2_3 * e2_3) + 2790 * (e2_3 * e2_6)
        + (-522) * (e2_6 * e2_6)) * (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-978) * (e2_1 * e2_2) + 972 * (e2_1 * e2_3) + 990 * (e2_1 * e2_6) + 348 * (e2_2 * e2_2)
        + (-900) * (e2_2 * e2_3) + 5580 * (e2_2 * e2_6) + 2592 * (e2_3 * e2_3)
        + (-13500) * (e2_3 * e2_6)
        + 2160 * (e2_6 * e2_6)) * (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-156) * (e2_1 * e2_2) + 495 * (e2_1 * e2_3) + (-522) * (e2_1 * e2_6)
        + (-600) * (e2_2 * e2_2) + 2790 * (e2_2 * e2_3) + (-1044) * (e2_2 * e2_6)
        + (-3375) * (e2_3 * e2_3) + 2160 * (e2_3 * e2_6)
        + 972 * (e2_6 * e2_6)) * (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (12 * (e2_1)) * (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-1266) * (e2_2 * e2_2) + 3288 * (e2_2 * e2_3) + 1020 * (e2_2 * e2_6)
        + (-2502) * (e2_3 * e2_3) + 144 * (e2_3 * e2_6)
        + (-1674) * (e2_6 * e2_6)) * (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-189) * (e2_2 * e2_2) + 489 * (e2_2 * e2_3) + 156 * (e2_2 * e2_6) + (-243) * (e2_3 * e2_3)
        + (-495) * (e2_3 * e2_6) + 261 * (e2_6 * e2_6)) * theta e2_1 + ((-378) * (e2_1 * e2_2)
        + 489 * (e2_1 * e2_3) + 156 * (e2_1 * e2_6) + 294 * (e2_2 * e2_2) + (-348) * (e2_2 * e2_3)
        + 1200 * (e2_2 * e2_6) + 225 * (e2_3 * e2_3) + (-2790) * (e2_3 * e2_6)
        + 522 * (e2_6 * e2_6)) * theta e2_2 + (489 * (e2_1 * e2_2) + (-486) * (e2_1 * e2_3)
        + (-495) * (e2_1 * e2_6) + (-174) * (e2_2 * e2_2) + 450 * (e2_2 * e2_3)
        + (-2790) * (e2_2 * e2_6) + (-1296) * (e2_3 * e2_3) + 6750 * (e2_3 * e2_6)
        + (-1080) * (e2_6 * e2_6)) * theta e2_3 + (156 * (e2_1 * e2_2) + (-495) * (e2_1 * e2_3)
        + 522 * (e2_1 * e2_6) + 600 * (e2_2 * e2_2) + (-2790) * (e2_2 * e2_3) + 1044 * (e2_2 * e2_6)
        + 3375 * (e2_3 * e2_3) + (-2160) * (e2_3 * e2_6) + (-972) * (e2_6 * e2_6)) * theta e2_6
        + (1) * theta e6_1 := by
    simp only [Rf5, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ ⊢
  linear_combination 24 * hθ + (2 * ((-189) * (e2_2 * e2_2) + 489 * (e2_2 * e2_3) + 156 * (e2_2 * e2_6)
    + (-243) * (e2_3 * e2_3) + (-495) * (e2_3 * e2_6) + 261 * (e2_6 * e2_6))) * h1
    + (2 * ((-378) * (e2_1 * e2_2) + 489 * (e2_1 * e2_3) + 156 * (e2_1 * e2_6) + 294 * (e2_2 * e2_2)
    + (-348) * (e2_2 * e2_3) + 1200 * (e2_2 * e2_6) + 225 * (e2_3 * e2_3) + (-2790) * (e2_3 * e2_6)
    + 522 * (e2_6 * e2_6))) * h2 + (2 * (489 * (e2_1 * e2_2) + (-486) * (e2_1 * e2_3)
    + (-495) * (e2_1 * e2_6) + (-174) * (e2_2 * e2_2) + 450 * (e2_2 * e2_3)
    + (-2790) * (e2_2 * e2_6) + (-1296) * (e2_3 * e2_3) + 6750 * (e2_3 * e2_6)
    + (-1080) * (e2_6 * e2_6))) * h3 + (2 * (156 * (e2_1 * e2_2) + (-495) * (e2_1 * e2_3)
    + 522 * (e2_1 * e2_6) + 600 * (e2_2 * e2_2) + (-2790) * (e2_2 * e2_3) + 1044 * (e2_2 * e2_6)
    + 3375 * (e2_3 * e2_3) + (-2160) * (e2_3 * e2_6) + (-972) * (e2_6 * e2_6))) * h4
    + (12 * (1)) * h9

theorem clos6 (h : Ram6) :
    24 * theta (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = (42 * (e2_2 * e2_2) + (-138) * (e2_2 * e2_3) + 24 * (e2_2 * e2_6) + 108 * (e2_3 * e2_3)
        + (-18) * (e2_3 * e2_6)
        + (-18) * (e2_6 * e2_6)) * (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (6 * (e2_1 * e2_2) + 3 * (e2_1 * e2_3) + (-24) * (e2_1 * e2_6) + (-42) * (e2_2 * e2_2)
        + 48 * (e2_2 * e2_3) + 120 * (e2_2 * e2_6) + 117 * (e2_3 * e2_3) + (-630) * (e2_3 * e2_6)
        + 522 * (e2_6 * e2_6)
        + (-48) * (e4_2)) * (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-138) * (e2_1 * e2_2) + 216 * (e2_1 * e2_3) + (-18) * (e2_1 * e2_6) + 12 * (e2_2 * e2_2)
        + (-396) * (e2_2 * e2_3) + 1548 * (e2_2 * e2_6) + 324 * (e2_3 * e2_3) + (-1404) * (e2_3 * e2_6)
        + (-864) * (e2_6 * e2_6)) * (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (12 * (e2_1 * e2_2) + (-9) * (e2_1 * e2_3) + (-18) * (e2_1 * e2_6) + (-264) * (e2_2 * e2_2)
        + 774 * (e2_2 * e2_3) + (-36) * (e2_2 * e2_6) + (-351) * (e2_3 * e2_3) + (-864) * (e2_3 * e2_6)
        + 972 * (e2_6 * e2_6)) * (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (24 * (e2_2)) * (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-174) * (e2_2 * e2_2) + 636 * (e2_2 * e2_3) + (-228) * (e2_2 * e2_6)
        + (-576) * (e2_3 * e2_3) + 396 * (e2_3 * e2_6)
        + (-54) * (e2_6 * e2_6)) * (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-21) * (e2_2 * e2_2) + 69 * (e2_2 * e2_3) + (-12) * (e2_2 * e2_6) + (-54) * (e2_3 * e2_3)
        + 9 * (e2_3 * e2_6) + 9 * (e2_6 * e2_6)) * theta e2_1 + ((-42) * (e2_1 * e2_2)
        + 69 * (e2_1 * e2_3) + (-12) * (e2_1 * e2_6) + (-42) * (e2_2 * e2_2) + (-12) * (e2_2 * e2_3)
        + 528 * (e2_2 * e2_6) + 99 * (e2_3 * e2_3) + (-774) * (e2_3 * e2_6)
        + 18 * (e2_6 * e2_6)) * theta e2_2 + (69 * (e2_1 * e2_2) + (-108) * (e2_1 * e2_3)
        + 9 * (e2_1 * e2_6) + (-6) * (e2_2 * e2_2) + 198 * (e2_2 * e2_3) + (-774) * (e2_2 * e2_6)
        + (-162) * (e2_3 * e2_3) + 702 * (e2_3 * e2_6) + 432 * (e2_6 * e2_6)) * theta e2_3
        + ((-12) * (e2_1 * e2_2) + 9 * (e2_1 * e2_3) + 18 * (e2_1 * e2_6) + 264 * (e2_2 * e2_2)
        + (-774) * (e2_2 * e2_3) + 36 * (e2_2 * e2_6) + 351 * (e2_3 * e2_3) + 864 * (e2_3 * e2_6)
        + (-972) * (e2_6 * e2_6)) * theta e2_6 + (8) * theta e6_2 := by
    simp only [Rf6, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ ⊢
  linear_combination 24 * hθ + (2 * ((-21) * (e2_2 * e2_2) + 69 * (e2_2 * e2_3) + (-12) * (e2_2 * e2_6)
    + (-54) * (e2_3 * e2_3) + 9 * (e2_3 * e2_6) + 9 * (e2_6 * e2_6))) * h1
    + (2 * ((-42) * (e2_1 * e2_2) + 69 * (e2_1 * e2_3) + (-12) * (e2_1 * e2_6)
    + (-42) * (e2_2 * e2_2) + (-12) * (e2_2 * e2_3) + 528 * (e2_2 * e2_6) + 99 * (e2_3 * e2_3)
    + (-774) * (e2_3 * e2_6) + 18 * (e2_6 * e2_6))) * h2 + (2 * (69 * (e2_1 * e2_2)
    + (-108) * (e2_1 * e2_3) + 9 * (e2_1 * e2_6) + (-6) * (e2_2 * e2_2) + 198 * (e2_2 * e2_3)
    + (-774) * (e2_2 * e2_6) + (-162) * (e2_3 * e2_3) + 702 * (e2_3 * e2_6)
    + 432 * (e2_6 * e2_6))) * h3 + (2 * ((-12) * (e2_1 * e2_2) + 9 * (e2_1 * e2_3)
    + 18 * (e2_1 * e2_6) + 264 * (e2_2 * e2_2) + (-774) * (e2_2 * e2_3) + 36 * (e2_2 * e2_6)
    + 351 * (e2_3 * e2_3) + 864 * (e2_3 * e2_6) + (-972) * (e2_6 * e2_6))) * h4 + (12 * (8)) * h10

theorem clos7 (h : Ram6) :
    24 * theta (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = (2 * (e2_2 * e2_3) + (-4) * (e2_2 * e2_6) + (-4) * (e2_3 * e2_3) + 10 * (e2_3 * e2_6)
        + (-4) * (e2_6 * e2_6)) * (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((e2_1 * e2_3) + (-2) * (e2_1 * e2_6) + (-2) * (e2_2 * e2_3) + 4 * (e2_2 * e2_6)
        + (-1) * (e2_3 * e2_3) + 4 * (e2_3 * e2_6)
        + (-4) * (e2_6 * e2_6)) * (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-2) * (e2_1 * e2_2) + 6 * (e2_1 * e2_6) + 2 * (e2_2 * e2_2) + (-6) * (e2_3 * e2_3)
        + 24 * (e2_3 * e2_6) + (-42) * (e2_6 * e2_6)
        + (-12) * (e4_3)) * (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-2) * (e2_1 * e2_2) + 5 * (e2_1 * e2_3) + (-4) * (e2_1 * e2_6) + 2 * (e2_2 * e2_2)
        + 4 * (e2_2 * e2_3) + (-8) * (e2_2 * e2_6) + (-15) * (e2_3 * e2_3) + 18 * (e2_3 * e2_6)
        + 6 * (e2_6 * e2_6)) * (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (36 * (e2_3)) * (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-4) * (e2_2 * e2_3) + 8 * (e2_2 * e2_6) + 8 * (e2_3 * e2_3) + (-20) * (e2_3 * e2_6)
        + 8 * (e2_6 * e2_6)) * (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-1) * (e2_2 * e2_3) + 2 * (e2_2 * e2_6) + 2 * (e2_3 * e2_3) + (-5) * (e2_3 * e2_6)
        + 2 * (e2_6 * e2_6)) * theta e2_1 + ((-1) * (e2_1 * e2_3) + 2 * (e2_1 * e2_6)
        + 2 * (e2_2 * e2_3) + (-4) * (e2_2 * e2_6) + (e2_3 * e2_3) + (-4) * (e2_3 * e2_6)
        + 4 * (e2_6 * e2_6)) * theta e2_2 + ((-1) * (e2_1 * e2_2) + 4 * (e2_1 * e2_3)
        + (-5) * (e2_1 * e2_6) + (e2_2 * e2_2) + 2 * (e2_2 * e2_3) + (-4) * (e2_2 * e2_6)
        + (-15) * (e2_3 * e2_3) + 30 * (e2_3 * e2_6) + (-9) * (e2_6 * e2_6)) * theta e2_3
        + (2 * (e2_1 * e2_2) + (-5) * (e2_1 * e2_3) + 4 * (e2_1 * e2_6) + (-2) * (e2_2 * e2_2)
        + (-4) * (e2_2 * e2_3) + 8 * (e2_2 * e2_6) + 15 * (e2_3 * e2_3) + (-18) * (e2_3 * e2_6)
        + (-6) * (e2_6 * e2_6)) * theta e2_6 + (1) * theta e6_3 := by
    simp only [Rf7, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ ⊢
  linear_combination 24 * hθ + (2 * ((-1) * (e2_2 * e2_3) + 2 * (e2_2 * e2_6) + 2 * (e2_3 * e2_3)
    + (-5) * (e2_3 * e2_6) + 2 * (e2_6 * e2_6))) * h1 + (2 * ((-1) * (e2_1 * e2_3)
    + 2 * (e2_1 * e2_6) + 2 * (e2_2 * e2_3) + (-4) * (e2_2 * e2_6) + (e2_3 * e2_3)
    + (-4) * (e2_3 * e2_6) + 4 * (e2_6 * e2_6))) * h2 + (2 * ((-1) * (e2_1 * e2_2)
    + 4 * (e2_1 * e2_3) + (-5) * (e2_1 * e2_6) + (e2_2 * e2_2) + 2 * (e2_2 * e2_3)
    + (-4) * (e2_2 * e2_6) + (-15) * (e2_3 * e2_3) + 30 * (e2_3 * e2_6)
    + (-9) * (e2_6 * e2_6))) * h3 + (2 * (2 * (e2_1 * e2_2) + (-5) * (e2_1 * e2_3)
    + 4 * (e2_1 * e2_6) + (-2) * (e2_2 * e2_2) + (-4) * (e2_2 * e2_3) + 8 * (e2_2 * e2_6)
    + 15 * (e2_3 * e2_3) + (-18) * (e2_3 * e2_6) + (-6) * (e2_6 * e2_6))) * h4 + (12 * (1)) * h11

theorem clos8 (h : Ram6) :
    24 * theta (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = (2 * (e2_2 * e2_3) + (-4) * (e2_2 * e2_6) + (-4) * (e2_3 * e2_3) + 10 * (e2_3 * e2_6)
        + (-4) * (e2_6 * e2_6)) * (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((e2_1 * e2_3) + (-2) * (e2_1 * e2_6) + (-2) * (e2_2 * e2_3) + 4 * (e2_2 * e2_6)
        + (-1) * (e2_3 * e2_3) + 4 * (e2_3 * e2_6)
        + (-4) * (e2_6 * e2_6)) * (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (2 * (e2_1 * e2_2) + (-8) * (e2_1 * e2_3) + 10 * (e2_1 * e2_6) + (-2) * (e2_2 * e2_2)
        + (-4) * (e2_2 * e2_3) + 8 * (e2_2 * e2_6) + (-12) * (e2_3 * e2_3) + 108 * (e2_3 * e2_6)
        + (-150) * (e2_6 * e2_6)) * (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (2 * (e2_1 * e2_2) + (-3) * (e2_1 * e2_3) + (-2) * (e2_2 * e2_2) + 3 * (e2_3 * e2_3)
        + 6 * (e2_3 * e2_6) + (-6) * (e2_6 * e2_6)
        + (-48) * (e4_6)) * (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (72 * (e2_6)) * (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-4) * (e2_2 * e2_3) + 8 * (e2_2 * e2_6) + 8 * (e2_3 * e2_3) + (-20) * (e2_3 * e2_6)
        + 8 * (e2_6 * e2_6)) * (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-1) * (e2_2 * e2_3) + 2 * (e2_2 * e2_6) + 2 * (e2_3 * e2_3) + (-5) * (e2_3 * e2_6)
        + 2 * (e2_6 * e2_6)) * theta e2_1 + ((-1) * (e2_1 * e2_3) + 2 * (e2_1 * e2_6)
        + 2 * (e2_2 * e2_3) + (-4) * (e2_2 * e2_6) + (e2_3 * e2_3) + (-4) * (e2_3 * e2_6)
        + 4 * (e2_6 * e2_6)) * theta e2_2 + ((-1) * (e2_1 * e2_2) + 4 * (e2_1 * e2_3)
        + (-5) * (e2_1 * e2_6) + (e2_2 * e2_2) + 2 * (e2_2 * e2_3) + (-4) * (e2_2 * e2_6)
        + 6 * (e2_3 * e2_3) + (-54) * (e2_3 * e2_6) + 75 * (e2_6 * e2_6)) * theta e2_3
        + (2 * (e2_1 * e2_2) + (-5) * (e2_1 * e2_3) + 4 * (e2_1 * e2_6) + (-2) * (e2_2 * e2_2)
        + (-4) * (e2_2 * e2_3) + 8 * (e2_2 * e2_6) + (-27) * (e2_3 * e2_3) + 150 * (e2_3 * e2_6)
        + (-174) * (e2_6 * e2_6)) * theta e2_6 + (8) * theta e6_6 := by
    simp only [Rf8, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ ⊢
  linear_combination 24 * hθ + (2 * ((-1) * (e2_2 * e2_3) + 2 * (e2_2 * e2_6) + 2 * (e2_3 * e2_3)
    + (-5) * (e2_3 * e2_6) + 2 * (e2_6 * e2_6))) * h1 + (2 * ((-1) * (e2_1 * e2_3)
    + 2 * (e2_1 * e2_6) + 2 * (e2_2 * e2_3) + (-4) * (e2_2 * e2_6) + (e2_3 * e2_3)
    + (-4) * (e2_3 * e2_6) + 4 * (e2_6 * e2_6))) * h2 + (2 * ((-1) * (e2_1 * e2_2)
    + 4 * (e2_1 * e2_3) + (-5) * (e2_1 * e2_6) + (e2_2 * e2_2) + 2 * (e2_2 * e2_3)
    + (-4) * (e2_2 * e2_6) + 6 * (e2_3 * e2_3) + (-54) * (e2_3 * e2_6) + 75 * (e2_6 * e2_6))) * h3
    + (2 * (2 * (e2_1 * e2_2) + (-5) * (e2_1 * e2_3) + 4 * (e2_1 * e2_6) + (-2) * (e2_2 * e2_2)
    + (-4) * (e2_2 * e2_3) + 8 * (e2_2 * e2_6) + (-27) * (e2_3 * e2_3) + 150 * (e2_3 * e2_6)
    + (-174) * (e2_6 * e2_6))) * h4 + (12 * (8)) * h12

theorem clos9 (h : Ram6) :
    24 * theta (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-4) * (e2_1) + 16 * (e2_2)
        + (-12) * (e2_3)) * (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (8 * (e2_1) + (-8) * (e2_2)
        + (-24) * (e2_6)) * (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-12) * (e2_1) + (-36) * (e2_3)
        + 144 * (e2_6)) * (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + ((-24) * (e2_2) + 72 * (e2_3)
        + (-72) * (e2_6)) * (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (4 * (e2_1) + (-40) * (e2_2) + 60 * (e2_3)
        + 24 * (e2_6)) * (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = (2 * (e2_1) + (-8) * (e2_2) + 6 * (e2_3)) * theta e2_1 + ((-8) * (e2_1) + 8 * (e2_2)
        + 24 * (e2_6)) * theta e2_2 + (6 * (e2_1) + 18 * (e2_3) + (-72) * (e2_6)) * theta e2_3
        + (24 * (e2_2) + (-72) * (e2_3) + 72 * (e2_6)) * theta e2_6 := by
    simp only [Rf9, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ ⊢
  linear_combination 24 * hθ + (2 * (2 * (e2_1) + (-8) * (e2_2) + 6 * (e2_3))) * h1 + (2 * ((-8) * (e2_1)
    + 8 * (e2_2) + 24 * (e2_6))) * h2 + (2 * (6 * (e2_1) + 18 * (e2_3) + (-72) * (e2_6))) * h3
    + (2 * (24 * (e2_2) + (-72) * (e2_3) + 72 * (e2_6))) * h4

/-! ## The coefficient of `Xⁿ` in the closed system -/

theorem ceq1 (h : Ram6) (n : ℕ)
    (H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    : 24 * ((n : ℝ) * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = (-12) * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-60) * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 336 * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-96) * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-8) * PowerSeries.coeff n (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-60) * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  have hc := congrArg (PowerSeries.coeff n) (clos1 h)
  rw [coeff_ofNat_mul, coeff_theta] at hc
  simp only [map_add] at hc
  rw [coeff_mul_of_lower_zero _ _ n H1, coeff_mul_of_lower_zero _ _ n H2, coeff_mul_of_lower_zero _ _ n H3, coeff_mul_of_lower_zero _ _ n H4, coeff_mul_of_lower_zero _ _ n H5, coeff_mul_of_lower_zero _ _ n H9] at hc
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, cc_e2_1, cc_e2_2, cc_e2_3, cc_e2_6, cc_e4_1, cc_e4_2, cc_e4_3, cc_e4_6, cc_e6_1, cc_e6_2, cc_e6_3, cc_e6_6] at hc
  linear_combination hc

theorem ceq2 (h : Ram6) (n : ℕ)
    (H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    : 24 * ((n : ℝ) * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = 0 * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-24) * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 144 * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-24) * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-8) * PowerSeries.coeff n (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  have hc := congrArg (PowerSeries.coeff n) (clos2 h)
  rw [coeff_ofNat_mul, coeff_theta] at hc
  simp only [map_add] at hc
  rw [coeff_mul_of_lower_zero _ _ n H1, coeff_mul_of_lower_zero _ _ n H2, coeff_mul_of_lower_zero _ _ n H3, coeff_mul_of_lower_zero _ _ n H4, coeff_mul_of_lower_zero _ _ n H6, coeff_mul_of_lower_zero _ _ n H9] at hc
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, cc_e2_1, cc_e2_2, cc_e2_3, cc_e2_6, cc_e4_1, cc_e4_2, cc_e4_3, cc_e4_6, cc_e6_1, cc_e6_2, cc_e6_3, cc_e6_6] at hc
  linear_combination hc

theorem ceq3 (h : Ram6) (n : ℕ)
    (H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    : 24 * ((n : ℝ) * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = 0 * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 12 * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 12 * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-72) * PowerSeries.coeff n (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  have hc := congrArg (PowerSeries.coeff n) (clos3 h)
  rw [coeff_ofNat_mul, coeff_theta] at hc
  simp only [map_add] at hc
  rw [coeff_mul_of_lower_zero _ _ n H1, coeff_mul_of_lower_zero _ _ n H2, coeff_mul_of_lower_zero _ _ n H3, coeff_mul_of_lower_zero _ _ n H4, coeff_mul_of_lower_zero _ _ n H7, coeff_mul_of_lower_zero _ _ n H9] at hc
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, cc_e2_1, cc_e2_2, cc_e2_3, cc_e2_6, cc_e4_1, cc_e4_2, cc_e4_3, cc_e4_6, cc_e6_1, cc_e6_2, cc_e6_3, cc_e6_6] at hc
  linear_combination hc

theorem ceq4 (h : Ram6) (n : ℕ)
    (H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    : 24 * ((n : ℝ) * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = 0 * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-48) * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 96 * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-72) * PowerSeries.coeff n (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  have hc := congrArg (PowerSeries.coeff n) (clos4 h)
  rw [coeff_ofNat_mul, coeff_theta] at hc
  simp only [map_add] at hc
  rw [coeff_mul_of_lower_zero _ _ n H1, coeff_mul_of_lower_zero _ _ n H2, coeff_mul_of_lower_zero _ _ n H3, coeff_mul_of_lower_zero _ _ n H4, coeff_mul_of_lower_zero _ _ n H8, coeff_mul_of_lower_zero _ _ n H9] at hc
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, cc_e2_1, cc_e2_2, cc_e2_3, cc_e2_6, cc_e4_1, cc_e4_2, cc_e4_3, cc_e4_6, cc_e6_1, cc_e6_2, cc_e6_3, cc_e6_6] at hc
  linear_combination hc

theorem ceq5 (h : Ram6) (n : ℕ)
    (H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    : 24 * ((n : ℝ) * PowerSeries.coeff n (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = 18 * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 630 * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-2736) * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 720 * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 12 * PowerSeries.coeff n (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-990) * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  have hc := congrArg (PowerSeries.coeff n) (clos5 h)
  rw [coeff_ofNat_mul, coeff_theta] at hc
  simp only [map_add] at hc
  rw [coeff_mul_of_lower_zero _ _ n H1, coeff_mul_of_lower_zero _ _ n H2, coeff_mul_of_lower_zero _ _ n H3, coeff_mul_of_lower_zero _ _ n H4, coeff_mul_of_lower_zero _ _ n H5, coeff_mul_of_lower_zero _ _ n H9] at hc
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, cc_e2_1, cc_e2_2, cc_e2_3, cc_e2_6, cc_e4_1, cc_e4_2, cc_e4_3, cc_e4_6, cc_e6_1, cc_e6_2, cc_e6_3, cc_e6_6] at hc
  linear_combination hc

theorem ceq6 (h : Ram6) (n : ℕ)
    (H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    : 24 * ((n : ℝ) * PowerSeries.coeff n (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = 0 * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 72 * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-720) * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 216 * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 24 * PowerSeries.coeff n (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  have hc := congrArg (PowerSeries.coeff n) (clos6 h)
  rw [coeff_ofNat_mul, coeff_theta] at hc
  simp only [map_add] at hc
  rw [coeff_mul_of_lower_zero _ _ n H1, coeff_mul_of_lower_zero _ _ n H2, coeff_mul_of_lower_zero _ _ n H3, coeff_mul_of_lower_zero _ _ n H4, coeff_mul_of_lower_zero _ _ n H6, coeff_mul_of_lower_zero _ _ n H9] at hc
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, cc_e2_1, cc_e2_2, cc_e2_3, cc_e2_6, cc_e4_1, cc_e4_2, cc_e4_3, cc_e4_6, cc_e6_1, cc_e6_2, cc_e6_3, cc_e6_6] at hc
  linear_combination hc

theorem ceq7 (h : Ram6) (n : ℕ)
    (H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    : 24 * ((n : ℝ) * PowerSeries.coeff n (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = 0 * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-30) * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 6 * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 36 * PowerSeries.coeff n (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  have hc := congrArg (PowerSeries.coeff n) (clos7 h)
  rw [coeff_ofNat_mul, coeff_theta] at hc
  simp only [map_add] at hc
  rw [coeff_mul_of_lower_zero _ _ n H1, coeff_mul_of_lower_zero _ _ n H2, coeff_mul_of_lower_zero _ _ n H3, coeff_mul_of_lower_zero _ _ n H4, coeff_mul_of_lower_zero _ _ n H7, coeff_mul_of_lower_zero _ _ n H9] at hc
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, cc_e2_1, cc_e2_2, cc_e2_3, cc_e2_6, cc_e4_1, cc_e4_2, cc_e4_3, cc_e4_6, cc_e6_1, cc_e6_2, cc_e6_3, cc_e6_6] at hc
  linear_combination hc

theorem ceq8 (h : Ram6) (n : ℕ)
    (H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    : 24 * ((n : ℝ) * PowerSeries.coeff n (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = 0 * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-48) * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-48) * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 72 * PowerSeries.coeff n (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 0 * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  have hc := congrArg (PowerSeries.coeff n) (clos8 h)
  rw [coeff_ofNat_mul, coeff_theta] at hc
  simp only [map_add] at hc
  rw [coeff_mul_of_lower_zero _ _ n H1, coeff_mul_of_lower_zero _ _ n H2, coeff_mul_of_lower_zero _ _ n H3, coeff_mul_of_lower_zero _ _ n H4, coeff_mul_of_lower_zero _ _ n H8, coeff_mul_of_lower_zero _ _ n H9] at hc
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, cc_e2_1, cc_e2_2, cc_e2_3, cc_e2_6, cc_e4_1, cc_e4_2, cc_e4_3, cc_e4_6, cc_e6_1, cc_e6_2, cc_e6_3, cc_e6_6] at hc
  linear_combination hc

theorem ceq9 (h : Ram6) (n : ℕ)
    (H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    (H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0)
    : 24 * ((n : ℝ) * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = 0 * PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-24) * PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 96 * PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + (-24) * PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
        + 48 * PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) := by
  have hc := congrArg (PowerSeries.coeff n) (clos9 h)
  rw [coeff_ofNat_mul, coeff_theta] at hc
  simp only [map_add] at hc
  rw [coeff_mul_of_lower_zero _ _ n H1, coeff_mul_of_lower_zero _ _ n H2, coeff_mul_of_lower_zero _ _ n H3, coeff_mul_of_lower_zero _ _ n H4, coeff_mul_of_lower_zero _ _ n H9] at hc
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, cc_e2_1, cc_e2_2, cc_e2_3, cc_e2_6, cc_e4_1, cc_e4_2, cc_e4_3, cc_e4_6, cc_e6_1, cc_e6_2, cc_e6_3, cc_e6_6] at hc
  linear_combination hc

/-! ## The linear algebra: `n⁶ (n-2)(n-3)(n-6) r = 0` -/

theorem lin9 (n r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ) (hn : 7 ≤ n)
    (e1 : 24 * (n * r1) = (-12) * r1 + (-60) * r2 + 336 * r3 + (-96) * r4 + (-8) * r5 + (-60) * r9)
    (e2 : 24 * (n * r2) = 0 * r1 + (-24) * r2 + 144 * r3 + (-24) * r4 + (-8) * r6 + 0 * r9)
    (e3 : 24 * (n * r3) = 0 * r1 + 0 * r2 + 12 * r3 + 12 * r4 + (-72) * r7 + 0 * r9)
    (e4 : 24 * (n * r4) = 0 * r1 + 0 * r2 + (-48) * r3 + 96 * r4 + (-72) * r8 + 0 * r9)
    (e5 : 24 * (n * r5) = 18 * r1 + 630 * r2 + (-2736) * r3 + 720 * r4 + 12 * r5 + (-990) * r9)
    (e6 : 24 * (n * r6) = 0 * r1 + 72 * r2 + (-720) * r3 + 216 * r4 + 24 * r6 + 0 * r9)
    (e7 : 24 * (n * r7) = 0 * r1 + 0 * r2 + (-30) * r3 + 6 * r4 + 36 * r7 + 0 * r9)
    (e8 : 24 * (n * r8) = 0 * r1 + 0 * r2 + (-48) * r3 + (-48) * r4 + 72 * r8 + 0 * r9)
    (e9 : 24 * (n * r9) = 0 * r1 + (-24) * r2 + 96 * r3 + (-24) * r4 + 48 * r9)
    : r1 = 0 ∧ r2 = 0 ∧ r3 = 0 ∧ r4 = 0 ∧ r5 = 0 ∧ r6 = 0 ∧ r7 = 0 ∧ r8 = 0 ∧ r9 = 0 := by
  have hd : (0 : ℝ) < n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6 := by
    have e : n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6 = n ^ 6 * ((n - 2) * ((n - 3) * (n - 6))) := by ring
    rw [e]
    exact mul_pos (pow_pos (by linarith) 6) (mul_pos (by linarith) (mul_pos (by linarith) (by linarith)))
  have z1 : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r1 = 0 := by
    linear_combination ((1 * n ^ 8 + (-23 / 2) * n ^ 7 + (83 / 2) * n ^ 6 + (-54) * n ^ 5 + 18 * n ^ 4) / 24) * e1
      + (((-5 / 2) * n ^ 7 + 25 * n ^ 6 + (-135 / 2) * n ^ 5 + 45 * n ^ 4) / 24) * e2 + ((14 * n ^ 7
      + (-133) * n ^ 6 + 336 * n ^ 5 + (-252) * n ^ 4) / 24) * e3 + (((-4) * n ^ 7 + 32 * n ^ 6
      + (-84) * n ^ 5 + 72 * n ^ 4) / 24) * e4 + (((-1 / 3) * n ^ 7 + (11 / 3) * n ^ 6 + (-12) * n ^ 5
      + 12 * n ^ 4) / 24) * e5 + (((5 / 6) * n ^ 6 + (-15 / 2) * n ^ 5 + 15 * n ^ 4) / 24) * e6
      + (((-42) * n ^ 6 + 336 * n ^ 5 + (-504) * n ^ 4) / 24) * e7 + ((12 * n ^ 6 + (-60) * n ^ 5
      + 72 * n ^ 4) / 24) * e8 + (((-5 / 2) * n ^ 7 + (75 / 2) * n ^ 6 + (-180) * n ^ 5
      + 270 * n ^ 4) / 24) * e9
  have z2 : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r2 = 0 := by
    linear_combination ((1 * n ^ 8 + (-12) * n ^ 7 + 47 * n ^ 6 + (-72) * n ^ 5 + 36 * n ^ 4) / 24) * e2 + ((6 * n ^ 7
      + (-57) * n ^ 6 + 144 * n ^ 5 + (-108) * n ^ 4) / 24) * e3 + (((-1) * n ^ 7 + 8 * n ^ 6
      + (-21) * n ^ 5 + 18 * n ^ 4) / 24) * e4 + (((-1 / 3) * n ^ 7 + (11 / 3) * n ^ 6 + (-12) * n ^ 5
      + 12 * n ^ 4) / 24) * e6 + (((-18) * n ^ 6 + 144 * n ^ 5 + (-216) * n ^ 4) / 24) * e7
      + ((3 * n ^ 6 + (-15) * n ^ 5 + 18 * n ^ 4) / 24) * e8
  have z3 : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r3 = 0 := by
    linear_combination ((1 * n ^ 8 + (-21 / 2) * n ^ 7 + (67 / 2) * n ^ 6 + (-42) * n ^ 5 + 18 * n ^ 4) / 24) * e3
      + (((1 / 2) * n ^ 7 + (-4) * n ^ 6 + (21 / 2) * n ^ 5 + (-9) * n ^ 4) / 24) * e4
      + (((-3) * n ^ 7 + 27 * n ^ 6 + (-60) * n ^ 5 + 36 * n ^ 4) / 24) * e7 + (((-3 / 2) * n ^ 6
      + (15 / 2) * n ^ 5 + (-9) * n ^ 4) / 24) * e8
  have z4 : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r4 = 0 := by
    linear_combination (((-2) * n ^ 7 + 19 * n ^ 6 + (-48) * n ^ 5 + 36 * n ^ 4) / 24) * e3 + ((1 * n ^ 8
      + (-7) * n ^ 7 + 13 * n ^ 6 + 3 * n ^ 5 + (-18) * n ^ 4) / 24) * e4 + ((6 * n ^ 6
      + (-48) * n ^ 5 + 72 * n ^ 4) / 24) * e7 + (((-3) * n ^ 7 + 12 * n ^ 6 + (-3) * n ^ 5
      + (-18) * n ^ 4) / 24) * e8
  have z5 : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r5 = 0 := by
    linear_combination (((3 / 4) * n ^ 7 + (-33 / 4) * n ^ 6 + 27 * n ^ 5 + (-27) * n ^ 4) / 24) * e1
      + (((105 / 4) * n ^ 7 + (-525 / 2) * n ^ 6 + (2835 / 4) * n ^ 5 + (-945 / 2) * n ^ 4) / 24) * e2
      + (((-114) * n ^ 7 + 1083 * n ^ 6 + (-2736) * n ^ 5 + 2052 * n ^ 4) / 24) * e3 + ((30 * n ^ 7
      + (-240) * n ^ 6 + 630 * n ^ 5 + (-540) * n ^ 4) / 24) * e4 + ((1 * n ^ 8 + (-21 / 2) * n ^ 7
      + (61 / 2) * n ^ 6 + (-18) * n ^ 5 + (-18) * n ^ 4) / 24) * e5 + (((-35 / 4) * n ^ 6
      + (315 / 4) * n ^ 5 + (-315 / 2) * n ^ 4) / 24) * e6 + ((342 * n ^ 6 + (-2736) * n ^ 5
      + 4104 * n ^ 4) / 24) * e7 + (((-90) * n ^ 6 + 450 * n ^ 5 + (-540) * n ^ 4) / 24) * e8
      + (((-165 / 4) * n ^ 7 + (1395 / 4) * n ^ 6 + (-540) * n ^ 5 + (-405) * n ^ 4) / 24) * e9
  have z6 : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r6 = 0 := by
    linear_combination ((3 * n ^ 7 + (-33) * n ^ 6 + 108 * n ^ 5 + (-108) * n ^ 4) / 24) * e2 + (((-30) * n ^ 7
      + 285 * n ^ 6 + (-720) * n ^ 5 + 540 * n ^ 4) / 24) * e3 + ((9 * n ^ 7 + (-72) * n ^ 6
      + 189 * n ^ 5 + (-162) * n ^ 4) / 24) * e4 + ((1 * n ^ 8 + (-10) * n ^ 7 + 25 * n ^ 6
      + (-36) * n ^ 4) / 24) * e6 + ((90 * n ^ 6 + (-720) * n ^ 5 + 1080 * n ^ 4) / 24) * e7
      + (((-27) * n ^ 6 + 135 * n ^ 5 + (-162) * n ^ 4) / 24) * e8
  have z7 : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r7 = 0 := by
    linear_combination (((-5 / 4) * n ^ 7 + (43 / 4) * n ^ 6 + (-21) * n ^ 5 + 9 * n ^ 4) / 24) * e3
      + (((1 / 4) * n ^ 7 + (-2) * n ^ 6 + (21 / 4) * n ^ 5 + (-9 / 2) * n ^ 4) / 24) * e4
      + ((1 * n ^ 8 + (-19 / 2) * n ^ 7 + (51 / 2) * n ^ 6 + (-30) * n ^ 5 + 18 * n ^ 4) / 24) * e7
      + (((-3 / 4) * n ^ 6 + (15 / 4) * n ^ 5 + (-9 / 2) * n ^ 4) / 24) * e8
  have z8 : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r8 = 0 := by
    linear_combination (((-2) * n ^ 7 + 19 * n ^ 6 + (-48) * n ^ 5 + 36 * n ^ 4) / 24) * e3 + (((-2) * n ^ 7
      + 7 * n ^ 6 + 3 * n ^ 5 + (-18) * n ^ 4) / 24) * e4 + ((6 * n ^ 6 + (-48) * n ^ 5
      + 72 * n ^ 4) / 24) * e7 + ((1 * n ^ 8 + (-8) * n ^ 7 + 18 * n ^ 6 + (-3) * n ^ 5
      + (-18) * n ^ 4) / 24) * e8
  have z9 : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r9 = 0 := by
    linear_combination (((-1) * n ^ 7 + 10 * n ^ 6 + (-27) * n ^ 5 + 18 * n ^ 4) / 24) * e2 + ((4 * n ^ 7
      + (-38) * n ^ 6 + 96 * n ^ 5 + (-72) * n ^ 4) / 24) * e3 + (((-1) * n ^ 7 + 8 * n ^ 6
      + (-21) * n ^ 5 + 18 * n ^ 4) / 24) * e4 + (((1 / 3) * n ^ 6 + (-3) * n ^ 5
      + 6 * n ^ 4) / 24) * e6 + (((-12) * n ^ 6 + 96 * n ^ 5 + (-144) * n ^ 4) / 24) * e7
      + ((3 * n ^ 6 + (-15) * n ^ 5 + 18 * n ^ 4) / 24) * e8 + ((1 * n ^ 8 + (-9) * n ^ 7
      + 18 * n ^ 6) / 24) * e9
  exact ⟨(mul_eq_zero.mp z1).resolve_left hd.ne', (mul_eq_zero.mp z2).resolve_left hd.ne', (mul_eq_zero.mp z3).resolve_left hd.ne', (mul_eq_zero.mp z4).resolve_left hd.ne', (mul_eq_zero.mp z5).resolve_left hd.ne', (mul_eq_zero.mp z6).resolve_left hd.ne', (mul_eq_zero.mp z7).resolve_left hd.ne', (mul_eq_zero.mp z8).resolve_left hd.ne', (mul_eq_zero.mp z9).resolve_left hd.ne'⟩

/-! ## The relations -/

theorem rel_all_zero (h : Ram6) (n : ℕ) :
    PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0
      ∧ PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0
      ∧ PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0
      ∧ PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0
      ∧ PowerSeries.coeff n (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0
      ∧ PowerSeries.coeff n (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0
      ∧ PowerSeries.coeff n (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0
      ∧ PowerSeries.coeff n (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0
      ∧ PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 7 with hn | hn
    · exact ⟨coeff_eq_zero_of_dvd7 dvd7_Rf1 hn, coeff_eq_zero_of_dvd7 dvd7_Rf2 hn, coeff_eq_zero_of_dvd7 dvd7_Rf3 hn, coeff_eq_zero_of_dvd7 dvd7_Rf4 hn, coeff_eq_zero_of_dvd7 dvd7_Rf5 hn, coeff_eq_zero_of_dvd7 dvd7_Rf6 hn, coeff_eq_zero_of_dvd7 dvd7_Rf7 hn, coeff_eq_zero_of_dvd7 dvd7_Rf8 hn, coeff_eq_zero_of_dvd7 dvd7_Rf9 hn⟩
    · have H1 : ∀ m < n, PowerSeries.coeff m (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := fun m hm => (ih m hm).1
      have H2 : ∀ m < n, PowerSeries.coeff m (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := fun m hm => (ih m hm).2.1
      have H3 : ∀ m < n, PowerSeries.coeff m (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := fun m hm => (ih m hm).2.2.1
      have H4 : ∀ m < n, PowerSeries.coeff m (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := fun m hm => (ih m hm).2.2.2.1
      have H5 : ∀ m < n, PowerSeries.coeff m (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := fun m hm => (ih m hm).2.2.2.2.1
      have H6 : ∀ m < n, PowerSeries.coeff m (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := fun m hm => (ih m hm).2.2.2.2.2.1
      have H7 : ∀ m < n, PowerSeries.coeff m (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := fun m hm => (ih m hm).2.2.2.2.2.2.1
      have H8 : ∀ m < n, PowerSeries.coeff m (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := fun m hm => (ih m hm).2.2.2.2.2.2.2.1
      have H9 : ∀ m < n, PowerSeries.coeff m (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6) = 0 := fun m hm => (ih m hm).2.2.2.2.2.2.2.2
      have hn' : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact lin9 (n : ℝ) (PowerSeries.coeff n (Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) (PowerSeries.coeff n (Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) (PowerSeries.coeff n (Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) (PowerSeries.coeff n (Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) (PowerSeries.coeff n (Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) (PowerSeries.coeff n (Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) (PowerSeries.coeff n (Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) (PowerSeries.coeff n (Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) (PowerSeries.coeff n (Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) hn'
        (ceq1 h n H1 H2 H3 H4 H5 H6 H7 H8 H9)
        (ceq2 h n H1 H2 H3 H4 H5 H6 H7 H8 H9)
        (ceq3 h n H1 H2 H3 H4 H5 H6 H7 H8 H9)
        (ceq4 h n H1 H2 H3 H4 H5 H6 H7 H8 H9)
        (ceq5 h n H1 H2 H3 H4 H5 H6 H7 H8 H9)
        (ceq6 h n H1 H2 H3 H4 H5 H6 H7 H8 H9)
        (ceq7 h n H1 H2 H3 H4 H5 H6 H7 H8 H9)
        (ceq8 h n H1 H2 H3 H4 H5 H6 H7 H8 H9)
        (ceq9 h n H1 H2 H3 H4 H5 H6 H7 H8 H9)

theorem Rf1_eq_zero (h : Ram6) : Rf1 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 = 0 := by
  ext n
  rw [(rel_all_zero h n).1, map_zero]

theorem Rf2_eq_zero (h : Ram6) : Rf2 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 = 0 := by
  ext n
  rw [(rel_all_zero h n).2.1, map_zero]

theorem Rf3_eq_zero (h : Ram6) : Rf3 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 = 0 := by
  ext n
  rw [(rel_all_zero h n).2.2.1, map_zero]

theorem Rf4_eq_zero (h : Ram6) : Rf4 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 = 0 := by
  ext n
  rw [(rel_all_zero h n).2.2.2.1, map_zero]

theorem Rf5_eq_zero (h : Ram6) : Rf5 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 = 0 := by
  ext n
  rw [(rel_all_zero h n).2.2.2.2.1, map_zero]

theorem Rf6_eq_zero (h : Ram6) : Rf6 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 = 0 := by
  ext n
  rw [(rel_all_zero h n).2.2.2.2.2.1, map_zero]

theorem Rf7_eq_zero (h : Ram6) : Rf7 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 = 0 := by
  ext n
  rw [(rel_all_zero h n).2.2.2.2.2.2.1, map_zero]

theorem Rf8_eq_zero (h : Ram6) : Rf8 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 = 0 := by
  ext n
  rw [(rel_all_zero h n).2.2.2.2.2.2.2.1, map_zero]

theorem Rf9_eq_zero (h : Ram6) : Rf9 e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6 = 0 := by
  ext n
  rw [(rel_all_zero h n).2.2.2.2.2.2.2.2, map_zero]

/-! ## The generating series of `psiW` satisfies `12 θΓ = (E₂(q) + 2E₂(q²) + 3E₂(q³) + 6E₂(q⁶)) Γ` -/

/-- `25920 ∑ psiW(n) Xⁿ` as a polynomial in the twelve series. -/
noncomputable def Gamf (x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ) : PowerSeries ℝ :=
  (-25) * (x1 * x1) + 100 * (x1 * x2) + 1350 * (x1 * x3) + (-2700) * (x1 * x6)
    + (-100) * (x2 * x2) + (-2700) * (x2 * x3) + 5400 * (x2 * x6) + (-18225) * (x3 * x3)
    + 72900 * (x3 * x6) + (-72900) * (x6 * x6) + (-22) * (u1) + (-88) * (u2) + 3402 * (u3)
    + 13608 * (u6)

theorem thetaGam_scaled (h : Ram6) :
    1 * (12 * theta (Gamf e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6))
      = 1 * ((e2_1 + 2 * e2_2 + 3 * e2_3 + 6 * e2_6) * (Gamf e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)) := by
  have r1 := Rf1_eq_zero h
  have r2 := Rf2_eq_zero h
  have r3 := Rf3_eq_zero h
  have r4 := Rf4_eq_zero h
  have r5 := Rf5_eq_zero h
  have r6 := Rf6_eq_zero h
  have r7 := Rf7_eq_zero h
  have r8 := Rf8_eq_zero h
  have r9 := Rf9_eq_zero h
  unfold Ram6 at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hθ : theta (Gamf e2_1 e2_2 e2_3 e2_6 e4_1 e4_2 e4_3 e4_6 e6_1 e6_2 e6_3 e6_6)
      = ((-50) * (e2_1) + 100 * (e2_2) + 1350 * (e2_3) + (-2700) * (e2_6)) * theta e2_1 + (100 * (e2_1)
        + (-200) * (e2_2) + (-2700) * (e2_3) + 5400 * (e2_6)) * theta e2_2 + (1350 * (e2_1)
        + (-2700) * (e2_2) + (-36450) * (e2_3) + 72900 * (e2_6)) * theta e2_3 + ((-2700) * (e2_1)
        + 5400 * (e2_2) + 72900 * (e2_3) + (-145800) * (e2_6)) * theta e2_6 + ((-22)) * theta e4_1
        + ((-88)) * theta e4_2 + (3402) * theta e4_3 + (13608) * theta e4_6 := by
    simp only [Gamf, theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one]
    ring
  simp only [Gamf, Rf1, Rf2, Rf3, Rf4, Rf5, Rf6, Rf7, Rf8, Rf9] at hθ r1 r2 r3 r4 r5 r6 r7 r8 r9 ⊢
  linear_combination (1 * 12) * hθ + (1 * ((-50) * (e2_1) + 100 * (e2_2) + 1350 * (e2_3) + (-2700) * (e2_6))) * h1
    + (1 * (100 * (e2_1) + (-200) * (e2_2) + (-2700) * (e2_3) + 5400 * (e2_6))) * h2
    + (1 * (1350 * (e2_1) + (-2700) * (e2_2) + (-36450) * (e2_3) + 72900 * (e2_6))) * h3
    + (1 * ((-2700) * (e2_1) + 5400 * (e2_2) + 72900 * (e2_3) + (-145800) * (e2_6))) * h4
    + (4 * ((-22))) * h5 + (4 * ((-88))) * h6 + (4 * (3402)) * h7 + (4 * (13608)) * h8
    + ((-16) * (e2_1) + (-56) * (e2_2) + (-1284) * (e2_3) + 2832 * (e2_6)) * r1 + ((-28) * (e2_1)
    + (-32) * (e2_2) + 1416 * (e2_3) + (-2568) * (e2_6)) * r2 + ((-2484) * (e2_1) + 432 * (e2_2)
    + 46656 * (e2_3) + (-79704) * (e2_6)) * r3 + (216 * (e2_1) + (-4968) * (e2_2)
    + (-39852) * (e2_3) + 93312 * (e2_6)) * r4 + (88) * r5 + (88) * r6 + ((-40824)) * r7
    + ((-40824)) * r8 + ((-25) * (e2_1) + (-3206) * (e2_2) + 6177 * (e2_3) + (-2586) * (e2_6)) * r9

end Tower.RV6
