#!/usr/bin/env python3
"""Writes Tower/RV6/Level6.lean from the certificates computed by rv6_114a.py.

usage: gen_level6.py <certificates.json> <outfile>

The certificates are polynomials with rational coefficients (the nine relations among
E2, E4, E6 at q, q^2, q^3, q^6, the matrix of their closed system under theta, its adjugate,
truncations at X^7).  This script only prints them as Lean terms; Lean checks every identity.
"""
import sys, json
from fractions import Fraction as Fr

cert = json.load(open(sys.argv[1]))
out = []
def w(s=""): out.append(s)

D = [1, 2, 3, 6]
ATOMS = ["e2_1", "e2_2", "e2_3", "e2_6", "e4_1", "e4_2", "e4_3", "e4_6", "e6_1", "e6_2", "e6_3", "e6_6"]
PATOMS = ["p" + a for a in ATOMS]
VARS = ["x1", "x2", "x3", "x6", "u1", "u2", "u3", "u6", "v1", "v2", "v3", "v6"]
RN = ["Rf1", "Rf2", "Rf3", "Rf4", "Rf5", "Rf6", "Rf7", "Rf8", "Rf9"]
NEHD = {2: "two_ne", 3: "three_ne", 6: "six_ne"}

def dec(p):
    return {tuple(m): Fr(c) for m, c in p}

def num(c, real=False):
    c = Fr(c)
    if c.denominator == 1:
        return str(c.numerator) if c >= 0 else "(%d)" % c.numerator
    assert real
    return "(%d / %d)" % (c.numerator, c.denominator)

def mono(m, names):
    f = []
    for i, e in enumerate(m):
        f += [names[i]] * e
    return " * ".join(f)

def poly(p, names, real=False):
    """Lean term for a polynomial {exponents: coefficient}."""
    if not p:
        return "0"
    ts = []
    for m, c in sorted(p.items(), reverse=True):
        mm = mono(m, names)
        if not mm:
            ts.append(num(c, real))
        elif c == 1:
            ts.append(mm if " * " not in mm else "(" + mm + ")")
        else:
            ts.append("%s * (%s)" % (num(c, real), mm))
    return " + ".join(ts)

def is_int(p):
    return all(Fr(c).denominator == 1 for c in p.values())

def xpoly(cs, var="T"):
    """Lean term for a polynomial in T given by its integer coefficient list."""
    ts = []
    for k, c in enumerate(cs):
        c = Fr(c)
        if c == 0:
            continue
        ts.append(num(c) if k == 0 else "%s * %s ^ %d" % (num(c), var, k))
    return " + ".join(ts) if ts else "0"

def p7(cs):
    cs = list(cs) + [0] * (7 - len(cs))
    return "P7 " + " ".join(num(c) for c in cs[:7])

def wrap(s, ind, width=96):
    """break a long sum at ' + ' """
    parts = s.split(" + ")
    lines, cur = [], ""
    for i, t in enumerate(parts):
        piece = t if i == 0 else "+ " + t
        if cur and len(cur) + len(piece) + 1 > width:
            lines.append(cur); cur = piece
        else:
            cur = piece if not cur else cur + " " + piece
    lines.append(cur)
    return ("\n" + " " * ind).join(lines)

R = [dec(p) for p in cert["R"]]
Mt = [[dec(q) for q in row] for row in cert["Mt"]]
M0 = cert["M0"]
L = cert["L"]
dR = [[dec(q) for q in row] for row in cert["dR"]]
Gam = dec(cert["Gam"]); dGam = [dec(q) for q in cert["dGam"]]
Zc = [dec(q) for q in cert["Zc"]]
assert all(is_int(p) for p in R) and all(is_int(q) for row in Mt for q in row) and L == 24

ARGS = " ".join(ATOMS); PARGS = " ".join(PATOMS)
BIND = "(" + " ".join(VARS) + " : PowerSeries ℝ)"
REL = [nm + " " + ARGS for nm in RN]          # the nine series

w("import Mathlib")
w("import Tower.RV6.Psi")
w("import Tower.RV6.QSeries")
w("import Tower.RV6.Ser")
w("")
w("/-!")
w("# The Eisenstein series of level six as power series: nine relations")
w("")
w("`e2_d, e4_d, e6_d` are `E₂, E₄, E₆` at `q^d` for `d ∣ 6`, as formal power series (`E₆` is defined")
w("as `E₂ E₄ - 3 θE₄`).  Under Ramanujan's identities (`Ram6`, a hypothesis in this file) nine")
w("polynomial relations hold among them: one quadratic relation among the four `e2_d`, and each")
w("`e4_d`, `e6_d` is a polynomial in the `e2`'s.")
w("")
w("The proof does not use modular forms.  The nine differences `R` satisfy `24 θR = M R` with a")
w("matrix `M` of polynomials (`clos1 … clos9`, each a polynomial identity); the matrix at `X = 0`")
w("has characteristic polynomial `n⁶ (n-2)(n-3)(n-6)` (`lin9`); and `R` vanishes modulo `X⁷`")
w("(`dvd7_Rf1 …`), by explicit truncations.  Hence `R = 0` (`rel_all_zero`).")
w("")
w("This file is written by `tools/gen_level6.py` from certificates computed in exact arithmetic;")
w("every identity is checked here by `ring`.")
w("-/")
w("")
w("namespace Tower.RV6")
w("")
w("open PowerSeries")
w("")
w("set_option maxHeartbeats 1600000")
w("")
w("local notation \"T\" => (PowerSeries.X : PowerSeries ℝ)")
w("")
w("theorem two_ne : (2 : ℕ) ≠ 0 := by norm_num")
w("theorem three_ne : (3 : ℕ) ≠ 0 := by norm_num")
w("theorem six_ne : (6 : ℕ) ≠ 0 := by norm_num")
w("")
w("/-! ## The series -/")
w("")
w("/-- `∑ σ₁(n) Xⁿ`. -/")
w("noncomputable def S1 : PowerSeries ℝ := PowerSeries.mk (sig 1)")
w("/-- `∑ σ₃(n) Xⁿ`. -/")
w("noncomputable def S3 : PowerSeries ℝ := PowerSeries.mk (sig 3)")
w("/-- `E₂ = 1 - 24 ∑ σ₁(n) Xⁿ`. -/")
w("noncomputable def xE : PowerSeries ℝ := 1 - 24 * S1")
w("/-- `E₄ = 1 + 240 ∑ σ₃(n) Xⁿ`. -/")
w("noncomputable def uE : PowerSeries ℝ := 1 + 240 * S3")
w("/-- `E₆`, defined as `E₂ E₄ - 3 θE₄`. -/")
w("noncomputable def vE : PowerSeries ℝ := xE * uE - 3 * theta uE")
for nm, base in (("e2", "xE"), ("e4", "uE"), ("e6", "vE")):
    w("noncomputable def %s_1 : PowerSeries ℝ := %s" % (nm, base))
    for d in (2, 3, 6):
        w("noncomputable def %s_%d : PowerSeries ℝ := PowerSeries.expand %d %s %s" % (nm, d, d, NEHD[d], base))
w("")
w("/-- Ramanujan's identities at `q, q², q³, q⁶`, in integer form. -/")
w("def Ram6 : Prop :=")
conj = []
for d in D:
    conj.append("(12 * theta e2_%d = %d * (e2_%d * e2_%d - e4_%d))" % (d, d, d, d, d))
for d in D:
    conj.append("(3 * theta e4_%d = %d * (e2_%d * e4_%d - e6_%d))" % (d, d, d, d, d))
for d in D:
    conj.append("(2 * theta e6_%d = %d * (e2_%d * e6_%d - e4_%d * e4_%d))" % (d, d, d, d, d, d))
w("  " + "\n    ∧ ".join(conj))
w("")
w("theorem ode4_base : 3 * theta uE = xE * uE - vE := by")
w("  unfold vE")
w("  ring")
w("")
for (nm, c, lhs, rhs, hyp) in (
        ("ode2_expand", 12, "xE", "PowerSeries.expand d hd xE * PowerSeries.expand d hd xE - PowerSeries.expand d hd uE", "(h : 12 * theta xE = xE * xE - uE)"),
        ("ode4_expand", 3, "uE", "PowerSeries.expand d hd xE * PowerSeries.expand d hd uE - PowerSeries.expand d hd vE", "(h : 3 * theta uE = xE * uE - vE)"),
        ("ode6_expand", 2, "vE", "PowerSeries.expand d hd xE * PowerSeries.expand d hd vE - PowerSeries.expand d hd uE * PowerSeries.expand d hd uE", "(h : 2 * theta vE = xE * vE - uE * uE)")):
    w("theorem %s (d : ℕ) (hd : d ≠ 0) %s :" % (nm, hyp))
    w("    %d * theta (PowerSeries.expand d hd %s)" % (c, lhs))
    w("      = (d : PowerSeries ℝ) * (%s) := by" % rhs)
    w("  have h' := congrArg (fun t => PowerSeries.expand d hd t) h")
    w("  simp only [map_mul, map_sub, map_ofNat] at h'")
    w("  rw [theta_expand]")
    w("  linear_combination (d : PowerSeries ℝ) * h'")
    w("")
w("/-- Ramanujan's identities at `q` give them at `q², q³, q⁶`. -/")
w("theorem ram6_of_base (h2 : 12 * theta xE = xE * xE - uE) (h6 : 2 * theta vE = xE * vE - uE * uE) :")
w("    Ram6 := by")
w("  have h4 := ode4_base")
for d in (2, 3, 6):
    for k, hh in ((2, "h2"), (4, "h4"), (6, "h6")):
        w("  have a%d_%d := ode%d_expand %d %s %s" % (k, d, k, d, NEHD[d], hh))
        w("  simp only [Nat.cast_ofNat] at a%d_%d" % (k, d))
w("  unfold Ram6")
w("  refine ⟨?_, a2_2, a2_3, a2_6, ?_, a4_2, a4_3, a4_6, ?_, a6_2, a6_3, a6_6⟩")
w("  · show 12 * theta xE = 1 * (xE * xE - uE)")
w("    linear_combination h2")
w("  · show 3 * theta uE = 1 * (xE * uE - vE)")
w("    linear_combination h4")
w("  · show 2 * theta vE = 1 * (xE * vE - uE * uE)")
w("    linear_combination h6")
w("")
w("/-! ## Constant terms -/")
w("")
w("theorem constantCoeff_theta (φ : PowerSeries ℝ) : PowerSeries.constantCoeff (theta φ) = 0 := by")
w("  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_theta, Nat.cast_zero, zero_mul]")
w("")
w("theorem cc_xE : PowerSeries.constantCoeff xE = 1 := by")
w("  simp only [xE, S1, map_sub, map_mul, map_one, map_ofNat, PowerSeries.constantCoeff_mk, sig_zero]")
w("  norm_num")
w("")
w("theorem cc_uE : PowerSeries.constantCoeff uE = 1 := by")
w("  simp only [uE, S3, map_add, map_mul, map_one, map_ofNat, PowerSeries.constantCoeff_mk, sig_zero]")
w("  norm_num")
w("")
w("theorem cc_vE : PowerSeries.constantCoeff vE = 1 := by")
w("  simp only [vE, map_sub, map_mul, map_ofNat, cc_xE, cc_uE, constantCoeff_theta]")
w("  norm_num")
w("")
for nm, base in (("e2", "xE"), ("e4", "uE"), ("e6", "vE")):
    w("theorem cc_%s_1 : PowerSeries.constantCoeff %s_1 = 1 := cc_%s" % (nm, nm, base))
    for d in (2, 3, 6):
        w("theorem cc_%s_%d : PowerSeries.constantCoeff %s_%d = 1 := by" % (nm, d, nm, d))
        w("  unfold %s_%d" % (nm, d))
        w("  rw [PowerSeries.constantCoeff_expand, cc_%s]" % base)
w("")
CCS = ", ".join("cc_" + a for a in ATOMS)

w("/-! ## Truncations at `X⁷` -/")
w("")
q1, q3, tq3 = cert["q1"], cert["q3"], cert["tq3"]
px, pu, pv, Ev = cert["px"], cert["pu"], cert["pv"], cert["Ev"]
w("noncomputable def q1 : PowerSeries ℝ := %s" % p7(q1))
w("noncomputable def q3 : PowerSeries ℝ := %s" % p7(q3))
w("noncomputable def tq3 : PowerSeries ℝ := %s" % p7(tq3))
w("noncomputable def pxE : PowerSeries ℝ := %s" % p7(px))
w("noncomputable def puE : PowerSeries ℝ := %s" % p7(pu))
w("noncomputable def pvE : PowerSeries ℝ := %s" % p7(pv))
for a in ATOMS:
    w("noncomputable def p%s : PowerSeries ℝ := %s" % (a, p7(cert["tr"][{"e2": "x", "e4": "u", "e6": "v"}[a[:2]] + a[3:]])))
w("")
PROJ = [".1", ".2.1", ".2.2.1", ".2.2.2.1", ".2.2.2.2.1", ".2.2.2.2.2.1", ".2.2.2.2.2.2"]
for nm, k, vals, cs in (("S1", 1, "sig1_vals", q1), ("S3", 3, "sig3_vals", q3)):
    w("theorem dvd_%s : T ^ 7 ∣ %s - q%d := by" % (nm, nm, k))
    w("  exact dvd7_sub_P7 %s %s" % (nm, " ".join(num(c) for c in cs)))
    for j in range(7):
        w("    ((PowerSeries.coeff_mk %d (sig %d)).trans %s%s)" % (j, k, vals, PROJ[j]))
    w("")
w("theorem dvd_tS3 : T ^ 7 ∣ theta S3 - tq3 := by")
w("  have c : ∀ k : ℕ, PowerSeries.coeff k (theta S3) = (k : ℝ) * sig 3 k := fun k => by")
w("    rw [coeff_theta]")
w("    exact congrArg (fun t => (k : ℝ) * t) (PowerSeries.coeff_mk k (sig 3))")
w("  refine dvd7_sub_P7 (theta S3) %s ?_ ?_ ?_ ?_ ?_ ?_ ?_" % " ".join(num(c) for c in tq3))
for j in range(7):
    w("  · rw [c %d, sig3_vals%s]; norm_num" % (j, PROJ[j]))
w("")
UNF = "P7, map_ofNat, map_neg, map_one, map_zero"
w("theorem dvd_xE : T ^ 7 ∣ xE - pxE := by")
w("  have e : xE - pxE = (-24) * (S1 - q1) := by")
w("    simp only [xE, pxE, q1, %s]" % UNF)
w("    ring")
w("  rw [e]")
w("  exact Dvd.dvd.mul_left dvd_S1 _")
w("")
w("theorem dvd_uE : T ^ 7 ∣ uE - puE := by")
w("  have e : uE - puE = 240 * (S3 - q3) := by")
w("    simp only [uE, puE, q3, %s]" % UNF)
w("    ring")
w("  rw [e]")
w("  exact Dvd.dvd.mul_left dvd_S3 _")
w("")
w("theorem theta_uE : theta uE = 240 * theta S3 := by")
w("  unfold uE")
w("  rw [theta_add, theta_one, theta_mul, theta_ofNat]")
w("  ring")
w("")
w("theorem pi7_vE : pi7 vE = pi7 pvE := by")
w("  have hx := pi7_eq_of_dvd dvd_xE")
w("  have hu := pi7_eq_of_dvd dvd_uE")
w("  have ht := pi7_eq_of_dvd dvd_tS3")
w("  have e : pxE * puE - 3 * (240 * tq3) = pvE + T ^ 7 * (%s) := by" % xpoly(Ev))
w("    simp only [pxE, puE, tq3, pvE, %s]" % UNF)
w("    ring")
w("  have e1 : pi7 vE = pi7 (pxE * puE - 3 * (240 * tq3)) := by")
w("    simp only [vE, theta_uE, map_sub, map_mul, map_ofNat, hx, hu, ht]")
w("  rw [e1, e, map_add, pi7_X_pow_mul, add_zero]")
w("")
w("theorem dvd_vE : T ^ 7 ∣ vE - pvE := by")
w("  apply dvd7_of_pi7_eq_zero")
w("  rw [map_sub, pi7_vE, sub_self]")
w("")
for nm, base, key in (("e2", "xE", "x"), ("e4", "uE", "u"), ("e6", "vE", "v")):
    w("theorem pi7_%s_1 : pi7 %s_1 = pi7 p%s_1 := by" % (nm, nm, nm))
    w("  have e : p%s_1 = p%s := rfl" % (nm, base))
    w("  rw [e]")
    w("  exact pi7_eq_of_dvd dvd_%s" % base)
    w("")
    for d in (2, 3, 6):
        quo = cert["quo"][key + str(d)]
        w("theorem pi7_%s_%d : pi7 %s_%d = pi7 p%s_%d := by" % (nm, d, nm, d, nm, d))
        w("  have h1 : pi7 %s_%d = pi7 (PowerSeries.expand %d %s p%s) :=" % (nm, d, d, NEHD[d], base))
        w("    pi7_eq_of_dvd (dvd7_expand %d %s dvd_%s)" % (d, NEHD[d], base))
        w("  have e : PowerSeries.expand %d %s p%s = p%s_%d + T ^ 7 * (%s) := by" % (d, NEHD[d], base, nm, d, wrap(xpoly(quo), 10)))
        w("    simp only [p%s, p%s_%d, P7, map_add, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X," % (base, nm, d))
        w("      map_ofNat, map_neg, map_one, map_zero]")
        w("    ring")
        w("  rw [h1, e, map_add, pi7_X_pow_mul, add_zero]")
        w("")
PI7S = ", ".join("pi7_" + a for a in ATOMS)

w("/-! ## The nine relations -/")
w("")
DOC = ["`E₄(q) - U₁`", "`4 E₄(q²) - U₂`", "`3 E₄(q³) - U₃`", "`12 E₄(q⁶) - U₆`",
       "`E₆(q) - V₁`", "`8 E₆(q²) - V₂`", "`E₆(q³) - V₃`", "`8 E₆(q⁶) - V₆`", "the quadratic relation `ρ`"]
for i in range(9):
    w("/-- %s as a polynomial in the twelve series. -/" % DOC[i])
    w("noncomputable def %s %s : PowerSeries ℝ :=" % (RN[i], BIND))
    w("  " + wrap(poly(R[i], VARS), 4))
    w("")
RFS = ", ".join(RN)
for i in range(9):
    sq = [Fr(c) for c in cert["Squo"][i]]
    w("theorem dvd7_%s : T ^ 7 ∣ %s := by" % (RN[i], REL[i]))
    w("  have key : pi7 (%s) = pi7 (%s %s) := by" % (REL[i], RN[i], PARGS))
    w("    simp only [%s, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, %s]" % (RN[i], PI7S))
    w("  have hR : %s %s = T ^ 7 * (%s) := by" % (RN[i], PARGS, wrap(xpoly(sq), 8)))
    w("    simp only [%s, %s, P7, map_ofNat, map_neg, map_one, map_zero]" % (RN[i], ", ".join(PATOMS)))
    w("    ring")
    w("  apply dvd7_of_pi7_eq_zero")
    w("  rw [key, hR]")
    w("  exact pi7_X_pow_mul _")
    w("")

w("/-! ## The closed system `24 θR = M R` -/")
w("")
OBT = "⟨" + ", ".join("h%d" % k for k in range(1, 13)) + "⟩"
CS = [2] * 4 + [8] * 4 + [12] * 4
THS = "theta_add, theta_sub, theta_mul, theta_neg, theta_ofNat, theta_one"
for i in range(9):
    rhs = " + ".join("(%s) * (%s)" % (poly(Mt[i][j], ATOMS), REL[j]) for j in range(9) if Mt[i][j])
    w("theorem clos%d (h : Ram6) :" % (i + 1))
    w("    24 * theta (%s)" % REL[i])
    w("      = " + wrap(rhs, 8) + " := by")
    w("  unfold Ram6 at h")
    w("  obtain %s := h" % OBT)
    dsum = " + ".join("(%s) * theta %s" % (poly(dR[i][s], ATOMS), ATOMS[s]) for s in range(12) if dR[i][s])
    w("  have hθ : theta (%s)" % REL[i])
    w("      = " + wrap(dsum, 8) + " := by")
    w("    simp only [%s, %s]" % (RN[i], THS))
    w("    ring")
    w("  simp only [%s] at hθ ⊢" % RFS)
    lc = ["24 * hθ"] + ["(%d * (%s)) * h%d" % (CS[s], poly(dR[i][s], ATOMS), s + 1) for s in range(12) if dR[i][s]]
    w("  linear_combination " + wrap(" + ".join(lc), 4))
    w("")

w("/-! ## The coefficient of `Xⁿ` in the closed system -/")
w("")
HYP = " ".join("(H%d : ∀ m < n, PowerSeries.coeff m (%s) = 0)" % (j + 1, REL[j]) for j in range(9))
for i in range(9):
    js = [j for j in range(9) if Mt[i][j]]
    rhs = " + ".join("%s * PowerSeries.coeff n (%s)" % (num(M0[i][j]), REL[j]) for j in js)
    w("theorem ceq%d (h : Ram6) (n : ℕ)" % (i + 1))
    for j in range(9):
        w("    (H%d : ∀ m < n, PowerSeries.coeff m (%s) = 0)" % (j + 1, REL[j]))
    w("    : 24 * ((n : ℝ) * PowerSeries.coeff n (%s))" % REL[i])
    w("      = " + wrap(rhs, 8) + " := by")
    w("  have hc := congrArg (PowerSeries.coeff n) (clos%d h)" % (i + 1))
    w("  rw [coeff_ofNat_mul, coeff_theta] at hc")
    if len(js) > 1:
        w("  simp only [map_add] at hc")
    w("  rw [" + ", ".join("coeff_mul_of_lower_zero _ _ n H%d" % (j + 1) for j in js) + "] at hc")
    w("  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, %s] at hc" % CCS)
    w("  linear_combination hc")
    w("")

w("/-! ## The linear algebra: `n⁶ (n-2)(n-3)(n-6) r = 0` -/")
w("")
Nk = [[[Fr(e) for e in row] for row in N] for N in cert["Nk"]]
def adj(i, j):
    ts = []
    for k in range(9):
        c = Nk[k][i][j]
        if c == 0:
            continue
        e = 8 - k
        ts.append(num(c, True) if e == 0 else "%s * n ^ %d" % (num(c, True), e))
    return " + ".join(ts) if ts else None
w("theorem lin9 (n r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ) (hn : 7 ≤ n)")
for i in range(9):
    js = [j for j in range(9) if Mt[i][j]]
    w("    (e%d : 24 * (n * r%d) = %s)" % (i + 1, i + 1, " + ".join("%s * r%d" % (num(M0[i][j]), j + 1) for j in js)))
w("    : r1 = 0 ∧ r2 = 0 ∧ r3 = 0 ∧ r4 = 0 ∧ r5 = 0 ∧ r6 = 0 ∧ r7 = 0 ∧ r8 = 0 ∧ r9 = 0 := by")
w("  have hd : (0 : ℝ) < n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6 := by")
w("    have e : n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6 = n ^ 6 * ((n - 2) * ((n - 3) * (n - 6))) := by ring")
w("    rw [e]")
w("    exact mul_pos (pow_pos (by linarith) 6) (mul_pos (by linarith) (mul_pos (by linarith) (by linarith)))")
for i in range(9):
    lc = []
    for j in range(9):
        a = adj(i, j)
        if a is not None:
            lc.append("((%s) / 24) * e%d" % (a, j + 1))
    w("  have z%d : (n ^ 9 - 11 * n ^ 8 + 36 * n ^ 7 - 36 * n ^ 6) * r%d = 0 := by" % (i + 1, i + 1))
    w("    linear_combination " + wrap(" + ".join(lc), 6))
w("  exact ⟨" + ", ".join("(mul_eq_zero.mp z%d).resolve_left hd.ne'" % (i + 1) for i in range(9)) + "⟩")
w("")

w("/-! ## The relations -/")
w("")
CONJ = " ∧ ".join("PowerSeries.coeff n (%s) = 0" % REL[j] for j in range(9))
w("theorem rel_all_zero (h : Ram6) (n : ℕ) :")
w("    " + wrap(CONJ.replace(" ∧ ", " + ∧ "), 6).replace("+ ∧", "∧") + " := by")
w("  induction n using Nat.strong_induction_on with")
w("  | _ n ih =>")
w("    rcases Nat.lt_or_ge n 7 with hn | hn")
w("    · exact ⟨" + ", ".join("coeff_eq_zero_of_dvd7 dvd7_%s hn" % RN[j] for j in range(9)) + "⟩")
PR9 = [".1", ".2.1", ".2.2.1", ".2.2.2.1", ".2.2.2.2.1", ".2.2.2.2.2.1", ".2.2.2.2.2.2.1", ".2.2.2.2.2.2.2.1", ".2.2.2.2.2.2.2.2"]
for j in range(9):
    w("    · have H%d : ∀ m < n, PowerSeries.coeff m (%s) = 0 := fun m hm => (ih m hm)%s" % (j + 1, REL[j], PR9[j]) if j == 0 else
      "      have H%d : ∀ m < n, PowerSeries.coeff m (%s) = 0 := fun m hm => (ih m hm)%s" % (j + 1, REL[j], PR9[j]))
w("      have hn' : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn")
HS = " ".join("H%d" % (j + 1) for j in range(9))
w("      exact lin9 (n : ℝ) " + " ".join("(PowerSeries.coeff n (%s))" % REL[j] for j in range(9)) + " hn'")
for i in range(9):
    w("        (ceq%d h n %s)" % (i + 1, HS))
w("")
for i in range(9):
    w("theorem %s_eq_zero (h : Ram6) : %s = 0 := by" % (RN[i], REL[i]))
    w("  ext n")
    w("  rw [(rel_all_zero h n)%s, map_zero]" % PR9[i])
    w("")

w("/-! ## The generating series of `psiW` satisfies `12 θΓ = (E₂(q) + 2E₂(q²) + 3E₂(q³) + 6E₂(q⁶)) Γ` -/")
w("")
w("/-- `25920 ∑ psiW(n) Xⁿ` as a polynomial in the twelve series. -/")
w("noncomputable def Gamf %s : PowerSeries ℝ :=" % BIND)
w("  " + wrap(poly(Gam, VARS), 4))
w("")
# scale the certificate to integers
import math
Lz = 1
for q in Zc:
    for c in q.values():
        Lz = Lz * c.denominator // math.gcd(Lz, c.denominator)
Zs = [{m: c * Lz for m, c in q.items()} for q in Zc]
GAM = "Gamf " + ARGS
w("theorem thetaGam_scaled (h : Ram6) :")
w("    %d * (12 * theta (%s))" % (Lz, GAM))
w("      = %d * ((e2_1 + 2 * e2_2 + 3 * e2_3 + 6 * e2_6) * (%s)) := by" % (Lz, GAM))
for i in range(9):
    w("  have r%d := %s_eq_zero h" % (i + 1, RN[i]))
w("  unfold Ram6 at h")
w("  obtain %s := h" % OBT)
dsum = " + ".join("(%s) * theta %s" % (poly(dGam[s], ATOMS), ATOMS[s]) for s in range(12) if dGam[s])
w("  have hθ : theta (%s)" % GAM)
w("      = " + wrap(dsum, 8) + " := by")
w("    simp only [Gamf, %s]" % THS)
w("    ring")
w("  simp only [Gamf, %s] at hθ r1 r2 r3 r4 r5 r6 r7 r8 r9 ⊢" % RFS)
CG = [1] * 4 + [4] * 4 + [6] * 4
lc = ["(%d * 12) * hθ" % Lz] + ["(%d * (%s)) * h%d" % (Lz * CG[s], poly(dGam[s], ATOMS), s + 1) for s in range(12) if dGam[s]]
lc += ["(%s) * r%d" % (poly(Zs[j], ATOMS), j + 1) for j in range(9) if Zs[j]]
w("  linear_combination " + wrap(" + ".join(lc), 4))
w("")
w("end Tower.RV6")
open(sys.argv[2], "w").write("\n".join(out) + "\n")
print("wrote", sys.argv[2], len(out), "lines; Lz =", Lz)
