#!/usr/bin/env python3
"""Writes Tower/RV6/DomG.lean: the chain of g = I0^2 K0^2 and the three auxiliary chains in the class PDom of AJ.lean.

theta^k g = sum_i C(k,i) pB_i pB_(k-i) (a polynomial identity under theta I0 = t I1, theta (t I1) = t^2 I0, theta K0 = -t K1,
theta (t K1) = -t^2 K0, checked here); at infinity t pB_i and t^3 (pB_j + pB_(j+1)) are bounded (LaplaceDecay.lean), so every
function of the chains is O(t^-2) and (theta+2)^m g (m = 1, 2, 3) and B = -theta^5 g/(4 t^2) are O(t^-4); near 0 every pB_i is
O(e (1 + log(2/t))), so every function is O(t^(-1/2)).  All constants are computed here in exact arithmetic, every polynomial
identity is checked here, and every linear_combination cofactor is produced by exact division by (t t^-1 - 1).
usage: python3 tools/gen_domg.py  (from the repository root)
"""
import os
from fractions import Fraction
from math import comb

import sympy as sp

# ---------------------------------------------------------------- the polynomial model
t, I0, I1, K0, K1, ti = sp.symbols('t I0 I1 K0 K1 ti')
u, v = t * I1, t * K1


def th(e):
    """theta = t d/dt on polynomials in t, I0, I1, K0, K1 (I0' = I1, I1' = I0 - I1/t, K0' = -K1, K1' = -K0 - K1/t)."""
    d = (sp.diff(e, t) + sp.diff(e, I0) * I1 + sp.diff(e, I1) * (I0 - I1 / t)
         + sp.diff(e, K0) * (-K1) + sp.diff(e, K1) * (-K0 - K1 / t))
    return sp.expand(t * d)


ldG = [I0 ** 2 * K0 ** 2,
       2 * (I0 * u * K0 ** 2) + (-2) * (I0 ** 2 * K0 * v),
       u ** 2 * K0 ** 2 + (-4) * (I0 * u * K0 * v) + I0 ** 2 * v ** 2,
       2 * (I0 * u * v ** 2) + (-2) * (u ** 2 * K0 * v),
       u ** 2 * v ** 2]
thG = [ldG[0], ldG[1], 2 * ldG[2] + 4 * (t ** 2 * ldG[0]),
       6 * ldG[3] + 10 * (t ** 2 * ldG[1]) + 8 * (t ** 2 * ldG[0]),
       24 * ldG[4] + 32 * (t ** 2 * ldG[2]) + 28 * (t ** 2 * ldG[1]) + 16 * (t ** 2 * ldG[0]) + 40 * (t ** 4 * ldG[0]),
       120 * (t ** 2 * ldG[3]) + 120 * (t ** 2 * ldG[2]) + 72 * (t ** 2 * ldG[1]) + 32 * (t ** 2 * ldG[0])
       + 136 * (t ** 4 * ldG[1]) + 272 * (t ** 4 * ldG[0])]
thG = [sp.expand(e) for e in thG]
pB = [I0 * K0, t * I1 * K0 - I0 * (t * K1), 2 * (t ** 2 * I0 * K0) - 2 * ((t * I1) * (t * K1))]
pB.append(4 * t ** 2 * (pB[0] + pB[1]))
pB.append(8 * t ** 2 * (pB[0] + pB[1]) + 4 * t ** 2 * (pB[1] + pB[2]))
pB.append(16 * t ** 2 * (pB[0] + pB[1]) + 16 * t ** 2 * (pB[1] + pB[2]) + 4 * t ** 2 * (pB[2] + pB[3]))
pB = [sp.expand(e) for e in pB]
for k in range(5):
    assert sp.expand(th(pB[k]) - pB[k + 1]) == 0, k
for k in range(5):
    assert sp.expand(th(thG[k]) - thG[k + 1]) == 0, k
for k in range(6):
    assert sp.expand(thG[k] - sum(comb(k, i) * pB[i] * pB[k - i] for i in range(k + 1))) == 0, k
L5 = sp.expand(thG[5] - 4 * t ** 2 * (5 * thG[3] + 15 * thG[2] + 18 * thG[1] + 8 * thG[0])
               + 64 * t ** 4 * (thG[1] + 2 * thG[0]))
assert L5 == 0

# P-forms of theta^k g, grouped: list of (coeff, i, j) with i <= j
PF = {}
for k in range(6):
    terms = {}
    for i in range(k + 1):
        a, b = sorted((i, k - i))
        terms[(a, b)] = terms.get((a, b), 0) + comb(k, i)
    PF[k] = sorted((c, a, b) for (a, b), c in terms.items())

# ---------------------------------------------------------------- constants
A_INF = [2, 4, 20, 148]                      # |t pB_i|
S_INF = {'01': 124, '12': 1014, '23': 11286}  # |t^3 (pB_j + pB_j+1)|
A_INF.append(8 * S_INF['01'] + 4 * S_INF['12'])
A_INF.append(16 * S_INF['01'] + 16 * S_INF['12'] + 4 * S_INF['23'])
K0B = [1, 2, 4, 12, 48, 208]                 # near 0: |pB_i| <= K0B[i] e L
M_INF = [sum(c * A_INF[a] * A_INF[b] for c, a, b in PF[k]) for k in range(6)]   # |t^2 thG_k|
N0 = [sum(c * K0B[a] * K0B[b] for c, a, b in PF[k]) for k in range(6)]          # |thG_k| <= N0 (e L)^2

# chain functions as combinations of thG_k (coefficients), with tau = t^2 parts
# name: (plain coefficients c_k, tau-part: (factor, list of coefficients d_k) or None)
CH = {
    'gQ1': ([4, 4, 1, 0, 0, 0], None),
    'gQ1a': ([0, 4, 4, 1, 0, 0], None),
    'gQ1b': ([0, 0, 4, 4, 1, 0], None),
    'gQ2': ([8, 12, 6, 1, 0, 0], None),
    'gQ2a': ([0, 8, 12, 6, 1, 0], None),
    'gQ2b': ([0, 0, 8, 12, 6, 1], None),
    'gR': ([-8, -18, -15, -5, 0, 0], (16, [2, 1, 0, 0, 0, 0])),
    'gR1': ([0, -8, -18, -15, -5, 0], (16, [4, 4, 1, 0, 0, 0])),
    'gR2': ([0, 0, -8, -18, -15, -5], (16, [8, 12, 6, 1, 0, 0])),
}
CHAINS = [('gQ1', 'gQ1a', 'gQ1b'), ('gQ2', 'gQ2a', 'gQ2b'), ('gR', 'gR1', 'gR2')]


def ch_poly(name):
    c, tp = CH[name]
    e = sum(c[k] * thG[k] for k in range(6))
    if tp:
        e += tp[0] * t ** 2 * sum(tp[1][k] * thG[k] for k in range(6))
    return sp.expand(e)


for a, b, c in CHAINS:
    assert sp.expand(th(ch_poly(a)) - ch_poly(b)) == 0, a
    assert sp.expand(th(ch_poly(b)) - ch_poly(c)) == 0, b
# 4 t^2 gR = -thG5
assert sp.expand(4 * t ** 2 * ch_poly('gR') + thG[5]) == 0

# t^4 (theta+2)^m g in terms of a_i = t pB_i and s_j = t^3 (pB_j + pB_(j+1))
a_ = sp.symbols('a0:6')
s01, s12, s23 = sp.symbols('s01 s12 s23')
P = sp.symbols('P0:4')
S = {'01': P[0] + P[1], '12': P[1] + P[2], '23': P[2] + P[3]}
# Q1 = (theta+2)^2 g = 2 P1 S01 + 2 P0 S12 + 4 P0 S01; Q2 = theta Q1 + 2 Q1;  U0 = (theta + 2) g = 2 P0 S01
U = {
    'U0': [(2, 0, '01')],
    'gQ1': [(2, 1, '01'), (2, 0, '12'), (4, 0, '01')],
    'gQ2': [(2, 2, '01'), (2, 1, '12'), (2, 1, '12'), (2, 0, '23'), (4, 1, '01'), (4, 0, '12'),
            (4, 1, '01'), (4, 0, '12'), (8, 0, '01')],
}
# check: in the P-model (P_i = pB_i, theta P_i = P_(i+1)), these equal the chain functions
for name, terms in U.items():
    e = sum(c * pB[i] * (pB[int(j[0])] + pB[int(j[1])]) for c, i, j in terms)
    tgt = sp.expand(thG[1] + 2 * thG[0]) if name == 'U0' else ch_poly(name)
    assert sp.expand(e - tgt) == 0, name


def collect(terms):
    r = {}
    for c, i, j in terms:
        r[(i, j)] = r.get((i, j), 0) + c
    return sorted((c, i, j) for (i, j), c in r.items() if c != 0)


for k in U:
    U[k] = collect(U[k])
U_INF = {k: sum(abs(c) * A_INF[i] * S_INF[j] for c, i, j in v) for k, v in U.items()}

# ---------------------------------------------------------------- Lean text
OUT = []


def w(s=''):
    OUT.append(s)


def pBt(i):
    return 'pB%d t' % i


w('import Mathlib')
w('import Tower.RV6.AJ')
w('import Tower.RV6.HankelDom')
w('')
w('/-!')
w('# The chain of `g = I₀² K₀²` in the class `PDom`')
w('')
w('Generated by `tools/gen_domg.py`.  With `pB4 = θ pB3`, `pB5 = θ pB4` (`LaplaceDecay.lean` has `pB0 … pB3`):')
w('')
w('* `thGk_eq_P`: `θᵏ g = Σᵢ C(k,i) pBᵢ pB_{k-i}` (polynomial identities);')
w('* at infinity (`t > 0`): `|t² θᵏ g| ≤ Mₖ`, and `|t⁴ (θ+2)ᵐ g|` bounded for `m = 1, 2, 3` (`|t pBᵢ|` and')
w('  `|t³ (pBⱼ + pBⱼ₊₁)|` are bounded, `LaplaceDecay.lean`);')
w('* near `0` (`0 < t ≤ 1`): `|pBᵢ| ≤ kᵢ e (1 + log(2/t))`, so `√t |f| ≤ C` for every function of the chains;')
w('* the auxiliary chains `gQ1 = (θ+2)²g`, `gQ2 = (θ+2)³g`, `gR = 16t²(θ+2)g - P₃(θ)g = -θ⁵g/(4t²)` with their')
w('  `θ` and `θ²`, as `HasDerivAt` chains;')
w('* **`pdom_thG0` … `pdom_gR2`**: all fifteen functions are in `PDom`, and `t⁴ |f| ≤ C` on `[1, ∞)` for')
w('  `f = gQ1, gQ2, gR` (`pdom4_gQ1`, `pdom4_gQ2`, `pdom4_gR`): the hypotheses of R1 and R2 of `AJ.lean`.')
w('-/')
w('')
w('namespace Tower.RV6')
w('')
w('open Real MeasureTheory')
w('')
w('/-! ## Helpers -/')
w('')
w('theorem abs_cmul_leG {c C X B : ℝ} (hc : |c| = C) (hX : |X| ≤ B) : |c * X| ≤ C * B := by')
w('  rw [abs_mul, hc]')
w('  have hC : 0 ≤ C := hc ▸ abs_nonneg c')
w('  exact mul_le_mul_of_nonneg_left hX hC')
w('')
w('theorem abs_mul_leG {p r P R : ℝ} (hp : |p| ≤ P) (hr : |r| ≤ R) : |p * r| ≤ P * R := by')
w('  rw [abs_mul]')
w('  exact mul_le_mul hp hr (abs_nonneg _) ((abs_nonneg _).trans hp)')
w('')
w('/-- `pB4 = θ pB3`. -/')
w('noncomputable def pB4 (t : ℝ) : ℝ := 8 * t ^ 2 * (pB0 t + pB1 t) + 4 * t ^ 2 * (pB1 t + pB2 t)')
w('')
w('/-- `pB5 = θ pB4`. -/')
w('noncomputable def pB5 (t : ℝ) : ℝ :=')
w('  16 * t ^ 2 * (pB0 t + pB1 t) + 16 * t ^ 2 * (pB1 t + pB2 t) + 4 * t ^ 2 * (pB2 t + pB3 t)')
w('')


def lin_bound(lhs_terms, name_prefix, indent='  '):
    """lhs_terms: list of (coef, lean_expr, bound_hyp_name, bound_value_lean); emits haves and returns lines.
    The sum is c1 * X1 + c2 * X2 + ... (left associated)."""
    lines = []
    for n, (c, X, hyp, B) in enumerate(lhs_terms):
        cabs = abs(c)
        lines.append('%shave %s%d : |(%s : ℝ) * %s| ≤ %s * %s := abs_cmul_leG (by norm_num) %s'
                     % (indent, name_prefix, n, c, X, cabs, B, hyp))
    acc = '(%s : ℝ) * %s' % (lhs_terms[0][0], lhs_terms[0][1])
    for n in range(1, len(lhs_terms)):
        nxt = '(%s : ℝ) * %s' % (lhs_terms[n][0], lhs_terms[n][1])
        lines.append('%shave %st%d := abs_add_le (%s) (%s)' % (indent, name_prefix, n, acc, nxt))
        acc = acc + ' + ' + nxt
    return lines, acc


# ---- P-forms
for k in range(6):
    rhs = ' + '.join('%d * (pB%d t * pB%d t)' % (c, a, b) for c, a, b in PF[k])
    unf = ['thG%d' % k, 'ldG4', 'ldG3', 'ldG2', 'ldG1', 'ldG0', 'pB5', 'pB4', 'pB3', 'pB2', 'pB1', 'pB0']
    w('theorem thG%d_eq_P (t : ℝ) : thG%d t = %s := by' % (k, k, rhs))
    w('  simp only [%s]' % ', '.join(unf))
    w('  ring')
    w('')

# ---- at infinity
w('/-! ## At infinity -/')
w('')
w('theorem abs_mul_pB4_le {t : ℝ} (ht : 0 < t) : |t * pB4 t| ≤ %d := by' % A_INF[4])
w('  have h1 := abs_pB01_le ht')
w('  have h2 := abs_pB12_le ht')
w('  have e : t * pB4 t = (8 : ℝ) * (t ^ 3 * (pB0 t + pB1 t)) + (4 : ℝ) * (t ^ 3 * (pB1 t + pB2 t)) := by')
w('    unfold pB4')
w('    ring')
w('  rw [e]')
w('  have b0 : |(8 : ℝ) * (t ^ 3 * (pB0 t + pB1 t))| ≤ 8 * 124 := abs_cmul_leG (by norm_num) h1')
w('  have b1 : |(4 : ℝ) * (t ^ 3 * (pB1 t + pB2 t))| ≤ 4 * 1014 := abs_cmul_leG (by norm_num) h2')
w('  have a := abs_add_le ((8 : ℝ) * (t ^ 3 * (pB0 t + pB1 t))) ((4 : ℝ) * (t ^ 3 * (pB1 t + pB2 t)))')
w('  linarith')
w('')
w('theorem abs_mul_pB5_le {t : ℝ} (ht : 0 < t) : |t * pB5 t| ≤ %d := by' % A_INF[5])
w('  have h1 := abs_pB01_le ht')
w('  have h2 := abs_pB12_le ht')
w('  have h3 := abs_pB23_le ht')
w('  have e : t * pB5 t = (16 : ℝ) * (t ^ 3 * (pB0 t + pB1 t)) + (16 : ℝ) * (t ^ 3 * (pB1 t + pB2 t))')
w('      + (4 : ℝ) * (t ^ 3 * (pB2 t + pB3 t)) := by')
w('    unfold pB5')
w('    ring')
w('  rw [e]')
w('  have b0 : |(16 : ℝ) * (t ^ 3 * (pB0 t + pB1 t))| ≤ 16 * 124 := abs_cmul_leG (by norm_num) h1')
w('  have b1 : |(16 : ℝ) * (t ^ 3 * (pB1 t + pB2 t))| ≤ 16 * 1014 := abs_cmul_leG (by norm_num) h2')
w('  have b2 : |(4 : ℝ) * (t ^ 3 * (pB2 t + pB3 t))| ≤ 4 * 11286 := abs_cmul_leG (by norm_num) h3')
w('  have a1 := abs_add_le ((16 : ℝ) * (t ^ 3 * (pB0 t + pB1 t))) ((16 : ℝ) * (t ^ 3 * (pB1 t + pB2 t)))')
w('  have a2 := abs_add_le ((16 : ℝ) * (t ^ 3 * (pB0 t + pB1 t)) + (16 : ℝ) * (t ^ 3 * (pB1 t + pB2 t)))')
w('    ((4 : ℝ) * (t ^ 3 * (pB2 t + pB3 t)))')
w('  linarith')
w('')
APL = ['abs_mul_pB%d_le ht' % i for i in range(6)]
for k in range(6):
    w('theorem abs_tsq_thG%d_le {t : ℝ} (ht : 0 < t) : |t ^ 2 * thG%d t| ≤ %d := by' % (k, k, M_INF[k]))
    for i in range(6):
        w('  have h%d := %s' % (i, APL[i]))
    terms = []
    for c, a, b in PF[k]:
        X = '((t * pB%d t) * (t * pB%d t))' % (a, b)
        hyp = '(abs_mul_leG h%d h%d)' % (a, b)
        B = '(%d * %d)' % (A_INF[a], A_INF[b])
        terms.append((c, X, hyp, B))
    lines, acc = lin_bound(terms, 'b')
    w('  have e : t ^ 2 * thG%d t = %s := by' % (k, acc))
    w('    rw [thG%d_eq_P]' % k)
    w('    ring')
    w('  rw [e]')
    for l in lines:
        w(l)
    w('  linarith')
    w('')

SNAME = {'01': ('abs_pB01_le ht', 't ^ 3 * (pB0 t + pB1 t)'), '12': ('abs_pB12_le ht', 't ^ 3 * (pB1 t + pB2 t)'),
         '23': ('abs_pB23_le ht', 't ^ 3 * (pB2 t + pB3 t)')}
for name, terms0 in U.items():
    target = '(thG1 t + 2 * thG0 t)' if name == 'U0' else '%s t' % name
    lname = 'abs_t4_thG10_le' if name == 'U0' else 'abs_t4_%s_le' % name
    if name != 'U0':
        continue
    w('theorem %s {t : ℝ} (ht : 0 < t) : |t ^ 4 * %s| ≤ %d := by' % (lname, target, U_INF[name]))
    for i in range(4):
        w('  have h%d := %s' % (i, APL[i]))
    for j, (hj, _) in SNAME.items():
        w('  have s%s := %s' % (j, hj))
    terms = []
    for c, i, j in terms0:
        X = '((t * pB%d t) * (%s))' % (i, SNAME[j][1])
        terms.append((c, X, '(abs_mul_leG h%d s%s)' % (i, j), '(%d * %d)' % (A_INF[i], S_INF[j])))
    lines, acc = lin_bound(terms, 'b')
    w('  have e : t ^ 4 * %s = %s := by' % (target, acc))
    w('    rw [thG1_eq_P, thG0_eq_P]')
    w('    ring')
    w('  rw [e]')
    for l in lines:
        w(l)
    w('  linarith')
    w('')

# ---- the chain functions
w('/-! ## The three auxiliary chains -/')
w('')
DOC = {'gQ1': '`(θ+2)² g`', 'gQ1a': '`θ (θ+2)² g`', 'gQ1b': '`θ² (θ+2)² g`', 'gQ2': '`(θ+2)³ g`',
       'gQ2a': '`θ (θ+2)³ g`', 'gQ2b': '`θ² (θ+2)³ g`', 'gR': '`16t²(θ+2)g - P₃(θ)g = -θ⁵g/(4t²)`',
       'gR1': '`θ gR`', 'gR2': '`θ² gR`'}


def ch_lean(name):
    c, tp = CH[name]
    plain = ' + '.join('(%d : ℝ) * thG%d t' % (c[k], k) for k in range(6) if c[k] != 0)
    if tp:
        inner = ' + '.join('(%d : ℝ) * thG%d t' % (tp[1][k], k) for k in range(6) if tp[1][k] != 0)
        return '16 * t ^ 2 * (%s) + (%s)' % (inner, plain)
    return plain


for name in CH:
    w('/-- %s. -/' % DOC[name])
    w('noncomputable def %s (t : ℝ) : ℝ := %s' % (name, ch_lean(name)))
    w('')

for name in ('gQ2', 'gR'):
    pass

# t^4 bounds for gQ1, gQ2
for name in ('gQ1', 'gQ2'):
    terms0 = U[name]
    w('theorem abs_t4_%s_le {t : ℝ} (ht : 0 < t) : |t ^ 4 * %s t| ≤ %d := by' % (name, name, U_INF[name]))
    for i in range(4):
        w('  have h%d := %s' % (i, APL[i]))
    for j, (hj, _) in SNAME.items():
        w('  have s%s := %s' % (j, hj))
    terms = []
    for c, i, j in terms0:
        X = '((t * pB%d t) * (%s))' % (i, SNAME[j][1])
        terms.append((c, X, '(abs_mul_leG h%d s%s)' % (i, j), '(%d * %d)' % (A_INF[i], S_INF[j])))
    lines, acc = lin_bound(terms, 'b')
    w('  have e : t ^ 4 * %s t = %s := by' % (name, acc))
    w('    unfold %s' % name)
    w('    rw [%s]' % ', '.join('thG%d_eq_P' % k for k in range(6) if CH[name][0][k] != 0))
    w('    ring')
    w('  rw [e]')
    for l in lines:
        w(l)
    w('  linarith')
    w('')

# 4 t^2 gR = - thG5
w('theorem gR_eq (t : ℝ) : 4 * t ^ 2 * gR t = -thG5 t := by')
w('  have h := L5_thG t')
w('  unfold gR')
w('  linear_combination (1 : ℝ) * h')
w('')

# t^2 bounds for all chain functions (at infinity, any t > 0)


def tsq_bound(name):
    c, tp = CH[name]
    tot = sum(abs(c[k]) * M_INF[k] for k in range(6))
    if tp:
        key = {'gR': 'U0', 'gR1': 'gQ1', 'gR2': 'gQ2'}[name]
        tot += 16 * U_INF[key]
    return tot


TSQ = {n: tsq_bound(n) for n in CH}
for name in CH:
    c, tp = CH[name]
    w('theorem abs_tsq_%s_le {t : ℝ} (ht : 0 < t) : |t ^ 2 * %s t| ≤ %d := by' % (name, name, TSQ[name]))
    terms = []
    for k in range(6):
        if c[k] != 0:
            w('  have h%d := abs_tsq_thG%d_le ht' % (k, k))
            terms.append((c[k], '(t ^ 2 * thG%d t)' % k, 'h%d' % k, str(M_INF[k])))
    if tp:
        key = {'gR': ('abs_t4_thG10_le', '(t ^ 4 * (thG1 t + 2 * thG0 t))', 'U0'),
               'gR1': ('abs_t4_gQ1_le', '(t ^ 4 * gQ1 t)', 'gQ1'), 'gR2': ('abs_t4_gQ2_le', '(t ^ 4 * gQ2 t)', 'gQ2')}[name]
        w('  have hU := %s ht' % key[0])
        terms = [(16, key[1], 'hU', str(U_INF[key[2]]))] + terms
    lines, acc = lin_bound(terms, 'b')
    w('  have e : t ^ 2 * %s t = %s := by' % (name, acc))
    w('    unfold %s' % name)
    if name == 'gR1':
        w('    unfold gQ1')
    if name == 'gR2':
        w('    unfold gQ2')
    w('    ring')
    w('  rw [e]')
    for l in lines:
        w(l)
    w('  linarith')
    w('')

# ---- near 0
w('/-! ## Near `0` -/')
w('')
w('theorem abs_pB_near0 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :')
w('    |pB0 t| ≤ 1 * (Real.exp 1 * (1 + Real.log (2 / t))) ∧ |pB1 t| ≤ 2 * (Real.exp 1 * (1 + Real.log (2 / t))) ∧')
w('      |pB2 t| ≤ 4 * (Real.exp 1 * (1 + Real.log (2 / t))) ∧ |pB3 t| ≤ 12 * (Real.exp 1 * (1 + Real.log (2 / t))) ∧')
w('      |pB4 t| ≤ 48 * (Real.exp 1 * (1 + Real.log (2 / t))) ∧ |pB5 t| ≤ 208 * (Real.exp 1 * (1 + Real.log (2 / t))) := by')
w('  have hI0 := ity_besselI0.2.1 t ht ht1')
w('  have hI1 : |t * besselI1 t| ≤ Real.exp 1 := ity_mul_besselI1.2.1 t ht ht1')
w('  have hK0 := kty_besselK0.2.1 t ht ht1')
w('  have hK1 : |t * besselK1 t| ≤ 1 + Real.log (2 / t) := kty_mul_besselK1.2.1 t ht ht1')
w('  have ht2 : |t ^ 2| ≤ 1 := by')
w('    rw [abs_of_nonneg (sq_nonneg t)]')
w('    exact pow_le_one₀ ht.le ht1')
w('  have p0 : |pB0 t| ≤ 1 * (Real.exp 1 * (1 + Real.log (2 / t))) := by')
w('    have h : |besselI0 t * besselK0 t| ≤ (Real.exp 1 * (1 + Real.log (2 / t))) := abs_mul_leG hI0 hK0')
w('    unfold pB0')
w('    linarith')
w('  have p1 : |pB1 t| ≤ 2 * (Real.exp 1 * (1 + Real.log (2 / t))) := by')
w('    have h1 : |t * besselI1 t * besselK0 t| ≤ (Real.exp 1 * (1 + Real.log (2 / t))) := abs_mul_leG hI1 hK0')
w('    have h2 : |besselI0 t * (t * besselK1 t)| ≤ (Real.exp 1 * (1 + Real.log (2 / t))) := abs_mul_leG hI0 hK1')
w('    have a := abs_add_le (t * besselI1 t * besselK0 t) (-(besselI0 t * (t * besselK1 t)))')
w('    rw [abs_neg, ← sub_eq_add_neg] at a')
w('    unfold pB1')
w('    linarith')
w('  have p2 : |pB2 t| ≤ 4 * (Real.exp 1 * (1 + Real.log (2 / t))) := by')
w('    have h1 : |t ^ 2 * besselI0 t * besselK0 t| ≤ 1 * Real.exp 1 * (1 + Real.log (2 / t)) :=')
w('      abs_mul_leG (abs_mul_leG ht2 hI0) hK0')
w('    have h2 : |(t * besselI1 t) * (t * besselK1 t)| ≤ (Real.exp 1 * (1 + Real.log (2 / t))) := abs_mul_leG hI1 hK1')
w('    have h1b : |t ^ 2 * besselI0 t * besselK0 t| ≤ (Real.exp 1 * (1 + Real.log (2 / t))) := by linarith')
w('    have b1 : |(2 : ℝ) * (t ^ 2 * besselI0 t * besselK0 t)| ≤ 2 * (Real.exp 1 * (1 + Real.log (2 / t))) :=')
w('      abs_cmul_leG (by norm_num) h1b')
w('    have b2 : |(2 : ℝ) * ((t * besselI1 t) * (t * besselK1 t))| ≤ 2 * (Real.exp 1 * (1 + Real.log (2 / t))) :=')
w('      abs_cmul_leG (by norm_num) h2')
w('    have a := abs_add_le ((2 : ℝ) * (t ^ 2 * besselI0 t * besselK0 t))')
w('      (-((2 : ℝ) * ((t * besselI1 t) * (t * besselK1 t))))')
w('    rw [abs_neg, ← sub_eq_add_neg] at a')
w('    unfold pB2')
w('    linarith')
w('  have p3 : |pB3 t| ≤ 12 * (Real.exp 1 * (1 + Real.log (2 / t))) := by')
w('    have h := abs_add_le (pB0 t) (pB1 t)')
w('    have h2 : |t ^ 2 * (pB0 t + pB1 t)| ≤ 1 * (3 * (Real.exp 1 * (1 + Real.log (2 / t)))) := abs_mul_leG ht2 (by linarith)')
w('    have e : pB3 t = (4 : ℝ) * (t ^ 2 * (pB0 t + pB1 t)) := by unfold pB3; ring')
w('    rw [e]')
w('    have b := abs_cmul_leG (c := (4 : ℝ)) (C := 4) (by norm_num) h2')
w('    linarith')
w('  have p4 : |pB4 t| ≤ 48 * (Real.exp 1 * (1 + Real.log (2 / t))) := by')
w('    have h01 := abs_add_le (pB0 t) (pB1 t)')
w('    have h12 := abs_add_le (pB1 t) (pB2 t)')
w('    have c1 : |t ^ 2 * (pB0 t + pB1 t)| ≤ 1 * (3 * (Real.exp 1 * (1 + Real.log (2 / t)))) := abs_mul_leG ht2 (by linarith)')
w('    have c2 : |t ^ 2 * (pB1 t + pB2 t)| ≤ 1 * (6 * (Real.exp 1 * (1 + Real.log (2 / t)))) := abs_mul_leG ht2 (by linarith)')
w('    have e : pB4 t = (8 : ℝ) * (t ^ 2 * (pB0 t + pB1 t)) + (4 : ℝ) * (t ^ 2 * (pB1 t + pB2 t)) := by')
w('      unfold pB4; ring')
w('    rw [e]')
w('    have b1 := abs_cmul_leG (c := (8 : ℝ)) (C := 8) (by norm_num) c1')
w('    have b2 := abs_cmul_leG (c := (4 : ℝ)) (C := 4) (by norm_num) c2')
w('    have a := abs_add_le ((8 : ℝ) * (t ^ 2 * (pB0 t + pB1 t))) ((4 : ℝ) * (t ^ 2 * (pB1 t + pB2 t)))')
w('    linarith')
w('  have p5 : |pB5 t| ≤ 208 * (Real.exp 1 * (1 + Real.log (2 / t))) := by')
w('    have h01 := abs_add_le (pB0 t) (pB1 t)')
w('    have h12 := abs_add_le (pB1 t) (pB2 t)')
w('    have h23 := abs_add_le (pB2 t) (pB3 t)')
w('    have c1 : |t ^ 2 * (pB0 t + pB1 t)| ≤ 1 * (3 * (Real.exp 1 * (1 + Real.log (2 / t)))) := abs_mul_leG ht2 (by linarith)')
w('    have c2 : |t ^ 2 * (pB1 t + pB2 t)| ≤ 1 * (6 * (Real.exp 1 * (1 + Real.log (2 / t)))) := abs_mul_leG ht2 (by linarith)')
w('    have c3 : |t ^ 2 * (pB2 t + pB3 t)| ≤ 1 * (16 * (Real.exp 1 * (1 + Real.log (2 / t)))) := abs_mul_leG ht2 (by linarith)')
w('    have e : pB5 t = (16 : ℝ) * (t ^ 2 * (pB0 t + pB1 t)) + (16 : ℝ) * (t ^ 2 * (pB1 t + pB2 t))')
w('        + (4 : ℝ) * (t ^ 2 * (pB2 t + pB3 t)) := by')
w('      unfold pB5; ring')
w('    rw [e]')
w('    have b1 := abs_cmul_leG (c := (16 : ℝ)) (C := 16) (by norm_num) c1')
w('    have b2 := abs_cmul_leG (c := (16 : ℝ)) (C := 16) (by norm_num) c2')
w('    have b3 := abs_cmul_leG (c := (4 : ℝ)) (C := 4) (by norm_num) c3')
w('    have a1 := abs_add_le ((16 : ℝ) * (t ^ 2 * (pB0 t + pB1 t))) ((16 : ℝ) * (t ^ 2 * (pB1 t + pB2 t)))')
w('    have a2 := abs_add_le ((16 : ℝ) * (t ^ 2 * (pB0 t + pB1 t)) + (16 : ℝ) * (t ^ 2 * (pB1 t + pB2 t)))')
w('      ((4 : ℝ) * (t ^ 2 * (pB2 t + pB3 t)))')
w('    linarith')
w('  exact ⟨p0, p1, p2, p3, p4, p5⟩')
w('')
for k in range(6):
    w('theorem abs_thG%d_near0 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :' % k)
    w('    |thG%d t| ≤ %d * (Real.exp 1 * (1 + Real.log (2 / t))) ^ 2 := by' % (k, N0[k]))
    w('  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := abs_pB_near0 ht ht1')
    w('  set E := Real.exp 1 * (1 + Real.log (2 / t)) with hE')
    terms = []
    for c, a, b in PF[k]:
        X = '(pB%d t * pB%d t)' % (a, b)
        terms.append((c, X, '(abs_mul_leG h%d h%d)' % (a, b), '(%d * E * (%d * E))' % (K0B[a], K0B[b])))
    lines, acc = lin_bound(terms, 'b')
    w('  rw [thG%d_eq_P]' % k)
    w('  have e : %s = %s := by ring' % (' + '.join('%d * (pB%d t * pB%d t)' % (c, a, b) for c, a, b in PF[k]), acc))
    w('  rw [e]')
    for l in lines:
        w(l)
    w('  linarith')
    w('')


def near0_bound(name):
    c, tp = CH[name]
    tot = sum(abs(c[k]) * N0[k] for k in range(6))
    if tp:
        tot += tp[0] * sum(abs(tp[1][k]) * N0[k] for k in range(6))
    return tot


NB = {n: near0_bound(n) for n in CH}
for name in CH:
    c, tp = CH[name]
    w('theorem abs_%s_near0 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :' % name)
    w('    |%s t| ≤ %d * (Real.exp 1 * (1 + Real.log (2 / t))) ^ 2 := by' % (name, NB[name]))
    w('  set E := Real.exp 1 * (1 + Real.log (2 / t)) with hE')
    for k in range(6):
        w('  have h%d := abs_thG%d_near0 ht ht1' % (k, k))
    w('  have ht2 : |t ^ 2| ≤ 1 := by')
    w('    rw [abs_of_nonneg (sq_nonneg t)]')
    w('    exact pow_le_one₀ ht.le ht1')
    terms = []
    if tp:
        d = tp[1]
        inner_terms = [(d[k], 'thG%d t' % k, 'h%d' % k, '(%d * E ^ 2)' % N0[k]) for k in range(6) if d[k] != 0]
        ilines, iacc = lin_bound(inner_terms, 'i')
        for l in ilines:
            w(l)
        tot_in = sum(abs(d[k]) * N0[k] for k in range(6))
        w('  have hin : |%s| ≤ %d * E ^ 2 := by linarith' % (iacc, tot_in))
        w('  have hin2 : |t ^ 2 * (%s)| ≤ 1 * (%d * E ^ 2) := abs_mul_leG ht2 hin' % (iacc, tot_in))
        terms.append((16, '(t ^ 2 * (%s))' % iacc, 'hin2', '(1 * (%d * E ^ 2))' % tot_in))
    for k in range(6):
        if c[k] != 0:
            terms.append((c[k], 'thG%d t' % k, 'h%d' % k, '(%d * E ^ 2)' % N0[k]))
    lines, acc = lin_bound(terms, 'b')
    w('  have e : %s t = %s := by' % (name, acc))
    w('    unfold %s' % name)
    w('    ring')
    w('  rw [e]')
    for l in lines:
        w(l)
    w('  linarith')
    w('')

w('theorem sqrt_mul_one_add_log_sq_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :')
w('    Real.sqrt t * (Real.exp 1 * (1 + Real.log (2 / t))) ^ 2 ≤ Real.exp 1 ^ 2 * (343 * Real.sqrt 2) := by')
w('  have h := sqrt_mul_one_add_log_cube_le ht ht1')
w('  have hL : 1 ≤ 1 + Real.log (2 / t) := by')
w('    have : 0 ≤ Real.log (2 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)')
w('    linarith')
w('  have hs := Real.sqrt_nonneg t')
w('  have h2 : (1 + Real.log (2 / t)) ^ 2 ≤ (1 + Real.log (2 / t)) ^ 3 := by')
w('    have := pow_le_pow_right₀ hL (by norm_num : 2 ≤ 3)')
w('    exact this')
w('  have h3 : Real.sqrt t * (1 + Real.log (2 / t)) ^ 2 ≤ 343 * Real.sqrt 2 :=')
w('    le_trans (mul_le_mul_of_nonneg_left h2 hs) h')
w('  have e : Real.sqrt t * (Real.exp 1 * (1 + Real.log (2 / t))) ^ 2')
w('      = Real.exp 1 ^ 2 * (Real.sqrt t * (1 + Real.log (2 / t)) ^ 2) := by ring')
w('  rw [e]')
w('  exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)')
w('')

# ---- derivatives of the chains
w('/-! ## The chains as `HasDerivAt` -/')
w('')
HD = ['hasDerivAt_thG%d ht' % k for k in range(5)]


def deriv_value(name):
    """the derivative computed by the product rule, as a sympy expression in atoms T0..T5 (thG_k t), t, ti (= t^-1)."""
    T = sp.symbols('T0:6')
    c, tp = CH[name]
    e = sum(c[k] * T[k + 1] * ti for k in range(6) if c[k] != 0)
    if tp:
        inner = sum(tp[1][k] * T[k] for k in range(6))
        dinner = sum(tp[1][k] * T[k + 1] * ti for k in range(6) if tp[1][k] != 0)
        e += tp[0] * (2 * t * inner + t ** 2 * dinner)
    return e, T


def lean_of(e):
    s = str(e)
    for k in range(6):
        s = s.replace('T%d' % k, 'thG%d t' % k)
    s = s.replace('ti', 't⁻¹').replace('**', '^')
    return s


for a, b, cname in CHAINS:
    for src, dst in ((a, b), (b, cname)):
        c, tp = CH[src]
        e, T = deriv_value(src)
        cd, tpd = CH[dst]
        tgt = sum(cd[k] * T[k] for k in range(6))
        if tpd:
            tgt += tpd[0] * t ** 2 * sum(tpd[1][k] * T[k] for k in range(6))
        diff = sp.expand(e - tgt * ti)
        q, r = sp.div(diff, t * ti - 1, ti)
        assert sp.expand(r) == 0, (src, r)
        assert sp.expand(diff - q * (t * ti - 1)) == 0
        w('theorem hasDerivAt_%s {t : ℝ} (ht : 0 < t) : HasDerivAt %s (%s t / t) t := by' % (src, src, dst))
        pieces = []
        for k in range(6):
            if c[k] != 0:
                if k == 5:
                    raise SystemExit('thG5 has no derivative')
                w('  have d%d := (%s).const_mul (%d : ℝ)' % (k, HD[k], c[k]))
                pieces.append('d%d' % k)
        if tp:
            inner_pieces = []
            for k in range(6):
                if tp[1][k] != 0:
                    w('  have i%d := (%s).const_mul (%d : ℝ)' % (k, HD[k], tp[1][k]))
                    inner_pieces.append('i%d' % k)
            acc = inner_pieces[0]
            for p in inner_pieces[1:]:
                acc = '(%s).add %s' % (acc, p)
            in_x = ' + '.join('(%d : ℝ) * thG%d x' % (tp[1][k], k) for k in range(6) if tp[1][k] != 0)
            in_t = ' + '.join('(%d : ℝ) * thG%d t' % (tp[1][k], k) for k in range(6) if tp[1][k] != 0)
            in_d = ' + '.join('(%d : ℝ) * (thG%d t / t)' % (tp[1][k], k + 1) for k in range(6) if tp[1][k] != 0)
            w('  have hin : HasDerivAt (fun x : ℝ => %s) (%s) t := %s' % (in_x, in_d, acc))
            w('  have hsq : HasDerivAt (fun x : ℝ => (16 : ℝ) * x ^ 2 * (%s))' % in_x)
            w('      ((16 : ℝ) * (2 * t) * (%s) + (16 : ℝ) * t ^ 2 * (%s)) t :=' % (in_t, in_d))
            w('    ((hasDerivAt_sqx t).const_mul (16 : ℝ)).mul hin')
            pieces = ['hsq'] + pieces
        acc = pieces[0]
        for p in pieces[1:]:
            acc = '(%s).add %s' % (acc, p)
        w('  have h0 := %s' % acc)
        # the function
        plain = ' + '.join('(%d : ℝ) * thG%d x' % (c[k], k) for k in range(6) if c[k] != 0)
        if tp:
            inner = ' + '.join('(%d : ℝ) * thG%d x' % (tp[1][k], k) for k in range(6) if tp[1][k] != 0)
            fun = '(16 : ℝ) * x ^ 2 * (%s) + %s' % (inner, plain)
            fun_def = '16 * x ^ 2 * (%s) + (%s)' % (inner, plain)
        else:
            fun = plain
            fun_def = plain
        w('  have hfun : %s = fun x : ℝ => %s := by' % (src, fun))
        w('    funext x')
        w('    unfold %s' % src)
        w('    ring')
        w('  rw [hfun]')
        w('  refine h0.congr_deriv ?_')
        w('  have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne\'')
        w('  unfold %s' % dst)
        w('  linear_combination (%s) * hti' % lean_of(sp.expand(q)))
        w('')

# ---- continuity
w('/-! ## Continuity -/')
w('')
for k in range(5):
    w('theorem continuousOn_thG%d : ContinuousOn thG%d (Set.Ioi 0) :=' % (k, k))
    w('  fun t ht => (hasDerivAt_thG%d (Set.mem_Ioi.mp ht)).continuousAt.continuousWithinAt' % k)
    w('')
w('theorem continuousOn_thG5 : ContinuousOn thG5 (Set.Ioi 0) := by')
w('  have hfun : ∀ t ∈ Set.Ioi (0 : ℝ), (fun t : ℝ => 4 * t ^ 2 * (5 * thG3 t + 15 * thG2 t + 18 * thG1 t + 8 * thG0 t)')
w('      - 64 * t ^ 4 * (thG1 t + 2 * thG0 t)) t = thG5 t := by')
w('    intro t _')
w('    have h := L5_thG t')
w('    show 4 * t ^ 2 * (5 * thG3 t + 15 * thG2 t + 18 * thG1 t + 8 * thG0 t)')
w('      - 64 * t ^ 4 * (thG1 t + 2 * thG0 t) = thG5 t')
w('    linarith')
w('  have hc : ContinuousOn (fun t : ℝ => 4 * t ^ 2 * (5 * thG3 t + 15 * thG2 t + 18 * thG1 t + 8 * thG0 t)')
w('      - 64 * t ^ 4 * (thG1 t + 2 * thG0 t)) (Set.Ioi 0) := by')
w('    have c0 := continuousOn_thG0')
w('    have c1 := continuousOn_thG1')
w('    have c2 := continuousOn_thG2')
w('    have c3 := continuousOn_thG3')
w('    fun_prop')
w('  exact hc.congr (fun t ht => (hfun t ht).symm)')
w('')
for name in CH:
    c, tp = CH[name]
    w('theorem continuousOn_%s : ContinuousOn %s (Set.Ioi 0) := by' % (name, name))
    for k in range(6):
        w('  have c%d := continuousOn_thG%d' % (k, k))
    w('  unfold %s' % name)
    w('  fun_prop')
    w('')

# ---- PDom
w('/-! ## Membership in `PDom` -/')
w('')
CONST = 'Real.exp 1 ^ 2 * (343 * Real.sqrt 2)'


def pdom(fname, n0, minf, tsq_lemma, near0_lemma, cont):
    w('theorem pdom_%s : PDom %s := by' % (fname, fname))
    w('  refine ⟨%s, %d * (%s) + %d, by positivity, fun t ht ht1 => ?_, fun t ht => ?_⟩' % (cont, n0, CONST, minf))
    w('  · have h := %s ht ht1' % near0_lemma)
    w('    have hs := sqrt_mul_one_add_log_sq_le ht ht1')
    w('    have hsq := Real.sqrt_nonneg t')
    w('    have h2 : Real.sqrt t * |%s t| ≤ Real.sqrt t * (%d * (Real.exp 1 * (1 + Real.log (2 / t))) ^ 2) :=' % (fname, n0))
    w('      mul_le_mul_of_nonneg_left h hsq')
    w('    have e : Real.sqrt t * (%d * (Real.exp 1 * (1 + Real.log (2 / t))) ^ 2)' % n0)
    w('        = %d * (Real.sqrt t * (Real.exp 1 * (1 + Real.log (2 / t))) ^ 2) := by ring' % n0)
    w('    have h3 : %d * (Real.sqrt t * (Real.exp 1 * (1 + Real.log (2 / t))) ^ 2) ≤ %d * (%s) :=' % (n0, n0, CONST))
    w('      mul_le_mul_of_nonneg_left hs (by norm_num)')
    w('    linarith')
    w('  · have ht0 : 0 < t := by linarith')
    w('    have h := %s ht0' % tsq_lemma)
    w('    rw [abs_mul, abs_of_nonneg (sq_nonneg t)] at h')
    w('    have hc : 0 ≤ %d * (%s) := by positivity' % (n0, CONST))
    w('    linarith')
    w('')


for k in range(6):
    pdom('thG%d' % k, N0[k], M_INF[k], 'abs_tsq_thG%d_le' % k, 'abs_thG%d_near0' % k, 'continuousOn_thG%d' % k)
for name in CH:
    pdom(name, NB[name], TSQ[name], 'abs_tsq_%s_le' % name, 'abs_%s_near0' % name, 'continuousOn_%s' % name)

# ---- PDom4
w('theorem pdom4_gQ1 : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |gQ1 t| ≤ %d := by' % U_INF['gQ1'])
w('  intro t ht')
w('  have h := abs_t4_gQ1_le (by linarith : (0 : ℝ) < t)')
w('  rwa [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4)] at h')
w('')
w('theorem pdom4_gQ2 : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |gQ2 t| ≤ %d := by' % U_INF['gQ2'])
w('  intro t ht')
w('  have h := abs_t4_gQ2_le (by linarith : (0 : ℝ) < t)')
w('  rwa [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4)] at h')
w('')
w('theorem pdom4_gR : ∀ t : ℝ, 1 ≤ t → t ^ 4 * |gR t| ≤ %d := by' % M_INF[5])
w('  intro t ht')
w('  have ht0 : (0 : ℝ) < t := by linarith')
w('  have h := abs_tsq_thG5_le ht0')
w('  have e : t ^ 4 * gR t = -(t ^ 2 * thG5 t) / 4 := by')
w('    have := gR_eq t')
w('    linear_combination (t ^ 2 / 4) * this')
w('  have h2 : |t ^ 4 * gR t| ≤ %d / 4 := by' % M_INF[5])
w('    rw [e, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]')
w('    linarith')
w('  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4)] at h2')
w('  linarith')
w('')
w('end Tower.RV6')

open('Tower/RV6/DomG.lean', 'w', encoding='utf-8').write('\n'.join(OUT) + '\n')
print('wrote Tower/RV6/DomG.lean:', len(OUT), 'lines')
print('M_INF', M_INF, 'N0', N0, 'U_INF', U_INF, 'TSQ', TSQ, 'NB', NB)
