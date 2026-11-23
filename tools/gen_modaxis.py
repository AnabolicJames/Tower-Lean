#!/usr/bin/env python3
"""Generator of Tower/RV6/AxisEv.lean and Tower/RV6/ModAxis.lean.

The five relations Rf1..Rf4, Rf9 of Level6.lean are read from that file.  For each of them the generator
writes the proof that carries it to the imaginary axis, and for the identities of ModAxis.lean it computes
the constants of the `linear_combination` steps; every one of these steps is checked here in exact rational
arithmetic before the files are written.

Usage: python3 tools/gen_modaxis.py   (from the repository root)
"""
import re
from fractions import Fraction

LEVEL6 = 'Tower/RV6/Level6.lean'
OUT1 = 'Tower/RV6/AxisEv.lean'
OUT2 = 'Tower/RV6/ModAxis.lean'


# ----------------------------------------------------------------------------------------------------------
# exact polynomials
# ----------------------------------------------------------------------------------------------------------
class Poly:
    __slots__ = ('n', 'd')

    def __init__(self, n, d=None):
        self.n = n
        self.d = {k: v for k, v in (d or {}).items() if v != 0}

    @staticmethod
    def const(n, c):
        return Poly(n, {(0,) * n: Fraction(c)})

    @staticmethod
    def var(n, i):
        e = [0] * n
        e[i] = 1
        return Poly(n, {tuple(e): Fraction(1)})

    def _c(self, o):
        return o if isinstance(o, Poly) else Poly.const(self.n, o)

    def __add__(self, o):
        o = self._c(o)
        d = dict(self.d)
        for k, v in o.d.items():
            d[k] = d.get(k, 0) + v
        return Poly(self.n, d)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.n, {k: -v for k, v in self.d.items()})

    def __sub__(self, o):
        return self + (-self._c(o))

    def __rsub__(self, o):
        return self._c(o) + (-self)

    def __mul__(self, o):
        o = self._c(o)
        d = {}
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                d[k] = d.get(k, 0) + v1 * v2
        return Poly(self.n, d)

    __rmul__ = __mul__

    def __truediv__(self, c):
        return self * (Fraction(1) / Fraction(c))

    def iszero(self):
        return len(self.d) == 0


def read_Rf():
    src = open(LEVEL6, encoding='utf-8').read()
    out = {}
    for k in (1, 2, 3, 4, 9):
        m = re.search(r'noncomputable def Rf%d \(x1 x2 x3 x6 u1 u2 u3 u6 v1 v2 v3 v6 : PowerSeries ℝ\) : PowerSeries ℝ :=\n(.*?)\n\n' % k,
                      src, flags=re.S)
        assert m, k
        body = ' '.join(m.group(1).split())
        assert re.fullmatch(r'[0-9xu\s\(\)\+\-\*]+', body), body
        out[k] = body
    return out


BODIES = read_Rf()
IDX = (1, 2, 3, 6)
PAIRS = [(1, 1), (1, 2), (1, 3), (1, 6), (2, 2), (2, 3), (2, 6), (3, 3), (3, 6), (6, 6)]
UOF = {1: 1, 2: 2, 3: 3, 4: 6, 9: None}     # the E4 series of each relation


def lit(c):
    c = Fraction(c)
    assert c.denominator == 1
    return '(%d : ℝ)' % c.numerator


def frac(c):
    c = Fraction(c)
    if c.denominator == 1:
        return '(%d : ℝ)' % c.numerator
    return '(%d / %d : ℝ)' % (c.numerator, c.denominator)


def wrap_commas(terms, indent, width=92):
    """Join terms with commas, breaking lines after a comma."""
    lines = []
    cur = ''
    for t in terms:
        piece = t if not cur else ', ' + t
        if cur and len(indent) + len(cur) + len(piece) > width - 1:
            lines.append(cur + ',')
            cur = t
        else:
            cur += piece
    lines.append(cur)
    return ('\n' + indent).join(lines)


def wrap(terms, indent, width=90, sep=' + '):
    """Join terms with `sep`, breaking lines before the separator."""
    lines = []
    cur = ''
    for t in terms:
        piece = t if not cur else sep + t
        if cur and len(indent) + len(cur) + len(piece) > width:
            lines.append(cur)
            cur = (sep.strip() + ' ' + t) if sep.strip() else t
        else:
            cur += piece
    lines.append(cur)
    return ('\n' + indent).join(lines)


# ----------------------------------------------------------------------------------------------------------
# the relations in the variables M_d (= sum sigma_1(n) q^(dn)) and N (= sum sigma_3(n) q^(dn))
# ----------------------------------------------------------------------------------------------------------
def analyse(k):
    """Coefficients (a_d, c_ij, b) of the relation k after x_d = 1 - 24 M_d, u = 1 + 240 N."""
    names = ['M1', 'M2', 'M3', 'M6', 'N']
    n = 5
    V = {nm: Poly.var(n, i) for i, nm in enumerate(names)}
    env = {'x1': 1 - 24 * V['M1'], 'x2': 1 - 24 * V['M2'], 'x3': 1 - 24 * V['M3'], 'x6': 1 - 24 * V['M6']}
    for d in IDX:
        env['u%d' % d] = (1 + 240 * V['N']) if UOF[k] == d else Poly.const(n, 0)
    body = BODIES[k]
    for d in IDX:
        if UOF[k] != d:
            assert ('u%d' % d) not in body
    R = eval(body, {'__builtins__': {}}, env)
    pos = {1: 0, 2: 1, 3: 2, 6: 3}

    def mono(*ds):
        e = [0] * n
        for d in ds:
            e[pos[d]] += 1
        return tuple(e)

    a = {d: R.d.get(mono(d), Fraction(0)) for d in IDX}
    c = {p: R.d.get(mono(*p), Fraction(0)) for p in PAIRS}
    b = R.d.get((0, 0, 0, 0, 1), Fraction(0))
    # check: R is exactly the form with these coefficients (in particular no constant term)
    S = Poly(n)
    for d in IDX:
        S = S + a[d] * V['M%d' % d]
    for (i, j) in PAIRS:
        S = S + c[(i, j)] * V['M%d' % i] * V['M%d' % j]
    S = S + b * V['N']
    assert (R - S).iszero(), k
    return a, c, b


def axis_body(k):
    mp = {'x1': 'E2im y', 'x2': 'E2im (2 * y)', 'x3': 'E2im (3 * y)', 'x6': 'E2im (6 * y)',
          'u1': 'E4im y', 'u2': 'E4im (2 * y)', 'u3': 'E4im (3 * y)', 'u6': 'E4im (6 * y)'}
    return re.sub(r'\b(x1|x2|x3|x6|u1|u2|u3|u6)\b', lambda m: mp[m.group(1)], BODIES[k])


MSER = {1: 'S1', 2: 'sM2', 3: 'sM3', 6: 'sM6'}
NSER = {1: 'S3', 2: 'sN2', 3: 'sN3', 6: 'sN6'}
ABSM = {1: 'absS_S1', 2: 'absS_M2', 3: 'absS_M3', 6: 'absS_M6'}
ABSN = {1: 'absS_S3', 2: 'absS_N2', 3: 'absS_N3', 6: 'absS_N6'}
EVM = {1: 'evA_S1', 2: 'evA_M2', 3: 'evA_M3', 6: 'evA_M6'}
EVN = {1: 'evA_S3', 2: 'evA_N2', 3: 'evA_N3', 6: 'evA_N6'}
HPOS = {1: 'hy', 2: 'h2', 3: 'h3', 6: 'h6'}


def par(s):
    return '(%s)' % s if ' ' in s else s


def series_terms(coef_a, coef_c, coef_b, M, N):
    t = ['PowerSeries.C %s * %s' % (coef_a[d], M[d]) for d in IDX]
    t += ['PowerSeries.C %s * (%s * %s)' % (coef_c[p], M[p[0]], M[p[1]]) for p in PAIRS]
    t += ['PowerSeries.C %s * %s' % (coef_b, N)]
    return t


def real_terms(coef_a, coef_c, coef_b, M, N, fn):
    t = ['%s * %s' % (coef_a[d], fn(M[d])) for d in IDX]
    t += ['%s * (%s * %s)' % (coef_c[p], fn(M[p[0]]), fn(M[p[1]])) for p in PAIRS]
    t += ['%s * %s' % (coef_b, fn(N))]
    return t


def gen_axis_rel(k):
    a, c, b = analyse(k)
    dN = UOF[k] if UOF[k] is not None else 1
    ca = {d: lit(a[d]) for d in IDX}
    cc = {p: lit(c[p]) for p in PAIRS}
    cb = lit(b)
    ser = wrap(series_terms(ca, cc, cb, MSER, NSER[dN]), '        ')
    rw_e = ['e2_1_eq', 'e2_2_eq', 'e2_3_eq', 'e2_6_eq'] + (['e4_%d_eq' % dN] if UOF[k] is not None else [])
    args = wrap([ca[d] for d in IDX] + [cc[p] for p in PAIRS] + [cb], '    ', sep=' ')
    rw_ev = [EVM[d] for d in IDX] + [EVN[dN]]
    rw_E = ['E2im_eq_qa hy', 'E2im_eq_qa h2', 'E2im_eq_qa h3', 'E2im_eq_qa h6'] + (['E4im_eq_qa %s' % HPOS[dN]] if UOF[k] is not None else [])
    stmt = wrap(re.split(r'\s\+\s', axis_body(k)), '      ')
    return f"""/-- The relation `Rf{k}` of `Level6.lean` at `q = e^{{-2πy}}`. -/
theorem axis_Rf{k} {{y : ℝ}} (hy : 0 < y) :
    {stmt} = 0 := by
  have h2 : (0 : ℝ) < 2 * y := mul_pos (by norm_num) hy
  have h3 : (0 : ℝ) < 3 * y := mul_pos (by norm_num) hy
  have h6 : (0 : ℝ) < 6 * y := mul_pos (by norm_num) hy
  have hS : ({ser}
        : PowerSeries ℝ) = 0 := by
    have h := Rf{k}_eq_zero ram6
    unfold Rf{k} at h
    rw [{', '.join(rw_e)}] at h
    simp only [map_neg, map_ofNat, map_zero, map_one]
    linear_combination h
  have hev := evA_qform {args}
    {ABSM[1]} {ABSM[2]} {ABSM[3]} {ABSM[6]} {ABSN[dN]} hy
  rw [hS, evA_zero, {', '.join(rw_ev)}] at hev
  rw [{', '.join(rw_E)}]
  linear_combination (-1 : ℝ) * hev
"""


# ----------------------------------------------------------------------------------------------------------
# AxisEv.lean
# ----------------------------------------------------------------------------------------------------------
def gen_qform():
    A = {d: 'a%d' % d for d in IDX}
    C = {p: 'c%d%d' % p for p in PAIRS}
    M = {d: 'M%d' % d for d in IDX}
    H = {1: 'h1', 2: 'h2', 3: 'h3', 6: 'h6'}
    ser = wrap(series_terms(A, C, 'b', M, 'N'), '        ')
    rea = wrap(real_terms(A, C, 'b', M, 'N', lambda s: 'evA %s y' % s), '        ')
    lines = ['  have s1 := absS_C_mul a1 h1']
    prev = 's1'
    steps = []          # (sum hypothesis, AbsS proof of the new factor, coefficient)
    idx = 1
    for d in (2, 3, 6):
        idx += 1
        lines.append('  have s%d := absS_add %s (absS_C_mul a%d %s)' % (idx, prev, d, H[d]))
        steps.append((prev, H[d], 'a%d' % d))
        prev = 's%d' % idx
    for p in PAIRS:
        idx += 1
        pr = '(absS_mul %s %s)' % (H[p[0]], H[p[1]])
        lines.append('  have s%d := absS_add %s (absS_C_mul %s %s)' % (idx, prev, C[p], pr))
        steps.append((prev, pr, C[p]))
        prev = 's%d' % idx
    steps.append((prev, 'hN', 'b'))
    rws = ['evA_add_C_mul %s %s %s hy' % st for st in reversed(steps)]
    rws.append('evA_C_mul a1 M1 y')
    rws += ['evA_mul %s %s hy' % (H[p[0]], H[p[1]]) for p in PAIRS]
    rwtxt = wrap_commas(rws, '    ')
    return f"""/-- The value of a quadratic form in four series, plus a multiple of a fifth. -/
theorem evA_qform (a1 a2 a3 a6 c11 c12 c13 c16 c22 c23 c26 c33 c36 c66 b : ℝ)
    {{M1 M2 M3 M6 N : PowerSeries ℝ}} (h1 : AbsS M1) (h2 : AbsS M2) (h3 : AbsS M3) (h6 : AbsS M6)
    (hN : AbsS N) {{y : ℝ}} (hy : 0 < y) :
    evA ({ser}) y
      = {rea} := by
{chr(10).join(lines)}
  rw [{rwtxt}]
"""


HEAD1 = """import Mathlib
import Tower.RV6.LadderB

/-!
# Power series at `q = e^{-2πy}`: the relations of level six on the imaginary axis

`Level6.lean` proves nine polynomial relations among `E₂, E₄, E₆` at `X, X², X³, X⁶` in
`ℝ⟦X⟧`.  This file evaluates the five of them that involve `E₂` and `E₄` only at `q = e^{-2πy}`,
`y > 0`:

* `cfS F`, `AbsS F`, `evA F y`: the coefficients of a power series, absolute summability of
  `∑ cₙ e^{-2πny}` for every `y > 0`, and the value of that sum (`qa` of `QSeries.lean`);
* `evA_add`, `evA_C_mul`, `evA_mul` (the Cauchy product, `qa_mul`), `evA_expand`
  (`X ↦ X^d` is `y ↦ d y`, `qa_dilate`), `evA_qform`: the value of a quadratic form in four
  series;
* `axis_Rf1 … axis_Rf4`: `E₄(i d y)` for `d = 1, 2, 3, 6` as a quadratic form in the four
  numbers `E₂(iy), E₂(2iy), E₂(3iy), E₂(6iy)`;  `axis_Rf9`: the quadratic relation among these
  four numbers.

The relations are used in the variables `M_d = ∑ σ₁(n) X^{dn}`, `N_d = ∑ σ₃(n) X^{dn}`
(`E₂(X^d) = 1 - 24 M_d`, `E₄(X^d) = 1 + 240 N_d`), in which they have no constant term.

This file is written by `tools/gen_modaxis.py`, which reads the relations from `Level6.lean` and
checks every `linear_combination` in exact arithmetic.
-/

namespace Tower.RV6

open Real

/-! ## The value of a power series on the axis -/

/-- The coefficient sequence of a power series. -/
noncomputable def cfS (F : PowerSeries ℝ) (n : ℕ) : ℝ := PowerSeries.coeff n F

/-- `∑ |cₙ| e^{-2πny}` converges for every `y > 0`. -/
def AbsS (F : PowerSeries ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → Summable fun n : ℕ => |cfS F n| * Real.exp (-(2 * π * (n : ℝ) * y))

/-- The value `∑ cₙ e^{-2πny}` of a power series at `q = e^{-2πy}`. -/
noncomputable def evA (F : PowerSeries ℝ) (y : ℝ) : ℝ := qa (cfS F) y

theorem absS_of_le {F : PowerSeries ℝ} {B : ℝ} {K : ℕ}
    (h : ∀ n : ℕ, |cfS F n| ≤ B * (n : ℝ) ^ K) : AbsS F := by
  intro y hy
  have hs := summable_qa_abs h hy
  exact hs

theorem summable_of_absS {F : PowerSeries ℝ} (h : AbsS F) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => cfS F n * Real.exp (-(2 * π * (n : ℝ) * y)) :=
  summable_of_abs_axis (h y hy)

theorem cfS_add (F G : PowerSeries ℝ) (n : ℕ) : cfS (F + G) n = cfS F n + cfS G n := by
  unfold cfS
  rw [map_add]

theorem cfS_C_mul (c : ℝ) (F : PowerSeries ℝ) (n : ℕ) :
    cfS (PowerSeries.C c * F) n = c * cfS F n := by
  unfold cfS
  exact PowerSeries.coeff_C_mul n F c

theorem cfS_mul (F G : PowerSeries ℝ) (n : ℕ) :
    cfS (F * G) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, cfS F p.1 * cfS G p.2 := by
  unfold cfS
  exact PowerSeries.coeff_mul n F G

theorem cfS_expand (F : PowerSeries ℝ) (d : ℕ) (hd : d ≠ 0) :
    cfS (PowerSeries.expand d hd F) = fun n => if d ∣ n then cfS F (n / d) else 0 := by
  funext n
  unfold cfS
  exact PowerSeries.coeff_expand d hd F

/-! ## Absolute summability -/

theorem absS_add {F G : PowerSeries ℝ} (hF : AbsS F) (hG : AbsS G) : AbsS (F + G) := by
  intro y hy
  have hsum := (hF y hy).add (hG y hy)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
  · exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  · show |cfS (F + G) n| * Real.exp (-(2 * π * (n : ℝ) * y))
      ≤ |cfS F n| * Real.exp (-(2 * π * (n : ℝ) * y))
        + |cfS G n| * Real.exp (-(2 * π * (n : ℝ) * y))
    rw [cfS_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.exp_pos _).le

theorem absS_C_mul (c : ℝ) {F : PowerSeries ℝ} (hF : AbsS F) : AbsS (PowerSeries.C c * F) := by
  intro y hy
  have h := (hF y hy).mul_left |c|
  refine h.congr (fun n => ?_)
  show |c| * (|cfS F n| * Real.exp (-(2 * π * (n : ℝ) * y)))
    = |cfS (PowerSeries.C c * F) n| * Real.exp (-(2 * π * (n : ℝ) * y))
  rw [cfS_C_mul, abs_mul]
  ring

theorem absS_mul {F G : PowerSeries ℝ} (hF : AbsS F) (hG : AbsS G) : AbsS (F * G) := by
  intro y hy
  have hF1 : Summable fun n : ℕ => ‖cfS F n * Real.exp (-(2 * π * (n : ℝ) * y))‖ := by
    refine (hF y hy).congr (fun n => ?_)
    show |cfS F n| * Real.exp (-(2 * π * (n : ℝ) * y))
      = ‖cfS F n * Real.exp (-(2 * π * (n : ℝ) * y))‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hG1 : Summable fun n : ℕ => ‖cfS G n * Real.exp (-(2 * π * (n : ℝ) * y))‖ := by
    refine (hG y hy).congr (fun n => ?_)
    show |cfS G n| * Real.exp (-(2 * π * (n : ℝ) * y))
      = ‖cfS G n * Real.exp (-(2 * π * (n : ℝ) * y))‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hF1 hG1
  refine hs.congr (fun n => ?_)
  show ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        cfS F p.1 * Real.exp (-(2 * π * (p.1 : ℝ) * y))
          * (cfS G p.2 * Real.exp (-(2 * π * (p.2 : ℝ) * y)))‖
    = |cfS (F * G) n| * Real.exp (-(2 * π * (n : ℝ) * y))
  have hsum : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        cfS F p.1 * Real.exp (-(2 * π * (p.1 : ℝ) * y))
          * (cfS G p.2 * Real.exp (-(2 * π * (p.2 : ℝ) * y)))
      = cfS (F * G) n * Real.exp (-(2 * π * (n : ℝ) * y)) := by
    rw [cfS_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp1 : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have he : Real.exp (-(2 * π * (p.1 : ℝ) * y)) * Real.exp (-(2 * π * (p.2 : ℝ) * y))
        = Real.exp (-(2 * π * (n : ℝ) * y)) := by
      rw [← Real.exp_add, ← hp1]
      congr 1
      push_cast
      ring
    rw [← he]
    ring
  rw [hsum, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-! ## The value is additive and multiplicative -/

theorem evA_zero (y : ℝ) : evA 0 y = 0 := by
  have h : ∀ n : ℕ, cfS (0 : PowerSeries ℝ) n * Real.exp (-(2 * π * (n : ℝ) * y)) = 0 := by
    intro n
    unfold cfS
    rw [map_zero, zero_mul]
  unfold evA qa
  first
    | (rw [tsum_congr h]; exact tsum_zero)
    | simp only [h, tsum_zero]

theorem evA_add {F G : PowerSeries ℝ} (hF : AbsS F) (hG : AbsS G) {y : ℝ} (hy : 0 < y) :
    evA (F + G) y = evA F y + evA G y := by
  have h := qa_add (summable_of_absS hF hy) (summable_of_absS hG hy)
  have hc : cfS (F + G) = fun n => cfS F n + cfS G n := funext (cfS_add F G)
  unfold evA
  rw [hc]
  exact h

theorem evA_C_mul (c : ℝ) (F : PowerSeries ℝ) (y : ℝ) :
    evA (PowerSeries.C c * F) y = c * evA F y := by
  have hc : cfS (PowerSeries.C c * F) = fun n => c * cfS F n := funext (cfS_C_mul c F)
  unfold evA
  rw [hc]
  exact qa_const_mul c (cfS F) y

theorem evA_mul {F G : PowerSeries ℝ} (hF : AbsS F) (hG : AbsS G) {y : ℝ} (hy : 0 < y) :
    evA (F * G) y = evA F y * evA G y := by
  have h := qa_mul (hF y hy) (hG y hy)
  have hc : cfS (F * G)
      = fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, cfS F p.1 * cfS G p.2 :=
    funext (cfS_mul F G)
  unfold evA
  rw [hc]
  exact h.symm

theorem evA_add_C_mul {A G : PowerSeries ℝ} (hA : AbsS A) (hG : AbsS G) (c : ℝ) {y : ℝ}
    (hy : 0 < y) : evA (A + PowerSeries.C c * G) y = evA A y + c * evA G y := by
  rw [evA_add hA (absS_C_mul c hG) hy, evA_C_mul]

theorem evA_expand (F : PowerSeries ℝ) (d : ℕ) (hd : d ≠ 0) (y : ℝ) :
    evA (PowerSeries.expand d hd F) y = evA F ((d : ℝ) * y) := by
  unfold evA
  rw [cfS_expand F d hd]
  exact qa_dilate (cfS F) d (Nat.pos_of_ne_zero hd) y

theorem absS_expand {F : PowerSeries ℝ} {B : ℝ} {K : ℕ} (hB : 0 ≤ B)
    (hF : ∀ n : ℕ, |cfS F n| ≤ B * (n : ℝ) ^ K) (d : ℕ) (hd : d ≠ 0) :
    AbsS (PowerSeries.expand d hd F) := by
  refine absS_of_le (B := B) (K := K) (fun n => ?_)
  rw [cfS_expand F d hd]
  exact dil_abs_le hB hF d n

"""

MID1 = """
/-! ## The series of `σ₁` and `σ₃` and their dilates -/

theorem cfS_S1 : cfS S1 = sig 1 := funext (fun n => coeff_S1 n)

theorem cfS_S3 : cfS S3 = sig 3 := funext (fun n => coeff_S3 n)

theorem sig1_cfS_le (n : ℕ) : |cfS S1 n| ≤ 1 * (n : ℝ) ^ (1 + 1) := by
  rw [cfS_S1]
  exact sig_abs_le 1 n

theorem sig3_cfS_le (n : ℕ) : |cfS S3 n| ≤ 1 * (n : ℝ) ^ (3 + 1) := by
  rw [cfS_S3]
  exact sig_abs_le 3 n

theorem absS_S1 : AbsS S1 := absS_of_le sig1_cfS_le

theorem absS_S3 : AbsS S3 := absS_of_le sig3_cfS_le

/-- `∑ σ₁(n) X^{2n}`. -/
noncomputable def sM2 : PowerSeries ℝ := PowerSeries.expand 2 two_ne S1

/-- `∑ σ₁(n) X^{3n}`. -/
noncomputable def sM3 : PowerSeries ℝ := PowerSeries.expand 3 three_ne S1

/-- `∑ σ₁(n) X^{6n}`. -/
noncomputable def sM6 : PowerSeries ℝ := PowerSeries.expand 6 six_ne S1

/-- `∑ σ₃(n) X^{2n}`. -/
noncomputable def sN2 : PowerSeries ℝ := PowerSeries.expand 2 two_ne S3

/-- `∑ σ₃(n) X^{3n}`. -/
noncomputable def sN3 : PowerSeries ℝ := PowerSeries.expand 3 three_ne S3

/-- `∑ σ₃(n) X^{6n}`. -/
noncomputable def sN6 : PowerSeries ℝ := PowerSeries.expand 6 six_ne S3

theorem absS_M2 : AbsS sM2 := absS_expand zero_le_one sig1_cfS_le 2 two_ne

theorem absS_M3 : AbsS sM3 := absS_expand zero_le_one sig1_cfS_le 3 three_ne

theorem absS_M6 : AbsS sM6 := absS_expand zero_le_one sig1_cfS_le 6 six_ne

theorem absS_N2 : AbsS sN2 := absS_expand zero_le_one sig3_cfS_le 2 two_ne

theorem absS_N3 : AbsS sN3 := absS_expand zero_le_one sig3_cfS_le 3 three_ne

theorem absS_N6 : AbsS sN6 := absS_expand zero_le_one sig3_cfS_le 6 six_ne

theorem evA_S1 (y : ℝ) : evA S1 y = qa (sig 1) y := by
  unfold evA
  rw [cfS_S1]

theorem evA_S3 (y : ℝ) : evA S3 y = qa (sig 3) y := by
  unfold evA
  rw [cfS_S3]

theorem evA_M2 (y : ℝ) : evA sM2 y = qa (sig 1) (2 * y) := by
  have e := evA_expand S1 2 two_ne y
  rw [Nat.cast_ofNat, evA_S1] at e
  exact e

theorem evA_M3 (y : ℝ) : evA sM3 y = qa (sig 1) (3 * y) := by
  have e := evA_expand S1 3 three_ne y
  rw [Nat.cast_ofNat, evA_S1] at e
  exact e

theorem evA_M6 (y : ℝ) : evA sM6 y = qa (sig 1) (6 * y) := by
  have e := evA_expand S1 6 six_ne y
  rw [Nat.cast_ofNat, evA_S1] at e
  exact e

theorem evA_N2 (y : ℝ) : evA sN2 y = qa (sig 3) (2 * y) := by
  have e := evA_expand S3 2 two_ne y
  rw [Nat.cast_ofNat, evA_S3] at e
  exact e

theorem evA_N3 (y : ℝ) : evA sN3 y = qa (sig 3) (3 * y) := by
  have e := evA_expand S3 3 three_ne y
  rw [Nat.cast_ofNat, evA_S3] at e
  exact e

theorem evA_N6 (y : ℝ) : evA sN6 y = qa (sig 3) (6 * y) := by
  have e := evA_expand S3 6 six_ne y
  rw [Nat.cast_ofNat, evA_S3] at e
  exact e

theorem e2_1_eq : e2_1 = 1 - 24 * S1 := rfl

theorem e2_2_eq : e2_2 = 1 - 24 * sM2 := by
  unfold e2_2 xE sM2
  simp only [map_sub, map_mul, map_one, map_ofNat]

theorem e2_3_eq : e2_3 = 1 - 24 * sM3 := by
  unfold e2_3 xE sM3
  simp only [map_sub, map_mul, map_one, map_ofNat]

theorem e2_6_eq : e2_6 = 1 - 24 * sM6 := by
  unfold e2_6 xE sM6
  simp only [map_sub, map_mul, map_one, map_ofNat]

theorem e4_1_eq : e4_1 = 1 + 240 * S3 := rfl

theorem e4_2_eq : e4_2 = 1 + 240 * sN2 := by
  unfold e4_2 uE sN2
  simp only [map_add, map_mul, map_one, map_ofNat]

theorem e4_3_eq : e4_3 = 1 + 240 * sN3 := by
  unfold e4_3 uE sN3
  simp only [map_add, map_mul, map_one, map_ofNat]

theorem e4_6_eq : e4_6 = 1 + 240 * sN6 := by
  unfold e4_6 uE sN6
  simp only [map_add, map_mul, map_one, map_ofNat]

/-! ## The five relations on the axis -/

"""


# ----------------------------------------------------------------------------------------------------------
# ModAxis.lean: certificates
# ----------------------------------------------------------------------------------------------------------
def certificates():
    names = ['x1', 'x2', 'x3', 'x6', 'u1', 'u2', 'u3', 'u6']
    n = len(names)
    V = {nm: Poly.var(n, i) for i, nm in enumerate(names)}
    x1, x2, x3, x6, u1, u2, u3, u6 = (V[nm] for nm in names)
    Rf = {k: eval(BODIES[k], {'__builtins__': {}}, dict(V)) for k in BODIES}
    Z = (x1 - 4 * x2 - 3 * x3 + 12 * x6) / 6
    U = (-x1 + x2 + 3 * x3 - 3 * x6) / 24
    Pm = -x1 + 2 * x2 - 3 * x3 + 6 * x6
    E = (x1 - x2 + 3 * x3 - 3 * x6) / 6
    th = {1: (x1 * x1 - u1) / 12, 2: 2 * (x2 * x2 - u2) / 12, 3: 3 * (x3 * x3 - u3) / 12, 6: 6 * (x6 * x6 - u6) / 12}
    thZ = (th[1] - 4 * th[2] - 3 * th[3] + 12 * th[6]) / 6
    thU = (-th[1] + th[2] + 3 * th[3] - 3 * th[6]) / 24
    thE = (th[1] - th[2] + 3 * th[3] - 3 * th[6]) / 6
    key = {1: (0, 0, 0, 0, 1, 0, 0, 0), 2: (0, 0, 0, 0, 0, 1, 0, 0), 3: (0, 0, 0, 0, 0, 0, 1, 0), 4: (0, 0, 0, 0, 0, 0, 0, 1),
           9: (2, 0, 0, 0, 0, 0, 0, 0)}

    def solve(D):
        lam = {}
        rest = D
        for k in (1, 2, 3, 4, 9):
            lam[k] = rest.d.get(key[k], Fraction(0)) / Rf[k].d[key[k]]
            rest = rest - lam[k] * Rf[k]
        assert rest.iszero()
        return lam

    assert (Pm * Pm - 16 * Z * Z - 320 * Z * U - 1024 * U * U - Rf[9]).iszero()
    return {'Z': solve(thZ - Z * E), 'U': solve(thU - U * (E + Pm / 4)),
            'E': solve(thE - (E * E / 2 - 4 * Z * U - 32 * U * U)),
            'g4': solve(Fraction(2, 15) * (u1 - u2 - 9 * u3 + 9 * u6) - 8 * U * Pm)}


def lc(lam, pre=None):
    terms = ['%s * axis_Rf%d hy' % (frac(lam[k]), k) for k in (1, 2, 3, 4, 9)]
    body = wrap(terms, '      ', width=80)
    if pre is None:
        return body
    return '%s * (%s)' % (pre, body)


DER = {1: 'dE1 y', 2: 'dE2 2 y', 3: 'dE2 3 y', 6: 'dE2 6 y'}
ARG = {1: 'E2im t', 2: 'E2im (2 * t)', 3: 'E2im (3 * t)', 6: 'E2im (6 * t)'}


def gen_deriv(name, unf, coeffs, den, target, cert_line, doc):
    """coeffs: list of (sign, multiplier, d) in order d = 1, 2, 3, 6; the function is (sum)/den."""
    fun = ''
    der = ''
    proof = ''
    lines = []
    first = True
    hyp = {1: 'h1', 2: 'h2', 3: 'h3', 6: 'h6'}
    prev = None
    step = 0
    for sgn, mul, d in coeffs:
        fterm = ARG[d] if mul == 1 else '%d * %s' % (mul, ARG[d])
        dterm = DER[d] if mul == 1 else '%d * %s' % (mul, DER[d])
        hterm = hyp[d] if mul == 1 else '(%s.const_mul %d)' % (hyp[d], mul)
        if first:
            if sgn < 0:
                fun = '-%s' % fterm
                der = '-%s' % dterm
                cur = '%s.neg' % hyp[d]
                assert mul == 1
            else:
                fun = fterm
                der = dterm
                cur = hterm
            first = False
            step += 1
            lines.append('  have k%d : HasDerivAt\n      (fun t : ℝ => %s)\n      (%s) y := %s' % (step, fun, der, cur))
        else:
            op = ' + ' if sgn > 0 else ' - '
            fun = fun + op + fterm
            der = der + op + dterm
            comb = 'add' if sgn > 0 else 'sub'
            step += 1
            lines.append('  have k%d : HasDerivAt\n      (fun t : ℝ => %s)\n      (%s) y := k%d.%s %s' % (step, fun, der, step - 1, comb, hterm))
    step += 1
    lines.append('  have k%d : HasDerivAt\n      (fun t : ℝ => (%s) / %d)\n      ((%s) / %d) y := k%d.div_const %d' % (step, fun, den, der, den, step - 1, den))
    return f"""/-- {doc} -/
theorem hasDerivAt_{name} {{y : ℝ}} (hy : 0 < y) :
    HasDerivAt {name} ({target}) y := by
  have h1 : HasDerivAt E2im (dE1 y) y := hasDerivAt_E2im hy
  have h2 := hasDerivAt_E2im_mul 2 (by norm_num) hy
  have h3 := hasDerivAt_E2im_mul 3 (by norm_num) hy
  have h6 := hasDerivAt_E2im_mul 6 (by norm_num) hy
{chr(10).join(lines)}
  have kf : HasDerivAt {name}
      (({der}) / {den}) y := k{step}
  have e : ({der}) / {den}
      = {target} := by
    unfold dE1 dE2 {unf}
    linear_combination {cert_line}
  exact kf.congr_deriv e
"""


def check_final(cert):
    """The four final identities, with pi as a variable, in exact arithmetic."""
    names = ['x1', 'x2', 'x3', 'x6', 'u1', 'u2', 'u3', 'u6', 'pi']
    n = len(names)
    V = {nm: Poly.var(n, i) for i, nm in enumerate(names)}
    x1, x2, x3, x6, u1, u2, u3, u6, pi = (V[nm] for nm in names)
    env = {nm: V[nm] for nm in names[:8]}
    Rf = {k: eval(BODIES[k], {'__builtins__': {}}, dict(env)) for k in BODIES}
    Z = (x1 - 4 * x2 - 3 * x3 + 12 * x6) / 6
    U = (-x1 + x2 + 3 * x3 - 3 * x6) / 24
    Pm = -x1 + 2 * x2 - 3 * x3 + 6 * x6
    E = (x1 - x2 + 3 * x3 - 3 * x6) / 6
    D = {1: -(pi / 6) * (x1 * x1 - u1), 2: -(pi * 2 / 6) * (x2 * x2 - u2), 3: -(pi * 3 / 6) * (x3 * x3 - u3),
         6: -(pi * 6 / 6) * (x6 * x6 - u6)}

    def comb(lam):
        r = Poly(n)
        for k in (1, 2, 3, 4, 9):
            r = r + lam[k] * Rf[k]
        return r

    dZ = (D[1] - 4 * D[2] - 3 * D[3] + 12 * D[6]) / 6
    assert (dZ - (-(2 * pi) * (Z * E)) - (-(2 * pi)) * comb(cert['Z'])).iszero()
    dU = (-D[1] + D[2] + 3 * D[3] - 3 * D[6]) / 24
    assert (dU - (-(2 * pi) * (U * (E + Pm / 4))) - (-(2 * pi)) * comb(cert['U'])).iszero()
    dE = (D[1] - D[2] + 3 * D[3] - 3 * D[6]) / 6
    assert (dE - (-(2 * pi) * (E * E / 2 - 4 * Z * U - 32 * U * U)) - (-(2 * pi)) * comb(cert['E'])).iszero()
    g4 = Fraction(2, 15) * (u1 - u2 - 9 * u3 + 9 * u6)
    assert (g4 - 8 * U * Pm - comb(cert['g4'])).iszero()
    assert (Pm * Pm - (16 * Z * Z + 320 * Z * U + 1024 * U * U) - Rf[9]).iszero()


HEAD2 = """import Mathlib
import Tower.RV6.AxisEv

/-!
# The four functions of the modular side of Rung B on the imaginary axis

With `e_d = E₂(i d y)` (`E2im (d * y)` of `EisAxis.lean`):

* `Zax = (e₁ - 4e₂ - 3e₃ + 12e₆)/6`, the weight-two form `η(τ)⁴η(3τ)⁴/(η(2τ)²η(6τ)²)` of the
  paper (here it is *defined* as this Eisenstein combination; no eta product is used);
* `Uax = (-e₁ + e₂ + 3e₃ - 3e₆)/24`, the form `x² Z/64`;
* `Pax = -e₁ + 2e₂ - 3e₃ + 6e₆`, the paper's `P`;
* `Eax = (e₁ - e₂ + 3e₃ - 3e₆)/6`, the logarithmic derivative `q d/dq log Z`.

Proved here, from the relations `axis_Rf1 … axis_Rf9` and Ramanujan's identity on the axis:

* `Pax_sq : P² = 16 Z² + 320 Z U + 1024 U²` (so `P = (Z/2) √((x²+4)(x²+16))` with
  `x² = 64U/Z`);
* `hasDerivAt_Zax : Z' = -2π Z E`,  `hasDerivAt_Uax : U' = -2π U (E + P/4)`,
  `hasDerivAt_Eax : E' = -2π (E²/2 - 4ZU - 32U²)`;
* `g4_eq_UP : g₄(iy) = 8 U P` for the `g₄` of `Defs.lean`.

This file is written by `tools/gen_modaxis.py`; the constants of every `linear_combination` are
computed and checked there in exact arithmetic.
-/

namespace Tower.RV6

open Real

/-! ## The derivative of `E₂(i d y)` -/

/-- Ramanujan's identity as a derivative on the axis: `d/dy E₂(iy) = -(π/6)(E₂² - E₄)`. -/
theorem hasDerivAt_E2im {y : ℝ} (hy : 0 < y) :
    HasDerivAt E2im (-(π / 6) * (E2im y ^ 2 - E4im y)) y := by
  have h := hasDerivAt_const_add_qa (polyBdd_sig 1) (g := E2im) (a := 1) (b := -24)
    (fun t ht => by rw [E2im_eq_qa ht]; ring) hy
  have r := ram2_axis hy
  have e : -(2 * π) * (-24 * qa (fun n => (n : ℝ) * sig 1 n) y)
      = -(π / 6) * (E2im y ^ 2 - E4im y) := by
    linear_combination (-(2 * π)) * r
  exact h.congr_deriv e

/-- The derivative of `E₂(iy)` in `y`. -/
noncomputable def dE1 (y : ℝ) : ℝ := -(π / 6) * (E2im y ^ 2 - E4im y)

/-- The derivative of `E₂(i d y)` in `y`. -/
noncomputable def dE2 (d y : ℝ) : ℝ := -(π * d / 6) * (E2im (d * y) ^ 2 - E4im (d * y))

theorem hasDerivAt_E2im_mul (d : ℝ) (hd : 0 < d) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => E2im (d * t)) (dE2 d y) y := by
  have h0 := hasDerivAt_E2im (mul_pos hd hy)
  have hlin : HasDerivAt (fun t : ℝ => d * t) (d * 1) y := (hasDerivAt_id' y).const_mul d
  have hc := HasDerivAt.comp y h0 hlin
  have e : -(π / 6) * (E2im (d * y) ^ 2 - E4im (d * y)) * (d * 1)
      = -(π * d / 6) * (E2im (d * y) ^ 2 - E4im (d * y)) := by ring
  have hc2 := hc.congr_deriv e
  exact hc2

/-! ## The four functions -/

/-- `Z(iy) = (E₂(iy) - 4E₂(2iy) - 3E₂(3iy) + 12E₂(6iy))/6`. -/
noncomputable def Zax (y : ℝ) : ℝ :=
  (E2im y - 4 * E2im (2 * y) - 3 * E2im (3 * y) + 12 * E2im (6 * y)) / 6

/-- `U(iy) = (-E₂(iy) + E₂(2iy) + 3E₂(3iy) - 3E₂(6iy))/24`. -/
noncomputable def Uax (y : ℝ) : ℝ :=
  (-E2im y + E2im (2 * y) + 3 * E2im (3 * y) - 3 * E2im (6 * y)) / 24

/-- `P(iy) = -E₂(iy) + 2E₂(2iy) - 3E₂(3iy) + 6E₂(6iy)`. -/
noncomputable def Pax (y : ℝ) : ℝ :=
  -E2im y + 2 * E2im (2 * y) - 3 * E2im (3 * y) + 6 * E2im (6 * y)

/-- `E(iy) = (E₂(iy) - E₂(2iy) + 3E₂(3iy) - 3E₂(6iy))/6`. -/
noncomputable def Eax (y : ℝ) : ℝ :=
  (E2im y - E2im (2 * y) + 3 * E2im (3 * y) - 3 * E2im (6 * y)) / 6

/-- The quadratic relation of level six: `P² = 16 Z² + 320 Z U + 1024 U²`. -/
theorem Pax_sq {y : ℝ} (hy : 0 < y) :
    Pax y ^ 2 = 16 * Zax y ^ 2 + 320 * Zax y * Uax y + 1024 * Uax y ^ 2 := by
  unfold Pax Zax Uax
  linear_combination axis_Rf9 hy

"""


def main():
    cert = certificates()
    check_final(cert)
    # AxisEv.lean
    out = HEAD1 + gen_qform() + MID1
    out += '\n'.join(gen_axis_rel(k) for k in (1, 2, 3, 4, 9))
    out += '\nend Tower.RV6\n'
    open(OUT1, 'w', encoding='utf-8').write(out)
    # ModAxis.lean
    out = HEAD2
    out += gen_deriv('Zax', 'Zax Eax', [(1, 1, 1), (-1, 4, 2), (-1, 3, 3), (1, 12, 6)], 6,
                     '-(2 * π) * (Zax y * Eax y)', lc(cert['Z'], '(-(2 * π))'), "`Z' = -2π Z E`.")
    out += '\n'
    out += gen_deriv('Uax', 'Uax Eax Pax', [(-1, 1, 1), (1, 1, 2), (1, 3, 3), (-1, 3, 6)], 24,
                     '-(2 * π) * (Uax y * (Eax y + Pax y / 4))', lc(cert['U'], '(-(2 * π))'), "`U' = -2π U (E + P/4)`.")
    out += '\n'
    out += gen_deriv('Eax', 'Eax Zax Uax', [(1, 1, 1), (-1, 1, 2), (1, 3, 3), (-1, 3, 6)], 6,
                     '-(2 * π) * (Eax y ^ 2 / 2 - 4 * Zax y * Uax y - 32 * Uax y ^ 2)', lc(cert['E'], '(-(2 * π))'),
                     "`E' = -2π (E²/2 - 4ZU - 32U²)`.")
    out += f"""
/-- `g₄(iy) = 8 U(iy) P(iy)` for the `g₄` of `Defs.lean`. -/
theorem g4_eq_UP {{y : ℝ}} (hy : 0 < y) : g4 y = 8 * Uax y * Pax y := by
  rw [g4_eq_g4E hy]
  unfold g4E Uax Pax
  linear_combination {lc(cert['g4'])}

end Tower.RV6
"""
    open(OUT2, 'w', encoding='utf-8').write(out)
    for nm in ('Z', 'U', 'E', 'g4'):
        print(nm, {k: str(v) for k, v in cert[nm].items()})
    for k in (1, 2, 3, 4, 9):
        a, c, b = analyse(k)
        print('Rf%d' % k, [str(a[d]) for d in IDX], [str(c[p]) for p in PAIRS], str(b))


if __name__ == '__main__':
    main()
