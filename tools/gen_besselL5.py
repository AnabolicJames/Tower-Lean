#!/usr/bin/env python3
"""Writes Tower/RV6/BesselL5.lean: the fifth-order equation of f = I0 K0^3 and g = I0^2 K0^2.

Every algebraic step of the Lean file is checked here first, in exact rational arithmetic:
  * the ladder lemmas: (four-factor product-rule derivative) * t = R_k, in Q[t, I0, I1, K0, K1];
  * the theta-chain lemmas: D * t - T_(k+1) - c * (t * w - 1) = 0 in Q[t, w, e0..e4] with w = t^(-1) an independent
    variable, c being the linear_combination cofactor of `t * t⁻¹ = 1`;
  * the L5 identity of the theta-chain, in Q[t, e0..e4].
usage: python3 tools/gen_besselL5.py  (from the repository root)
"""
import os
from fractions import Fraction


class Poly:
    def __init__(self, n, d=None):
        self.n = n
        self.d = {k: Fraction(v) for k, v in (d or {}).items() if v != 0}

    @staticmethod
    def const(n, c):
        return Poly(n, {(0,) * n: Fraction(c)})

    @staticmethod
    def var(n, i):
        e = [0] * n
        e[i] = 1
        return Poly(n, {tuple(e): 1})

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

    def __mul__(self, o):
        o = self._c(o)
        d = {}
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                d[k] = d.get(k, 0) + v1 * v2
        return Poly(self.n, d)

    __rmul__ = __mul__

    def __pow__(self, m):
        r = Poly.const(self.n, 1)
        for _ in range(m):
            r = r * self
        return r

    def iszero(self):
        return not self.d


# monomials (coefficient, four factors); u = I0, p = t I1, v = K0, q = t K1
LADDER = {
    'F': [[(1, 'uvvv')],
          [(1, 'pvvv'), (-3, 'uvvq')],
          [(-3, 'pvvq'), (3, 'uvqq')],
          [(3, 'pvqq'), (-1, 'uqqq')],
          [(-1, 'pqqq')]],
    'G': [[(1, 'uuvv')],
          [(2, 'upvv'), (-2, 'uuvq')],
          [(1, 'ppvv'), (-4, 'upvq'), (1, 'uuqq')],
          [(2, 'upqq'), (-2, 'ppvq')],
          [(1, 'ppqq')]],
}
TPOW = [
    [(1, 0, 0)],
    [(1, 0, 1)],
    [(2, 0, 2), (4, 2, 0)],
    [(6, 0, 3), (10, 2, 1), (8, 2, 0)],
    [(24, 0, 4), (32, 2, 2), (28, 2, 1), (16, 2, 0), (40, 4, 0)],
    [(120, 2, 3), (120, 2, 2), (72, 2, 1), (32, 2, 0), (136, 4, 1), (272, 4, 0)],
]
L5 = [(1, 0, 5), (-20, 2, 3), (-60, 2, 2), (-72, 2, 1), (-32, 2, 0), (64, 4, 1), (128, 4, 0)]

# ---------------------------------------------------------------------------------------------------------------------
# exact checks
# ---------------------------------------------------------------------------------------------------------------------
N = 5  # t, I0, I1, K0, K1
tt, I0, I1, K0, K1 = (Poly.var(N, i) for i in range(N))
FAC = {'u': I0, 'p': tt * I1, 'v': K0, 'q': tt * K1}
DFAC = {'u': I1, 'p': tt * I0, 'v': -K1, 'q': -(tt * K0)}


def ldpoly(mons):
    s = Poly(N)
    for c, fs in mons:
        m = Poly.const(N, c)
        for ch in fs:
            m = m * FAC[ch]
        s = s + m
    return s


def check_ladder(name):
    ld = [ldpoly(m) for m in LADDER[name]]
    z = Poly(N)
    for k, mons in enumerate(LADDER[name]):
        D = Poly(N)
        for c, fs in mons:
            for i in range(4):
                m = Poly.const(N, c)
                for jj, ch in enumerate(fs):
                    m = m * (DFAC[ch] if jj == i else FAC[ch])
                D = D + m
        R = (k + 1) * (ld[k + 1] if k < 4 else z) + (5 - k) * tt * tt * (ld[k - 1] if k > 0 else z)
        assert (D * tt - R).iszero(), (name, k)


NC = 7  # t, w, E0..E4
ct, cw = Poly.var(NC, 0), Poly.var(NC, 1)
CE = [Poly.var(NC, 2 + j) for j in range(5)]


def Rj(j):
    z = Poly(NC)
    return (j + 1) * (CE[j + 1] if j < 4 else z) + (5 - j) * ct * ct * (CE[j - 1] if j > 0 else z)


def chain_cert(k):
    D = Poly(NC)
    c = Poly(NC)
    for co, m, j in TPOW[k]:
        dpow = Poly.const(NC, m) * ct ** (m - 1) if m else Poly(NC)
        D = D + co * (dpow * CE[j] + ct ** m * Rj(j) * cw)
        c = c + co * ct ** m * Rj(j)
    T1 = Poly(NC)
    for co, m, j in TPOW[k + 1]:
        T1 = T1 + co * ct ** m * CE[j]
    assert (D * ct - T1 - c * (ct * cw - 1)).iszero(), k
    return c


def check_L5():
    th = []
    for k in range(6):
        T = Poly(NC)
        for co, m, j in TPOW[k]:
            T = T + co * ct ** m * CE[j]
        th.append(T)
    # theta acts on the chain as T_(k+1); L5 in terms of the T_k is a polynomial identity in t, e0..e4
    L = Poly(NC)
    for co, m, k in L5:
        L = L + co * ct ** m * th[k]
    assert L.iszero()


# ---------------------------------------------------------------------------------------------------------------------
# Lean text
# ---------------------------------------------------------------------------------------------------------------------
LEANF = {'u': 'besselI0 {x}', 'p': '{x} * besselI1 {x}', 'v': 'besselK0 {x}', 'q': '{x} * besselK1 {x}'}
HYP = {'u': 'hu', 'p': 'hp', 'v': 'hv', 'q': 'hq'}
HYPDEF = {'u': 'hasDerivAt_besselI0 t', 'p': 'hasDerivAt_mul_besselI1 t',
          'v': 'hasDerivAt_besselK0 ht', 'q': 'hasDerivAt_mul_besselK1 ht'}


def fac_def(ch, x, e):
    s = LEANF[ch].format(x=x)
    if ch in 'pq':
        s = '(' + s + ')'
    return s if e == 1 else s + ' ^ %d' % e


def mon_def(c, fs, x):
    """the definition form: grouped powers"""
    parts = []
    for ch in 'upvq':
        e = fs.count(ch)
        if e:
            parts.append(fac_def(ch, x, e))
    body = ' * '.join(parts)
    return body if c == 1 else '(%d) * (%s)' % (c, body) if c < 0 else '%d * (%s)' % (c, body)


def mon_prod(fs, x):
    """the product form built by hasDerivAt_prod4"""
    return ' * '.join('(' + LEANF[ch].format(x=x) + ')' if ch in 'pq' else LEANF[ch].format(x=x) for ch in fs)


def wrap(head, terms, indent, tail='', width=100):
    """head + terms joined by ' + ', broken after ' +' so that no line exceeds width (where possible)."""
    lines = []
    cur = head
    for i, tm in enumerate(terms):
        piece = tm + (' +' if i < len(terms) - 1 else tail)
        if cur.strip() and len(cur) + 1 + len(piece) > width and cur != head:
            lines.append(cur)
            cur = ' ' * indent + piece
        else:
            cur = cur + ('' if cur.endswith(' ') or cur == '' else ' ') + piece
    lines.append(cur)
    return lines


def coef(c):
    return '(%d)' % c if c < 0 else '%d' % c


def Rtext(P, k):
    terms = []
    if k < 4:
        terms.append(('%s * ' % (k + 1) if k + 1 != 1 else '') + 'ld%s%d t' % (P, k + 1))
    if k > 0:
        terms.append(('%d * ' % (5 - k) if 5 - k != 1 else '') + 't ^ 2 * ld%s%d t' % (P, k - 1))
    s = ' + '.join(terms)
    return '(' + s + ') / t' if len(terms) > 1 else s + ' / t'


def single(k):
    return len(TPOW[k]) == 1 and TPOW[k][0][0] == 1 and TPOW[k][0][1] == 0


def tpow_term(co, m, j, P, x):
    base = 'ld%s%d %s' % (P, j, x) if m == 0 else '(%s ^ %d * ld%s%d %s)' % (x, m, P, j, x)
    return '%s * %s' % (coef(co), base)


def cert_text(c, P):
    out = []
    for k, v in sorted(c.d.items()):
        assert k[1] == 0 and sum(k[2:]) == 1
        j = [i for i in range(5) if k[2 + i] == 1][0]
        assert v.denominator == 1
        s = '%d' % v.numerator
        if k[0]:
            s += ' * t ^ %d' % k[0]
        s += ' * ld%s%d t' % (P, j)
        out.append(s)
    return ' + '.join(out)


def ladder_section(P, name_fun):
    L = []
    for k, mons in enumerate(LADDER[P]):
        L.append('/-- `e%d` of the ladder of `%s`. -/' % (k, name_fun))
        L.append('noncomputable def ld%s%d (t : ℝ) : ℝ :=' % (P, k))
        L += wrap('  ', [mon_def(c, fs, 't') for c, fs in mons], 4)
        L.append('')
    for k, mons in enumerate(LADDER[P]):
        need = sorted(set(''.join(fs for _, fs in mons)), key='upvq'.index)
        rhs = []
        if k < 4:
            rhs.append(('%d ' % (k + 1) if k + 1 != 1 else '') + 'e%d' % (k + 1))
        if k > 0:
            rhs.append(('%d ' % (5 - k) if 5 - k != 1 else '') + 't² e%d' % (k - 1))
        L.append('/-- `θ e%d = %s`, as `HasDerivAt` (`θ = t d/dt`). -/' % (k, ' + '.join(rhs)))
        L.append('theorem hasDerivAt_ld%s%d {t : ℝ} (ht : 0 < t) :' % (P, k))
        L.append('    HasDerivAt ld%s%d (%s) t := by' % (P, k, Rtext(P, k)))
        for ch in need:
            L.append('  have %s := %s' % (HYP[ch], HYPDEF[ch]))
        for i, (c, fs) in enumerate(mons):
            L.append('  have m%d := (hasDerivAt_prod4 %s).const_mul (%d : ℝ)' % (i + 1, ' '.join(HYP[ch] for ch in fs), c))
        expr = 'm1'
        for i in range(1, len(mons)):
            expr = '(%s).add m%d' % (expr, i + 1) if i > 1 else 'm1.add m2'
        L.append('  have h0 := %s' % expr)
        L.append('  have hfun : ld%s%d = fun x : ℝ =>' % (P, k))
        L += wrap('      ', ['%s * (%s)' % (coef(c), mon_prod(fs, 'x')) for c, fs in mons], 8, tail=' := by')
        L.append('    funext x')
        L.append('    unfold ld%s%d' % (P, k))
        L.append('    ring')
        L.append('  rw [hfun]')
        L.append('  refine h0.congr_deriv ?_')
        L.append('  beta_reduce')
        L.append('  rw [eq_div_iff ht.ne\']')
        names = []
        if k < 4:
            names.append('ld%s%d' % (P, k + 1))
        if k > 0:
            names.append('ld%s%d' % (P, k - 1))
        L.append('  unfold ' + ' '.join(names))
        L.append('  ring')
        L.append('')
    return L


def chain_section(P, fname):
    L = []
    for k in range(6):
        if single(k):
            body = 'ld%s%d t' % (P, TPOW[k][0][2])
        else:
            body = None
        L.append('/-- `θ^%d %s`. -/' % (k, fname))
        L.append('noncomputable def th%s%d (t : ℝ) : ℝ :=' % (P, k))
        if body is None:
            L += wrap('  ', [tpow_term(co, m, j, P, 't') for co, m, j in TPOW[k]], 4)
        else:
            L.append('  ' + body)
        L.append('')
    for k in range(5):
        c = chain_cert(k)
        js = sorted(set(j for _, _, j in TPOW[k]))
        ms = sorted(set(m for _, m, _ in TPOW[k] if m))
        L.append('theorem hasDerivAt_th%s%d {t : ℝ} (ht : 0 < t) : HasDerivAt th%s%d (th%s%d t / t) t := by'
                 % (P, k, P, k, P, k + 1))
        for j in js:
            L.append('  have e%d := hasDerivAt_ld%s%d ht' % (j, P, j))
        for m in ms:
            L.append('  have s%d := %s t' % (m, 'hasDerivAt_sqx' if m == 2 else 'hasDerivAt_powfour'))
        for i, (co, m, j) in enumerate(TPOW[k]):
            if single(k):
                pass
            elif m == 0:
                L.append('  have m%d := e%d.const_mul (%d : ℝ)' % (i + 1, j, co))
            else:
                L.append('  have m%d := (s%d.mul e%d).const_mul (%d : ℝ)' % (i + 1, m, j, co))
        n = len(TPOW[k])
        expr = 'm1' if not single(k) else 'e%d' % TPOW[k][0][2]
        for i in range(1, n):
            expr = '(%s).add m%d' % (expr, i + 1) if i > 1 else 'm1.add m2'
        L.append('  have h0 := %s' % expr)
        if single(k):
            L.append('  have hfun : th%s%d = ld%s%d := rfl' % (P, k, P, TPOW[k][0][2]))
        else:
            L.append('  have hfun : th%s%d = fun x : ℝ =>' % (P, k))
            L += wrap('      ', [tpow_term(co, m, j, P, 'x') for co, m, j in TPOW[k]], 8, tail=' := rfl')
        L.append('  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne\'')
        L.append('  rw [hfun]')
        L.append('  refine h0.congr_deriv ?_')
        L.append('  beta_reduce')
        L.append('  rw [eq_div_iff ht.ne\']')
        L.append('  unfold th%s%d' % (P, k + 1))
        ct_terms = cert_text(c, P).split(' + ')
        ct_terms[0] = '(' + ct_terms[0]
        L += wrap('  linear_combination ', ct_terms, 4, tail=') * hinv')
        L.append('')
    L.append('/-- **`L₅` annihilates the θ-chain**: `θ⁵ - 4t²(5θ³ + 15θ² + 18θ + 8) + 64t⁴(θ + 2)`. -/')
    L.append('theorem L5_th%s (t : ℝ) :' % P)
    L.append('    th%s5 t - 4 * t ^ 2 * (5 * th%s3 t + 15 * th%s2 t + 18 * th%s1 t + 8 * th%s0 t)' % ((P,) * 5))
    L.append('      + 64 * t ^ 4 * (th%s1 t + 2 * th%s0 t) = 0 := by' % (P, P))
    L.append('  unfold th%s5 th%s3 th%s2 th%s1 th%s0' % ((P,) * 5))
    L.append('  ring')
    L.append('')
    return L


def package(P, B):
    L = []
    L.append('theorem th%s0_eq_%s : th%s0 = %s := by' % (P, B, P, B))
    L.append('  funext x')
    L.append('  rfl')
    L.append('')
    L.append('/-- `L₅ %s = 0` on `t > 0`, as a chain of derivatives: `th%sk = θ^k %s` and the equation. -/' % (B, P, B))
    L.append('theorem l5_%s : th%s0 = %s ∧' % (B, P, B))
    L.append('    (∀ t : ℝ, 0 < t → HasDerivAt th%s0 (th%s1 t / t) t ∧ HasDerivAt th%s1 (th%s2 t / t) t ∧' % ((P,) * 4))
    L.append('      HasDerivAt th%s2 (th%s3 t / t) t ∧ HasDerivAt th%s3 (th%s4 t / t) t ∧' % ((P,) * 4))
    L.append('      HasDerivAt th%s4 (th%s5 t / t) t) ∧' % (P, P))
    L.append('    ∀ t : ℝ, th%s5 t - 4 * t ^ 2 * (5 * th%s3 t + 15 * th%s2 t + 18 * th%s1 t + 8 * th%s0 t)' % ((P,) * 5))
    L.append('      + 64 * t ^ 4 * (th%s1 t + 2 * th%s0 t) = 0 :=' % (P, P))
    L.append('  ⟨th%s0_eq_%s, fun _ ht => ⟨hasDerivAt_th%s0 ht, hasDerivAt_th%s1 ht, hasDerivAt_th%s2 ht,' % (P, B, P, P, P))
    L.append('    hasDerivAt_th%s3 ht, hasDerivAt_th%s4 ht⟩, L5_th%s⟩' % (P, P, P))
    L.append('')
    return L


HEADER = '''import Mathlib
import Tower.RV6.BesselI
import Tower.RV6.BesselK
import Tower.RV6.BesselW
import Tower.RV6.LadderB

/-!
# The fifth-order equation of `f = I₀ K₀³` and `g = I₀² K₀²`

With `θ = t d/dt`, `u = I₀`, `p = t I₁`, `v = K₀`, `q = t K₁`, the four derivative lemmas give, for `t > 0`,
`θu = p`, `θp = t²u`, `θv = -q`, `θq = -t²v`.  For a product of four factors put
`e_k = ∑_{|S| = k} ∏_{S} θ(factor) ∏_{not S} factor` (the ladder).  Then

`θ e_k = (k + 1) e_{k+1} + (5 - k) t² e_{k-1}`,  `e_{-1} = e_5 = 0`

(`hasDerivAt_ldFk`, `hasDerivAt_ldGk`, stated as `HasDerivAt e_k (R_k / t)`), with no use of the Wronskian.  The θ-powers of
`e₀` are explicit combinations of the ladder (`thFk`, `thGk`, with `HasDerivAt th_k (th_{k+1} t / t)`), and

`L₅ = θ⁵ - 4t²(5θ³ + 15θ² + 18θ + 8) + 64t⁴(θ + 2)`

annihilates them identically (`L5_thF`, `L5_thG`; it is `5! e₅ = 0`).  With `thF0 = fB`, `thG0 = gB`: `L₅ f = L₅ g = 0`
(`l5_fB`, `l5_gB`).  This is item 1 of the plan for `ZhouF` and `ZhouG`; the Hankel duals come next.

Generated by `tools/gen_besselL5.py`, which checks every identity and every `linear_combination` cofactor in exact rational
arithmetic first (`t⁻¹` an independent variable).
-/

namespace Tower.RV6

/-- The product rule for four factors. -/
theorem hasDerivAt_prod4 {a b c d : ℝ → ℝ} {a1 b1 c1 d1 t : ℝ} (ha : HasDerivAt a a1 t)
    (hb : HasDerivAt b b1 t) (hc : HasDerivAt c c1 t) (hd : HasDerivAt d d1 t) :
    HasDerivAt (fun x => a x * b x * c x * d x)
      (a1 * b t * c t * d t + a t * b1 * c t * d t + a t * b t * c1 * d t
        + a t * b t * c t * d1) t := by
  have h0 := ((ha.mul hb).mul hc).mul hd
  have h1 : HasDerivAt (fun x => a x * b x * c x * d x)
      (((a1 * b t + a t * b1) * c t + a t * b t * c1) * d t + a t * b t * c t * d1) t := h0
  exact h1.congr_deriv (by ring)

theorem hasDerivAt_sqx (t : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t :=
  (hasDerivAt_pow 2 t).congr_deriv (by norm_num)

theorem hasDerivAt_powfour (t : ℝ) : HasDerivAt (fun x : ℝ => x ^ 4) (4 * t ^ 3) t :=
  (hasDerivAt_pow 4 t).congr_deriv (by norm_num)

/-! ## `f = I₀ K₀³` -/

'''


def main():
    for P in 'FG':
        check_ladder(P)
    for k in range(5):
        chain_cert(k)
    check_L5()
    out = HEADER.split('\n')
    out += ladder_section('F', 'f = I₀ K₀³')
    out += chain_section('F', 'f')
    out += package('F', 'fB')
    out += ['/-! ## `g = I₀² K₀²` -/', '']
    out += ladder_section('G', 'g = I₀² K₀²')
    out += chain_section('G', 'g')
    out += package('G', 'gB')
    out += ['end Tower.RV6', '']
    text = '\n'.join(out)
    path = os.path.join('Tower', 'RV6', 'BesselL5.lean')
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(text)
    print('certificates checked; wrote %s (%d lines)' % (path, text.count('\n')))


if __name__ == '__main__':
    main()
