#!/usr/bin/env python3
"""Writes Tower/RV6/CuspModF.lean: the modular side of the cusp, a0 = pi^2/16, and ZhouF.

X(w) = xm(1/(6w)) = 8/xm(w); Phi_0(X) = X^2 A_0(X) = 48 a0 w^2 Z(w); by uniqueness of derivatives Phi_1(X) = -X^2 A_1(X) = m1F(w)
and Phi_2(X) = X^2 A_2(X) = m2F(w), explicit in w, Z, E, U, P, 1/P; m2F -> 96 a0/pi^2 as w -> inf, while Phi_2(X) -> 6
(tendsto_x2_hk_thF2): a0 = pi^2/16.  Every linear_combination certificate is produced by a recorded reduction modulo
P (1/P) = 1 and pi pi^(-1) = 1 and re-expanded to zero here; the limit uses a factorization of each monomial of m2F through
Z, P, 1/P, E, U, wE, wU, w^2 E, w^2 U, checked here.
usage: python3 tools/gen_cuspmodf.py  (from the repository root)
"""
import os
from fractions import Fraction


def add(p, q):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + v
    return {k: v for k, v in r.items() if v != 0}


def mul(p, q):
    r = {}
    for a, u in p.items():
        for b, v in q.items():
            k = tuple(sorted(a + b))
            r[k] = r.get(k, 0) + u * v
    return {k: v for k, v in r.items() if v != 0}


def sc(p, c):
    c = Fraction(c)
    return {k: v * c for k, v in p.items() if v * c != 0}


def at(n):
    return {(n,): Fraction(1)}


def cst(c):
    return {(): Fraction(c)} if c else {}


def prod(*ps):
    r = cst(1)
    for p in ps:
        r = mul(r, p)
    return r


w, Z, E, U, Pp, Pi, pi, pii, a0 = (at(n) for n in ('w', 'Z', 'E', 'U', 'P', 'Pi', 'pi', 'pii', 'a0'))
DER = {'w': cst(1), 'Z': sc(prod(pi, Z, E), -2), 'U': sc(prod(pi, U, add(E, sc(Pp, Fraction(1, 4)))), -2),
       'E': sc(prod(pi, add(add(sc(prod(E, E), Fraction(1, 2)), sc(prod(Z, U), -4)), sc(prod(U, U), -32))), -2),
       'P': sc(prod(pi, add(add(prod(E, Pp), sc(prod(Z, U), 40)), sc(prod(U, U), 256))), -2),
       'pi': {}, 'pii': {}, 'a0': {}, 'Phi1': {}, 'Phi2': {}}
DER['Pi'] = sc(prod(DER['P'], Pi, Pi), -1)


def D(p):
    r = {}
    for m, c in p.items():
        for i, a in enumerate(m):
            r = add(r, mul({m[:i] + m[i + 1:]: c}, DER[a]))
    return r


PAIRS = {'hP': ('P', 'Pi'), 'hpi': ('pi', 'pii')}


def rel(n):
    a1, b1 = PAIRS[n]
    return add(prod(at(a1), at(b1)), cst(-1))


def reduce(G, names):
    cof = {n: {} for n in names}
    G = dict(G)
    while True:
        hit = None
        for m, c in G.items():
            for n in names:
                a1, b1 = PAIRS[n]
                lst = list(m)
                if a1 in lst:
                    lst.remove(a1)
                    if b1 in lst:
                        lst.remove(b1)
                        hit = (n, {tuple(lst): c})
                        break
            if hit:
                break
        if not hit:
            return G, cof
        n, t = hit
        G = add(G, sc(mul(t, rel(n)), -1))
        cof[n] = add(cof[n], t)


def certify(G, names):
    R, cof = reduce(G, names)
    assert R == {}, ('not in the ideal', R)
    chk = dict(G)
    for n in names:
        chk = add(chk, sc(mul(cof[n], rel(n)), -1))
    assert chk == {}
    return cof


m1F = add(prod(cst(384), a0, pii, w, Z, Pi), sc(prod(a0, w, w, Z, E, Pi), -384))
m1dF, _ = reduce(D(m1F), ['hP'])
m2F, _ = reduce(prod(cst(4), pii, Pi, m1dF), ['hP', 'hpi'])
COF_m1d = certify(add(D(m1F), sc(m1dF, -1)), ['hP'])
Phi1, Phi2 = at('Phi1'), at('Phi2')
g0 = prod(cst(48), a0, w, w, Z)
hu = add(prod(sc(pi, Fraction(1, 4)), Pp, Phi1), sc(D(g0), -1))
COF_phi1 = certify(add(add(Phi1, sc(m1F, -1)), sc(mul(prod(cst(4), pii, Pi), hu), -1)), ['hP', 'hpi'])
hu1 = add(prod(sc(pi, Fraction(1, 4)), Pp, Phi2), sc(m1dF, -1))
COF_phi2 = certify(add(add(Phi2, sc(m2F, -1)), sc(mul(prod(cst(4), pii, Pi), hu1), -1)), ['hP', 'hpi'])

# ---- the limit: factor each monomial of m2F ----
LIMVAL = {'Z': Fraction(1), 'P': Fraction(4), 'Pi': Fraction(1, 4), 'E': 0, 'U': 0, 'WE': 0, 'WU': 0, 'W2E': 0, 'W2U': 0}


def factor(m):
    lst = list(m)
    k = lst.count('w')
    lst = [a for a in lst if a != 'w']
    out = []
    while k > 0:
        if k >= 2 and 'U' in lst:
            lst.remove('U'); out.append('W2U'); k -= 2
        elif k >= 2 and 'E' in lst and lst.count('E') == 1 and 'U' not in lst:
            lst.remove('E'); out.append('W2E'); k -= 2
        elif 'E' in lst:
            lst.remove('E'); out.append('WE'); k -= 1
        elif 'U' in lst:
            lst.remove('U'); out.append('WU'); k -= 1
        else:
            raise AssertionError(('w not absorbed', m))
    return [a for a in lst if a not in ('a0', 'pi', 'pii')] + out


limit_value = {}
for m, c in m2F.items():
    f = factor(m)
    v = c
    for a in f:
        v *= LIMVAL[a]
    if v:
        key = tuple(a for a in m if a in ('a0', 'pi', 'pii'))
        limit_value[key] = limit_value.get(key, 0) + v
assert limit_value == {('a0', 'pii', 'pii'): Fraction(96)}, limit_value

# ---- Lean text ----
ATOM = {'w': 'w', 'Z': 'Zax w', 'E': 'Eax w', 'U': 'Uax w', 'P': 'Pax w', 'Pi': '(Pax w)⁻¹',
        'Phi1': '(-(Xc w ^ 2 * hk thF1 (Xc w)))', 'Phi2': '(Xc w ^ 2 * hk thF2 (Xc w))'}
DNAME = {'w': 'dw', 'Z': 'dZ', 'E': 'dE', 'U': 'dU', 'P': 'dP', 'Pi': 'dPi'}
ORDER = ['w', 'Z', 'E', 'U', 'P', 'Pi', 'Phi1', 'Phi2']
LATOM = {'Z': ('tZ', 'Zax w'), 'P': ('tP', 'Pax w'), 'Pi': ('tPi', '(Pax w)⁻¹'), 'E': ('tE', 'Eax w'), 'U': ('tU', 'Uax w'),
         'WE': ('tWE', '(w * Eax w)'), 'WU': ('tWU', '(w * Uax w)'), 'W2E': ('tW2E', '(w ^ 2 * Eax w)'), 'W2U': ('tW2U', '(w ^ 2 * Uax w)')}
LVAL = {'Z': '1', 'P': '4', 'Pi': '4⁻¹', 'E': '0', 'U': '0', 'WE': '0', 'WU': '0', 'W2E': '0', 'W2U': '0'}


def coef(c, m):
    parts = ['(%d : ℝ)' % c.numerator if c.denominator == 1 else '(%d / %d : ℝ)' % (c.numerator, c.denominator)]
    na, npi, npii = m.count('a0'), m.count('pi'), m.count('pii')
    if na:
        parts.append('hk thF0 0' if na == 1 else 'hk thF0 0 ^ %d' % na)
    if npi:
        parts.append('π' if npi == 1 else 'π ^ %d' % npi)
    if npii:
        parts.append('π⁻¹' if npii == 1 else 'π⁻¹ ^ %d' % npii)
    return '(' + ' * '.join(parts) + ')'


def atoms_of(m):
    return sorted([a for a in m if a not in ('a0', 'pi', 'pii')], key=ORDER.index)


def poly_text(p):
    parts = []
    for m in sorted(p, key=lambda mm: (atoms_of(mm), mm)):
        rest = atoms_of(m)
        parts.append(coef(p[m], m) + (' * (' + ' * '.join(ATOM[a] for a in rest) + ')' if rest else ''))
    return ' + '.join(parts) if parts else '0'


def monos(p):
    return [(coef(p[m], m), atoms_of(m)) for m in sorted(p, key=lambda mm: (atoms_of(mm), mm))]


def def_body(p):
    return ' +\n    '.join('%s * (%s)' % (c, ' * '.join(ATOM[a] for a in rest)) for c, rest in monos(p))


def deriv_proof(p):
    L = []
    ms = monos(p)
    for i, (c, rest) in enumerate(ms):
        e = DNAME[rest[0]]
        for j, a in enumerate(rest[1:]):
            e = ('%s.mul %s' if j == 0 else '(%s).mul %s') % (e, DNAME[a])
        L.append('  have m%d := (%s).const_mul %s' % (i + 1, e, c))
    s = 'm1'
    for i in range(1, len(ms)):
        s = '(%s).add m%d' % (s, i + 1) if i > 1 else 'm1.add m2'
    L.append('  have h := %s' % s)
    return L


def lc(cof, extra=None):
    parts = [extra] if extra else []
    for n in ('hP', 'hpi'):
        if n in cof and cof[n]:
            parts.append('(%s) * %s' % (poly_text(cof[n]), n))
    return ' + '.join(parts)


def limit_proof(p):
    L = []
    terms_fun, terms_lim = [], []
    for i, (c, rest) in enumerate(monos(p)):
        m = [mm for mm in p if coef(p[mm], mm) == c and atoms_of(mm) == rest][0]
        f = factor(m)
        e = LATOM[f[0]][0]
        ftxt = [LATOM[f[0]][1]]
        ltxt = [LVAL[f[0]]]
        for j, a in enumerate(f[1:]):
            e = ('%s.mul %s' if j == 0 else '(%s).mul %s') % (e, LATOM[a][0])
            ftxt.append(LATOM[a][1])
            ltxt.append(LVAL[a])
        L.append('  have l%d := (%s).const_mul %s' % (i + 1, e, c))
        terms_fun.append('%s * (%s)' % (c, ' * '.join(ftxt)))
        terms_lim.append('%s * (%s)' % (c, ' * '.join(ltxt)))
    n = len(terms_fun)
    s = 'l1'
    for i in range(1, n):
        s = '(%s).add l%d' % (s, i + 1) if i > 1 else 'l1.add l2'
    L.append('  have h : Tendsto (fun w : ℝ =>')
    L.append('      ' + ' +\n        '.join(terms_fun) + ')')
    L.append('      atTop (nhds (' + ' + '.join(terms_lim) + ')) :=')
    L.append('    ' + s)
    L.append('  have e : (' + ' + '.join(terms_lim) + ' : ℝ) = 96 * hk thF0 0 * π⁻¹ ^ 2 := by ring')
    L.append('  rw [e] at h')
    L.append('  refine h.congr\' ?_')
    L.append('  filter_upwards with w')
    L.append('  unfold m2F')
    L.append('  ring')
    return L




def main():
    pre = PREAMBLE_TEXT
    L = pre.split('\n')
    L.append('/-- `Φ₁(X(w))`, explicitly. -/')
    L.append('noncomputable def m1F (w : ℝ) : ℝ :=')
    L.append('  ' + def_body(m1F))
    L.append('')
    L.append('/-- `m1F′`. -/')
    L.append('noncomputable def m1dF (w : ℝ) : ℝ :=')
    L.append('  ' + def_body(m1dF))
    L.append('')
    L.append('/-- `Φ₂(X(w))`, explicitly. -/')
    L.append('noncomputable def m2F (w : ℝ) : ℝ :=')
    L.append('  ' + def_body(m2F))
    L.append('')
    L.append('theorem hasDerivAt_m1F {w : ℝ} (hw : 0 < w) : HasDerivAt m1F (m1dF w) w := by')
    L.append("  have hP : Pax w * (Pax w)⁻¹ = 1 := mul_inv_cancel₀ (Pax_ne_zero hw)")
    L.append("  have dw : HasDerivAt (fun x : ℝ => x) 1 w := hasDerivAt_id' w")
    L.append('  have dZ := hasDerivAt_Zax hw')
    L.append('  have dE := hasDerivAt_Eax hw')
    L.append('  have dPi := (hasDerivAt_Pax hw).inv (Pax_ne_zero hw)')
    L += deriv_proof(m1F)
    L.append('  exact h.congr_deriv (by')
    L.append('    unfold m1dF')
    L.append('    simp only [Pi.mul_apply, Pi.inv_apply]')
    L.append('    linear_combination ' + lc(COF_m1d) + ')')
    L.append('')
    L.append('/-- **`Φ₁(X(w)) = m1F w`** (uniqueness of the derivative of `Φ₀(X(w)) = 48 a₀ w² Z(w)`). -/')
    L.append('theorem phi1_eq {w : ℝ} (hw : 0 < w) : -(Xc w ^ 2 * hk thF1 (Xc w)) = m1F w := by')
    L.append('  have hc := hasDerivAt_g0 hw')
    L.append('  have he : HasDerivAt (fun w : ℝ => 48 * hk thF0 0 * w ^ 2 * Zax w)')
    L.append('      (48 * hk thF0 0 * (2 * w) * Zax w + 48 * hk thF0 0 * w ^ 2 * (-(2 * π) * (Zax w * Eax w))) w :=')
    L.append('    ((hasDerivAt_sqx w).const_mul (48 * hk thF0 0)).mul (hasDerivAt_Zax hw)')
    L.append('  have heq : (fun w : ℝ => Xc w ^ 2 * hk thF0 (Xc w))')
    L.append('      =ᶠ[nhds w] (fun w : ℝ => 48 * hk thF0 0 * w ^ 2 * Zax w) := by')
    L.append('    filter_upwards [Ioi_mem_nhds hw] with s hs')
    L.append('    exact g0_eq hs')
    L.append('  have hu := hc.unique (he.congr_of_eventuallyEq heq)')
    L.append("  have hP : Pax w * (Pax w)⁻¹ = 1 := mul_inv_cancel₀ (Pax_ne_zero hw)")
    L.append("  have hpi : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero")
    L.append('  unfold m1F')
    L.append('  linear_combination ' + lc(COF_phi1, '(4 * π⁻¹ * (Pax w)⁻¹) * hu'))
    L.append('')
    L.append('/-- **`Φ₂(X(w)) = m2F w`**. -/')
    L.append('theorem phi2_eq {w : ℝ} (hw : 0 < w) : Xc w ^ 2 * hk thF2 (Xc w) = m2F w := by')
    L.append('  have hc := hasDerivAt_g1 hw')
    L.append('  have he := hasDerivAt_m1F hw')
    L.append('  have heq : (fun w : ℝ => -(Xc w ^ 2 * hk thF1 (Xc w))) =ᶠ[nhds w] m1F := by')
    L.append('    filter_upwards [Ioi_mem_nhds hw] with s hs')
    L.append('    exact phi1_eq hs')
    L.append('  have hu := hc.unique (he.congr_of_eventuallyEq heq)')
    L.append("  have hP : Pax w * (Pax w)⁻¹ = 1 := mul_inv_cancel₀ (Pax_ne_zero hw)")
    L.append("  have hpi : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero")
    L.append('  unfold m1dF at hu')
    L.append('  unfold m2F')
    L.append('  linear_combination ' + lc(COF_phi2, '(4 * π⁻¹ * (Pax w)⁻¹) * hu'))
    L.append('')
    L.append('/-- `m2F → 96 a₀/π²` as `w → ∞`. -/')
    L.append('theorem tendsto_m2F : Tendsto m2F atTop (nhds (96 * hk thF0 0 * π⁻¹ ^ 2)) := by')
    used = set()
    for mm in m2F:
        used |= set(factor(mm))
    SRC = {'Z': 'tendsto_Zax_atTop', 'P': 'tendsto_Pax_atTop', 'Pi': 'tendsto_inv_Pax_atTop', 'E': 'tendsto_Eax_atTop',
           'U': 'tendsto_Uax_atTop', 'WE': 'tendsto_mul_Eax', 'WU': 'tendsto_mul_Uax', 'W2E': 'tendsto_sq_Eax', 'W2U': 'tendsto_sq_Uax'}
    for a in ('Z', 'P', 'Pi', 'E', 'U', 'WE', 'WU', 'W2E', 'W2U'):
        if a in used:
            L.append('  have %s := %s' % (LATOM[a][0], SRC[a]))
    L += limit_proof(m2F)
    L.append('')
    L += POSTAMBLE.split('\n')
    text = '\n'.join(L)
    path = os.path.join('Tower', 'RV6', 'CuspModF.lean')
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(text)
    print('certificates checked; m1dF %d, m2F %d monomials; limit 96 a0/pi^2; wrote %s (%d lines)'
          % (len(m1dF), len(m2F), path, text.count('\n')))


PREAMBLE_TEXT = r'''import Mathlib
import Tower.RV6.CuspBesselF
import Tower.RV6.ZhouFa0
import Tower.RV6.PullbackF
import Tower.RV6.QTail
import Tower.RV6.BMBounds

/-!
# The modular side of the cusp: `a₀ = ∫₀^∞ t I₀K₀³ dt = π²/16`, hence `ZhouF`

With `X(w) = xm(1/(6w)) = 8/xm(w)` (`Xc`, `Xc_eq`), `X' = (π/4) P X` and `X → ∞`; `Φ₀ = x² A₀`, `Φ₁ = -x² A₁`,
`Φ₂ = x² A₂` (`A_k = hk(θᵏ f)`), so `d/dw Φ_k(X) = (π/4) P Φ_{k+1}(X)` (`hasDerivAt_g0`, `hasDerivAt_g1`):

* `g0_eq`: `Φ₀(X(w)) = 48 a₀ w² Z(w)` (`zhouF_a0`, `xm_sq`, `Uax_fricke`);
* `phi1_eq`, `phi2_eq`: by uniqueness of derivatives `Φ₁(X) = m1F`, `Φ₂(X) = m2F`, explicit in `w, Z, E, U, P, 1/P`;
* `tendsto_m2F`: `m2F → 96 a₀/π²` (`w² E, w² U → 0` from the `q`-series tail);
* **`a0_pi_sq`**: `a₀ = π²/16` (with `tendsto_x2_hk_thF2`), so **`zhouF`** and `rv6_of_zhou3`.

Generated by `tools/gen_cuspmodf.py`, which produces and checks every certificate in exact arithmetic.
-/

namespace Tower.RV6

open Real Filter MeasureTheory

/-! ## `X(w) = x(1/(6w))` -/

/-- `X(w) = x(1/(6w))`. -/
noncomputable def Xc (w : ℝ) : ℝ := xm (1 / (6 * w))

theorem Xc_pos (w : ℝ) : 0 < Xc w := xm_pos _

theorem Xc_eq {w : ℝ} (hw : 0 < w) : Xc w = 8 * (xm w)⁻¹ := by
  have h := xm_mul_fricke hw
  have hx : xm w * (xm w)⁻¹ = 1 := mul_inv_cancel₀ (xm_pos w).ne'
  unfold Xc
  linear_combination (xm w)⁻¹ * h + (-xm (1 / (6 * w))) * hx

theorem hasDerivAt_Xc {w : ℝ} (hw : 0 < w) : HasDerivAt Xc (π / 4 * Pax w * Xc w) w := by
  have h1 := ((hasDerivAt_xm hw).inv (xm_pos w).ne').const_mul 8
  have hx : xm w * (xm w)⁻¹ = 1 := mul_inv_cancel₀ (xm_pos w).ne'
  have hX := Xc_eq hw
  have h2 : HasDerivAt (fun y : ℝ => 8 * (xm y)⁻¹) (π / 4 * Pax w * Xc w) w := by
    refine h1.congr_deriv ?_
    rw [hX]
    linear_combination (2 * π * Pax w * (xm w)⁻¹) * hx
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hw] with s hs
  exact Xc_eq hs

theorem tendsto_Xc_atTop : Tendsto Xc atTop atTop := by
  have h1 : Tendsto xm atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_xm_atTop, Eventually.of_forall (fun y => xm_pos y)⟩
  have h2 : Tendsto (fun y : ℝ => 8 * (xm y)⁻¹) atTop atTop :=
    (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (by norm_num)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  exact (Xc_eq hw).symm

/-! ## `Φ₀`, `Φ₁` and the chain rule -/

theorem hasDerivAt_Phi0 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => x ^ 2 * hk thF0 x) (-(x * hk thF1 x)) x := by
  have h := (hasDerivAt_sqx x).mul (hasDerivAt_hk_thF0 hx)
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  exact h.congr_deriv (by
    linear_combination (-(x * (2 * hk thF0 x + hk thF1 x))) * hinv)

theorem hasDerivAt_Phi1 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(x ^ 2 * hk thF1 x)) (x * hk thF2 x) x := by
  have h := ((hasDerivAt_sqx x).mul (hasDerivAt_hk_thF1 hx)).neg
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  exact h.congr_deriv (by
    linear_combination (x * (2 * hk thF1 x + hk thF2 x)) * hinv)

theorem hasDerivAt_g0 {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun w : ℝ => Xc w ^ 2 * hk thF0 (Xc w))
      (π / 4 * Pax w * (-(Xc w ^ 2 * hk thF1 (Xc w)))) w := by
  have h := (hasDerivAt_Phi0 (Xc_pos w)).comp w (hasDerivAt_Xc hw)
  exact h.congr_deriv (by ring)

theorem hasDerivAt_g1 {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun w : ℝ => -(Xc w ^ 2 * hk thF1 (Xc w)))
      (π / 4 * Pax w * (Xc w ^ 2 * hk thF2 (Xc w))) w := by
  have h := (hasDerivAt_Phi1 (Xc_pos w)).comp w (hasDerivAt_Xc hw)
  exact h.congr_deriv (by ring)

/-! ## `Φ₀(X(w)) = 48 a₀ w² Z(w)` -/

theorem Uax_inv_six {w : ℝ} (hw : 0 < w) : Uax (1 / (6 * w)) = 3 / 4 * w ^ 2 * Zax w := by
  have hF := Uax_fricke hw
  have hw1 : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  rw [hF]
  linear_combination (-(Uax (1 / (6 * w)) * (w * w⁻¹ + 1))) * hw1

theorem g0_eq {w : ℝ} (hw : 0 < w) : Xc w ^ 2 * hk thF0 (Xc w) = 48 * hk thF0 0 * w ^ 2 * Zax w := by
  have hy : 0 < 1 / (6 * w) := one_div_pos.mpr (mul_pos (by norm_num) hw)
  have hA : hk thF0 (Xc w) = hk thF0 0 * Zax (1 / (6 * w)) := by
    have h := zhouF_a0 (1 / (6 * w)) hy
    rw [hjF_eq_hk, ← thF0_eq_fB] at h
    exact h
  have hX2 : Xc w ^ 2 * Zax (1 / (6 * w)) = 64 * Uax (1 / (6 * w)) := by
    unfold Xc
    rw [xm_sq hy]
    exact div_mul_cancel₀ _ (Zax_pos hy).ne'
  have hU := Uax_inv_six hw
  rw [hA]
  linear_combination (hk thF0 0) * hX2 + 64 * (hk thF0 0) * hU

/-! ## The atoms at `w → ∞` -/

theorem tendsto_sq_E2im_sub {d : ℝ} (hd : 1 ≤ d) :
    Tendsto (fun w : ℝ => w ^ 2 * (E2im (d * w) - 1)) atTop (nhds 0) := by
  have hS0 : 0 ≤ ∑' n : ℕ, |sig 1 n| * Real.exp (-(2 * π * (n : ℝ) * 1)) :=
    tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  have hlim : Tendsto (fun w : ℝ => 24 * (∑' n : ℕ, |sig 1 n| * Real.exp (-(2 * π * (n : ℝ) * 1)))
      * Real.exp (2 * π) * (w ^ 2 * Real.exp (-w))) atTop
      (nhds (24 * (∑' n : ℕ, |sig 1 n| * Real.exp (-(2 * π * (n : ℝ) * 1))) * Real.exp (2 * π) * 0)) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul _
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ((eventually_ge_atTop (1 : ℝ)).mono (fun w hw => ?_)) hlim
  have hdw : 1 ≤ d * w := by nlinarith
  have hq := qa_abs_le_tail (sig_abs_le 1) 1 (sig_zero_or 1) hdw
  have hE := E2im_eq_qa (lt_of_lt_of_le one_pos hdw)
  rw [Real.norm_eq_abs, hE]
  have e1 : w ^ 2 * (1 - 24 * qa (sig 1) (d * w) - 1) = -(24 * w ^ 2) * qa (sig 1) (d * w) := by ring
  rw [e1, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 24 * w ^ 2)]
  have hpd : 1 ≤ 2 * π * d := by nlinarith [Real.pi_gt_three]
  have hw2 : w ≤ 2 * π * d * w := by nlinarith
  have hexp : Real.exp (-(2 * π * 1 * (d * w - 1))) ≤ Real.exp (2 * π) * Real.exp (-w) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc 24 * w ^ 2 * |qa (sig 1) (d * w)|
      ≤ 24 * w ^ 2 * (Real.exp (-(2 * π * 1 * (d * w - 1)))
          * ∑' n : ℕ, |sig 1 n| * Real.exp (-(2 * π * (n : ℝ) * 1))) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ 24 * w ^ 2 * (Real.exp (2 * π) * Real.exp (-w)
          * ∑' n : ℕ, |sig 1 n| * Real.exp (-(2 * π * (n : ℝ) * 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hS0) (by positivity)
    _ = 24 * (∑' n : ℕ, |sig 1 n| * Real.exp (-(2 * π * (n : ℝ) * 1)))
          * Real.exp (2 * π) * (w ^ 2 * Real.exp (-w)) := by ring

theorem tendsto_sq_Eax : Tendsto (fun w : ℝ => w ^ 2 * Eax w) atTop (nhds 0) := by
  have h1 := tendsto_sq_E2im_sub (d := 1) le_rfl
  simp only [one_mul] at h1
  have h2 := tendsto_sq_E2im_sub (d := 2) (by norm_num)
  have h3 := tendsto_sq_E2im_sub (d := 3) (by norm_num)
  have h6 := tendsto_sq_E2im_sub (d := 6) (by norm_num)
  have h := (((h1.sub h2).add (h3.const_mul 3)).sub (h6.const_mul 3)).div_const 6
  have e : ((0 : ℝ) - 0 + 3 * 0 - 3 * 0) / 6 = 0 := by norm_num
  rw [e] at h
  refine h.congr' ?_
  filter_upwards with w
  unfold Eax
  ring

theorem tendsto_sq_Uax : Tendsto (fun w : ℝ => w ^ 2 * Uax w) atTop (nhds 0) := by
  have h1 := tendsto_sq_E2im_sub (d := 1) le_rfl
  simp only [one_mul] at h1
  have h2 := tendsto_sq_E2im_sub (d := 2) (by norm_num)
  have h3 := tendsto_sq_E2im_sub (d := 3) (by norm_num)
  have h6 := tendsto_sq_E2im_sub (d := 6) (by norm_num)
  have h := ((((h1.neg).add h2).add (h3.const_mul 3)).sub (h6.const_mul 3)).div_const 24
  have e : (-(0 : ℝ) + 0 + 3 * 0 - 3 * 0) / 24 = 0 := by norm_num
  rw [e] at h
  refine h.congr' ?_
  filter_upwards with w
  unfold Uax
  ring

theorem tendsto_div_w {f : ℝ → ℝ} (h : Tendsto (fun w : ℝ => w * f w) atTop (nhds 0)) :
    Tendsto f atTop (nhds 0) := by
  have h2 := h.mul tendsto_inv_atTop_zero
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  have hw1 : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  linear_combination (f w) * hw1

theorem tendsto_mul_Eax : Tendsto (fun w : ℝ => w * Eax w) atTop (nhds 0) :=
  tendsto_div_w (f := fun w : ℝ => w * Eax w) (tendsto_sq_Eax.congr (fun w => by
    show w ^ 2 * Eax w = w * (w * Eax w)
    ring))

theorem tendsto_mul_Uax : Tendsto (fun w : ℝ => w * Uax w) atTop (nhds 0) :=
  tendsto_div_w (f := fun w : ℝ => w * Uax w) (tendsto_sq_Uax.congr (fun w => by
    show w ^ 2 * Uax w = w * (w * Uax w)
    ring))

theorem tendsto_Eax_atTop : Tendsto Eax atTop (nhds 0) := tendsto_div_w tendsto_mul_Eax

theorem tendsto_Uax_atTop : Tendsto Uax atTop (nhds 0) := tendsto_div_w tendsto_mul_Uax

theorem tendsto_inv_Pax_atTop : Tendsto (fun w : ℝ => (Pax w)⁻¹) atTop (nhds 4⁻¹) :=
  tendsto_Pax_atTop.inv₀ (by norm_num)

/-! ## `Φ₁`, `Φ₂` explicitly -/
'''

POSTAMBLE = r'''/-- **`a₀ = ∫₀^∞ t I₀K₀³ dt = π²/16`**. -/
theorem a0_pi_sq : hk thF0 0 = π ^ 2 / 16 := by
  have h1 : Tendsto (fun w : ℝ => Xc w ^ 2 * hk thF2 (Xc w)) atTop (nhds 6) :=
    tendsto_x2_hk_thF2.comp tendsto_Xc_atTop
  have h2 : Tendsto (fun w : ℝ => Xc w ^ 2 * hk thF2 (Xc w)) atTop
      (nhds (96 * hk thF0 0 * π⁻¹ ^ 2)) := by
    refine tendsto_m2F.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    exact (phi2_eq hw).symm
  have h := tendsto_nhds_unique h2 h1
  have hpi : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  linear_combination (π ^ 2 / 96) * h + (-(hk thF0 0 * (π * π⁻¹ + 1))) * hpi

/-- The Bessel moment `∫₀^∞ t I₀(t) K₀(t)³ dt = π²/16`. -/
theorem integral_t_I0_K0_cube : ∫ t in Set.Ioi (0 : ℝ), t * (besselI0 t * besselK0 t ^ 3) = π ^ 2 / 16 := by
  rw [← hk_thF0_zero, a0_pi_sq]

/-- **Zhou's parametrisation of `hjF`.** -/
theorem zhouF : ZhouF := zhouF_of_const a0_pi_sq

/-- The six-step theorem from `RungBP` and `ZhouG`. -/
theorem rv6_of_zhou3 (hP : RungBP) (hG : ZhouG) : mu6 = 648 / π ^ 6 * Lf5 :=
  rv6_of_zhou2 hP zhouF hG

end Tower.RV6
'''

if __name__ == '__main__':
    main()
