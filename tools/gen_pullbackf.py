#!/usr/bin/env python3
"""Writes Tower/RV6/PullbackF.lean: hjF(xm y) / Zax y is a quadratic in y.

D = d/dy.  Atoms: A_k = hk thF_k (xm y), P, Z, E, U = Pax, Zax, Eax, Uax at y, W = (Zax y)^(-1), x = xm y.
DA_k = (pi/4) P (2 A_k + A_(k+1)), DZ = -2 pi Z E, DU = -2 pi U (E + P/4), DE = -2 pi (E^2/2 - 4 Z U - 32 U^2),
DP = -2 pi (E P + 40 Z U + 256 U^2), DW = 2 pi Z E W^2 (HasDerivAt.inv).  h0 = A_0 W, h1, h2 as below; D h2 = -(pi^3/256) P Z uF(x).
Each linear_combination certificate is produced by a recorded reduction modulo Z W - 1, P^2 - Q, x^2 - 64 U W and the
identity re-expanded to zero here, in exact arithmetic.
usage: python3 tools/gen_pullbackf.py  (from the repository root)
"""
import os
from fractions import Fraction

# ---- polynomials: {monomial (sorted tuple of atom names): Fraction} ----


def P_(d):
    return {k: Fraction(v) for k, v in d.items() if v != 0}


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


pi, Pp, Z, E, U, W, X = at('pi'), at('P'), at('Z'), at('E'), at('U'), at('W'), at('x')
A = [at('A%d' % k) for k in range(5)]

DER = {
    'Z': sc(prod(pi, Z, E), -2),
    'U': sc(prod(pi, U, add(E, sc(Pp, Fraction(1, 4)))), -2),
    'E': sc(prod(pi, add(add(sc(prod(E, E), Fraction(1, 2)), sc(prod(Z, U), -4)), sc(prod(U, U), -32))), -2),
    'P': sc(prod(pi, add(add(prod(E, Pp), sc(prod(Z, U), 40)), sc(prod(U, U), 256))), -2),
    'W': sc(prod(pi, Z, E, W, W), 2),
    'pi': {},
}
for k in range(4):
    DER['A%d' % k] = prod(sc(pi, Fraction(1, 4)), Pp, add(sc(A[k], 2), A[k + 1]))


def D(p):
    r = {}
    for m, c in p.items():
        for i, a in enumerate(m):
            rest = {m[:i] + m[i + 1:]: c}
            r = add(r, mul(rest, DER[a]))
    return r


Q = add(add(sc(prod(Z, Z), 16), sc(prod(Z, U), 320)), sc(prod(U, U), 1024))
RULES = [  # (name, lead monomial, relation polynomial = lead - replacement)
    ('hx2', ('x', 'x'), add(prod(X, X), sc(prod(U, W), -64))),
    ('hP2', ('P', 'P'), add(prod(Pp, Pp), sc(Q, -1))),
    ('hinv', ('W', 'Z'), add(prod(Z, W), cst(-1))),
]


def divides(lead, m):
    m = list(m)
    for a in lead:
        if a in m:
            m.remove(a)
        else:
            return None
    return tuple(m)


def reduce(G, names):
    cof = {n: {} for n in names}
    G = dict(G)
    while True:
        hit = None
        for m, c in G.items():
            for n, lead, rel in RULES:
                if n not in names:
                    continue
                q = divides(lead, m)
                if q is not None:
                    hit = (n, rel, {q: c})
                    break
            if hit:
                break
        if not hit:
            return G, cof
        n, rel, t = hit
        G = add(G, sc(mul(t, rel), -1))
        cof[n] = add(cof[n], t)


def certify(G, names):
    R, cof = reduce(G, names)
    assert R == {}, ('not in the ideal', R)
    chk = dict(G)
    for n, lead, rel in RULES:
        if n in names:
            chk = add(chk, sc(mul(cof[n], rel), -1))
    assert chk == {}, 'cofactor check'
    return cof


# h0, h1, h2
h0 = prod(A[0], W)
h1 = prod(sc(pi, Fraction(1, 4)), add(add(sc(prod(E, A[0]), 8), sc(prod(Pp, A[0]), 2)), prod(Pp, A[1])), W)
h2, _ = reduce(D(h1), ['hinv'])
uF = add(add(add(mul(add(add(sc(prod(X, X, X, X), -1), sc(prod(X, X), -20)), cst(-64)), A[3]),
                 mul(add(sc(prod(X, X), -60), cst(-384)), A[2])),
             mul(add(sc(prod(X, X), -72), cst(-768)), A[1])),
         mul(add(sc(prod(X, X), -32), cst(-512)), A[0]))
target3 = sc(prod(pi, pi, pi, Pp, Z, uF), Fraction(-1, 256))

COF0 = certify(add(D(h0), sc(h1, -1)), ['hinv'])
COF1 = certify(add(D(h1), sc(h2, -1)), ['hinv'])
COF2 = certify(add(D(h2), sc(target3, -1)), ['hx2', 'hP2', 'hinv'])

# ---- Lean text ----
ATOM = {'P': 'Pax y', 'Z': 'Zax y', 'E': 'Eax y', 'U': 'Uax y', 'W': '(Zax y)⁻¹', 'x': 'xm y', 'pi': 'π'}
for k in range(5):
    ATOM['A%d' % k] = 'hk thF%d (xm y)' % k
DNAME = {'P': 'dP', 'Z': 'dZ', 'E': 'dE', 'U': 'dU', 'W': 'dW', 'A0': 'dA0', 'A1': 'dA1', 'A2': 'dA2'}
ORDER = ['A0', 'A1', 'A2', 'A3', 'A4', 'P', 'Z', 'E', 'U', 'W', 'x']


def ctext(c):
    c = Fraction(c)
    if c.denominator == 1:
        return '(%d : ℝ)' % c.numerator
    return '(%d / %d : ℝ)' % (c.numerator, c.denominator)


def split(m):
    k = m.count('pi')
    rest = sorted([a for a in m if a != 'pi'], key=ORDER.index)
    return k, rest


def coef_text(c, k):
    s = ctext(c)
    if k == 1:
        s += ' * π'
    elif k > 1:
        s += ' * π ^ %d' % k
    return '(' + s + ')'


def prod_text(rest):
    return ' * '.join(ATOM[a] for a in rest)


def poly_text(p):
    if not p:
        return '0'
    parts = []
    for m in sorted(p, key=lambda mm: (split(mm)[1], split(mm)[0])):
        k, rest = split(m)
        t = coef_text(p[m], k)
        parts.append(t + (' * (' + prod_text(rest) + ')' if rest else ''))
    return ' + '.join(parts)


def monos(p):
    out = []
    for m in sorted(p, key=lambda mm: (split(mm)[1], split(mm)[0])):
        k, rest = split(m)
        out.append((coef_text(p[m], k), rest))
    return out


def def_body(p):
    return ' +\n    '.join('%s * (%s)' % (c, prod_text(rest)) for c, rest in monos(p))


def deriv_proof(p):
    L = []
    ms = monos(p)
    for i, (c, rest) in enumerate(ms):
        e = DNAME[rest[0]]
        for a in rest[1:]:
            e = '(%s).mul %s' % (e, DNAME[a]) if e != DNAME[rest[0]] else '%s.mul %s' % (e, DNAME[a])
        L.append('  have m%d := (%s).const_mul %s' % (i + 1, e, c))
    s = 'm1'
    for i in range(1, len(ms)):
        s = '(%s).add m%d' % (s, i + 1) if i > 1 else 'm1.add m2'
    L.append('  have h := %s' % s)
    return L


def cof_lc(cof):
    parts = []
    for n in ('hinv', 'hP2', 'hx2'):
        if n in cof and cof[n]:
            parts.append('(%s) * %s' % (poly_text(cof[n]), n))
    return ' + '.join(parts)


PREAMBLE = r'''import Mathlib
import Tower.RV6.HankelZeroF
import Tower.RV6.XMod
import Tower.RV6.ModAxis
import Tower.RV6.FrickeAx
import Tower.RV6.EtaForm

/-!
# The pull-back: `hjF(x(y)) / Z(y)` is a quadratic in `y`

On the axis (`D = d/dy`, `x = xm y`, `A_k = hk(θᵏ f)(x)`):

* `hasDerivAt_Pax`: `P' = -2π (E P + 40 Z U + 256 U²)` (from `P² = 16Z² + 320ZU + 1024U²` and `P ≠ 0`);
* `hasDerivAt_hkxm_thF0 … 2`: `D A_k = (π/4) P (2A_k + A_{k+1})` (chain rule with `x' = -(π/4) P x`);
* `hF0 = A₀/Z`, `hF1 = D hF0`, `hF2 = D hF1`, and `D hF2 = -(π³/256) P Z uF(x)` (`hasDerivAt_hF2`), which is `0` by `uF_zero`;
* `quad_of_third_deriv_zero` and **`hjF_xm_quad`**: `hjF(xm y) = (a + b y + c y²) Zax y` for `y > 0`.

Generated by `tools/gen_pullbackf.py`, which produces and checks every certificate in exact arithmetic.
-/

namespace Tower.RV6

open Real

/-- `P' = -2π (E P + 40 Z U + 256 U²)`. -/
theorem hasDerivAt_Pax {y : ℝ} (hy : 0 < y) :
    HasDerivAt Pax (-(2 * π) * (Eax y * Pax y + 40 * Zax y * Uax y + 256 * Uax y ^ 2)) y := by
  have h1 : HasDerivAt E2im (dE1 y) y := hasDerivAt_E2im hy
  have h2 := hasDerivAt_E2im_mul 2 (by norm_num) hy
  have h3 := hasDerivAt_E2im_mul 3 (by norm_num) hy
  have h6 := hasDerivAt_E2im_mul 6 (by norm_num) hy
  have kf : HasDerivAt Pax (-dE1 y + 2 * dE2 2 y - 3 * dE2 3 y + 6 * dE2 6 y) y := by
    have k : HasDerivAt
        (fun t : ℝ => -E2im t + 2 * E2im (2 * t) - 3 * E2im (3 * t) + 6 * E2im (6 * t))
        (-dE1 y + 2 * dE2 2 y - 3 * dE2 3 y + 6 * dE2 6 y) y :=
      ((h1.neg.add (h2.const_mul 2)).sub (h3.const_mul 3)).add (h6.const_mul 6)
    exact k
  have dZ := hasDerivAt_Zax hy
  have dU := hasDerivAt_Uax hy
  have hQ := (((dZ.mul dZ).const_mul 16).add ((dZ.mul dU).const_mul 320)).add
    ((dU.mul dU).const_mul 1024)
  have heq : (fun t : ℝ => Pax t * Pax t) =ᶠ[nhds y]
      (fun t : ℝ => 16 * (Zax t * Zax t) + 320 * (Zax t * Uax t) + 1024 * (Uax t * Uax t)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    have e := Pax_sq ht
    linear_combination e
  have hQ' := hQ.congr_of_eventuallyEq heq
  have hu := (kf.mul kf).unique hQ'
  have hP0 := Pax_ne_zero hy
  have key : Pax y * ((-dE1 y + 2 * dE2 2 y - 3 * dE2 3 y + 6 * dE2 6 y)
      - (-(2 * π) * (Eax y * Pax y + 40 * Zax y * Uax y + 256 * Uax y ^ 2))) = 0 := by
    linear_combination (1 / 2 : ℝ) * hu + (2 * π * Eax y) * Pax_sq hy
  have k2 := (mul_eq_zero.mp key).resolve_left hP0
  exact kf.congr_deriv (by linear_combination k2)

'''

CHAIN = r'''/-- `D A_{K} = (π/4) P (2 A_{K} + A_{K1})`. -/
theorem hasDerivAt_hkxm_thF{K} {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => hk thF{K} (xm y))
      (π / 4 * Pax y * (2 * hk thF{K} (xm y) + hk thF{K1} (xm y))) y := by
  have h := (hasDerivAt_hk_thF{K} (xm_pos y)).comp y (hasDerivAt_xm hy)
  have h' : HasDerivAt (fun y : ℝ => hk thF{K} (xm y))
      (-(2 * hk thF{K} (xm y) + hk thF{K1} (xm y)) / xm y * (-(π / 4) * Pax y * xm y)) y := h
  have hx : xm y * (xm y)⁻¹ = 1 := mul_inv_cancel₀ (xm_pos y).ne'
  exact h'.congr_deriv (by
    linear_combination (π / 4 * Pax y * (2 * hk thF{K} (xm y) + hk thF{K1} (xm y))) * hx)

'''

QUAD = r'''/-- `g' = g₁`, `g₁' = g₂`, `g₂' = 0` on `(0, ∞)` gives `g = a + b y + c y²`. -/
theorem quad_of_third_deriv_zero {g g1 g2 : ℝ → ℝ}
    (h0 : ∀ y : ℝ, 0 < y → HasDerivAt g (g1 y) y) (h1 : ∀ y : ℝ, 0 < y → HasDerivAt g1 (g2 y) y)
    (h2 : ∀ y : ℝ, 0 < y → HasDerivAt g2 0 y) :
    ∃ a b c : ℝ, ∀ y : ℝ, 0 < y → g y = a + b * y + c * y ^ 2 := by
  have c2 : ∀ y : ℝ, 0 < y → g2 y = g2 1 := fun y hy => eq_one_of_hasDerivAt_zero h2 hy
  have d1 : ∀ z : ℝ, 0 < z → HasDerivAt (fun y : ℝ => g1 y - g2 1 * y) 0 z := by
    intro z hz
    have h := (h1 z hz).sub ((hasDerivAt_id' z).const_mul (g2 1))
    refine h.congr_deriv ?_
    rw [c2 z hz]
    ring
  have c1 : ∀ y : ℝ, 0 < y → g1 y - g2 1 * y = g1 1 - g2 1 * 1 :=
    fun y hy => eq_one_of_hasDerivAt_zero d1 hy
  have d0 : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun y : ℝ => g y - (g1 1 - g2 1 * 1) * y - g2 1 / 2 * y ^ 2) 0 z := by
    intro z hz
    have h := ((h0 z hz).sub ((hasDerivAt_id' z).const_mul (g1 1 - g2 1 * 1))).sub
      ((hasDerivAt_sqx z).const_mul (g2 1 / 2))
    refine h.congr_deriv ?_
    linear_combination c1 z hz
  refine ⟨g 1 - (g1 1 - g2 1 * 1) * 1 - g2 1 / 2 * 1 ^ 2, g1 1 - g2 1 * 1, g2 1 / 2,
    fun y hy => ?_⟩
  have e : g y - (g1 1 - g2 1 * 1) * y - g2 1 / 2 * y ^ 2
      = g 1 - (g1 1 - g2 1 * 1) * 1 - g2 1 / 2 * 1 ^ 2 := eq_one_of_hasDerivAt_zero d0 hy
  linear_combination e

'''


def main():
    L = PREAMBLE.split('\n')
    for k in range(3):
        L += CHAIN.replace('{K}', str(k)).replace('{K1}', str(k + 1)).split('\n')
    L.append('/-- `A₀ / Z`. -/')
    L.append('noncomputable def hF0 (y : ℝ) : ℝ := hk thF0 (xm y) * (Zax y)⁻¹')
    L.append('')
    L.append('/-- `D (A₀ / Z)`. -/')
    L.append('noncomputable def hF1 (y : ℝ) : ℝ :=')
    L.append('  ' + def_body(h1))
    L.append('')
    L.append('/-- `D² (A₀ / Z)`. -/')
    L.append('noncomputable def hF2 (y : ℝ) : ℝ :=')
    L.append('  ' + def_body(h2))
    L.append('')
    HAVE = {'A0': '  have dA0 := hasDerivAt_hkxm_thF0 hy', 'A1': '  have dA1 := hasDerivAt_hkxm_thF1 hy',
            'A2': '  have dA2 := hasDerivAt_hkxm_thF2 hy', 'Z': '  have dZ := hasDerivAt_Zax hy',
            'U': '  have dU := hasDerivAt_Uax hy', 'E': '  have dE := hasDerivAt_Eax hy', 'P': '  have dP := hasDerivAt_Pax hy',
            'W': "  have dW := (hasDerivAt_Zax hy).inv (Zax_pos hy).ne'"}

    def atoms_have(p):
        used = sorted({a for m in p for a in m if a != 'pi'}, key=ORDER.index)
        return ["  have hinv : Zax y * (Zax y)⁻¹ = 1 := mul_inv_cancel₀ (Zax_pos hy).ne'"] + [HAVE[a] for a in used]
    L.append('theorem hasDerivAt_hF0 {y : ℝ} (hy : 0 < y) : HasDerivAt hF0 (hF1 y) y := by')
    L += atoms_have(h0)
    L.append('  have h := dA0.mul dW')
    L.append('  exact h.congr_deriv (by')
    L.append('    unfold hF1')
    L.append('    linear_combination ' + cof_lc(COF0) + ')')
    L.append('')
    L.append('theorem hasDerivAt_hF1 {y : ℝ} (hy : 0 < y) : HasDerivAt hF1 (hF2 y) y := by')
    L += atoms_have(h1)
    L += deriv_proof(h1)
    L.append('  exact h.congr_deriv (by')
    L.append('    unfold hF2')
    L.append('    linear_combination ' + cof_lc(COF1) + ')')
    L.append('')
    L.append('/-- **`D³ (A₀ / Z) = -(π³/256) P Z uF(x)`**. -/')
    L.append('theorem hasDerivAt_hF2 {y : ℝ} (hy : 0 < y) :')
    L.append('    HasDerivAt hF2 (-(π ^ 3 / 256) * Pax y * Zax y * uF (xm y)) y := by')
    L += atoms_have(h2)
    L.append('  have hP2 := Pax_sq hy')
    L.append('  have hx2 : xm y ^ 2 = 64 * Uax y * (Zax y)⁻¹ := by')
    L.append('    rw [xm_sq hy, div_eq_mul_inv]')
    L += deriv_proof(h2)
    L.append('  exact h.congr_deriv (by')
    L.append('    unfold uF')
    L.append('    linear_combination ' + cof_lc(COF2) + ')')
    L.append('')
    L.append('theorem hasDerivAt_hF2_zero {y : ℝ} (hy : 0 < y) : HasDerivAt hF2 0 y := by')
    L.append('  have h := hasDerivAt_hF2 hy')
    L.append('  rw [uF_zero (xm_pos y), mul_zero] at h')
    L.append('  exact h')
    L.append('')
    L += QUAD.split('\n')
    L.append('/-- **`hjF(xm y) = (a + b y + c y²) Zax y`** for `y > 0`. -/')
    L.append('theorem hjF_xm_quad : ∃ a b c : ℝ, ∀ y : ℝ, 0 < y →')
    L.append('    hjF (xm y) = (a + b * y + c * y ^ 2) * Zax y := by')
    L.append('  obtain ⟨a, b, c, h⟩ := quad_of_third_deriv_zero (g := hF0) (g1 := hF1) (g2 := hF2)')
    L.append('    (fun y hy => hasDerivAt_hF0 hy) (fun y hy => hasDerivAt_hF1 hy)')
    L.append('    (fun y hy => hasDerivAt_hF2_zero hy)')
    L.append('  refine ⟨a, b, c, fun y hy => ?_⟩')
    L.append('  have e : hk thF0 (xm y) * (Zax y)⁻¹ = a + b * y + c * y ^ 2 := h y hy')
    L.append('  have hz : Zax y * (Zax y)⁻¹ = 1 := mul_inv_cancel₀ (Zax_pos hy).ne\'')
    L.append('  have hj : hjF (xm y) = hk thF0 (xm y) := by')
    L.append('    rw [hjF_eq_hk, ← thF0_eq_fB]')
    L.append('  rw [hj]')
    L.append('  linear_combination (Zax y) * e + (-(hk thF0 (xm y))) * hz')
    L.append('')
    L.append('end Tower.RV6')
    L.append('')
    text = '\n'.join(L)
    path = os.path.join('Tower', 'RV6', 'PullbackF.lean')
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(text)
    print('certificates checked; h2 has %d monomials; cofactor sizes %s; wrote %s (%d lines)'
          % (len(h2), [sum(len(c) for c in cf.values()) for cf in (COF0, COF1, COF2)], path, text.count('\n')))


if __name__ == '__main__':
    main()
