#!/usr/bin/env python3
"""Writes Tower/RV6/HankelZeroF.lean: c1 = c2 = 0 in uF_eq, i.e. L3' hjF = 0 on (0, inf).

With a_k = hk thF_k 0, b_k = hk (t^2 thF_k) 0:  the shifts a_(k+1) = -2 a_k, b_(k+1) = -4 b_k (hk_shift_zero,
hk_shift3_zero), the s = 0 relation of L5 (hk_s0_F: the integral of thF5/t is thF4(inf) - thF4(0+) = 0), hence the x^0 and
x^2 coefficients of uF vanish (hk_mom0F, hk_mom2F); hk_taylor gives |uF x| <= K x^3 on (0, 1] (uF_small); with uF_eq
and log_consts_eq_zero, uF = 0 (uF_zero).  Every linear_combination certificate is checked here in exact arithmetic.
usage: python3 tools/gen_hankelzerof.py  (from the repository root)
"""
import os
from fractions import Fraction

# uF = sum_k (al x^4 + be x^2 + ga) A_k  (as in gen_hankelodef.py)
U = {3: (-1, -20, -64), 2: (0, -60, -384), 1: (0, -72, -768), 0: (0, -32, -512)}
# Phi = thF5 / t^2 by L5_thF: (coefficient, 'A' = thF_k | 'B' = t^2 thF_k, k)
PHI = [(20, 'A', 3), (60, 'A', 2), (72, 'A', 1), (32, 'A', 0), (-64, 'B', 1), (-128, 'B', 0)]
M0 = {2: -64, 1: -256, 0: -256}          # x^0 relation = sum M0[k] * (a_(k+1) + 2 a_k)
M2Z, M2S = -1, {2: 16, 1: 32}            # x^2 relation = M2Z * (s0 relation) + sum M2S[k] * (b_(k+1) + 4 b_k)


# ---- exact polynomials over named atoms ----
def padd(p, q):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + v
    return {k: v for k, v in r.items() if v != 0}


def pmul(p, q):
    r = {}
    for a, u in p.items():
        for b, v in q.items():
            k = tuple(sorted(a + b))
            r[k] = r.get(k, 0) + u * v
    return {k: v for k, v in r.items() if v != 0}


def sc(p, c):
    return {k: v * Fraction(c) for k, v in p.items() if v * Fraction(c) != 0}


def at(name):
    return {(name,): Fraction(1)}


def cst(c):
    return {(): Fraction(c)} if c else {}


def xpow(n):
    r = cst(1)
    for _ in range(n):
        r = pmul(r, at('x'))
    return r


def pk(k):
    al, be, ga = U[k]
    return padd(padd(sc(xpow(4), al), sc(xpow(2), be)), cst(ga))


def a(k):
    return at('a%d' % k)


def b(k):
    return at('b%d' % k)


def A(k):
    return at('A%d' % k)


def r(k):  # hk thF_k x - a_k + x^2/4 b_k
    return padd(padd(A(k), sc(a(k), -1)), sc(pmul(xpow(2), b(k)), Fraction(1, 4)))


def check():
    S1 = {k: padd(a(k + 1), sc(a(k), 2)) for k in range(3)}
    S3 = {k: padd(b(k + 1), sc(b(k), 4)) for k in range(3)}
    Z = {}
    for c, s, k in PHI:
        Z = padd(Z, sc(a(k) if s == 'A' else b(k), c))
    rel0 = {}
    for k, c in M0.items():
        rel0 = padd(rel0, sc(S1[k], c))
    rel2 = sc(Z, M2Z)
    for k, c in M2S.items():
        rel2 = padd(rel2, sc(S3[k], c))
    # the statements of hk_mom0F, hk_mom2F
    m0 = {}
    for k in U:
        m0 = padd(m0, sc(a(k), U[k][2]))
    m2 = {}
    for k in U:
        m2 = padd(padd(m2, sc(a(k), U[k][1])), sc(b(k), Fraction(-U[k][2], 4)))
    assert padd(rel0, sc(m0, -1)) == {}, 'm0'
    assert padd(rel2, sc(m2, -1)) == {}, 'm2'
    # uF = x^4 (q4 + q6 x^2) + sum p_k r_k + m0 + x^2 m2
    q4 = {}
    for k in U:
        q4 = padd(padd(q4, sc(a(k), U[k][0])), sc(b(k), Fraction(-U[k][1], 4)))
    q6 = {}
    for k in U:
        q6 = padd(q6, sc(b(k), Fraction(-U[k][0], 4)))
    uF = {}
    for k in U:
        uF = padd(uF, pmul(pk(k), A(k)))
    rhs = pmul(xpow(4), padd(q4, pmul(q6, xpow(2))))
    for k in U:
        rhs = padd(rhs, pmul(pk(k), r(k)))
    rhs = padd(padd(rhs, m0), pmul(xpow(2), m2))
    assert padd(uF, sc(rhs, -1)) == {}, 'uF'
    # t^2 Phi = thF5 - L5_thF expression
    t2 = {('t', 't'): Fraction(1)}
    T = {k: at('T%d' % k) for k in range(6)}
    phi = {}
    for c, s, k in PHI:
        phi = padd(phi, sc(T[k] if s == 'A' else pmul(t2, T[k]), c))
    L5 = padd(padd(T[5], sc(pmul(t2, padd(padd(padd(sc(T[3], 5), sc(T[2], 15)), sc(T[1], 18)), sc(T[0], 8))), -4)),
              sc(pmul(pmul(t2, t2), padd(T[1], sc(T[0], 2))), 64))
    assert padd(pmul(t2, phi), sc(padd(T[5], sc(L5, -1)), -1)) == {}, 'phi'
    return q4, q6


# ---- Lean text ----
def num(c):
    return '(%d)' % c if c < 0 else '%d' % c


def frac(c):
    c = Fraction(c)
    if c.denominator == 1:
        return num(c.numerator)
    return '(%d / %d)' % (c.numerator, c.denominator) if c > 0 else '(-(%d / %d))' % (-c.numerator, c.denominator)


def av(k):
    return 'hk thF%d 0' % k


def bv(k):
    return 'hk (fun t => t ^ 2 * thF%d t) 0' % k


def lin(p):
    """a linear form in a_k, b_k as Lean text"""
    parts = []
    for key in sorted(p, key=lambda kk: (kk[0][0], -int(kk[0][1:]))):
        nm = key[0]
        v = av(int(nm[1:])) if nm[0] == 'a' else bv(int(nm[1:]))
        parts.append('%s * %s' % (frac(p[key]), v))
    return ' + '.join(parts)


def ptext(k, v='x'):
    al, be, ga = U[k]
    return '(%s * %s ^ 4 + %s * %s ^ 2 + %s)' % (num(al), v, num(be), v, num(ga))


def rtext(k):
    return '(hk thF%d x - hk thF%d 0 + x ^ 2 / 4 * hk (fun t => t ^ 2 * thF%d t) 0)' % (k, k, k)


def Ntext(k):
    return '(∫ t in Set.Ioi (0 : ℝ), |t ^ 4 * thF%d t|)' % k


PREAMBLE = r'''import Mathlib
import Tower.RV6.HankelTaylor
import Tower.RV6.HankelRelF
import Tower.RV6.HankelODEF

/-!
# `L₃′ hjF = 0` on `(0, ∞)`

The constants of `uF_eq` vanish.  With `a_k = hk(θᵏ f)(0) = ∫ t θᵏ f` and `b_k = hk(t² θᵏ f)(0) = ∫ t³ θᵏ f`:

* `a_{k+1} = -2 a_k`, `b_{k+1} = -4 b_k` (`hk_shift_zero`, `hk_shift3_zero`);
* the `s = 0` relation of `L₅` (`hk_s0_F`): `θ⁵ f / t = (θ⁴ f)'` and `θ⁴ f = t² ψ₄` with `ψ₄ ∈ HDom`
  (`thF4_eq_sq`, `hdom_psiF4`), so `θ⁴ f → 0` at `0+` and at `∞` and `∫₀^∞ θ⁵ f / t = 0`; by `L5_thF` this is
  `20 a₃ + 60 a₂ + 72 a₁ + 32 a₀ - 64 b₁ - 128 b₀ = 0`, i.e. `a₀ = 4 b₀` (numerically `π²/16 = 4 · π²/64`);
* the `x⁰` and `x²` coefficients of `uF` vanish (`hk_mom0F`, `hk_mom2F`), so by `hk_taylor`
  `|uF x| ≤ K x³` on `(0, 1]` (`uF_small`);
* **`uF_zero`**: `uF x = 0` for `x > 0` (`uF_eq` and `log_consts_eq_zero`).

Generated by `tools/gen_hankelzerof.py`, which checks every certificate in exact arithmetic.
-/

namespace Tower.RV6

open MeasureTheory

/-- `θ⁴ f = t² ψ₄` (`I₁(t) = (t/2) B(t²/4)`). -/
noncomputable def psiF4 (t : ℝ) : ℝ :=
  (-24) * (Bser (t / 2 * (t / 2)) / 2 * (t * besselK1 t) * (t * besselK1 t) * (t * besselK1 t)) +
    32 * ldF2 t + 28 * ldF1 t + 16 * ldF0 t + 40 * (t ^ 2 * ldF0 t)

theorem hdom_psiF4 : HDom psiF4 := by
  have h : HDom (fun t : ℝ => (-24) * (Bser (t / 2 * (t / 2)) / 2 * (t * besselK1 t) *
      (t * besselK1 t) * (t * besselK1 t)) + 32 * ldF2 t + 28 * ldF1 t + 16 * ldF0 t +
      40 * (t ^ 2 * ldF0 t)) :=
    hdom_add (hdom_add (hdom_add (hdom_add (hdom_const_mul (-24)
      (hdom_prod4 ity_bserI1 kty_mul_besselK1 kty_mul_besselK1 kty_mul_besselK1))
      (hdom_const_mul 32 hdom_ldF2)) (hdom_const_mul 28 hdom_ldF1)) (hdom_const_mul 16 hdom_ldF0))
      (hdom_const_mul 40 (hdom_pow_mul 2 hdom_ldF0))
  exact h

theorem thF4_eq_sq (t : ℝ) : thF4 t = t ^ 2 * psiF4 t := by
  unfold thF4 psiF4 ldF4
  rw [besselI1_eq]
  ring

theorem thF4_zero : thF4 0 = 0 := by
  rw [thF4_eq_sq]
  ring

theorem tendsto_thF4_zero : Filter.Tendsto thF4 (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : Filter.Tendsto (fun t : ℝ => t ^ 2 * psiF4 t * (fun _ : ℝ => (1 : ℝ)) t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_hdom_zero (g := fun _ : ℝ => (1 : ℝ)) hdom_psiF4 (G := 1) (fun _ _ => by simp)
  refine Filter.Tendsto.congr (fun t => ?_) h
  show t ^ 2 * psiF4 t * 1 = thF4 t
  rw [mul_one, thF4_eq_sq]

theorem tendsto_thF4_atTop : Filter.Tendsto thF4 Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun t : ℝ => t ^ 2 * psiF4 t * (fun _ : ℝ => (1 : ℝ)) t)
      Filter.atTop (nhds 0) :=
    tendsto_hdom_atTop (g := fun _ : ℝ => (1 : ℝ)) hdom_psiF4 (G := 1) (fun _ _ => by simp)
  refine Filter.Tendsto.congr (fun t => ?_) h
  show t ^ 2 * psiF4 t * 1 = thF4 t
  rw [mul_one, thF4_eq_sq]

'''


def main():
    q4, q6 = check()
    L = PREAMBLE.split('\n')

    def body(c, s, j):
        f = 'thF%d t' % j if s == 'A' else '(t ^ 2 * thF%d t)' % j
        return '%s * %s' % (num(c), f)

    def hdom(s, j):
        return 'hdom_thF%d' % j if s == 'A' else '(hdom_pow_mul 2 hdom_thF%d)' % j

    def val(s, j):
        return av(j) if s == 'A' else bv(j)

    lam = ' + '.join(body(c, s, j) for c, s, j in PHI)
    stmt = ' + '.join('%s * %s' % (num(c), val(s, j)) for c, s, j in PHI)
    c0, s0, j0 = PHI[0]
    Q = ['(hdom_const_mul %s %s)' % (num(c0), hdom(s0, j0))]
    for c, s, j in PHI[1:]:
        Q.append('(hdom_add %s (hdom_const_mul %s %s))' % (Q[-1], num(c), hdom(s, j)))
    L.append('/-- The `s = 0` relation of `L₅`: `∫₀^∞ θ⁵ f / t = 0`, written through `a_k`, `b_k`. -/')
    L.append('theorem hk_s0_F :')
    L.append('    ' + stmt + ' = 0 := by')
    L.append('  have hP : HDom (fun t : ℝ => %s) :=' % lam)
    L.append('    ' + Q[-1])
    L.append('  have pt : ∀ t : ℝ, 0 < t →')
    L.append('      besselJ0 (0 * t) * (%s) * t = thF5 t / t := by' % lam)
    L.append('    intro t ht')
    L.append('    rw [zero_mul, besselJ0_zero, eq_div_iff ht.ne\']')
    L.append('    linear_combination (-1 : ℝ) * L5_thF t')
    L.append('  have i0 : IntegrableOn (fun t : ℝ => besselJ0 (0 * t) * (%s) * t)' % lam)
    L.append('      (Set.Ioi 0) := integrableOn_hk hP (le_refl 0)')
    L.append('  have hint : IntegrableOn (fun t : ℝ => thF5 t / t) (Set.Ioi 0) :=')
    L.append('    i0.congr_fun (fun t ht => pt t ht) measurableSet_Ioi')
    L.append('  have hz : ∫ t in Set.Ioi (0 : ℝ), thF5 t / t = 0 :=')
    L.append('    integral_Ioi_deriv_eq_zero thF4_zero (fun t ht => hasDerivAt_thF4 ht) tendsto_thF4_zero')
    L.append('      tendsto_thF4_atTop hint')
    L.append('  have e : hk (fun t => %s) 0' % lam)
    L.append('      = ∫ t in Set.Ioi (0 : ℝ), thF5 t / t := by')
    L.append('    unfold hk')
    L.append('    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => pt t ht)')
    L.append('  have h0 : hk (fun t => %s) 0 = 0 := by' % lam)
    L.append('    rw [e, hz]')
    rws = []
    for i in range(len(PHI) - 1, 0, -1):
        c, s, j = PHI[i]
        rws.append('hk_add_cmul %s %s %s (le_refl 0)' % (Q[i - 1], hdom(s, j), num(c)))
    rws.append('hk_const_mul %s thF%d 0' % (num(c0), j0))
    L.append('  rw [' + rws[0] + ',')
    for rr in rws[1:-1]:
        L.append('    ' + rr + ',')
    L.append('    ' + rws[-1] + '] at h0')
    L.append('  exact h0')
    L.append('')
    # m0, m2
    m0 = ' + '.join('%s * %s' % (num(U[k][2]), av(k)) for k in (3, 2, 1, 0))
    m2 = ' + '.join(['%s * %s' % (num(U[k][1]), av(k)) for k in (3, 2, 1, 0)] +
                    ['%s * %s' % (frac(Fraction(-U[k][2], 4)), bv(k)) for k in (3, 2, 1, 0)])
    L.append('/-- The `x⁰` coefficient of `uF`: `-64 a₃ - 384 a₂ - 768 a₁ - 512 a₀ = 0`. -/')
    L.append('theorem hk_mom0F : ' + m0 + ' = 0 := by')
    for k in (0, 1, 2):
        L.append('  have s%d := hk_shift_zero hchain_thF%d' % (k, k))
    L.append('  linear_combination ' + ' + '.join('%s * s%d' % (num(M0[k]), k) for k in (2, 1, 0)))
    L.append('')
    L.append('/-- The `x²` coefficient of `uF`. -/')
    L.append('theorem hk_mom2F :')
    L.append('    ' + m2 + ' = 0 := by')
    L.append('  have z := hk_s0_F')
    for k in (1, 2):
        L.append('  have u%d := hk_shift3_zero hchain_thF%d' % (k, k))
    L.append('  linear_combination %s * z + ' % num(M2Z) + ' + '.join('%s * u%d' % (num(M2S[k]), k) for k in (2, 1)))
    L.append('')
    # uF_small
    q4t, q6t = '(' + lin(q4) + ')', '(' + lin(q6) + ')'
    P = {k: '(-(%s + %s + %s))' % tuple(num(c) for c in U[k]) for k in U}
    K = '|%s| + |%s| + ' % (q4t, q6t) + ' + '.join('%s * %s' % (P[k], Ntext(k)) for k in (3, 2, 1, 0))
    L.append('/-- `|uF x| ≤ K x³` on `(0, 1]`. -/')
    L.append('theorem uF_small : ∃ K : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 → |uF x| ≤ K * x ^ 3 := by')
    L.append('  refine ⟨' + K + ', fun x hx hx1 => ?_⟩')
    L.append('  have m0 := hk_mom0F')
    L.append('  have m2 := hk_mom2F')
    for k in (3, 2, 1, 0):
        L.append('  have t%d := hk_taylor hdom_thF%d hx.le' % (k, k))
        L.append('  have p%d : |%s| ≤ %s :=' % (k, ptext(k), P[k]))
        L.append('    abs_quart_le hx.le hx1 (by norm_num) (by norm_num) (by norm_num)')
        L.append('  have b%d := abs_mul_le_mul_of p%d t%d' % (k, k, k))
    L.append('  have hq := abs_x4_le (q4 := %s) (q6 := %s) hx.le hx1' % (q4t, q6t))
    L.append('  have e : uF x = x ^ 4 * (%s + %s * x ^ 2)' % (q4t, q6t))
    for k in (3, 2, 1, 0):
        L.append('      + %s * %s' % (ptext(k), rtext(k)))
    L.append('      := by')
    L.append('    unfold uF')
    L.append('    linear_combination m0 + x ^ 2 * m2')
    L.append('  rw [e]')
    L.append('  have h5 := abs_add5_le (x ^ 4 * (%s + %s * x ^ 2))' % (q4t, q6t))
    for k in (3, 2, 1, 0):
        L.append('    (%s * %s)' % (ptext(k), rtext(k)))
    L.append('  have hK : (%s) * x ^ 3 = x ^ 3 * (|%s| + |%s|) + ' % (K, q4t, q6t)
             + ' + '.join('%s * (x ^ 3 * %s)' % (P[k], Ntext(k)) for k in (3, 2, 1, 0)) + ' := by ring')
    L.append('  linarith [h5, hq, b3, b2, b1, b0, hK]')
    L.append('')
    L.append('/-- **`L₃′ hjF = 0`**: `uF x = 0` for every `x > 0`. -/')
    L.append('theorem uF_zero {x : ℝ} (hx : 0 < x) : uF x = 0 := by')
    L.append('  obtain ⟨c1, c2, hc⟩ := uF_eq')
    L.append('  obtain ⟨K, hK⟩ := uF_small')
    L.append('  have hb : ∀ y : ℝ, 0 < y → y ≤ 1 → |c1 + c2 * Real.log y| ≤ K * y := by')
    L.append('    intro y hy hy1')
    L.append('    have h1 := hK y hy hy1')
    L.append('    rw [hc y hy, abs_mul, abs_of_nonneg (pow_nonneg hy.le 2)] at h1')
    L.append('    have e : K * y ^ 3 = y ^ 2 * (K * y) := by ring')
    L.append('    rw [e] at h1')
    L.append('    exact le_of_mul_le_mul_left h1 (pow_pos hy 2)')
    L.append('  obtain ⟨h1, h2⟩ := log_consts_eq_zero hb')
    L.append('  rw [hc x hx, h1, h2]')
    L.append('  ring')
    L.append('')
    L.append('end Tower.RV6')
    L.append('')
    text = '\n'.join(L)
    path = os.path.join('Tower', 'RV6', 'HankelZeroF.lean')
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(text)
    print('certificates checked; wrote %s (%d lines)' % (path, text.count('\n')))


if __name__ == '__main__':
    main()
