#!/usr/bin/env python3
"""Generate, for each prime p: Tower/TangentLine/Orders<p>.lean (finite-field facts) and Red<p>.lean (glue with the
Reduction package); and Tower/TangentLine/NonTorsion.lean.  The generator computes; Lean checks every step.
Curve: Y^2 = X^3 + a2 X^2 + X, a2 = -7/4 mod p.  Mathlib: addX = l^2 - a2 - x1 - x2, addY = -(l (x3 - x1) + y1), negY x y = -y."""
import sys, os, itertools

def factor(n):
    f, d = [], 2
    while d * d <= n:
        if n % d == 0:
            f.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: f.append(n)
    return f

def orterm(k, n, t):
    """term proving the k-th (0-based) of n right-nested disjuncts from a proof t of that disjunct"""
    if n == 1: return t
    inner = t if k == n - 1 else f"Or.inl {t}"
    for _ in range(k):
        inner = f"Or.inr ({inner})"
    return inner

def gen(p, z, roots, expected_orders, with_diffs):
    inv = lambda a: pow(a % p, -1, p)
    a2 = (-7 * inv(4)) % p
    assert (z * z + z + 1) % p == 0
    Q4 = lambda t: (t**4 + (2 + 3*z)*t**3 - t*t + (2 + z)*t + (1 + z)) % p
    Gf = lambda t, y: (t*y*y + (t*t + t + 1)*y + t) % p
    Ff = lambda t, y: (y*(t*t - 1)*(-t*t - 1) + t*(y*y - 1)*(z*y*y - 1)) % p
    dQ = lambda x, xp: ((x**3 + x*x*xp + x*xp*xp + xp**3) + (2 + 3*z)*(x*x + x*xp + xp*xp) - (x + xp) + (2 + z)) % p
    assert sorted(t for t in range(p) if Q4(t) == 0) == sorted(roots)
    def add(P, Q):
        if P is None: return Q, 'left0', None
        if Q is None: return P, 'right0', None
        (x1, y1), (x2, y2) = P, Q
        if x1 != x2:
            l = (y1 - y2) * inv(x1 - x2) % p
            kind = 'chord'
        elif (y1 + y2) % p == 0:
            return None, 'zero', None
        else:
            assert y1 == y2
            l = (3 * x1 * x1 + 2 * a2 * x1 + 1) * inv(2 * y1) % p
            kind = 'dbl'
        x3 = (l * l - a2 - x1 - x2) % p
        y3 = (-(l * (x3 - x1) + y1)) % p
        assert (y3 * y3 - (x3 ** 3 + a2 * x3 * x3 + x3)) % p == 0
        return (x3, y3), kind, l
    def mul(n, P):
        R, Q = None, P
        while n:
            if n & 1: R = add(R, Q)[0]
            Q = add(Q, Q)[0]
            n >>= 1
        return R
    def order(P):
        n = 1
        while mul(n, P) is not None: n += 1
        return n
    out = []
    w = out.append
    w("import Mathlib")
    w("import Tower.EC.Cert")
    w("import Tower.TangentLine.Maps")
    w("")
    w("/-!")
    w(f"# The points over the roots of `Q₄` in `E(𝔽_{p})`")
    w("")
    w("This file is generated (the generator computes the slopes; Lean checks every step).")
    w(f"`E : Y² = X³ - (7/4) X² + X` over `𝔽_{p}`, where `-7/4 = {a2}`; cube root of unity `z = {z}`.")
    w("For each root `t` of `Q₄`: the point `(t, y)` of the curve `G = 0` with `F = 0`, its image")
    w("`(X, Y)` under `X = -1/(t y)`, `Y = (y - t) X (X - 1)/2`, the exact multiples that")
    w("determine its order in Mathlib's group `E(𝔽_p)`, and the fact that `(X, Y)` is determined by")
    w("`t`." + ("  The last section does the same for the six differences of the four points." if with_diffs else ""))
    w("-/")
    w("")
    w("namespace Tower.TangentLine")
    w("")
    w(f"namespace P{p}")
    w("")
    w("open WeierstrassCurve.Affine Tower.EC")
    w("")
    w(f"instance : Fact (Nat.Prime {p}) := ⟨by norm_num⟩")
    w("")
    w(f"/-- The curve `Y² = X³ + {a2} X² + X` over `𝔽_{p}`. -/")
    w(f"def E : WeierstrassCurve.Affine (ZMod {p}) := ⟨0, {a2}, 0, 1, 0⟩")
    w("")
    w(f"/-- `{z}` is a primitive cube root of unity in `𝔽_{p}`. -/")
    w(f"theorem cubeRoot : ({z} : ZMod {p}) ^ 2 + {z} + 1 = 0 := by decide")
    w("")
    w(f"/-- Over `𝔽_{p}` with `w = {z}`, the quartic `Q₄` has exactly the four roots `{', '.join(map(str, roots))}`. -/")
    w(f"theorem Q4_roots : ∀ t : ZMod {p}, Q4 t {z} = 0 ↔ ({' ∨ '.join(f't = {r}' for r in roots)}) := by")
    w("  decide +kernel")
    w("")
    ns_done = set()
    def ns(P):
        x, y = P
        name = f"ns_{x}_{y}"
        if name not in ns_done:
            ns_done.add(name)
            w(f"theorem {name} : E.Nonsingular ({x} : ZMod {p}) {y} := nonsingular_of (by decide) (by decide)")
        return name
    def term(P):
        if P is None: return f"(0 : E.Point)"
        return f"Point.some ({P[0]} : ZMod {p}) {P[1]} {ns(P)}"
    step_done = {}
    counter = [0]
    def step(P, Q):
        key = (P, Q)
        if key in step_done: return step_done[key]
        R, kind, l = add(P, Q)
        tP, tQ, tR = term(P), term(Q), term(R)
        counter[0] += 1
        name = f"step{counter[0]}"
        w(f"theorem {name} : {tP} + {tQ} = {tR} :=")
        if kind == 'chord':
            w(f"  add_cert (ℓ := ({l} : ZMod {p})) {ns(P)} {ns(Q)} {ns(R)} (by decide) (by decide) (by decide) (by decide)")
        elif kind == 'dbl':
            w(f"  dbl_cert (ℓ := ({l} : ZMod {p})) {ns(P)} {ns(R)} (by decide) (by decide) (by decide) (by decide)")
        elif kind == 'zero':
            w(f"  add_zero_cert {ns(P)} {ns(Q)} (by decide) (by decide)")
        elif kind == 'left0':
            w("  zero_add _")
        else:
            w("  add_zero _")
        step_done[key] = (name, R)
        return name, R
    def chain(nm, P0, n):
        """multiples of the point nm := P0 that pin its order n; then addOrderOf nm = n"""
        have = {1: P0}
        w(f"theorem {nm}_m1 : (1 : ℕ) • {nm} = {term(P0)} := one_nsmul _")
        def ensure_pow2(k):
            m = 1
            while m < (1 << k):
                if 2 * m not in have:
                    name, R = step(have[m], have[m])
                    have[2 * m] = R
                    w(f"theorem {nm}_m{2 * m} : ({2 * m} : ℕ) • {nm} = {term(R)} :=")
                    w(f"  nsmul_step {nm}_m{m} {nm}_m{m} {name} (by norm_num)")
                m *= 2
        def ensure(m):
            if m in have: return
            bits = [j for j in range(m.bit_length()) if (m >> j) & 1]
            ensure_pow2(bits[-1])
            acc = 1 << bits[-1]
            for j in reversed(bits[:-1]):
                nxt = acc + (1 << j)
                if nxt not in have:
                    name, R = step(have[acc], have[1 << j])
                    have[nxt] = R
                    w(f"theorem {nm}_m{nxt} : ({nxt} : ℕ) • {nm} = {term(R)} :=")
                    w(f"  nsmul_step {nm}_m{acc} {nm}_m{1 << j} {name} (by norm_num)")
                acc = nxt
        ensure(n)
        assert have[n] is None
        w("")
        w(f"/-- `{n} • {nm} = 0`. -/")
        w(f"theorem {nm}_nsmul_order : ({n} : ℕ) • {nm} = 0 := {nm}_m{n}")
        for q in factor(n):
            m = n // q
            ensure(m)
            assert have[m] is not None
            w("")
            w(f"/-- `({n}/{q}) • {nm} ≠ 0`. -/")
            w(f"theorem {nm}_nsmul_{m}_ne : ({m} : ℕ) • {nm} ≠ 0 := by")
            w(f"  rw [{nm}_m{m}]")
            w("  exact Point.some_ne_zero _")
        fac = []
        m = n
        for q in factor(n):
            e = 0
            while m % q == 0: m //= q; e += 1
            fac.append((q, e))
        prod = " * ".join(f"{q} ^ {e}" for q, e in fac)
        w("")
        w(f"/-- `{nm}` has exact order `{n}` in `E(𝔽_{p})`. -/")
        w(f"theorem {nm}_addOrderOf : addOrderOf {nm} = {n} := by")
        w(f"  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul {nm}_nsmul_order ?_")
        w("  intro q hq hdvd")
        w(f"  have e : ({prod} : ℕ) = {n} := by norm_num")
        w(f"  have h : q ∣ {prod} := by rw [e]; exact hdvd")
        def leaf(q0, hyp, ind):
            w(f"{ind}obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow {hyp})")
            w(f"{ind}exact {nm}_nsmul_{n // q0}_ne")
        def split(k, hyp, ind):
            if k == 1:
                leaf(fac[0][0], hyp, ind)
                return
            a, b = f"h{k}a", f"h{k}b"
            w(f"{ind}rcases (Nat.Prime.dvd_mul hq).mp {hyp} with {a} | {b}")
            w(f"{ind}· skip")
            split(k - 1, a, ind + "  ")
            w(f"{ind}· skip")
            leaf(fac[k - 1][0], b, ind + "  ")
        split(len(fac), "h", "  ")
    pts, ys, orders_found = [], [], []
    for idx, t in enumerate(roots, 1):
        cands = [y for y in range(p) if Gf(t, y) == 0 and Ff(t, y) == 0]
        assert len(cands) == 1, (p, t, cands)
        y = cands[0]
        assert (t * y) % p != 0
        X = (-inv(t * y)) % p
        Y = ((y - t) * X * (X - 1) * inv(2)) % p
        P0 = (X, Y)
        assert (Y * Y - (X ** 3 + a2 * X * X + X)) % p == 0
        assert [x for x in range(p) if (x * (t * y) + 1) % p == 0] == [X]
        assert [v for v in range(p) if (2 * v - (y - t) * X * (X - 1)) % p == 0] == [Y]
        n = order(P0)
        orders_found.append(n); pts.append(P0); ys.append(y)
        w("")
        w(f"/-! ## Root `t = {t}`: `y = {y}`, `(X, Y) = ({X}, {Y})`, order `{n}` -/")
        w("")
        w(f"/-- `(t, y) = ({t}, {y})` lies on `G = 0` and `F = 0`, and `(X, Y) = ({X}, {Y})` is its image. -/")
        w(f"theorem link{idx} : G ({t} : ZMod {p}) {y} = 0 ∧ F ({t} : ZMod {p}) {y} {z} = 0 ∧")
        w(f"    ({X} : ZMod {p}) * ({t} * {y}) = -1 ∧ 2 * ({Y} : ZMod {p}) = ({y} - {t}) * {X} * ({X} - 1) := by")
        w("  decide")
        w("")
        w(f"theorem uniq_y{idx} : ∀ y : ZMod {p}, G {t} y = 0 → F {t} y {z} = 0 → y = {y} := by")
        w("  decide +kernel")
        w(f"theorem uniq_X{idx} : ∀ X : ZMod {p}, X * ({t} * {y}) = -1 → X = {X} := by")
        w("  decide +kernel")
        w(f"theorem uniq_Y{idx} : ∀ Y : ZMod {p}, 2 * Y = ({y} - {t}) * {X} * ({X} - 1) → Y = {Y} := by")
        w("  decide +kernel")
        w("")
        w(f"/-- Over the root `t = {t}` the point `(X, Y)` is determined. -/")
        w(f"theorem coords{idx} (y X Y : ZMod {p}) (hG : G {t} y = 0) (hF : F {t} y {z} = 0)")
        w(f"    (hX : X * ({t} * y) = -1) (hY : 2 * Y = (y - {t}) * X * (X - 1)) : X = {X} ∧ Y = {Y} := by")
        w(f"  have hy : y = {y} := uniq_y{idx} y hG hF")
        w("  subst hy")
        w(f"  have hX' : X = {X} := uniq_X{idx} X hX")
        w("  subst hX'")
        w(f"  exact ⟨rfl, uniq_Y{idx} Y hY⟩")
        w("")
        assert dQ(t, t) != 0
        w(f"/-- `t = {t}` is a simple root of `Q₄`. -/")
        w(f"theorem diag{idx} : dQ4 ({t} : ZMod {p}) {t} {z} ≠ 0 := by decide")
        w("")
        nsP = ns(P0)
        w(f"/-- The point of `E(𝔽_{p})` over the root `t = {t}`. -/")
        w(f"abbrev P{idx} : E.Point := Point.some ({X} : ZMod {p}) {Y} {nsP}")
        w("")
        chain(f"P{idx}", P0, n)
    assert sorted(orders_found) == sorted(expected_orders), (orders_found, expected_orders)
    assert len(set(pts)) == 4
    diff_orders = {}
    if with_diffs:
        w("")
        w("/-! ## Differences of the four points -/")
        for i, j in itertools.combinations(range(1, 5), 2):
            Pi, Pj = pts[i - 1], pts[j - 1]
            negPj = (Pj[0], (-Pj[1]) % p)
            w("")
            w(f"/-! ### `P{i} - P{j}` -/")
            w("")
            nsn = ns(negPj)
            name, D = step(Pi, negPj)
            assert D is not None
            n = order(D)
            diff_orders[(i, j)] = n
            nsD = ns(D)
            w(f"/-- The difference `P{i} - P{j}` as an explicit point. -/")
            w(f"theorem D{i}{j}_eq : P{i} - P{j} = {term(D)} :=")
            w(f"  sub_cert {ns(Pi)} {ns(Pj)} {nsn} {nsD} (by decide) {name}")
            w("")
            w(f"abbrev D{i}{j} : E.Point := {term(D)}")
            w("")
            chain(f"D{i}{j}", D, n)
            w("")
            w(f"theorem P{i}_sub_P{j}_addOrderOf : addOrderOf (P{i} - P{j}) = {n} := by")
            w(f"  rw [D{i}{j}_eq]")
            w(f"  exact D{i}{j}_addOrderOf")
            w("")
            w(f"theorem P{j}_sub_P{i}_addOrderOf : addOrderOf (P{j} - P{i}) = {n} := by")
            w(f"  rw [← neg_sub P{i} P{j}, addOrderOf_neg]")
            w(f"  exact P{i}_sub_P{j}_addOrderOf")
    w("")
    w(f"end P{p}")
    w("")
    w("end Tower.TangentLine")
    orders_txt = "\n".join(out) + "\n"

    # ---------- glue with the Reduction package ----------
    out = []
    w = out.append
    S = sorted(set(orders_found))
    w("import Mathlib")
    w("import Tower.EC.Reduction")
    w(f"import Tower.TangentLine.Orders{p}")
    w("")
    w("/-!")
    w(f"# Reduction modulo a prime above `{p}` of the points over the roots of `Q₄`")
    w("")
    w("This file is generated.  Everything here is conditional on a `Tower.EC.Reduction` package")
    w(f"`R` at `{p}` (an assumption, see `Tower/EC/Reduction.lean`) with `R.res w = {z}`.")
    w("-/")
    w("")
    w("namespace Tower.TangentLine")
    w("")
    w(f"namespace P{p}")
    w("")
    w("open WeierstrassCurve.Affine Tower.EC")
    w("")
    w("variable {K A : Type*} [Field K] [DecidableEq K] [CommRing A] {ι : A →+* K}")
    w("  {W : WeierstrassCurve.Affine K}")
    w("")
    hyps = ["    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)",
            "    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))"]
    hyps2 = ["    (hQ' : Q4 t' w = 0) (hG' : G t' y' = 0) (hF' : F t' y' w = 0)",
             "    (hX' : X' * (t' * y') = -1) (hY' : 2 * Y' = (y' - t') * X' * (X' - 1))"]
    pt = "Point.some (ι X) (ι Y) h"
    pt2 = "Point.some (ι X') (ι Y') h'"
    w("/-- The reduction of the point over a root of `Q₄` is one of the four listed points. -/")
    w(f"theorem red_eq (R : Reduction ι W {p} E) {{w t y X Y : A}}")
    for l in hyps: w(l)
    w(f"    (hw : R.res w = {z}) (h : W.Nonsingular (ι X) (ι Y)) :")
    for idx, t in enumerate(roots, 1):
        w(f"    (R.res t = {t} ∧ R.red ({pt}) = P{idx})" + (" ∨" if idx < 4 else " := by"))
    w("  have rQ : Q4 (R.res t) (R.res w) = 0 := by rw [Q4_map, hQ, map_zero]")
    w("  have rG : G (R.res t) (R.res y) = 0 := by rw [G_map, hG, map_zero]")
    w("  have rF : F (R.res t) (R.res y) (R.res w) = 0 := by rw [F_map, hF, map_zero]")
    w("  have rX : R.res X * (R.res t * R.res y) = -1 := by")
    w("    have e := congrArg R.res hX")
    w("    simp only [map_mul, map_neg, map_one] at e")
    w("    exact e")
    w("  have rY : 2 * R.res Y = (R.res y - R.res t) * R.res X * (R.res X - 1) := by")
    w("    have e := congrArg R.res hY")
    w("    simp only [map_mul, map_sub, map_one, map_ofNat] at e")
    w("    exact e")
    w("  rw [hw] at rQ rF")
    w("  rcases (Q4_roots _).mp rQ with ht | ht | ht | ht")
    for idx, t in enumerate(roots, 1):
        X, Y = pts[idx - 1]
        w("  · rw [ht] at rG rF rX rY")
        w(f"    obtain ⟨hx, hy⟩ := coords{idx} _ _ _ rG rF rX rY")
        w(f"    exact {orterm(idx - 1, 4, f'⟨ht, R.red_some X Y h _ _ ns_{X}_{Y} hx hy⟩')}")
    w("")
    concl = " ∨\n".join(f"    addOrderOf (R.red ({pt})) = {n}" for n in S)
    w(f"/-- The order of the reduction of the point over a root of `Q₄` is one of `{', '.join(map(str, S))}`. -/")
    w(f"theorem red_order (R : Reduction ι W {p} E) {{w t y X Y : A}}")
    for l in hyps: w(l)
    w(f"    (hw : R.res w = {z}) (h : W.Nonsingular (ι X) (ι Y)) :")
    w(concl + " := by")
    w("  rcases red_eq R hQ hG hF hX hY hw h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩")
    for idx in range(1, 5):
        n = orders_found[idx - 1]
        w("  · rw [e]")
        w(f"    exact {orterm(S.index(n), len(S), f'P{idx}_addOrderOf')}")
    SD = sorted(set(diff_orders.values()))
    if with_diffs:
        w("")
        concl = " ∨\n".join(f"    addOrderOf (R.red ({pt} - {pt2})) = {n}" for n in SD)
        w(f"/-- For two distinct roots, the order of the reduction of the difference of the two points is")
        w(f"one of `{', '.join(map(str, SD))}`. -/")
        w(f"theorem red_sub_order [IsDomain A] (R : Reduction ι W {p} E) {{w t y X Y t' y' X' Y' : A}}")
        for l in hyps + hyps2: w(l)
        w(f"    (hne : t ≠ t') (hw : R.res w = {z})")
        w("    (h : W.Nonsingular (ι X) (ι Y)) (h' : W.Nonsingular (ι X') (ι Y')) :")
        w(concl + " := by")
        w(f"  have hd : dQ4 (R.res t) (R.res t') {z} = 0 := by")
        w("    rw [← hw, dQ4_map, dQ4_eq_zero hQ hQ' hne, map_zero]")
        w(f"  have hs : R.red ({pt} - {pt2}) =")
        w(f"      R.red ({pt}) - R.red ({pt2}) := map_sub R.red _ _")
        w("  rw [hs]")
        w("  rcases red_eq R hQ hG hF hX hY hw h with ⟨a, e⟩ | ⟨a, e⟩ | ⟨a, e⟩ | ⟨a, e⟩")
        for i in range(1, 5):
            w("  · rcases red_eq R hQ' hG' hF' hX' hY' hw h' with ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩ | ⟨a', e'⟩")
            for j in range(1, 5):
                if i == j:
                    w("    · rw [a, a'] at hd")
                    w(f"      exact absurd hd diag{i}")
                else:
                    n = diff_orders[(min(i, j), max(i, j))]
                    w("    · rw [e, e']")
                    w(f"      exact {orterm(SD.index(n), len(SD), f'P{i}_sub_P{j}_addOrderOf')}")
    w("")
    w(f"end P{p}")
    w("")
    w("end Tower.TangentLine")
    red_txt = "\n".join(out) + "\n"
    return orders_txt, red_txt, orders_found, diff_orders, S, SD

def nontorsion(info, pa, pb, pc, pd):
    """points: primes (pa, pb); differences: primes (pc, pd)"""
    out = []
    w = out.append
    w("import Mathlib")
    for p in sorted({pa, pb, pc, pd}):
        w(f"import Tower.TangentLine.Red{p}")
    w("")
    w("/-!")
    w("# The points over the roots of `Q₄` have infinite order (conditional on reduction maps)")
    w("")
    w("This file is generated.  Setting: `K` a field, `A` a commutative ring with `ι : A → K`, `W` a")
    w("Weierstrass curve over `K`; `w, t, y, X, Y ∈ A` with `Q₄(t, w) = 0`, `G(t, y) = 0`,")
    w("`F(t, y, w) = 0`, `X t y = -1`, `2 Y = (y - t) X (X - 1)`, so that `(ι X, ι Y)` is the point")
    w("of `W` over the root `t` (see `equation_of_link` for the curve).")
    w("")
    w("**Assumed, not proved:** reduction maps at two primes, as `Tower.EC.Reduction` packages")
    w("(homomorphism; reduces integral coordinates; torsion in the kernel is `p`-primary).")
    w("**Proved:** under these, the point has infinite order, and so does the difference of the")
    w("points over two distinct roots.  The orders of the reductions are computed in")
    w("`Orders*.lean`; they differ at the two primes, which no torsion point allows.")
    w("-/")
    w("")
    w("namespace Tower.TangentLine")
    w("")
    w("open WeierstrassCurve.Affine Tower.EC")
    w("")
    w("variable {K A : Type*} [Field K] [DecidableEq K] [CommRing A] {ι : A →+* K}")
    w("  {W : WeierstrassCurve.Affine K}")
    w("")
    za, zb, zc, zd = info[pa]['z'], info[pb]['z'], info[pc]['z'], info[pd]['z']
    Sa, Sb = info[pa]['S'], info[pb]['S']
    for m1 in Sa:
        for m2 in Sb:
            assert m1 != m2 and m2 % pa and m1 % pb
    pat = lambda n, v: " | ".join([v] * n)
    w(f"/-- **Infinite order.**  Given reduction packages at `{pa}` (with `w ↦ {za}`) and `{pb}`")
    w(f"(with `w ↦ {zb}`), the point over a root of `Q₄` is not a torsion point: its reductions have")
    w(f"orders in `{{{', '.join(map(str, Sa))}}}` and `{{{', '.join(map(str, Sb))}}}`. -/")
    w("theorem addOrderOf_eq_zero_of_reductions")
    w(f"    (R₁ : Reduction ι W {pa} P{pa}.E) (R₂ : Reduction ι W {pb} P{pb}.E) {{w t y X Y : A}}")
    w("    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)")
    w("    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))")
    w(f"    (hw₁ : R₁.res w = {za}) (hw₂ : R₂.res w = {zb}) (h : W.Nonsingular (ι X) (ι Y)) :")
    w("    addOrderOf (Point.some (ι X) (ι Y) h) = 0 := by")
    w(f"  have h₁ := P{pa}.red_order R₁ hQ hG hF hX hY hw₁ h")
    w(f"  have h₂ := P{pb}.red_order R₂ hQ hG hF hX hY hw₂ h")
    w(f"  rcases h₁ with {pat(len(Sa), 'e₁')} <;> rcases h₂ with {pat(len(Sb), 'e₂')} <;>")
    w(f"    exact addOrderOf_eq_zero_of_two_reductions R₁.red R₂.red (p₁ := {pa}) (p₂ := {pb})")
    w("      (by norm_num) (by norm_num) (by norm_num) R₁.ker_torsion R₂.ker_torsion _ e₁ e₂")
    w("      (by norm_num) (by norm_num) (by norm_num)")
    w("")
    Sc, Sd = info[pc]['SD'], info[pd]['SD']
    for m1 in Sc:
        for m2 in Sd:
            assert m1 != m2 and m2 % pc and m1 % pd, (m1, m2)
    w(f"/-- **Non-torsion differences.**  Given reduction packages at `{pc}` (with `w ↦ {zc}`) and")
    w(f"`{pd}` (with `w ↦ {zd}`), the difference of the points over two distinct roots of `Q₄` is not a")
    w(f"torsion point: its reductions have orders in `{{{', '.join(map(str, Sc))}}}` and")
    w(f"`{{{', '.join(map(str, Sd))}}}`. -/")
    w("theorem sub_addOrderOf_eq_zero_of_reductions [IsDomain A]")
    w(f"    (R₁ : Reduction ι W {pc} P{pc}.E) (R₂ : Reduction ι W {pd} P{pd}.E)")
    w("    {w t y X Y t' y' X' Y' : A}")
    w("    (hQ : Q4 t w = 0) (hG : G t y = 0) (hF : F t y w = 0)")
    w("    (hX : X * (t * y) = -1) (hY : 2 * Y = (y - t) * X * (X - 1))")
    w("    (hQ' : Q4 t' w = 0) (hG' : G t' y' = 0) (hF' : F t' y' w = 0)")
    w("    (hX' : X' * (t' * y') = -1) (hY' : 2 * Y' = (y' - t') * X' * (X' - 1))")
    w(f"    (hne : t ≠ t') (hw₁ : R₁.res w = {zc}) (hw₂ : R₂.res w = {zd})")
    w("    (h : W.Nonsingular (ι X) (ι Y)) (h' : W.Nonsingular (ι X') (ι Y')) :")
    w("    addOrderOf (Point.some (ι X) (ι Y) h - Point.some (ι X') (ι Y') h') = 0 := by")
    w(f"  have h₁ := P{pc}.red_sub_order R₁ hQ hG hF hX hY hQ' hG' hF' hX' hY' hne hw₁ h h'")
    w(f"  have h₂ := P{pd}.red_sub_order R₂ hQ hG hF hX hY hQ' hG' hF' hX' hY' hne hw₂ h h'")
    w(f"  rcases h₁ with {pat(len(Sc), 'e₁')} <;> rcases h₂ with {pat(len(Sd), 'e₂')} <;>")
    w(f"    exact addOrderOf_eq_zero_of_two_reductions R₁.red R₂.red (p₁ := {pc}) (p₂ := {pd})")
    w("      (by norm_num) (by norm_num) (by norm_num) R₁.ker_torsion R₂.ker_torsion _ e₁ e₂")
    w("      (by norm_num) (by norm_num) (by norm_num)")
    w("")
    w("end Tower.TangentLine")
    return "\n".join(out) + "\n"

if __name__ == '__main__':
    dest = sys.argv[1]
    info = {}
    for (p, z, roots, exp, diffs) in [(103, 56, [2, 41, 99, 100], [6, 24, 40, 120], True),
                                      (373, 284, [108, 200, 336, 367], [80, 400, 400, 400], False),
                                      (499, 359, [16, 88, 316, 497], [62, 124, 124, 248], True)]:
        otxt, rtxt, orders, dord, S, SD = gen(p, z, roots, exp, diffs)
        info[p] = dict(z=z, S=S, SD=SD)
        for nm, txt in ((f"Orders{p}.lean", otxt), (f"Red{p}.lean", rtxt)):
            open(os.path.join(dest, nm), 'w').write(txt)
        print(p, 'orders by root', orders, 'difference orders', dord, 'lines', otxt.count('\n'), rtxt.count('\n'))
    txt = nontorsion(info, 103, 373, 103, 499)
    open(os.path.join(dest, "NonTorsion.lean"), 'w').write(txt)
    print('NonTorsion lines', txt.count('\n'))
