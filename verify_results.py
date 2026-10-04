#!/usr/bin/env python3
"""
Computational verification for
  "Hybrid Cayley graphs of commuting group--semigroup actions"
Run:  python3 verify_results.py        (needs numpy, networkx)

Section 1  Theorem 3.1 / Props 3.5-3.7  : actionhood criterion, centralizer, invertible part, orbits
Section 2  Theorem 4.1                   : distances, reachability, strong components, right simplicity, terminal components
Section 3  Theorem 4.3                   : spectrum (sumset), block triangular form, spectral radius, multiplicities
Section 4  Worked examples 3.3, 3.4, 5.1, 5.2

Conventions: maps compose right to left; a transformation s acts on the left, (s1 s2)(x)=s1(s2(x)).
The right Cayley digraph of S has arcs s -> s*b.  Every check is brute force on the explicit objects
(the hybrid graph is built vertex by vertex, NOT through the product formula), and the script exits
with a non-zero status if any check fails.
"""
import itertools, random, sys
import numpy as np
import networkx as nx

random.seed(20260929)
TOL = 1e-4
FAILS = []

def check(cond, msg):
    if not cond:
        FAILS.append(msg)

# ----------------------------------------------------------------------------- semigroup toolkit
class Semi:
    """Finite semigroup given by an element list and a multiplication table."""
    def __init__(self, elems, mul):
        self.E = list(elems); self.mul = mul
        self.idx = {e: i for i, e in enumerate(self.E)}
        self.P = {s: frozenset([s] + [mul[s, t] for t in self.E]) for s in self.E}   # s S^1

    def right_simple(self):                       # sS = S for all s
        return all(len({self.mul[s, t] for t in self.E}) == len(self.E) for s in self.E)

    def R_classes(self):
        cl = {}
        for s in self.E: cl.setdefault(self.P[s], []).append(s)
        return cl                                  # key = principal right ideal sS^1

    def min_right_ideals(self):
        ideals = set(self.P.values())
        return [I for I in ideals if not any(J < I for J in ideals)]

    def generated_by(self, B):
        T = set(B); fr = list(B)
        while fr:
            new = []
            for s in fr:
                for b in B:
                    t = self.mul[s, b]
                    if t not in T: T.add(t); new.append(t)
            fr = new
        return len(T) == len(self.E)

def comp(f, g): return tuple(f[g[i]] for i in range(len(g)))

def transformation_semigroup(gens):
    S = set(gens); fr = list(gens)
    while fr:
        new = []
        for s in fr:
            for b in gens:
                t = comp(s, b)
                if t not in S: S.add(t); new.append(t)
        fr = new
    E = sorted(S)
    return Semi(E, {(a, b): comp(a, b) for a in E for b in E})

def right_group(m, r):
    """H x R with H = Z_m and R a right-zero semigroup of size r:  (h,a)(h',a') = (h+h', a')."""
    E = [(h, a) for h in range(m) for a in range(r)]
    return Semi(E, {(x, y): ((x[0] + y[0]) % m, y[1]) for x in E for y in E})

def left_zero(r):
    E = list(range(r)); return Semi(E, {(x, y): x for x in E for y in E})

def chain_min(r):
    E = list(range(1, r + 1)); return Semi(E, {(x, y): min(x, y) for x in E for y in E})

def random_generating_set(S, rng_tries=50):
    for _ in range(rng_tries):
        B = random.sample(S.E, random.randint(1, min(3, len(S.E))))
        if S.generated_by(B): return B
    return list(S.E)

def cyc_A(k):                                      # symmetric generating set of Z_k
    return [1] if k == 2 else [1, k - 1]

def hybrid_matrix(k, A, S, B):
    """Adjacency matrix (multigraph) of the hybrid graph built arc by arc."""
    V = [(g, s) for g in range(k) for s in S.E]; ix = {v: i for i, v in enumerate(V)}
    H = np.zeros((len(V), len(V)))
    for (g, s) in V:
        for a in A: H[ix[g, s], ix[(g + a) % k, s]] += 1          # A-step
        for b in B: H[ix[g, s], ix[g, S.mul[s, b]]] += 1          # B-step
    return V, ix, H

def cayley_matrix(S, B):
    M = np.zeros((len(S.E), len(S.E)))
    for s in S.E:
        for b in B: M[S.idx[s], S.idx[S.mul[s, b]]] += 1
    return M

def multiset_equal(a, b, tol=TOL):
    b = list(b)
    for x in a:
        j = next((i for i, y in enumerate(b) if abs(x - y) < tol), None)
        if j is None: return False
        b.pop(j)
    return not b

# ----------------------------------------------------------------------------- Section 1
def section1(trials=4000, n=4):
    print("== Section 1: actionhood criterion (Theorem 3.1), Props 3.5-3.7 ==")
    stats = dict(valid=0, action=0, action_global_fails=0, cent_nonempty=0, cent_closed=0, inv_ok=0, orb_ok=0)
    for _ in range(trials):
        k = random.choice([2, 3])
        p = list(range(n)); random.shuffle(p); p = tuple(p)
        pw = [tuple(range(n))]
        for _ in range(k - 1): pw.append(comp(p, pw[-1]))
        if comp(p, pw[-1]) != tuple(range(n)): continue          # need p^k = id so G = Z_k really acts
        gens = [tuple(random.randrange(n) for _ in range(n)) for _ in range(random.choice([1, 2]))]
        S = transformation_semigroup(gens)
        if len(S.E) > 40: continue
        stats["valid"] += 1
        a = lambda g, x: pw[g % k][x]
        Y = {s[x] for s in S.E for x in range(n)}
        phi = lambda g, s, x: a(g, s[x])
        action = all(phi(g1, s1, phi(g2, s2, x)) == phi(g1 + g2, S.mul[s1, s2], x)
                     for g1 in range(k) for g2 in range(k) for s1 in S.E for s2 in S.E for x in range(n))
        icY = all(s[a(g, y)] == a(g, s[y]) for s in S.E for g in range(k) for y in Y)
        icX = all(s[a(g, y)] == a(g, s[y]) for s in S.E for g in range(k) for y in range(n))
        check(action == icY, "Thm 3.1: action <=> local IC")                 # the criterion
        check(not icX or icY, "Thm 3.1: global IC => action")
        if icY and Y == set(range(n)): check(icX, "Thm 3.1: Y = X => global IC")
        if action: stats["action"] += 1
        if action and not icX: stats["action_global_fails"] += 1
        # Prop 3.5: intertwining centralizer is a subsemigroup; G x C is a genuine action
        C = [s for s in S.E if all(s[a(g, y)] == a(g, s[y]) for g in range(k) for y in Y)]
        if C:
            stats["cent_nonempty"] += 1
            ok = all(S.mul[s, t] in C for s in C for t in C)
            ok = ok and all(phi(g1, s1, phi(g2, s2, x)) == phi(g1 + g2, S.mul[s1, s2], x)
                            for g1 in range(k) for g2 in range(k) for s1 in C for s2 in C for x in range(n))
            check(ok, "Prop 3.5"); stats["cent_closed"] += ok
        # Prop 3.6: phi_(g,s) bijective <=> b_s bijective; bijective s form a subsemigroup; image is a group
        bij = [s for s in S.E if len(set(s)) == n]
        for s in S.E:
            for g in range(k):
                f = tuple(phi(g, s, x) for x in range(n))
                check((len(set(f)) == n) == (s in bij), "Prop 3.6 injectivity")
        check(all(S.mul[s, t] in bij for s in bij for t in bij), "Prop 3.6 closure")
        if action and bij:
            img = {tuple(phi(g, s, x) for x in range(n)) for g in range(k) for s in bij}
            ident = tuple(range(n))
            grp = all(comp(f, h) in img for f in img for h in img) and \
                  all(any(comp(f, h) == ident for h in img) for f in img) and ident in img
            check(grp, "Prop 3.6 image is a group"); stats["inv_ok"] += grp
        # Prop 3.7: O(x) = G . (S x); preorder is transitive when phi is an action
        for x in range(n):
            O = {phi(g, s, x) for g in range(k) for s in S.E}
            O2 = {a(g, y) for g in range(k) for y in {s[x] for s in S.E}}
            check(O == O2, "Prop 3.7 orbit formula")
        if action:
            Oset = {x: {phi(g, s, x) for g in range(k) for s in S.E} for x in range(n)}
            ok = all(z in Oset[x] for x in range(n) for y in Oset[x] for z in Oset[y])
            check(ok, "Prop 3.7 transitivity"); stats["orb_ok"] += ok
    print("  random (alpha,beta) pairs:", stats["valid"], "| genuine actions:", stats["action"],
          "| action although global IC fails:", stats["action_global_fails"])
    print("  centralizer nonempty:", stats["cent_nonempty"], "| invertible-part group checks:", stats["inv_ok"],
          "| orbit-preorder checks:", stats["orb_ok"])
    return stats

# ----------------------------------------------------------------------------- Section 2 & 3
def graph_cases():
    cases = []
    for _ in range(250):                                                          # random transformation semigroups
        gens = [tuple(random.randrange(4) for _ in range(4)) for _ in range(random.choice([1, 2, 3]))]
        S = transformation_semigroup(gens)
        if len(S.E) <= 9: cases.append((S, list(gens), "transf"))
    for r in range(1, 5):                                                         # right-simple (right groups) and others
        for m in range(1, 4):
            if m * r <= 8:
                S = right_group(m, r); cases.append((S, random_generating_set(S), "right-group"))
    for r in range(2, 5):
        S = left_zero(r); cases.append((S, list(S.E), "left-zero"))
        S = chain_min(r); cases.append((S, list(S.E), "chain-min"))
    return cases

def sections_2_3():
    print("== Section 2: Theorem 4.1 (reachability) and Section 3: Theorem 4.3 (spectrum) ==")
    cnt = dict(cases=0, strongly=0, nonstrongly=0)
    for S, B, kind in graph_cases():
        check(S.generated_by(B), "generating set")
        k = random.choice([2, 3, 4]); A = cyc_A(k)
        V, ix, H = hybrid_matrix(k, A, S, B)
        D = nx.from_numpy_array(H, create_using=nx.DiGraph)
        cl = S.R_classes(); minI = S.min_right_ideals()
        cnt["cases"] += 1
        # --- 4.1(a): additive distance, computed independently by BFS on the explicit graphs
        dist = dict(nx.all_pairs_shortest_path_length(D))
        DS = nx.from_numpy_array(cayley_matrix(S, B), create_using=nx.DiGraph)
        dS = dict(nx.all_pairs_shortest_path_length(DS))
        dG = lambda g, h: min((g - h) % k, (h - g) % k)
        for (g, s) in V:
            for (h, t) in V:
                d1 = dist[ix[g, s]].get(ix[h, t]); d2 = dS[S.idx[s]].get(S.idx[t])
                check((d1 is None) == (d2 is None) and (d1 is None or d1 == dG(g, h) + d2), "4.1(a) distance")
                # --- 4.1(b): reachable <=> t in sS^1
                check((d1 is not None) == (t in S.P[s]), "4.1(b) reachability")
        # --- 4.1(c): strong components = G x R-classes
        sccs = {frozenset(c) for c in nx.strongly_connected_components(D)}
        expect = {frozenset(ix[g, s] for g in range(k) for s in R) for R in cl.values()}
        check(sccs == expect, "4.1(c) strong components")
        # --- 4.1(d): strongly connected <=> right simple (<=> single R-class)
        sc = nx.is_strongly_connected(D)
        check(sc == S.right_simple() == (len(cl) == 1), "4.1(d) right simple")
        cnt["strongly" if sc else "nonstrongly"] += 1
        if kind == "right-group": check(sc, "right groups give strongly connected graphs")
        if kind == "left-zero" and len(S.E) > 1: check(not sc, "left zero (not right simple) is not strongly connected")
        # --- 4.1(e): terminal components <-> minimal right ideals
        cond = nx.condensation(D, scc=[set(c) for c in sccs])
        term = {frozenset(cond.nodes[n]["members"]) for n in cond.nodes if cond.out_degree(n) == 0}
        check(term == {frozenset(ix[g, s] for g in range(k) for s in I) for I in minI}, "4.1(e) terminal components")
        # --- 4.3(a): spectrum = sumset of component spectra (hybrid matrix built arc-by-arc, not as a Kronecker sum)
        N = np.zeros((k, k))
        for g in range(k):
            for a in A: N[g, (g + a) % k] += 1
        M = cayley_matrix(S, B)
        kap = np.linalg.eigvalsh(N); mu = np.linalg.eigvals(M)
        evH = np.linalg.eigvals(H)
        check(multiset_equal(evH, [x + y for x in kap for y in mu]), "4.3(a) sumset")
        # --- 4.3(b): block upper triangular form w.r.t. a linear extension of the R-order; spec = union of block spectra
        order = list(nx.topological_sort(nx.condensation(nx.from_numpy_array(M, create_using=nx.DiGraph))))
        cM = nx.condensation(nx.from_numpy_array(M, create_using=nx.DiGraph))
        perm = [i for c in order for i in sorted(cM.nodes[c]["members"])]
        Mp = M[np.ix_(perm, perm)]
        pos = 0; blocks = []
        for c in order:
            sz = len(cM.nodes[c]["members"]); blocks.append((pos, pos + sz)); pos += sz
        ok = True
        for bi, (l1, r1) in enumerate(blocks):
            for bj, (l2, r2) in enumerate(blocks):
                if bj < bi and np.any(Mp[l1:r1, l2:r2] != 0): ok = False
        check(ok, "4.3(b) block triangular")
        diag_ev = [e for (l, r) in blocks for e in np.linalg.eigvals(Mp[l:r, l:r])]
        check(multiset_equal(mu, diag_ev), "4.3(b) spectrum = union of block spectra")
        # --- 4.3(c): spectral radii
        check(abs(max(abs(mu)) - len(B)) < TOL, "4.3(c) rho(M) = |B|")
        check(abs(max(evH.real) - (len(A) + len(B))) < TOL and abs(max(abs(evH)) - (len(A) + len(B))) < TOL, "4.3(c) rho(H) = |A|+|B|")
        # --- 4.3(d): multiplicity m of the top eigenvalue, strict inequality for all other eigenvalues
        m = len(minI); rho = len(A) + len(B)
        top = [e for e in evH if abs(e - rho) < 1e-3]
        check(len(top) == m, "4.3(d) multiplicity = number of minimal right ideals")
        check(all(e.real < rho - 1e-3 for e in evH if abs(e - rho) >= 1e-3), "4.3(d) Re nu < rho for other eigenvalues")
        check(sum(abs(e - len(B)) < 1e-3 for e in mu) == m, "4.3(d) multiplicity of |B| in M")
    print("  graph cases:", cnt["cases"], "| strongly connected:", cnt["strongly"], "| not strongly connected:", cnt["nonstrongly"])
    return cnt

# ----------------------------------------------------------------------------- Section 4
def examples():
    print("== Section 4: worked examples ==")
    X = [1, 2, 3, 4]
    # Example 3.3 (genuine action, global commutation fails)
    a1 = {1: 2, 2: 1, 3: 4, 4: 3}
    psi = {"s": {1: 1, 2: 2, 3: 1, 4: 1}, "t": {1: 1, 2: 2, 3: 2, 4: 2}}
    act = lambda g, x: x if g == 0 else a1[x]
    phi = lambda g, s, x: act(g, psi[s][x])
    mul = lambda s, t: t                                            # right-zero semigroup
    is_act = all(phi((g1 + g2) % 2, mul(s1, s2), x) == phi(g1, s1, phi(g2, s2, x))
                 for g1 in (0, 1) for g2 in (0, 1) for s1 in psi for s2 in psi for x in X)
    Y = {psi[s][x] for s in psi for x in X}
    icY = all(psi[s][act(g, y)] == act(g, psi[s][y]) for s in psi for g in (0, 1) for y in Y)
    icX = all(psi[s][act(g, y)] == act(g, psi[s][y]) for s in psi for g in (0, 1) for y in X)
    print(f"  Ex 3.3: action={is_act}, IC on Y={icY}, global IC={icX}   (expected True, True, False)")
    check(is_act and icY and not icX, "Example 3.3")
    # Example 3.4 (pre-action)
    al = lambda g, x: x if g == 0 else 5 - x
    ph = lambda g, s, x: al(g, min(s, x))
    v1 = ph(1, 2, ph(1, 2, 1)); v2 = ph(0, 2, 1)
    Yc = {min(s, x) for s in (1, 2) for x in X}
    icYc = all(min(s, al(g, y)) == al(g, min(s, y)) for s in (1, 2) for g in (0, 1) for y in Yc)
    print(f"  Ex 3.4: phi((1,2),phi((1,2),1)) = {v1}, phi((0,2),1) = {v2}, IC on Y = {icYc}   (expected 3, 1, False)")
    check((v1, v2, icYc) == (3, 1, False), "Example 3.4")
    # Example 5.1
    S = right_group(1, 2); B = list(S.E)
    V, ix, H = hybrid_matrix(2, [1], S, B)
    ev = sorted(np.linalg.eigvals(H).real)
    print("  Ex 5.1: spectrum", np.round(ev, 6), "(expected [-1, 1, 1, 3]); strongly connected:",
          nx.is_strongly_connected(nx.from_numpy_array(H, create_using=nx.DiGraph)))
    check(multiset_equal(ev, [-1, 1, 1, 3]), "Example 5.1 spectrum")
    # Example 5.2
    S = chain_min(3); B = list(S.E)
    V, ix, H = hybrid_matrix(4, [1, 3], S, B)
    ev = sorted(np.linalg.eigvals(H).real)
    print("  Ex 5.2: spectrum", np.round(ev, 6))
    check(multiset_equal(ev, [5, 4, 3, 3, 3, 2, 2, 1, 1, 1, 0, -1]), "Example 5.2 spectrum")
    # layer-by-layer reading of Figure 1: 4-cycle spectrum shifted by 4-s
    for s in (1, 2, 3):
        loops = sum(min(s, b) == s for b in B)
        check(loops == 4 - s, "loops per layer = 4 - s")
    print("  layer shifts (loops per layer s=1,2,3):", [sum(min(s, b) == s for b in B) for s in (1, 2, 3)])
    # The dissertation's invalid example, for the record: B = {1} does not generate ({1,2}, min)
    S2 = chain_min(2)
    print("  ({1,2},min) generated by {1}?", S2.generated_by([1]), "(False: B must be all of S for a chain)")
    check(not S2.generated_by([1]), "generation remark")

if __name__ == "__main__":
    s1 = section1()
    c = sections_2_3()
    examples()
    print()
    if FAILS:
        from collections import Counter
        print("FAILED checks:", dict(Counter(FAILS))); sys.exit(1)
    print("ALL CHECKS PASSED")
