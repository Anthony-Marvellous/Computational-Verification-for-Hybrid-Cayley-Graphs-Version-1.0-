# Computational-Verification-for-Hybrid-Cayley-Graphs-Version-1.0-

# Hybrid Cayley graphs of group–semigroup actions — verification code

Supplementary code for the paper

> **Hybrid Cayley graphs of commuting group–semigroup actions: an exact actionhood criterion, reachability structure and spectra**
> Anthony Marvellous

The script `verify_results.py` checks every theorem, proposition and worked example in the paper by brute force on explicit finite objects. It exits with status 0 and prints `ALL CHECKS PASSED` if nothing fails.

## What is checked

| Paper result | Check |
|---|---|
| Theorem 3.1 (actionhood criterion) | For random pairs of a group action α (G = Z_k) and a semigroup action β (a transformation semigroup) on a 4-point set, whether φ((g,s),x) = α(g, β(s,x)) is an action is decided directly from φ_u∘φ_v = φ_{u⊛v} and compared with the local intertwining condition on Y = β(S×X) |
| Props 3.1–3.3 | The intertwining centralizer is a subsemigroup on which φ is an action; invertible part of φ and its image (a group); orbit formula and transitivity of the reachability preorder |
| Theorem 4.1 | On the hybrid graph built arc by arc: distances equal d_G + d_S, reachability iff s′ ∈ sS¹, strong components = G × (R-classes), strongly connected iff right simple, terminal components = G × (minimal right ideals) |
| Theorem 4.3 | Spectrum equals the sumset of the component spectra, block-triangular form with spectrum the union of the block spectra, ρ = \|A\| + \|B\|, multiplicity of ρ equals the number of minimal right ideals, all other eigenvalues have real part < ρ |
| Examples 3.1, 3.2, 3.3, 3.4 | Reproduced exactly (including the spectra and the per-layer loop counts used to explain Figure 1) |

Test families for Theorems 4.1 and 4.3: random transformation semigroups, right groups Z_m × R_r, left-zero bands and min-chains.

## Running it

Python 3.9 or later is recommended.

```bash
pip install -r requirements.txt
python3 verify_results.py
```

The random seed is fixed, so runs are repeatable on the same Python version. The exact counts of random cases (for example 1458 action pairs, 224 genuine
