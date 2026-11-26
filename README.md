# Equality in the Pólya-type bound for Dirichlet trees

A proof answering **Open Problem 1.12(3)** of E. M. Harrell II, J. B. Kennedy and G. J. Ramos,
*Bounds on eigenvalue ratios of quantum graph Laplacians*, [arXiv:2603.26172](https://arxiv.org/abs/2603.26172) (2026).

## The problem

For a compact Dirichlet tree Γ (a metric tree with Dirichlet conditions at the leaves and Kirchhoff conditions at the
other vertices) of total length L, the Laplacian eigenvalues satisfy the Pólya-type bound

  λ_k(Γ) ≥ π²k²/L²  for every k ≥ 1.   (1.6)

> **Open Problem 1.12(3).** Characterize the case of equality in (1.6) for all k ≥ 1. Is it true that there is
> equality if and only if all edges of Γ have length equal to an integer multiple of L/k?

The authors note that "if" is immediate and "only if" is not hard for k = 1, 2.

## Result

**Theorem.** Let Γ be a compact Dirichlet tree of total length L without degree-2 vertices, and let k ≥ 1.
Then λ_k(Γ) = π²k²/L² **if and only if every edge length is a positive integer multiple of L/k.**

So the answer to Open Problem 1.12(3) is **yes**, for every k.

**Idea of the proof.** For generic ω, the number of eigenvalues below ω² equals Σ_e ⌊t_e/π⌋, where the t_e are
Prüfer-type angles propagated from the leaves to a root by cot s = Σ cot t_i at each vertex. This turns
ωL/π − N(ω²) into a sum of local vertex terms Σ τ_i − s, each strictly positive by an elementary cotangent
inequality. That gives (1.6) again, and in the equality case forces every angle to vanish in the limit ω ↓ πk/L,
which is exactly the statement that every edge is a multiple of L/k. Full proof: [PROOF.md](PROOF.md).

## Status, honestly

- **Proof:** complete, written for a mathematician in [PROOF.md](PROOF.md).
- **Audit:** checked by an independent AI referee working from the paper, with its own code (verdict CORRECT,
  four small write-up gaps, all fixed): [AUDIT.md](AUDIT.md). **Not yet checked by a human expert.**
- **Numerics (evidence, not proof):** 16,008 random (tree, k) cases with 1,339 equality cases, and a second
  independent check with 4,641 cases. In every equality case all edges were multiples of L/k.
- **Lean 4 / Mathlib:** the algebraic identities and the two-child vertex lemma (the analytic heart of the
  counting step) are formally proved. The spectral parts (H¹ on metric graphs, min-max, inertia) are stated
  but left as `sorry`, since Mathlib has no spectral theory of quantum graphs yet. See PROOF.md §5.
- **AI use:** the proof was found, written and checked with AI assistance (Claude). I take responsibility for the
  claims here; corrections are very welcome.

## Reproduce

```bash
pip install -r requirements.txt
python scripts/check_identities.py      # symbolic check of the edge form, Schur, pivot and vertex identities
python scripts/test1.py                  # Prüfer count vs independent Dirichlet-to-Neumann count, 300 random trees
python scripts/test2.py 11 3000          # equality-case search, k = 1..6 (logged run: logs/test2_seed11.log)
cd independent-checks && python t_basic.py && python t_rand.py   # the auditor's independent code
```

Lean (toolchain in `lean/lean-toolchain`, Mathlib `v4.37.0-rc1`):

```bash
cd lean && lake exe cache get && lake build
```

## Files

- `PROOF.md`: full statement and proof, verification table, Lean status
- `AUDIT.md`: the independent referee report
- `scripts/`: identity checks and numerical tests (logs in `logs/`)
- `independent-checks/`: the auditor's separate implementation
- `lean/`: Lean 4 formalization

## Reference

E. M. Harrell II, J. B. Kennedy, G. J. Ramos, *Bounds on eigenvalue ratios of quantum graph Laplacians*,
arXiv:2603.26172 (2026).
