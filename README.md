# Equality in the Pólya-type bound for Dirichlet trees

This repository contains a proof that the answer to Open Problem 1.12(3) of E. M. Harrell II,
J. B. Kennedy and G. J. Ramos, *Bounds on eigenvalue ratios of quantum graph Laplacians*,
[arXiv:2603.26172](https://arxiv.org/abs/2603.26172) (2026), is yes.

## The problem and the result

Let Γ be a compact Dirichlet tree of total length L: a metric tree with Dirichlet conditions at the leaves
and Kirchhoff conditions at the other vertices. Harrell, Kennedy and Ramos note that its Laplacian
eigenvalues satisfy

  λ_k(Γ) ≥ π²k²/L²  for every k ≥ 1,   (1.6)

and ask whether equality holds exactly when every edge length is an integer multiple of L/k. They remark
that the "if" direction is immediate and that "only if" is not hard for k = 1, 2.

**Theorem.** Let Γ be a compact Dirichlet tree of total length L without vertices of degree 2, and let
k ≥ 1. Then λ_k(Γ) = π²k²/L² if and only if every edge length is a positive integer multiple of L/k.

The restriction on degree-2 vertices is the convention of the paper, and it is needed: a dummy vertex
placed at a generic point of an interval gives equality for every k.

**Idea of the proof.** For all but a discrete set of frequencies ω, the number of eigenvalues below ω²
equals Σ_e ⌊t_e/π⌋, where the angles t_e are carried from the leaves to a root, increasing by ωℓ_e along
each edge and combining at a vertex by cot s = Σ cot t_i. With this formula, ωL/π minus that number becomes a sum of
one term Σ τ_i − s per vertex, and each term is positive by an elementary inequality for the cotangent.
This reproves (1.6). If equality holds, the sum tends to 0 as ω decreases to πk/L, which forces every angle
to 0 modulo π, and that is the statement that every edge is a multiple of L/k. The full argument is in
[PROOF.md](PROOF.md).

## Status

- **Proof.** Complete and written for a mathematician in [PROOF.md](PROOF.md). It has **not yet been
  checked by a human expert**.
- **AI assistance.** The proof was found and written with the help of Claude (Anthropic). Three further,
  separate Claude sessions checked it, two of them asked to look for an error. They found none in the
  mathematics, and the gaps they found in the write-up have been filled. See [CHECKS.md](CHECKS.md).
- **Computer checks.** The algebraic identities used in the proof were verified symbolically. In a search
  over 16,008 pairs (tree, k), every case of equality had all edges multiples of L/k. A second implementation
  written independently agrees. These computations are evidence, not proof.
- **Lean.** Steps 3–4 of the proof are formalized in Lean 4 with Mathlib with no `sorry`. The
  eigenvalue-counting formula (2), which Steps 1–2 derive from standard spectral facts not available in
  Mathlib, enters as an explicit hypothesis `SpectralInput`; from it Lean derives both (1.6) and the
  Theorem. See
  PROOF.md, Section 7.

I take responsibility for the claims made here. Corrections and references to earlier work are welcome.

## Reproducing the checks

```bash
pip install -r requirements.txt
python scripts/check_identities.py      # symbolic check of the identities in Steps 1-3
python scripts/test1.py                 # angle count against an independent eigenvalue count, 300 random trees
python scripts/test2.py 11 3000         # search for counterexamples, k = 1..6 (logged run: logs/test2_seed11.log)
cd independent-checks && python t_basic.py && python t_rand.py   # the independent implementation
```

Lean (toolchain in `lean/lean-toolchain`, Mathlib `v4.37.0-rc1`):

```bash
cd lean && lake exe cache get && lake build
```

## Contents

- `PROOF.md`: statement, proof, remarks on the hypotheses, computer checks, Lean formalization
- `CHECKS.md`: the three independent checks and the corrections they led to
- `scripts/`, `logs/`: symbolic and numerical checks with their output
- `independent-checks/`: the separate implementation written during the first check
- `lean/`: the Lean 4 formalization

## Reference

E. M. Harrell II, J. B. Kennedy and G. J. Ramos, *Bounds on eigenvalue ratios of quantum graph Laplacians*,
arXiv:2603.26172 (2026).
