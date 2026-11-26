# Independent checks of the proof

The proof in [PROOF.md](PROOF.md) was found and written with the help of Claude, an AI model made by
Anthropic. To test it, we ran three further sessions of Claude, each separate from the one that wrote the
proof and from each other. Each was given the source paper [HKR] and the proof, and each wrote its own
code. The first was asked to check the proof. The second and third were asked to assume the proof was
wrong and to look for the error; one of them concentrated on the analytic steps, the other on the
combinatorial ones, and neither saw the report of the first. None of the three found an error in the
mathematics. Each pointed out places where the write-up skipped an argument or was imprecise, and those
places have been corrected in PROOF.md, as listed below.

These checks were done by AI models, not by a specialist in the field, and should be read in that light.

## First check

**Statement.** The checker extracted the text of [HKR] itself and confirmed that the problem is stated
correctly: Dirichlet trees have no cycles, Dirichlet conditions at the vertices of degree 1 and Kirchhoff
conditions elsewhere; degree-2 vertices are suppressed throughout [HKR]; λ_k is indexed from k = 1 with
multiplicity; and the Theorem answers Open Problem 1.12(3) for every k.

**Proof.** It re-derived the counting formula (1), the pivot identity and the update at the parent vertex,
the vertex lemma and the limit argument, and found them correct. It asked for four additions:

1. the step from negative pivots to floors, ⌊ω′ℓ_e/π⌋ + [p_c < 0] = ⌊t_e/π⌋ (now in Section 4.2, "From
   negative pivots to floors");
2. a proof that the non-generic frequencies form a discrete set (Section 4.2, "The exceptional set is
   discrete");
3. the induction from two children to d children in the vertex lemma, which must start at d = 2 (Section
   4.3);
4. a proof that the angles are monotone near πk/L, so that the right limits exist and lie in [0, π)
   (Section 4.4, "The angles are monotone on J").

**Computations.** Its own code, in `independent-checks/`, counts eigenvalues from the
Dirichlet-to-Neumann matrix and by finite elements, and shares no code with `scripts/`. It scanned stars
and H-shaped trees for k = 1, …, 7, including cases where eigenfunctions vanish on whole edges; compared
the angle count (2) with its own count on 400 random trees; and tested 4,641 random pairs (tree, k). In all
cases (1.6) held, formula (2) agreed, and equality occurred exactly when every edge was a multiple of L/k.

## Second check: the analytic steps

This checker went through the setting and Steps 1–4 and confirmed in particular:

- the form domain and the vertex conditions agree with [HKR, §2];
- H = H_harm ⊕ H_0 is a direct sum (a function in both has zero vertex values, hence is 0 because
  sin(ω′ℓ_e) ≠ 0), and the two summands are Q-orthogonal; it re-derived the edge form by hand;
- negative indices add over the splitting even when Q has a kernel on a summand;
- D_c is entire and not identically zero, and off E all pivots are nonzero, which forces sin t_e ≠ 0;
- multiplicities and eigenfunctions vanishing at vertices play no role in the argument.

It pointed out four imprecisions, all corrected: the inequality "≥" in the additivity of indices was not
proved; for d = 2 the vertex lemma gave "f > g" where "f ≥ g" was meant; Section 4.4 mixed up
"nondecreasing" and "strictly increasing"; and the write-up did not say that Dirichlet conditions at
interior vertices are excluded (now Remark 5.4).

Its computations used its own finite-element solver and determined multiplicities to 30 digits. On
equilateral stars with 3 to 8 edges, equality held exactly when the number of edges divides k. On random
trees, including near-equality cases with multiple eigenvalues, it found no counterexample, and a numerical
minimization of λ_k/(πk/L)² − 1 over the edge lengths of stars found minima only at the predicted lengths
or at degenerate boundary points.

## Third check: the combinatorial steps

This checker confirmed in particular:

- without degree-2 vertices every interior vertex has at least two children, and a single edge is also
  covered;
- in the step from pivots to floors the factors (−1)ⁿ cancel for every n, including n = 0;
- the grouping in identity (3) matches each interior vertex c with its parent edge e_c, edges starting at a
  leaf have s = 0, and the root edge contributes τ_root on its own;
- in Step 4, τ_e increases and stays below π, so its right limit is not π; ⌊t_e/π⌋ is constant on J; and
  m_e ≥ 1;
- the answer "yes" depends on suppressing degree-2 vertices, which is the convention of [HKR] (Remark 5.1).

It asked for the same wording corrections as the second check and, in addition, for "closed span" in
Section 4.1. Its computations compared the angle count with a finite-element count on 150 random trees
(no disagreements), tested identity (3) and the vertex lemma on random inputs, and searched 2,000 pairs
(tree, k) for counterexamples without finding one. The code of the second and third checks is not included
in this repository.

## Reference

[HKR] E. M. Harrell II, J. B. Kennedy and G. J. Ramos, Bounds on eigenvalue ratios of quantum graph
Laplacians, arXiv:2603.26172v1 (2026).
