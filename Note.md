# Sources and mathematical scope

This account preserves the primary-source comparison performed in Analytic-Lab
on **2026-10-09**. It is a bounded literature audit, not a priority determination
or an independent specialist review. The written precursor is pinned at
[`c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f`](https://github.com/JD-Jones-ASES/Analytic-Lab/tree/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient).

## The original question

Adrien B. Taylor, Julien M. Hendrickx and François Glineur,
[*Smooth Strongly Convex Interpolation and Exact Worst-case Performance of
First-order Methods*](https://arxiv.org/abs/1502.05666),
*Mathematical Programming* 161 (2017), 307–345,
[DOI 10.1007/s10107-016-1009-3](https://doi.org/10.1007/s10107-016-1009-3),
state Conjecture 3 in Section 4.1.3 of the
[author manuscript](https://optimization-online.org/wp-content/uploads/2015/03/4814.pdf).
The smooth-convex specialization concerns the norm of the **last gradient**
under an **initial-distance bound**. This is the normalization used here.
Their Huber and quadratic examples supply the two lower branches.

The full conjecture also includes a prescribed positive strong-convexity
parameter. The present project resolves the smooth-convex specialization;
it makes no claim to that additional parameter regime. Squaring the norm
bound squares the entire factor. Replacing the normalization by initial
function gap, or the terminal gradient by the smallest gradient seen so far,
would state a different result.

## Chikhi's balancing-step certificate

Salah R. Chikhi,
[*Last-Iterate Performance of Gradient Descent and Relaxed Proximal Point via
s-Composability*, v1](https://arxiv.org/html/2609.13765v1), September 12, 2026,
Section 4, supplies the factorized multiplier shape and the all-horizon
balancing-step result. Those mathematical ingredients motivated this work.
The precursor also checked [v2](https://arxiv.org/html/2609.13765v2), dated
September 20, 2026: its abstract and Section 1.1 still leave the complete
constant-step final-gradient curve open.

The contribution developed here is the choice of factors with **uniform
divergence** across all nonterminal iterates, the quadratic-root comparison
that proves their positivity throughout the oscillation branch, and the
scaling argument that retains the interpolation surplus to recover every
smaller step. [Proof.md](Proof.md) reconstructs every required coefficient
identity and sign. Chikhi's theorem is not an unproved premise of the Lean
development, but his published factorization remains a material source.
The appropriate provenance is a source-based adaptation.

## Nearby rate and proximal results

| Primary source | Checked relationship |
|---|---|
| Jungbin Kim, [*A Proof of the Exact Convergence Rate of Gradient Descent*, arXiv:2412.04427v2](https://arxiv.org/html/2412.04427v2), March 26, 2025 | Theorem 1.3 bounds final objective gap by initial squared distance; Theorem 1.5 bounds final squared gradient by initial objective gap. Composition gives the even-horizon target. Those published results explain a separate precursor argument, but are not imported as assumptions in this self-contained certificate. |
| Wang, Ma, Yang and Zhou, [*Relaxed Proximal Point Algorithm: Tight Complexity Bounds and Acceleration without Momentum*, arXiv:2410.08890v1](https://arxiv.org/html/2410.08890v1), Theorem 3.1 and Remark 3.1; [published abstract](https://pubsonline.informs.org/doi/abs/10.1287/ijoo.2025.0075) | The checked baseline covers constant relaxation through the square root of two. Chikhi supplies a balanced-step proximal result. The direct application here treats every nonnegative relaxation, the exact last residual, and the progress-branch objective–residual tradeoff. |

The proximal proof starts from literal minimization of the quadratic-regularized
objective over a convex feasible set. Its variational inequality is derived,
not supplied as an unexplained algorithm assumption. General cocoercive
operators do not satisfy all the function-interpolation information used by
the proof. No corresponding sharp rate is claimed for every such operator.

## Equality, scope and review

The structural extension classifies all equality trajectories and sampled
function values. At balance it allows an orthogonal mixture of progress and
oscillation. It does not say that every worst case is one-dimensional or
classify the objective away from the visited region. The fixed-metric
preconditioning interpretation follows by choosing the Hilbert-space inner
product; a changing preconditioner is outside scope.

Strict-branch quantitative stability is retained as supplementary written
mathematics. Proximal trajectories include their terminal minimizer; existence
of a total proximal operator for every extended-real objective is outside the
first formal contract. [VERIFICATION.md](VERIFICATION.md) distinguishes the
compiled contract from written extensions.

The precursor's bounded searches found no earlier complete resolution of this
precise curve. Absence from those searches does not establish worldwide
priority. Internal agent audits, Lean verification, release preparation,
Palomar submission, registration and human peer review are distinct statuses.
