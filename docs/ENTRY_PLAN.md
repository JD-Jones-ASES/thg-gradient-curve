> Historical design contract, copied from the pinned Lab precursor before implementation.
> Repository creation and Lean work were subsequently authorized on October 9, 2026.
> See ../VERIFICATION.md for current status.

# Planned Palomar entry: sharp last-iterate bounds and extremal trajectories

Date: 2026-10-09. **Planning and mathematical development only.** JD asked
for the entry structure, useful extensions/applications, and a Lean plan;
the separate repository will be built in a later session. No Lean source,
new repository, public release, or submission is authorized by this plan.

The base proof is pinned at
[`2aee32de27e8c34fb668e4600e05f203d1e32531`](https://github.com/JD-Jones-ASES/Analytic-Lab/tree/2aee32de27e8c34fb668e4600e05f203d1e32531).
Start with [PROOF](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/PROOF.md), then [UNIFORM_CERTIFICATE](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/UNIFORM_CERTIFICATE.md).
The [Lean plan](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/LEAN_PLAN.md) records verified library APIs and uncompiled
implementation choices. This document is the editorial and theorem contract.

## 1. One coherent entry

Recommended title: **Sharp last-iterate bounds and extremal trajectories
for constant-step gradient descent**.

The entry should lead with the exact final-gradient curve for actual convex
smooth functions, then explain what equality looks like and transfer the
same argument to proximal minimization. Its research audience is convex
optimization, first-order complexity, and performance-estimation methods.
The explicit certificate is the proof mechanism; it is not a replacement
for the analytic theorem in the public statement.

The opening mathematical statement is

    ||grad f(x_N)|| <= L||x_0-x_*|| rho_N(h),
    rho_N(h)=max{1/(1+Nh), |1-h|^N},
    x_{i+1}=x_i-(h/L)grad f(x_i).

State all horizons, all dimensions, every convex differentiable objective
with L-Lipschitz gradient and an attained minimum, and every constant step
in the claimed range. The original conjecture's range is 0<=h<=2; the
elementary continuation to h>2 belongs in the same rate theorem once
formalized. Explain that the factor then describes possible growth.

The self-contained proof only uses finite inner-product identities and
smooth convex interpolation. We should therefore implement the main theorem
over a real Hilbert space and display the Euclidean specialization explicitly.
Sharpness only needs real one-dimensional examples.

The [geometry extension](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/EXTENSIONS_GEOMETRY.md) and
[proximal application](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/EXTENSIONS_PROXIMAL.md) supply the additional written
mathematics. Their Lean status is still **not implemented**.

Draft abstract for the completed package, to be updated against the final
compiled contract before use:

> We establish the exact worst-case norm of the final gradient after a
> fixed number of constant-step gradient-descent iterations on a smooth
> convex function, under an initial-distance bound. The result holds in
> real Hilbert spaces and resolves the smooth-convex specialization of
> Taylor–Hendrickx–Glineur's Conjecture 3. We construct a nonnegative
> interpolation certificate extending the balanced-step factorization of
> Chikhi. Sharp examples attain both branches. We classify every equality
> trajectory: constant-gradient progress, quadratic oscillation, and their
> orthogonal mixtures at the balancing step. A direct optimality argument
> transfers the certificate to relaxed proximal minimization, giving its
> exact final-residual curve and a sharp objective–residual tradeoff over
> the progress branch.

The Hilbert-space statement also covers fixed metric preconditioning.
If a positive definite matrix M defines `||x||_M^2=x^T M x`, the gradient
in this inner product is `M^(-1) grad f`, and its norm equals the ordinary
gradient's dual norm `||grad f||_{M^(-1)}`. Under L-smoothness in that
metric, the same theorem gives

    x_{i+1}=x_i-(h/L)M^(-1)grad f(x_i),
    ||grad f(x_N)||_{M^(-1)} <= L||x_0-x_*||_M rho_N(h).

This is an interpretation of the generic inner-product theorem, not a
separate contribution requiring a matrix-heavy formalization in the first
entry. A changing preconditioner is not covered.

## 2. Proposed public claims

Use one Comparator configuration and a small statement surface. The names
below are proposed identifiers, not existing Lean declarations.

| Proposed declaration | Mathematical content | Role |
|---|---|---|
| `THGGradient.last_gradient_bound` | Full sharp upper bound for actual smooth convex functions, all horizons, real Hilbert spaces, and h>=0 | Principal theorem |
| `THGGradient.scalar_attainment` | For every N,h,L,R with L,R>0, a genuine convex L-smooth real function and trajectory attain rho_N(h) | Makes the rate exact |
| `THGGradient.progress_joint_bound` | Joint terminal distance, function gap, and squared-gradient bound throughout the progress branch | Stronger structural theorem |
| `THGGradient.progress_equality` | Complete constant-gradient trajectory characterization for strict progress steps | Extremal structure |
| `THGGradient.oscillation_equality` | Complete alternating quadratic trajectory characterization for strict oscillation steps | Extremal structure |
| `THGGradient.balance_equality` | At the balancing step, precisely the orthogonal combination of progress and oscillation trajectories | Main structural extension |
| `THGGradient.proximal_residual_bound` | Exact rate for relaxed iterations of actual proximal minimizers over a convex feasible set | Application |
| `THGGradient.proximal_residual_attainment` | Absolute-value and singleton-feasible-set examples attain both residual branches | Sharpness of the application |
| `THGGradient.proximal_progress_tradeoff` | Sharp relation between terminal proximal objective gap and residual throughout the progress branch | Useful accuracy guarantee |
| `THGGradient.proximal_objective_attainment` | The resulting objective-gap constant is attained by an explicit real example | Exactness of that consequence |

This is the preferred complete package, not a claim that ten declarations
have compiled. Implement and audit the first two before investing in the
rest. A release describing equality or proximal sharpness must include
those corresponding proofs in its compared contract. If the eventual
scope changes, rewrite the abstract to match it rather than leaving an
unproved advertised extension.

Keep strict-branch quantitative stability in the written supplement for
the first release. It is useful, but its parameter-dependent constants
would add a long public statement and more bookkeeping. The all-N
certificate and equality classification already give a coherent entry.

## 3. Make the analytic meaning auditable

The public gradient theorem may quantify over a field `g` with
`HasGradientAt f (g x) x` for every x. This expresses the actual gradient;
it must not replace differentiability by an assumed interpolation oracle.
State convexity, the Lipschitz bound, and minimization in ordinary Mathlib
terms. A supplied trajectory with the literal gradient-descent recurrence
avoids exposing a custom iterator as a new trusted definition.

For proximal minimization, use a convex feasible set C and a real objective
F convex on C. Each z_i must actually minimize

    z in C |-> lambda F(z) + ||x_i-z||^2/2,

and the relaxed update is `x_{i+1}=x_i+h(z_i-x_i)`. The statement applies
to any such trajectory. The proof must derive the needed variational
inequalities from this minimization condition; assuming certificate
inequalities in the public application would lose the intended result.
This formulation includes constrained objectives and indicator examples
without requiring an extended-real API. General proximal existence is a
separate issue from the rate of an actual proximal trajectory.

The finite interpolation-data theorem is a valuable internal interface:
prove it once, then instantiate it from gradients and proximal minimizers.
It may be documented as a reusable lemma, but it cannot be the only
principal contract.

Equality is a classification of the trajectory and sampled function values.
It does **not** classify the objective away from the visited region. At
balance, mixtures in orthogonal directions must be included: claiming
that every worst case is one-dimensional would be false.

## 4. Narrative and files in the future repository

Suggested repository name: `thg-gradient`; suggested Lean package/namespace
stem: `THGGradient`. These are proposals for the later creation session.

- `README.md`: theorem, exact meaning of sharpness, one proof overview,
  source comparison, and links to the formal statements and verification.
- `Proof.md`: one polished proof, ordered interpolation -> free factors ->
  uniform factors -> full curve -> equality -> proximal consequences.
  Omit the abandoned odd-horizon search from the main narrative.
- `Note.md`: comparison with THG's original conjecture, Chikhi's balanced
  result and factorization, and nearby but differently normalized results.
  State the positive strongly convex specialization remains outside scope.
- `THGGradientChallenge.lean` / `THGGradientSolution.lean`: unique module
  names, ordinary analytic statements, and matching proved wrappers.
- `THGGradient/`: substantive proof modules as specified in the Lean plan.
- `formalization.yaml`: precise source relationships, human responsibility,
  automation disclosure, and the review actually performed.
- `VERIFICATION.md`: exact source SHA, complete statement list, build and
  permitted-axiom audits, Comparator and independent replay evidence.

Preserve the Lab's discovery history, original factor obstruction, numerical
scouts and finite regression checks here. The formal proof must reconstruct
the general algebra in Lean; external Python results are not axioms.

## 5. Provenance and current Palomar requirements

The [official policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
was read on October 9. Recheck it when the new repository is created.
The current format uses a small Challenge/Solution pair, exact public
commit, pinned dependencies, `formalization.yaml`, and a license. All
submitted Lean sources require module headers. Use distinct module names,
Mathlib-only Challenge imports, and exposed public definitions where their
bodies are part of the interface. The intended Challenge should stay
comfortably below its size limits.

Credit THG for the conjecture and sharp examples, and Chikhi for the
balanced-step result and factorized multiplier shape. The new construction
extends those published ingredients; use a source-based `adapts` account,
with a separate precise description of the new uniform divergence,
scaling, equality, and application arguments. Do not label the project a
wholly source-independent discovery because the final proof is self-contained.
Pin the Lab proof as the written precursor. Human authors/maintainers and
material agent contributions belong in their respective metadata fields.

The final abstract should state the theorem and proved extensions, without
claiming worldwide priority, human peer review, or registry acceptance from
an internal audit. Current status is an internally audited written proof.

## 6. Implementation order and acceptance gates

1. **Freeze statements and prove the analytic bridge first.** Check the
   actual function assumptions, finite-dimensional specialization, and
   minimizer gradient zero. Derive the full smooth interpolation inequality.
   This is the early test of whether the library interfaces fit the theorem.
2. **Build the elementary factor library.** Positive geometric prefixes,
   one quadratic-root interface, comparison monotonicity, and admissible
   factors. Prove the critical ratio inequality before expanding every
   certificate coefficient.
3. **Prove the universal finite-data certificate.** Use natural-number
   indices and a shifted factor sequence to avoid a fictitious index -1.
   Establish telescoping and double-sum identities once. Keep squares in
   the main estimates until the final norm bound.
4. **Close the actual-function theorem and explicit witnesses.** This is
   the first complete mathematical milestone: all N, all h, all dimensions,
   no interpolation hypotheses in the final function theorem.
5. **Add equality and proximal results.** Equality uses vanishing
   nonnegative remainders; the balanced proof can avoid orthogonal
   projections. Proximal interpolation follows directly from minimization.
6. **Run the release gate on the exact commit.** Complete Lean build,
   statement comparison, permitted-axiom audit, Lean/NanoDa and the Lab's
   additional independent replay where supported, plus a clean Linux build.
   Check source resolution and the rendered public theorem descriptions.

No runtime estimate is promised before the first analytic-bridge and factor
prototypes compile. The proof has no large external certificate dataset;
the main risks are analytic API gaps and symbolic finite-sum elaboration.
Compiled supporting lemmas, numerical evidence, or a partially completed
build are not completion of the principal contract.

## 7. Later-session starting instruction

Read this plan and LEAN_PLAN, then create the separately authorized private
project using the user's current naming choice and current official
toolchain/template requirements. Start with the smallest actual-gradient
bridge and a public-statement skeleton, before the longer algebra. Preserve
the full smooth-convex theorem as the mandatory result. Keep each completed
extension aligned with its informal claim and record exact verification.
Publication and registration remain separate later actions.
