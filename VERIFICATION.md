# Verification record

Status: **complete Lean implementation; exact Linux release gate pending**, 2026-10-09. The private repository
was authorized by JD after the planning handoff. No publication, submission
or registry acceptance is claimed.

## Source and toolchain

- Written precursor: Analytic-Lab
  `c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f`, especially
  `research/thg_gradient/PROOF.md`, `UNIFORM_CERTIFICATE.md`,
  `EXTENSIONS_GEOMETRY.md`, `EXTENSIONS_PROXIMAL.md` and the two plans.
- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- All transitive dependencies are pinned in `lake-manifest.json`.

## Ten principal declarations

The complete local Lean build and principal permitted-axiom audit are complete.
The independent Challenge is Mathlib-only, with literal analytic hypotheses.
The Solution imports the proof modules. The principal contract is:

| Declaration in `THGGradient` | Scope |
|---|---|
| `last_gradient_bound` | Actual smooth convex functions; every horizon, all nonnegative steps, real Hilbert spaces. |
| `scalar_attainment` | Genuine convex differentiable real functions attain the maximum, for every positive L and R. |
| `progress_joint_bound` | Joint terminal distance, objective and gradient potential, with the original L normalization. |
| `progress_equality` | Complete sampled constant-gradient trajectory, strict progress branch, N and h positive. |
| `oscillation_equality` | Complete sampled quadratic trajectory, strict oscillation branch including h at least two. |
| `balance_equality` | Precisely the orthogonal progress/quadratic mixtures at the literal rate crossing. |
| `proximal_residual_bound` | Actual constrained proximal minimizers, including the terminal evaluation, all nonnegative steps. |
| `proximal_residual_attainment` | Actual absolute-value and singleton examples attain the residual factor. |
| `proximal_progress_tradeoff` | Progress-branch objective-residual tradeoff and its terminal objective-gap consequence. |
| `proximal_objective_attainment` | An actual scalar proximal problem attains the objective coefficient. |

The first, third, seventh and ninth statements include N=0. All equality
classifications use N>0 and h>0, and include the zero initial-distance case.
The objective witness exists for every nonnegative step; its matching universal
upper bound is asserted only in the proved progress range. The generic proximal
statements require only a real inner-product space; completeness is unnecessary.

Compiled supplementary declarations include the canonical-gradient theorem
with explicit differentiability, the explicit Euclidean specialization, and
attainment in every nonzero real Hilbert space and positive Euclidean dimension.
They are in the Solution closure. Written strict-branch quantitative stability,
off-trajectory segment descriptions, and general extended-real proximal
existence are outside the compared ten-declaration contract.

## Reproduction and exact-source gate

```sh
lake exe cache get
python3 scripts/check_sources.py
lake build
lake comparator --config comparator.json
```

The manual [Verify workflow](https://github.com/JD-Jones-ASES/thg-gradient-curve/actions/workflows/verify.yml)
records the checked-out full SHA in `verification/commit.txt` and checks that it
matches the GitHub workflow SHA. Its two fresh Linux runners build project
proofs from source. Only pinned public dependencies use Mathlib's cache; no
project proof artifacts are reused.

The kernel-replay job audits each principal declaration, compares the independent
statements and definitions, and replays the exported proof closure with Lean,
NanoDa and con-ron. The separate fresh-build job repeats the complete build and
principal axiom audit. Both preserve their evidence as private Actions artifacts.
The only permitted axioms are `propext`, `Quot.sound` and `Classical.choice`.
Intentional placeholders occur only in the independent Challenge; none occurs
in the Solution or its project proof closure.

**Linux results have not yet been recorded for the candidate commit.** A local
build, an internal mathematical audit or a partial CI run does not establish
exact-commit release verification. The successful workflow must identify the
intended full source SHA before the repository is described as ready.

## Review and provenance

The source requirements and minimum toolchain were checked against the
[Palomar policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and its [toolchain file](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json)
on October 9, 2026. Independent internal agent audits checked the actual-function
bridge, the all-horizon factor construction, all step endpoints, equality
necessity/converses, proximal optimality, and statement/description alignment.

This remains a private repository. Verification is distinct from public release,
Palomar submission, registration, worldwide priority or human specialist review.
