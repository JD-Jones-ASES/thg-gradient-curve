> Historical implementation plan, copied from the pinned Lab precursor.
> See ../VERIFICATION.md for current compiled status.

# Lean and Palomar implementation plan

Date: 2026-10-09. **Planning only; no Lean code in this note has been compiled.**
No `.lean` source was created, no Lean build was run, and no new repository
was created. The next implementation session belongs in a separately
authorized repository, outside Analytic-Lab.

## 1. Public mathematical contract

The principal statement must concern actual differentiable convex functions.
It must not assume the interpolation inequalities, certificate feasibility,
a descent lemma, cocoercivity, or a special trajectory decomposition.

For every natural horizon `N` (including zero), positive real `L`, and
`h>=0`, let `E` be a real Hilbert space, `f:E -> ℝ` be convex, and
`g:E -> E` satisfy `forall x, HasGradientAt f (g x) x` and the ordinary
`L`-Lipschitz gradient estimate. For any minimizer `x_*` and actual
gradient descent trajectory with step `h/L`, prove

    ||g(x_N)||
      <= L ||x_0-x_*|| max ((1+N*h)^(-1)) (|1-h|^N).

Use `ConvexOn ℝ Set.univ f`, `forall x, HasGradientAt f (g x) x`,
an explicit positive `L`, the ordinary pairwise gradient Lipschitz
estimate, and the ordinary minimizer condition. These are complete
analytic hypotheses: `HasGradientAt` already implies differentiability
and ties `g` to the actual function. Also provide the canonical-gradient
corollary using `Differentiable ℝ f` and mathlib `gradient f`, and an
explicit finite-dimensional corollary for every positive dimension `d`.
The substantive certificate proves `0<h<2`; the ordinary zero-step bound
and the elementary `h>=2` distance recursion complete the master theorem.
This preserves every step in the original conjecture range and adds the
sharp finite-horizon growth bound for larger steps.

Use `EuclideanSpace ℝ (Fin d)`, not the default norm on `Fin d -> ℝ`:
the latter function space carries a supremum norm rather than the intended
Euclidean norm. Most certificate modules need only a real inner-product space. The
analytic interface naturally requires `CompleteSpace`, because mathlib's
gradient API uses the Riesz identification. The main complete-space
statement and its explicit finite-dimensional corollary must both compile
before either scope is advertised; no compactness or finite-dimensional
argument is needed by the audited certificate.

The sharpness contract must quantify over actual functions too. Prove
scalar quadratic and Huber examples with exactly the required convexity,
differentiability, Lipschitz constant, minimizer, trajectory and attained
norm. One-dimensional examples already show the universal constant cannot
improve. If the public wording says sharp in every positive dimension,
include the lift along a unit vector or the first Euclidean coordinate.

The data-level interpolation theorem is a central reusable lemma, not the
headline endpoint. The submission is incomplete until the analytic bridge
and sharpness witnesses are proved without extra certificate hypotheses.

## 2. Source and environment audit

The existing package
`/Users/jjones/Documents/Grok-Repos/chiral-gap` was inspected read-only.
Its toolchain is `leanprover/lean4:v4.35.0-rc3`; its manifest pins mathlib to

    a98628e16c11f5167f16124105ddce53efa9bfe5.

Its `.lake/packages` directory is absent. The named PlanarMidpoint checkout
also had no `.lake` source tree at the inspected path. Accordingly the API
audit below read mathlib's primary raw source at the exact pin, without
creating a checkout or invoking Lean. The live mathlib documentation was
also checked; its gradient page pointed to source revision
`95142c9c4fdb4ff9632553901cfc82d5c84a8ad4` on this date. These are different
snapshots. The declarations listed below were checked against the
**a98628e16c11f5167f16124105ddce53efa9bfe5 source**, which is a verified
reference baseline, not a decision to force that version on the new repo.
Select and pin a mutually compatible Lean/mathlib/Comparator toolchain at
the beginning of the implementation session, then recheck these APIs.

The read-only chiral-gap layout confirms the useful packaging pattern:
a small Mathlib-only challenge source, a uniquely named solution source
importing the project, explicit exposed public definitions, a pinned
manifest, and a single Comparator configuration. For this project use
`THGGradientChallenge` and `THGGradientSolution`, not bare `Challenge` and
`Solution`. All new source files need the current required `module` header.
The root session's refreshed official Palomar policy owns final packaging
and verification requirements; this document does not freeze historical
policy as current.

## 3. Verified APIs and their intended role

These are source-verified declaration names, not claims that a proposed
application has already elaborated.

| Module at the reference pin | Verified declarations | Planned use |
|---|---|---|
| [Calculus/Gradient/Basic][gradient] | `HasGradientAt`, `gradient`, `HasGradientAt.hasFDerivAt`, `DifferentiableAt.hasGradientAt`, `HasGradientAt.gradient`, `gradient_eq`, `HasGradientAt.fderiv_apply`, `HasDerivAt.hasGradientAt'`, `gradient_eq_deriv'` | Canonical function interface; convert to Fréchet derivatives for calculus and to ordinary derivatives for scalar witnesses. |
| [Convex/Function][convex-function] | `ConvexOn.comp_affineMap`, `ConvexOn.comp_linearMap`, `ConvexOn.sub` | Restrict convex functions to affine lines; subtract linear functions. |
| [Convex/Deriv][convex-deriv] | `ConvexOn.le_slope_of_hasDerivAt`, `Monotone.convexOn_univ_of_deriv` | Derive the first-order support inequality on a line; prove convexity of the clipped-gradient primitive. |
| [Calculus/Deriv/AffineMap][affine-deriv] | `AffineMap.hasDerivAt_lineMap` | Derivative of the line from one point to another. |
| [Calculus/Deriv/Comp][deriv-comp] | `HasFDerivAt.comp_hasDerivAt` | Compose the function's derivative with that line. |
| [Calculus/Deriv/MeanValue][mean-value] | `antitoneOn_of_deriv_nonpos`, `monotoneOn_of_deriv_nonneg` | Sharp descent estimate and scalar monotonicity without measure-theoretic integration. |
| [Calculus/LocalExtr/Basic][local-extrema] | `IsLocalMin.hasFDerivAt_eq_zero`, `IsLocalMin.fderiv_eq_zero` | Gradient vanishes at the given global minimizer. |
| [InnerProductSpace/Basic][inner] | `sum_inner`, `inner_sum`, `real_inner_self_eq_norm_sq`, `norm_add_sq_real`, `norm_sub_sq_real`, `real_inner_le_norm` | Dimension-free finite certificate expansions and Cauchy–Schwarz. |
| [Analysis/Real/Sqrt][sqrt] | `Real.sqrt_nonneg`, `Real.sq_sqrt`, `Real.sqrt_pos`, `Real.sqrt_le_sqrt`, `Real.sqrt_le_left`, `Real.le_sqrt`, `Real.sqrt_sq_eq_abs` | The nonnegative root of `u²+B*u-Z=0`. |
| [Topology/Order/IntermediateValue][ivt] | `intermediate_value_Icc` | Existence of the balancing step; uniqueness is an elementary positive-power comparison. |
| [Topology/MetricSpace/Lipschitz][lipschitz] | `lipschitzWith_iff_dist_le_mul`, `LipschitzWith.dist_le_mul`, `LipschitzWith.min_const`, `LipschitzWith.const_max` | Convert pairwise estimates to the library predicate; prove the clipped identity is 1-Lipschitz. |
| [IntervalIntegral/FundThmCalculus][ftc] | `intervalIntegral.integral_hasDerivAt_right`, `intervalIntegral.differentiable_integral_of_continuous`, `intervalIntegral.integral_eq_sub_of_hasDerivAt` | Construct the Huber witness as a primitive of a continuous clipped identity. |
| [BigOperators/Group/Finset/Defs][finset] | `Finset.sum_bij`, `Finset.sum_bij'`, `Fintype.sum_bijective` | Reindex triangular finite sums; these additive declarations are generated by the source's `to_additive` declarations. |

No ready-made smooth-convex interpolation theorem or Huber-loss package was
identified in the inspected mathlib sources. This is a search result, not
a claim that such material is absent from every library or future version.
The plan builds the specific bridge directly and reads no peer optimization
formalization code.

## 4. Build the analytic bridge first

Before investing in the long multiplier development, implement and compile
these small unconditional lemmas in the new repository.

1. **Line derivative and first-order support.** For `v=y-x`, restrict
   `f` to `t -> x+t*v`. Use affine composition to obtain scalar convexity
   and `HasFDerivAt.comp_hasDerivAt` for its derivative. Apply
   `ConvexOn.le_slope_of_hasDerivAt` between `t=0` and `t=1`. The resulting
   support inequality is `f(y)>=f(x)+<gradient f x,y-x>`.
2. **Sharp descent estimate.** Let
   `P(t)=f(x+t*v)-f(x)-t<g(x),v>-(L/2)t²||v||²` on `[0,1]`.
   Its derivative is
   `<g(x+t*v)-g(x),v>-L*t*||v||²<=0`, by Cauchy–Schwarz and the
   actual gradient Lipschitz estimate. The verified antitone-derivative
   theorem gives `P(1)<=P(0)`. This retains the essential factor `1/2`;
   a crude constant derivative-norm bound would lose it.
3. **Interpolation.** Fix `y` and set `psi(z)=f(z)-<g(y),z>`.
   First-order support proves `y` minimizes `psi`. Its gradient is
   `g(z)-g(y)` and has the same Lipschitz constant. Compare its descent
   step from `x` with its value at `y`, obtaining
   `2L(f(x)-f(y)-<g(y),x-y>)>=||g(x)-g(y)||²`.
4. **Minimizer and normalization.** Derive `g(x_*)=0` from the genuine
   minimizer hypothesis. For the finite data, use positions `x_i-x_*`,
   values `(f(x_i)-f(x_*))/L` and gradients `g(x_i)/L`. This avoids
   repeatedly reproving derivative rules for translated objectives.
5. **One-step integration check.** Instantiate the bridge with an actual
   scalar quadratic and an actual one-step trajectory. This is an early
   interface check, not a substitute for the general result.

Use `HasGradientAt` for the mathematical interface and convert to
`HasFDerivAt` for standard composition/subtraction rules. Do not manually
construct derivatives as coordinate vectors. Keep the scalar line lemma
separate so coercions involving `InnerProductSpace.toDual` are solved once.
The explicit-gradient theorem must retain `forall x, HasGradientAt f (g x) x`.
Its canonical-gradient corollary must retain differentiability explicitly,
because the library's total `gradient` function is zero at nondifferentiable
points.

## 5. Finite-data architecture

Suggested modules below are future files, not files created in this session.

| Future module | Responsibility and completion condition |
|---|---|
| `THGGradient/Definitions` | Ordinary analytic class, rate, actual GD iteration, and plain finite-data interpolation quantities. Public definitions fully exposed. |
| `THGGradient/Interpolation` | Section 4's analytic bridge and zero-gradient-at-minimum theorem. |
| `THGGradient/FiniteSums` | A small fixed set of prefix, suffix and triangular-sum identities; index conventions established once. |
| `THGGradient/FactorIdentity` | Arbitrary-factor cancellation, divergence prefix and exact terminal completion in a real inner-product space. No positivity assumed until needed. |
| `THGGradient/ScalarRoots` | Generic nonnegative quadratic-root package, root ordering, geometric sums and prefix-average comparisons. |
| `THGGradient/UniformFactors` | Construct all factors for arbitrary `N`; prove domains, constant divergence and every multiplier sign. |
| `THGGradient/UpperBranch` | Nonnegative completion for the entire quadratic branch. |
| `THGGradient/Balance` | Existence/uniqueness of `H_N`, branch comparison and the stronger balanced potential. |
| `THGGradient/LowerBranch` | Data scaling identity with retained interpolation surplus; full progress branch. |
| `THGGradient/Main` | Assemble the unconditional actual-function theorem for all `h>=0`, including `N=0`, `h=0`, `h=1`, `h=2`, `h>2`, zero initial distance and zero terminal gradient. |
| `THGGradient/Witnesses` | Quadratic and clipped-gradient/Huber sharpness, including the needed Euclidean lift. |
| `THGGradient/Equality` | Proposed equality classification, only after its mathematical audit and the main bound compile. |
| `THGGradient/Proximal` | Optional later direct proximal application from actual minimization hypotheses. |

Prefer `x : ℕ -> E` and `Finset.range` for prefix calculations; restrict to
`i<=N` in the finite-data interface. A finite type may still be preferable
for the final double sum, but avoid switching index encodings inside every
lemma. Shift the factor indices to remove the artificial predecessor:
`U_0=0`, `U_1=1`, `U_k=A_{k-1}` for `k>=1`, and `p_k=U_k*D_k`.
Then for `a<b`, use

    lambda_ab=(U_{a+1}-U_a)(D_b+r*D_{b+1}),
    lambda_ba=(U_a+r*U_{a+1})(D_b-D_{b+1}).

This avoids integers and the truncated natural predecessor at zero.
Treat the minimizer as a separate distinguished datum or as an
`Option` index, never as a magic natural index that could collide with an
iterate. No algorithm-specific fact is assumed about arbitrary data beyond
the explicit recursion and interpolation conditions; the analytic bridge
will establish these for the public theorem.

Prove the arbitrary-factor identity in modular pieces: function-value
coefficients, one generic mixed-gradient coefficient, one generic diagonal
coefficient, then finite-sum assembly. Repeatedly expanding an unrestricted
all-pairs sum into one enormous `ring` goal is a poor implementation plan.
Normalize to scalar real polynomial goals only after applying inner-product
bilinearity and the proven finite-sum identities. Use `field_simp` only
after named nonzero-denominator lemmas have been proved. Finite rational
probe outputs may guide regression checks, but supply none of the universal
Lean proof obligations.

## 6. Remove unnecessary calculus from the scalar certificate

Use the exact general construction in [UNIFORM_CERTIFICATE.md](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/UNIFORM_CERTIFICATE.md)
and [AUDIT.md](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/AUDIT.md), with these formalization simplifications.

- Define the nonnegative root of `u²+B*u-Z=0` by
  `(Real.sqrt (B²+4*Z)-B)/2`, under `B>0`, `Z>=0`. Prove its equation,
  nonnegativity, strict positivity when `Z>0`, uniqueness among nonnegative
  roots, and polynomial-sign/root-order equivalences once. Downstream
  factor lemmas should consume the root equation and sign properties, not
  unfold `Real.sqrt`; this keeps radical expressions out of the large
  finite-sum proof.
- Prove monotonicity of the root in the artificial parameter `c` by
  **polynomial comparison**, not implicit differentiation. If `c1<c2`,
  then at `u=u_k(c1)`:

      F_k(c2,u)-F_k(c1,u)
        =(c2-c1)(k+1)/(h*p_{k+1}) * (u-k/2) < 0.

  The already established bound `u<k/2` and the root-order lemma imply
  `u_k(c1)<u_k(c2)`. The `k=0` root is identically zero.
- Prove increase of `(a^k-1)/k`, for `a>1`, by finite geometric sums and
  prefix averages. Apply it with `a=r^(-2)` to the `p_k/k` comparison,
  and with `a=r^(-1)` to `r^(-k)<1+k*h` for `0<k<N`.
  Real exponential convexity is unnecessary.
- The balancing step is a root of a polynomial in `r`, so the verified
  intermediate-value theorem is sufficient. No root solver or numerical
  approximation appears in the theorem.
- Handle `N=1` before ratios with `k>0`; handle `N=0` before defining
  the balancing step. Handle `h=0` and `h>=2` before introducing `r<1`
  geometric denominators. Handle `h=1` through the lower branch.
  For `h>=2`, interpolation with the minimizer gives
  `<g_i,x_i>>=||g_i||²` and `||g_i||<=||x_i||`, hence
  `||x_i-h*g_i||²<=(h-1)²||x_i||²`. Induction proves the sharp
  far-step factor; no limiting argument or new certificate is needed.
- Preserve the exact identity
  `Q_scaled=s Q+s(1-s)||g_i-g_j||²`. The retained starred surplus is
  essential. A lemma keeping only nonnegativity of scaled interpolation
  would be too weak for the lower branch.

The principal algebraic risks are endpoint indexing, strict denominator
signs, the artificial-parameter interval, and controlling expression size.
They are engineering risks to validate in compilation; the written proof
already supplies general mathematical lemmas for them.

## 7. Sharpness without a fragile piecewise derivative proof

A convenient construction is

    clip_a(t)=max (-a) (min t a),
    huber_a(x)=integral from 0 to x of clip_a(t),    a>0.

The verified `LipschitzWith.min_const` and `LipschitzWith.const_max`
show `clip_a` is 1-Lipschitz. It is continuous and monotone by elementary
order reasoning. The verified fundamental theorem of calculus gives the
actual derivative of `huber_a` at every real point, including `-a` and
`a`. `Monotone.convexOn_univ_of_deriv` supplies convexity. Its derivative
vanishes at zero, and the support lemma supplies a global minimum there.
The canonical gradient is the clipped identity by
`HasDerivAt.hasGradientAt'` and `HasGradientAt.gradient`.

This avoids separately matching two one-sided derivatives at both joins.
For the sharp gradient trajectory, an explicit closed formula for the
integral is not necessary: with `a=R/(1+N*h)` and initial point `R`,
prove by induction `x_i=R-i*h*a>=a` for `i<=N`, hence every gradient is
`a`. An optional later lemma identifies the primitive with the usual
piecewise Huber formula for exposition.

Prove the quadratic witness independently using ordinary polynomial
calculus and `x_i=(1-h)^i R`. Prove both examples before introducing an
`sSup` definition of a performance measure. A direct upper bound plus
an existential attaining example expresses sharpness with fewer
order-completeness obligations and clearer Comparator statements.

## 8. Worthwhile extensions after the principal contract

### Equality trajectories

The written equality classification in [EXTENSIONS_GEOMETRY.md](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/EXTENSIONS_GEOMETRY.md)
was independently checked against the general certificate. The strict
progress, balance and strict oscillation arguments have no identified
mathematical gap. It is valuable because it describes
all actual equality trajectories, not only chosen sharp examples.
Keep it behind the general bound in the implementation order, and freeze
the literal endpoint and normalization guards before writing its challenge
statements. The proposed
balanced form is in the normalized setting `L=1`, `x_*=0`, with
`N>=1`, `h=H_N`, and `r=h-1`,

    x_i=(1+(N-i)*h) b+(-r)^i a,
    g_i=b+(-r)^i a,    <a,b>=0.

The strict progress branch should leave only the Huber component; the
strict quadratic branch only the quadratic component. The expected formal
proof uses equality in the finite nonnegative certificate, vanishing
interpolation quantities, and elementary inner-product identities.
No orthogonal-projection or linear-span API is necessary. In the balanced
proof, show directly that each `z_i=x_i-g_i` is orthogonal to every
`g_j-g_k`; then the increments `c_i=z_i-z_{i+1}` are all equal,
because expanding `||c_i-c_j||²` gives zero. For the strict upper branch,
the adjacent interpolation identity and vanishing `E_i=f_i-||g_i||²/2`
immediately give `g_{i+1}=-(h-1)g_i`, avoiding a second decomposition.
Cases `N=0`, zero initial
distance, endpoints and branch equality must be stated deliberately;
the displayed classification must not be asserted outside the audited
hypotheses. If it is not completely compiled and verified, omit it from
the Comparator contract rather than weakening the main theorem.

### Direct relaxed proximal-point application

A useful later application can avoid formalizing Moreau-envelope
differentiability. Let `C` be a nonempty convex feasible set, let real-valued
`F` be convex on `C`, let `x_* in C` minimize `F`, and let each `z_i in C`
be an **actual minimizer** over `C` of

    z -> lambda*F(z)+||x_i-z||²/2,       lambda>0.

For relaxation `h`, set `e_i=x_i-z_i`,
`x_{i+1}=x_i-h*e_i`, and
`a_i=lambda*F(z_i)+||e_i||²/2`.
The required interpolation is the elementary identity

    Q_ij=2lambda(F(z_i)-F(z_j))-2<e_j,z_i-z_j>.

Its sign must be proved from the actual argmin property. Test the objective
at `z_j+t(z-z_j)` for `0<t<=1`, use convexity, divide by `t`, and let
`t` tend to zero (or choose an explicit small `t` in a contradiction).
This yields the necessary variational inequality. It is not acceptable
to assume that inequality as an unexplained certificate in the public
application theorem.

This trajectory formulation does not need a theorem asserting existence
of a proximal minimizer for every input; the supplied iterates are required
to be genuine minimizers. Prove global existence separately only if the
public contract introduces a total proximal operator. The real-valued
`F` plus feasible set `C` formulation covers important constrained examples
without introducing extended-real arithmetic.

Do not generalize the interpolation theorem to every cocoercive operator:
function interpolation includes stronger information than cocoercivity.
The separately recorded operator counterexample should become a useful
scope regression example if this application enters the package.

## 9. Alignment with the ten proposed public contracts

[ENTRY_PLAN.md](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/ENTRY_PLAN.md) owns the ten-declaration package. No conflict
with the architecture above was found, provided the following scope guards
and implementation priorities are preserved.

- `last_gradient_bound` and `scalar_attainment` cover every `h>=0` and
  `N>=0`. The scalar-attainment assumptions `L>0`, `R>0` avoid a vacuous
  normalized ratio; the bound itself includes zero initial distance.
- `progress_joint_bound` covers `N>=1`, `0<=h<=H_N`, with the trivial
  `N=0` version available separately. The main root construction need not
  become a public definition: an equivalent branch comparison can state
  the permitted range using only the two explicit rates. The `h=0`
  joint estimate is immediate, not a case of dividing by the step.
- `progress_equality` is for `N>=1`, `0<h<H_N`;
  `balance_equality` is for `N>=1`, `h=H_N`;
  `oscillation_equality` is for `N>=1`, `h>H_N`, including `h>=2`.
  The `h=0` equality statement is elementary and should be a separate
  supporting lemma. Do not impose the nontrivial decomposition on `N=0`.
  State all forms after normalization, or carry `L` and `x_*` explicitly.
- `proximal_residual_bound` and `proximal_residual_attainment` cover all
  `h>=0`, `N>=0`, but the algorithm needs a terminal proximal evaluation:
  `N` updates require `z_0,...,z_N`, not just `z_0,...,z_{N-1}`.
  Each evaluation must be an actual minimizer over the feasible set.
- `proximal_progress_tradeoff` and `proximal_objective_attainment` use
  `N>=1`, `0<=h<=H_N`, together with the separate `N=0` all-step case.
  The objective is evaluated at `z_N`, not the relaxed point `x_N`.
  The exact gap coefficient is `R²/[4*lambda*(1+N*h)]`. The existence of
  an attaining example must not be confused with an upper bound outside
  the proved progress range.

The last four declarations do not require an extended-real global
proximal-operator existence theorem. The supplied-minimizer contract in
[EXTENSIONS_PROXIMAL.md](https://github.com/JD-Jones-ASES/Analytic-Lab/blob/c6256b8dab3fe01fbeeeceef4b4d2c701dffeb2f/research/thg_gradient/EXTENSIONS_PROXIMAL.md) is sufficient and natural.
Adding a total proximal map for every proper lower-semicontinuous extended-
real objective would introduce substantial additional topology and
extended-real bookkeeping; it is supplementary to these ten contracts.

The principal risks, in priority order, are: obtaining the sharp analytic
interpolation bridge; validating the generic root/sign interface; keeping
finite-sum elaboration modular; and making the genuine Huber witness close
at its joining points. The master theorem's `h=0`/`h>=2` continuation is
low incremental cost. Equality is moderate finite-algebra work after the
certificate, with strict positivity of all history weights retained as
named lemmas. The proximal application adds a second short analytic bridge
from actual minimization, followed by explicit scalar absolute-value
witnesses. Keep quantitative stability, off-trajectory classification,
and global extended-real proximal existence outside the first compared
contract unless their completed proofs are deliberately added.

## 10. Completion gates for the later session

1. Fix the exact external repository, privacy, Lean/mathlib pins and unique
   modules. Write and inspect the literal Mathlib-only challenge statement.
2. Compile the analytic bridge and Huber witness interface before the long
   certificate proof. If either bridge fails, resolve it while the scope
   is still small; do not replace actual functions by assumed data.
3. Compile the arbitrary-factor identity independently from factor signs.
4. Compile the uniform construction for symbolic `N` and real parameters,
   including its nonnegative root comparison and every denominator sign.
5. Compile the upper, balanced and scaled lower branches; assemble the
   unconditional main theorem and sharpness witnesses.
6. Add equality and proximal results only at their fully proved scopes.
7. Audit the final theorem types against the written quantifiers, including
   actual gradient regularity, all horizons, all stated dimensions, every
   stepsize endpoint, the far-step growth regime and genuine minimizers. No `sorry`, unapproved axiom,
   finite-horizon replacement or imported unproved convergence theorem.
8. Run the authorized exact-commit Linux verification and fresh build
   required by the then-current Palomar policy. Record the SHA and proof
   closure. Release readiness, submission, registration and novelty remain
   separate statuses.

This session supplies the architecture, source-verified API inventory and
risk order. It supplies no evidence of Lean elaboration or kernel acceptance.

[gradient]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Analysis/Calculus/Gradient/Basic.lean
[convex-function]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Analysis/Convex/Function.lean
[convex-deriv]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Analysis/Convex/Deriv.lean
[affine-deriv]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Analysis/Calculus/Deriv/AffineMap.lean
[deriv-comp]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Analysis/Calculus/Deriv/Comp.lean
[mean-value]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean
[local-extrema]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean
[inner]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Analysis/InnerProductSpace/Basic.lean
[sqrt]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Analysis/Real/Sqrt.lean
[ivt]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Topology/Order/IntermediateValue.lean
[lipschitz]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Topology/MetricSpace/Lipschitz.lean
[ftc]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean
[finset]: https://github.com/leanprover-community/mathlib4/blob/a98628e16c11f5167f16124105ddce53efa9bfe5/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean
