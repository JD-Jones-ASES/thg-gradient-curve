# thg-gradient-curve

Sharp last-iterate bounds and extremal trajectories for **constant-step
gradient descent** on smooth convex functions. The project develops
the complete final-gradient curve, the structure of equality trajectories,
and a direct application to relaxed proximal minimization.

The complete package has ten principal Lean statements: the sharp curve and
attainment, the joint progress potential, all three equality classifications,
and four proximal results. [VERIFICATION.md](VERIFICATION.md) records their
precise verification scope and source evidence.

[Proof.md](Proof.md) gives the mathematical argument.
[Note.md](Note.md) compares the result with its primary sources.

## The exact final-gradient curve

Let $`E`$ be a real Hilbert space, $`N\ge0`$, $`L>0`$, and $`h\ge0`$.
Let $`f:E\to\mathbb R`$ be convex and differentiable, with an
$`L`$-Lipschitz gradient and a minimizer $`x_*`$. For the actual iteration

```math
x_{i+1}=x_i-\frac hL\nabla f(x_i),\qquad 0\le i<N,
```

the sharp factor is

```math
\|\nabla f(x_N)\|
\le L\|x_0-x_*\|\rho_N(h),\qquad
\rho_N(h)=\max\left\{\frac1{1+Nh},\ |1-h|^N\right\}.
```

This uses the **final gradient** and an **initial-distance bound**.
There is no finite-horizon or dimension cutoff. The zero-step and zero-horizon
cases are included. For $`h>2`$, the second branch describes possible growth.
One-dimensional Huber and quadratic functions attain the two branches;
their lifts give sharpness in every nonzero real Hilbert space.

For $`N\ge1`$, the unique balancing step $`H_N\in(1,2)`$ satisfies

```math
(H_N-1)^N(1+NH_N)=1.
```

The progress branch also has the stronger joint estimate, written after
normalizing $`L=1`$, $`x_*=0`$, and $`f(x_*)=0`$:

```math
\|x_N\|^2+2Nh f(x_N)+Nh(1+Nh)\|\nabla f(x_N)\|^2
\le\|x_0\|^2,\qquad 0\le h\le H_N.
```

## What equality means

For a positive horizon and positive step, equality trajectories are constant
gradient progress below the balancing step, quadratic oscillation above it,
and orthogonal combinations at balance. In the same normalization, the
balanced form is

```math
x_i=(1+(N-i)h)b+(1-h)^i a,\qquad
g_i=b+(1-h)^i a,\qquad \langle a,b\rangle=0.
```

The classification concerns visited points, gradients and sampled function
values. It does not determine the objective away from the trajectory.
Quantitative stability is included as a written supplement.

## Relaxed proximal minimization

Let $`C\subseteq E`$ be convex, let $`F`$ be convex on $`C`$, and let
$`x_*\in C`$ minimize $`F`$. Given $`\lambda>0`$, suppose each $`z_i`$
actually minimizes

```math
z\in C\longmapsto\lambda F(z)+\tfrac12\|z-x_i\|^2,
\qquad x_{i+1}=x_i+h(z_i-x_i).
```

With $`e_i=x_i-z_i`$ and $`R=\|x_0-x_*\|`$, the same sharp curve gives
$`\|e_N\|\le R\rho_N(h)`$. The terminal residual requires $`N+1`$
proximal evaluations for $`N`$ updates. On the progress branch,

```math
\lambda\bigl(F(z_N)-F(x_*)\bigr)+(1+Nh)\|e_N\|^2
\le R\|e_N\|,
\qquad
F(z_N)-F(x_*)\le\frac{R^2}{4\lambda(1+Nh)}.
```

The objective is evaluated at $`z_N`$. Explicit absolute-value and singleton
examples establish sharpness. The statements use supplied actual minimizers;
they do not assume an unexplained interpolation oracle or assert existence
of a total proximal operator for arbitrary objectives.

## Proof and provenance

The proof first derives smooth-convex interpolation from actual convexity,
derivatives and the Lipschitz bound. A finite inner-product identity then
reduces the estimate to nonnegative scalar multipliers. Their explicit
quadratic-root construction gives one common divergence throughout the
oscillation branch. At balance, retaining the interpolation surplus under
scaling proves the entire progress branch. Vanishing remainders explain
equality, and actual proximal optimality supplies the second analytic bridge.

Taylor, Hendrickx and Glineur posed the smooth-convex conjecture and supplied
the sharp examples. Chikhi proved the balancing-step result and supplied the
factorized multiplier shape adapted here. [Note.md](Note.md) distinguishes
these published ingredients from the new uniform construction and extensions.
Positive strong convexity, changing preconditioners and worldwide priority
are outside the established claim.

## Lean project

The project pins Lean `v4.35.0-rc3` and Mathlib
`a98628e16c11f5167f16124105ddce53efa9bfe5`. With Elan installed:

```sh
lake exe cache get
lake build
lake comparator --config comparator.json
```

The independent [THGGradientChallenge.lean](THGGradientChallenge.lean) imports
only Mathlib; [THGGradientSolution.lean](THGGradientSolution.lean) imports the
complete proved development. [comparator.json](comparator.json) lists the ten
principal declarations. Every definition in the statement surface is ordinary
Mathlib mathematics. [VERIFICATION.md](VERIFICATION.md) lists the compiled
declarations and their verification evidence. Comparator and independent
kernel replay run on Linux.

[formalization.yaml](formalization.yaml) records the mathematical scope,
source relationships.
