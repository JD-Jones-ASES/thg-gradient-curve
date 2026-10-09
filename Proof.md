# Sharp last-iterate bounds and extremal trajectories

This is the mathematical proof behind **thg-gradient-curve**. It treats actual
smooth convex functions on real Hilbert spaces, all finite horizons and all
nonnegative constant steps. The proof is written independently of Lean notation;
[VERIFICATION.md](VERIFICATION.md) records exactly which claims have compiled.

Taylor, Hendrickx and Glineur posed the final-gradient, initial-distance question
and supplied the sharp Huber and quadratic examples. The factorized multiplier
shape and balanced-step starting point are due to Chikhi. The uniform divergence
construction, its comparison proof, the scaling that retains interpolation
surplus, and the trajectory and proximal consequences are proved below.
See [Note.md](Note.md) for the source comparison and its limits.

## Part I. Interpolation and the uniform certificate

## 1. Statement and elementary interpolation facts

Let `E` be a real Hilbert space, let `L>0`, and let `f : E -> R` be
differentiable and convex with
`L`-Lipschitz gradient, let `x*` be any minimizer, and let

```math
x_{i+1}=x_i-\frac hL\nabla f(x_i),\qquad 0\le i\lt N.
```
For every integer `N>=0` and every `0<h<=2`,

**(1)**

```math
\boxed{\quad
\|\nabla f(x_N)\|\le L\|x_0-x_*\|
\max\{(1+Nh)^{-1},\ |1-h|^N\}.
\quad}
```
The constant is sharp. The one-dimensional quadratic and Huber examples
described below attain the two branches.

Dividing `f` by `L`, translating `x*` to zero, and subtracting `f*`
reduce the proof to `L=1`, `x*=0`, `f*=0`. Write `g_i=grad f(x_i)` and
`g_*=0`. Define

**(2)**

```math
Q_{ij}=2(f_i-f_j)-2\langle g_j,x_i-x_j\rangle
       -\|g_i-g_j\|^2.
```
All these quantities are nonnegative. Here is a direct derivation.
For fixed `y`, the function `phi(z)=f(z)-<grad f(y),z>` is convex,
1-smooth, and minimized at `y`. Integrating its Lipschitz gradient along
a segment gives the descent inequality
`phi(x-grad phi(x))<=phi(x)-||grad phi(x)||^2/2`. Compare the left side
with `phi(y)` to obtain (2).

In particular,

**(3)**

```math
Q_{i*}=2f_i-\|g_i\|^2\ge0,\qquad
Q_{*i}=-2f_i+2\langle g_i,x_i\rangle-\|g_i\|^2\ge0.
```
Adding `Q_ij` and `Q_ji` gives cocoercivity:

**(4)**

```math
\langle g_i-g_j,x_i-x_j\rangle\ge\|g_i-g_j\|^2.
```
Thus, along gradient descent with `0<h<=2`, the gradient norms are
nonincreasing. Indeed, for `e=g_i-g_{i+1}`, (4) gives
`h<g_i,e>>=||e||^2`, and hence

**(5)**

```math
\|g_{i+1}\|^2\le\|g_i\|^2-(2/h-1)\|e\|^2\le\|g_i\|^2.
```
Also `||g_i||<=||x_i||` by Lipschitz continuity and `g_*=0`.

## 2. The balancing step

Fix `N>=1`. There is a unique `H=H_N` in `(1,2)` such that

**(6)**

```math
(H-1)^N(1+NH)=1.
```
Existence and uniqueness follow because the left side is continuous and
strictly increasing on `[1,2]`, starting at zero and ending above one.
For `0<h<=1`, `(1-h)^N<=1/(1+Nh)`: for `h<1`, use
`(1-h)^{-N}>=(1+h)^N>=1+Nh`, and treat `h=1` directly.
For `1<h<2`, equation (6) determines which branch in (1) is larger.

We first prove the upper branch `H<=h<2`, and obtain a stronger identity
at `h=H`. That identity will prove the lower branch by scaling.

## 3. Free factors: identities before choosing them

For this section fix `1<h<2`, and put

**(7)**

```math
r=h-1\in(0,1),\qquad t=r^{-N},\qquad
p_j=\frac{r^{-2j}-1}{2}\quad(0\le j\le N).
```
Choose positive numbers `A_0,...,A_{N-1}` with `A_0=1`, and define

**(8)**

```math
A_{-1}=0,\qquad D_j=\frac{p_j}{A_{j-1}}\ (1\le j\le N),
\qquad D_{N+1}=0.
```
For `0<=a<b<=N`, set

**(9)**

```math
\lambda_{ab}=(A_a-A_{a-1})(D_b+rD_{b+1}),
\qquad
\lambda_{ba}=(A_{a-1}+rA_a)(D_b-D_{b+1}).
```
Only factors with `a<N` occur in (9); no `A_N` is needed.
If the `A` sequence increases and the `D` sequence decreases, every
multiplier in (9) is nonnegative.
Let

**(10)**

```math
d_i=\sum_{j\ne i}(\lambda_{ij}-\lambda_{ji}),\qquad
W=\sum_{i\ne j}\lambda_{ij}Q_{ij},\qquad
S=\sum_{i=0}^{N-1}d_i=-d_N.
```
### 3.1 Prefix divergences

For `0<=k<N`, let
`U_k=sum_{i=0}^{k-1}A_i` and `V_k=sum_{j=k+2}^N D_j`, with empty
sums zero. Summing (9) across the cut `a<=k<b` gives

**(11)**

```math
\begin{aligned}
C_k:=\sum_{i=0}^k d_i
&=A_k(D_{k+1}+hV_k)-(hU_k+rA_k)D_{k+1}\\
&=(1-r)p_{k+1}+h(A_kV_k-D_{k+1}U_k).
\end{aligned}
```
The telescoping sums used here are
`sum_{a<=k}(A_a-A_{a-1})=A_k`,
`sum_{a<=k}(A_{a-1}+rA_a)=hU_k+rA_k`, and
`sum_{b>k}(D_b-D_{b+1})=D_{k+1}`.

### 3.2 Cancellation of mixed gradient terms

Use `x_i=x_0-h sum_{k<i}g_k` in (2). For `a<b`, the coefficient of
`<g_a,g_b>` in `W`, divided by two, is

**(12)**

```math
\lambda_{ab}+\lambda_{ba}
-h\sum_{i=0}^a\lambda_{ib}
+h\sum_{j=b+1}^N\lambda_{ja}.
```
The three expressions in (12) are, respectively,

```math
h(A_aD_b-A_{a-1}D_{b+1}),\qquad
A_a(D_b+rD_{b+1}),\qquad
(A_{a-1}+rA_a)D_{b+1}.
```
Their indicated combination is zero. This is a literal coefficient
calculation, independent of the dimension and of how the factors are
chosen.

### 3.3 Diagonal coefficients

Let `c_i` denote the coefficient of `||g_i||^2` in `W`.
Expansion of (2) gives

```math
c_i=-\sum_{j\ne i}(\lambda_{ij}+\lambda_{ji})
       +2h\sum_{j\gt i}\lambda_{ji}.
```
Consequently, for `0<=i<N`,

**(13)**

```math
\begin{aligned}
c_i+d_i
&=-2A_{i-1}(D_i+rD_{i+1})
   +2r(A_{i-1}+rA_i)D_{i+1}\\
&=2(r^2p_{i+1}-p_i)=1-r^2.
\end{aligned}
```
At `i=0`, the first term is absent and `p_0=0`; the same result follows
from `2r^2A_0D_1=1-r^2`, without defining `D_0`.
At `i=N`, there are no terms with `j>N`, and

**(14)**

```math
c_N=-d_N-2A_{N-1}D_N=S-(t^2-1).
```
The coefficient of `f_i` is `2d_i`. Thus (12)--(14) prove the complete
identity

**(15)**

```math
W=2\sum_{i\lt N}d_i(E_i-E_N)
 +(1-r^2)\sum_{i\lt N}\|g_i\|^2-(t^2-1)\|g_N\|^2,
\qquad E_i=f_i-\frac12\|g_i\|^2.
```
### 3.4 Completion against the minimizer

The resulting exact completion is

**(16)**

```math
\boxed{\begin{aligned}
\|x_0\|^2-t^2\|g_N\|^2={}&W
 +h\sum_{i\lt N}Q_{*i}+Q_{*N}
 +\sum_{i\lt N}(h-d_i)Q_{i*}\\
 &+(1+S)Q_{N*}+\|x_N-g_N\|^2.
\end{aligned}}
```
For a direct verification, the function-value coefficients cancel using
`d_N=-S`. Substitution of (13)--(14) leaves
`2h sum_{i<N}<g_i,x_i>-h^2 sum_{i<N}||g_i||^2+||x_N||^2`
in the nonterminal distance terms. This equals `||x_0||^2` by summing
`||x_i||^2-||x_{i+1}||^2=2h<g_i,x_i>-h^2||g_i||^2`.
The remaining coefficient is `-t^2||g_N||^2`.

Therefore (16) proves the desired upper-branch estimate as soon as the
factors are monotone, `d_i<=h` for `i<N`, and `S>=-1`.

## 4. Prescribing one common divergence

Assume now `H<=h<2`, so `t<=T:=1+Nh`. Set

**(17)**

```math
\delta=\frac{2(1-r)\sum_{j=1}^N p_j}{N(N+1)}.
```
In particular `delta>0`. The geometric sum gives

```math
\sum_{j=1}^N p_j
=\frac12\left(\frac{t^2-1}{1-r^2}-N\right),
```
and hence

**(18)**

```math
\delta=\frac{t^2-1-N(1-r^2)}{hN(N+1)},\qquad
h-\delta=\frac{T^2-t^2}{hN(N+1)}\ge0.
```
Our construction will make **every** `d_i` with `i<N` equal to `delta`.

### 4.1 Increasing weighted averages

The sequence `p_j/j`, `j>=1`, strictly increases. To see this, write
`a=r^{-2}>1` and

```math
\frac{p_j}{j}=\frac{a-1}{2}\,
\frac{1+a+\cdots+a^{j-1}}j.
```
The average of the first `j` terms of a strictly increasing sequence
strictly increases with `j`. Therefore

```math
M_k=\frac{2\sum_{j=1}^k p_j}{k(k+1)}
```
also strictly increases: it is the weighted average of `p_j/j` with
positive weights `j`. In particular, for `1<=k<N`,

**(19)**

```math
\delta\gt (1-r)M_k.
```
### 4.2 Auxiliary quadratic roots

For a comparison parameter `c` in `[delta,h]`, and `0<=k<N`, define

**(20)**

```math
w_k(c)=\frac{c(k+1)/p_{k+1}-(1-r)}h,
\qquad
Z_k(c)=\frac{c\,k(k+1)/2-(1-r)\sum_{j=1}^k p_j}
                  {h p_{k+1}},
```
and let `u_k(c)` be the unique nonnegative root of

**(21)**

```math
P_{k,c}(z)=z^2+(1+w_k(c))z-Z_k(c).
```
These roots exist without ambiguity: `Z_0=0`; for `1<=k<N`, (19) gives
`Z_k(c)>0`; and `1+w_k(c)>=2r/h>0`. Thus `u_0(c)=0` and all other
roots are positive. For example, they may be defined explicitly by

**(22)**

```math
u_k(c)=\frac{\sqrt{(1+w_k(c))^2+4Z_k(c)}-(1+w_k(c))}{2}.
```
For the actual parameter `c=delta`, abbreviate `u_k=u_k(delta)`,
`w_k=w_k(delta)`, and `v_k=u_k+w_k`.
The definitions give

**(23)**

```math
p_{k+1}Z_k=\sum_{j=0}^{k-1}p_{j+1}w_j.
```
Since `u_k(1+u_k+w_k)=Z_k`, this also gives

**(24)**

```math
p_{k+1}v_k(1+u_k)
=\sum_{j=0}^{k}p_{j+1}w_j\ge0.
```
The final inequality follows from (19) for `k+1<N`, and from (17)
with equality for `k=N-1`. Hence `v_k>=0` and

**(25)**

```math
v_{N-1}=0.
```
For `1<=k<N`, subtracting consecutive versions of (23) proves

**(26)**

```math
Z_k=\frac{p_k}{p_{k+1}}(1+u_{k-1})v_{k-1}.
```
Indeed `Z_{k-1}+w_{k-1}=(1+u_{k-1})v_{k-1}`.

### 4.3 Constructing the factors and computing their divergences

Define

**(27)**

```math
q_k=\frac{1+u_{k-1}}{u_k},\qquad A_k=q_kA_{k-1}\quad(1\le k\lt N),
\quad A_0=1,
```
and then define the `D` factors by (8). By induction on (27),

**(28)**

```math
\frac{\sum_{i\lt k}A_i}{A_k}=u_k.
```
Equations (21) and (26) imply

```math
v_{k-1}=\frac{p_{k+1}}{p_kq_k}(1+v_k)
       =\frac{D_{k+1}}{D_k}(1+v_k).
```
Starting at (25) and proceeding backward therefore gives

**(29)**

```math
\frac{\sum_{j=k+2}^{N}D_j}{D_{k+1}}=v_k.
```
Insert (28)--(29) into the prefix identity (11):

**(30)**

```math
C_k=p_{k+1}\bigl((1-r)+h(v_k-u_k)\bigr)
    =\delta(k+1).
```
Thus `d_i=delta` for `i<N`, and `S=N delta>0`.
It remains to show that the factors in (27)--(8) are monotone.

## 5. Admissibility of the factors

We prove the stronger inequality

**(31)**

```math
q_k\gt \frac{p_{k+1}}{p_k}\gt 1\qquad(1\le k\lt N).
```
This makes `A_k>A_{k-1}` and `D_{k+1}<D_k`, as required in (9).

### 5.1 Monotonicity of the roots in the comparison parameter

For `1<=j<N`, substitution in (21) cancels every term containing `c`
and gives

**(32)**

```math
P_{j,c}(j/2)
=\frac{j^2}{4}+\frac{jr}{h}
 +\frac{(1-r)\sum_{\ell=1}^{j}p_\ell}{h p_{j+1}}\gt 0.
```
The polynomial is strictly increasing for `z>=0`, so
`0<u_j(c)<j/2`. If `delta<=c_1<=c_2<=h`, then

```math
P_{j,c_2}(u_j(c_1))
=\frac{(c_2-c_1)(j+1)}{h p_{j+1}}
       (u_j(c_1)-j/2)\le0.
```
It follows that `u_j(c_2)>=u_j(c_1)`. This argument uses only polynomial
comparison; differentiation of roots is unnecessary. The same
nondecreasing statement holds for the constant root `u_0(c)=0`.

### 5.2 Reduction to `c=h`

Fix `1<=k<N`, put `R=p_k/p_{k+1}`, and set
`B(c)=R(1+u_{k-1}(c))>0`. Equation (26), whose algebra is valid for
every comparison parameter `c`, gives

```math
P_{k,c}(B(c))=B(c)\mathcal M(c),
```
**(33)**

```math
\mathcal M(c)=R+1+w_k(c)-w_{k-1}(c)
                         -(1-R)u_{k-1}(c).
```
The coefficient of `c` in `w_k(c)-w_{k-1}(c)` is

```math
\frac1h\left(\frac{k+1}{p_{k+1}}-\frac{k}{p_k}\right)\lt 0
```
by the strict increase of `p_j/j`. Together with Section 5.1, this
shows that `mathcal M(c)` is nonincreasing. Thus it suffices to prove
`mathcal M(h)>0`.

### 5.3 The explicit endpoint roots

Direct substitution in (21) at `c=h` yields

**(34)**

```math
u_k(h)=\frac{1+kh-r^{-k}}{h(1+r^{-(k+1)})}.
```
Its numerator is positive for `0<k<N`. In fact, the strictly increasing
increments of the geometric sequence `r^{-j}` imply

```math
\frac{r^{-k}-1}{k}\lt \frac{r^{-N}-1}{N}\le h.
```
Consequently (34) is indeed the nonnegative root; at `k=0` it is zero.
One way to check the substitution without expanding (34) is to put
`U_j=p_j u_{j-1}(c)`. Using the geometric sum in (20), its quadratic is

```math
hU_j^2+(2rp_j+cj)U_j
-p_j\left(\frac{cj(j-1)}2+\frac{j(1-r)}2-\frac{r^2p_j}{h}\right)=0.
```
Its discriminant is

```math
\mathcal D_j(c)=c^2j^2+2jp_j\bigl(hcj+(1-r)(h-c)\bigr).
```
At `c=h`, its positive square root is `hj r^{-j}`, which immediately
gives (34).

The ratios derived from (34) are

**(35)**

```math
q_k(h)=\frac{(1+kh+r^{-k})(1+r^{-(k+1)})}
              {(1+r^{-k})(1+kh-r^{-k})}.
```
For `z=r^{-k}>1` and `A=1+kh`, the assertion
`q_k(h)>p_{k+1}/p_k` is equivalent to

```math
(A+z)(z-1)\gt (A-z)(z/r-1).
```
All denominators cleared here are positive. The difference is exactly

**(36)**

```math
\frac{hz}{r}\bigl(z-1-k(1-r)\bigr)\gt 0.
```
For the last sign, Bernoulli's inequality gives
`r^{-k}>=(1+(1-r)/r)^k>=1+k(1-r)/r>1+k(1-r)`.

It follows from (35)--(36) that `u_k(h)<B(h)`. Since `P_{k,h}` strictly
increases on nonnegative arguments, (33) gives `mathcal M(h)>0`.
Hence `mathcal M(delta)>0`, so `P_{k,delta}(B(delta))>0` and
`u_k<B(delta)`. This proves (31).

## 6. The upper branch and the `N=1` boundary

We have constructed nonnegative multipliers with
`d_i=delta<=h` and `S=N delta>0`. Every term on the right side of (16)
is nonnegative. Therefore

**(37)**

```math
\|g_N\|\le r^N\|x_0\|\qquad(H\le h\lt 2).
```
The construction includes `N=1`. There are then no ratios `q_k` to
define or test: `A_0=1`, `D_1=p_1`, and `D_2=0`.
The two multipliers are `lambda_01=p_1` and `lambda_10=r p_1`, so
`d_0=(1-r)p_1=delta`. The only auxiliary root is `u_0=0`, with
`w_0=v_0=0`. Equation (18) establishes `delta<=h` on the upper branch,
and (16) applies directly. Thus there is no implicit division by a
missing root or an empty prefix sum in this case.

## 7. The stronger identity at balance

At `h=H`, one has `t=1+NH` and (18) gives `delta=H`.
The terminal terms in (16) combine as

```math
Q_{*N}+tQ_{N*}+\|x_N-g_N\|^2
=\|x_N\|^2+2(t-1)f_N-t\|g_N\|^2.
```
Hence (16) becomes the exact stronger identity

**(38)**

```math
\boxed{\begin{aligned}
\|x_0\|^2={}&\|x_N\|^2+2NH f_N
       +NH(NH+1)\|g_N\|^2\\
&+W+H\sum_{i\lt N}Q_{*i}.
\end{aligned}}
```
Its remainder is nonnegative, and every multiplier in it has been
constructed and verified in this file. It is not being imported as a
black-box balanced-step theorem.

## 8. Scaling balance proves the entire lower branch

Let `0<h<=H`, set `s=h/H`, and apply (38) at step `H` to
`F=s f`. This function is convex and 1-smooth, because its gradient
Lipschitz constant is at most `s<=1`. Its step-`H` trajectory is exactly
the original step-`h` trajectory.

Write `Q^F` for its interpolation quantities. The starred terms retain
the additional nonnegative slack

**(39)**

```math
Q^F_{*i}=sQ^f_{*i}+s(1-s)\|g_i\|^2.
```
Substitution in (38), followed by nonnegativity of `W^F` and (5), gives

**(40)**

```math
\begin{aligned}
\|x_0\|^2
&\ge\|x_N\|^2+2Nh f_N+Nh(Nh+s)\|g_N\|^2
       +h(1-s)\sum_{i\lt N}\|g_i\|^2\\
&\ge\|x_N\|^2+2Nh f_N+Nh(Nh+1)\|g_N\|^2\\
&\ge(1+Nh)^2\|g_N\|^2.
\end{aligned}
```
The last line uses `||x_N||>=||g_N||` and `2f_N>=||g_N||^2`.
This proves the first branch of (1) for every `h<=H`, with no restriction
on the dimension or parity of `N`.

## Sharpness

For the normalized problem choose $`R\gt 0`$ and put $`\tau=R/(1+Nh)`$.
The one-dimensional convex, differentiable, 1-smooth Huber function is

```math
f(x)=\begin{cases}
x^2/2,&|x|\le\tau,\\
\tau|x|-\tau^2/2,&|x|\ge\tau.
\end{cases}
```

Starting at $`x_0=R`$, induction gives

```math
x_i=R-ih\tau\ge\tau\quad(0\le i\le N),
\qquad g_i=\tau,\qquad |g_N|=\frac{R}{1+Nh}.
```

The quadratic $`f(x)=x^2/2`$ instead gives
$`x_i=(1-h)^iR`$ and $`|g_N|=|1-h|^N R`$. Select the example
corresponding to the larger branch. Multiplying the objective by $`L`$
restores the prescribed Lipschitz constant. Composing either scalar
function with the inner product against a unit vector gives attainment
in every nonzero real Hilbert space, and hence every positive Euclidean
dimension. Flat orthogonal directions do not alter the gradient norm.

The formal Huber witness is the primitive of the continuous clipped identity.
The fundamental theorem of calculus supplies its actual derivative at the
joining points as well as elsewhere; convexity follows from monotonicity of
that derivative. This construction avoids any assumption about differentiability
at a piecewise join. All witness recurrences hold at every natural index;
the displayed affine formula is needed only through the chosen horizon.

## Part II. All-step continuation and equality trajectories

## All nonnegative constant steps

The extension from `(0,2]` to every `h>=0` is exact. Adding the two
interpolation inequalities involving `*` gives

**(E1)**

```math
\langle g_i,x_i\rangle\geq\|g_i\|^2,
\qquad \|g_i\|\leq\|x_i\|.
```
At `h=0` the trajectory is constant and (E1) proves the sharp bound (1) of Part I, whose coefficient
is 1. For `h>=2`,

```math
\begin{aligned}
\|x_i-hg_i\|^2
&\leq\|x_i\|^2+h(h-2)\|g_i\|^2\\
&\leq(h-1)^2\|x_i\|^2.
\end{aligned}
```
Induction and (E1) give `||g_N||<=(h-1)^N||x_0||`.
For `h>=2` this is the larger branch in the sharp bound (1) of Part I. The quadratic
`f(x)=||x||^2/2` on a line attains it, so these steps require no
asymptotic or limiting interpretation. The result is a bound on a fixed
finite horizon, not a claim of convergence when `h>=2`.

## Equality trajectories and the transition at the balancing step

Work with the normalized interpolation data of Part I, set `R=||x_0||`, and assume
`R>0` when discussing nontrivial equality. Let

```math
H_N=1+r_N,\qquad r_N^N(1+NH_N)=1.
```
The classifications below are statements about the full sampled
trajectory and its function values. They do not classify the objective
outside that trajectory.

### Strict progress branch: `0<h<H_N`

Equality `||g_N||=R/(1+Nh)` holds if and only if there is a vector `b`
such that, for every `0<=i<=N`,

**(E2)**

```math
\boxed{\quad
g_i=b,\qquad x_i=(1+(N-i)h)b,\qquad
f_i=((N-i)h+\tfrac12)\|b\|^2.
\quad}
```
To prove necessity, let `s=h/H_N`, so `0<s<1`, put `T=1+Nh`, and use
the balanced history multipliers `lambda^H_ij` in the rescaling proof.
Every one of these history multipliers is strictly positive. The full
deficit identity is

**(E3)**

```math
\begin{aligned}
R^2-T^2\|g_N\|^2={}&
s\sum_{i\ne j}\lambda^H_{ij}Q_{ij}
+h\sum_{i\lt N}Q_{*i}\\
&+s(1-s)\sum_{i\ne j}\lambda^H_{ij}\|g_i-g_j\|^2\\
&+h(1-s)\sum_{i\lt N}(\|g_i\|^2-\|g_N\|^2)\\
&+Q_{*N}+TQ_{N*}+\|x_N-g_N\|^2.
\end{aligned}
```
The history sums run over `0<=i,j<=N`. All summands are nonnegative;
the norm-difference terms use gradient-norm monotonicity. Equality makes
all gradients equal, makes `x_N=g_N`,
and makes every `Q_*i` zero. The iteration and these starred equalities
then give (E2). Conversely (E2) gives the stated equality directly, and
its interpolation data are realized by the Huber example.

For an actual normalized smooth convex function, (E2) also determines the
function and its full gradient on the visited ray segment `0<=u<=1+Nh`:

**(E4)**

```math
\nabla f(ub)=\min\{u,1\}b,
\qquad
f(ub)=\|b\|^2
\begin{cases}u^2/2,&0\leq u\leq1,\\u-1/2,&1\leq u\leq1+Nh.
\end{cases}
```
On `[0,b]`, equality of the endpoint gradient distance and point distance
forces equality in both Lipschitz estimates through each intermediate
point, giving `grad f(ub)=ub`. On `[b,(1+Nh)b]`, both endpoint gradients
equal `b`; adding cocoercivity against the two endpoints with the segment
weights forces the intermediate gradient to equal `b`. Integrating gives
(E4). No condition is imposed off this segment.

### Balance: `h=H_N`

Equality holds if and only if there are orthogonal vectors `a,b` such
that, for every `0<=i<=N`,

**(E5)**

```math
\boxed{\begin{aligned}
g_i&=b+(-r_N)^i a,\\
x_i&=(1+(N-i)H_N)b+(-r_N)^i a,\\
f_i&=((N-i)H_N+\tfrac12)\|b\|^2
                   +\tfrac12r_N^{2i}\|a\|^2.
\end{aligned}}
```
Thus the two one-dimensional mechanisms may coexist in orthogonal
directions, with no third equality trajectory hidden at the transition.

Here is a proof avoiding orthogonal projection or a choice of coordinates.
At balance the uniform certificate has `delta=h`, so the nonterminal
`Q_i*` coefficients vanish, but every history multiplier is strictly
positive. The coefficients of `Q_*i` are positive, the coefficient of
`Q_N*` is `1+Nh>0`, and the terminal square remains. Equality therefore
implies

**(E6)**

```math
Q_{ij}=0\ (0\leq i,j\leq N),\qquad
Q_{*i}=0\ (0\leq i\leq N),\qquad x_N=g_N.
```
Put `z_i=x_i-g_i`, and let `S` be the linear span of the finitely many
vectors `g_j-g_N`. The starred equality gives
`f_i=<g_i,x_i>-||g_i||^2/2`. Substituting in a history equality yields

```math
Q_{ij}=2\langle g_i-g_j,z_i\rangle=0.
```
First take `j=N`, then subtract the relation for a general `j`, to find
`z_i` orthogonal to `S`. Define

```math
c_i=z_i-z_{i+1}=r_Ng_i+g_{i+1}\qquad(0\leq i\lt N).
```
Each `c_i` is orthogonal to `S`; each `c_i-c_j` belongs to `S`.
Consequently `||c_i-c_j||^2=0`, so all `c_i` equal a vector `c`.
Since `z_N=0`, `z_i=(N-i)c`. Set

```math
b=c/H_N=z_0/(NH_N),\qquad a=g_0-b.
```
The recurrence is `g_{i+1}=-r_Ng_i+H_Nb`, proving the first two
formulas in (E5). Moreover `g_0-g_1=H_Na` belongs to `S` and
`z_0=NH_Nb` is orthogonal to `S`, so `a` and `b` are orthogonal.
The starred equality gives the formula for `f_i`.

Conversely, (E5) gives

```math
\|x_0\|^2=(1+NH_N)^2\|b\|^2+\|a\|^2,
\quad
\|g_N\|^2=\|b\|^2+r_N^{2N}\|a\|^2,
```
which are in the equality ratio. These data are realized by the sum of
a Huber function with threshold `||b||` in the `b` direction and a unit
quadratic in the orthogonal `a` direction. A zero component is simply
omitted. This construction also proves realizability in any Hilbert space
containing the specified vectors.

Strict positivity used in (E6) follows directly from the constructed
factors: `q_k>p_{k+1}/p_k>1`, hence `A` strictly increases and `D`
strictly decreases; `D_N>0=D_{N+1}`. Both expressions defining
`lambda_ab` and `lambda_ba` are therefore positive. For `N=1` this
is immediate from `p_1>0` and `r_N>0`.

### Strict oscillation branch: `H_N<h<2`

Equality `||g_N||=(h-1)^N R` holds if and only if

**(E7)**

```math
\boxed{\quad x_i=g_i=(1-h)^i x_0,\qquad
f_i=\tfrac12\|x_i\|^2\quad(0\leq i\leq N).\quad}
```
The equality argument leading from (E6) to the orthogonal decomposition
used only `r=h-1`, not terminal balance. It therefore still gives that
decomposition. In this strict branch, the uniform coefficient
`beta=h-delta` is positive, so equality additionally gives `Q_0*=0`.
The decomposition yields `f_0-||g_0||^2/2=Nh||b||^2`; thus `b=0`,
which proves (E7). The converse is the quadratic example.

For an actual normalized function, equality forces
`grad f(x)=x` and `f(x)=||x||^2/2` on the entire segment
`[(1-h)x_0,x_0]`: the endpoint gradients saturate the Lipschitz inequality,
so the argument used on `[0,b]` above applies. The objective outside
that segment need not be quadratic.

For `h>=2`, (E7) is also the equality classification. When `h>2`, equality
in the distance recursion forces equality in both inequalities following
(E1), hence `g_i=x_i` for each `i<N`; the terminal inequality also forces
`g_N=x_N`. At `h=2`, equality forces all iterate norms to equal `R`.
Gradient norms are nonincreasing by pairwise cocoercivity, while
`||g_N||=R` and `||g_i||<=||x_i||=R`, so again `g_i=x_i`.
At `h=0`, equality is simply `g_0=x_0`, `f_0=||x_0||^2/2`, with all
sampled points identical. If `R=0`, (E1) and the iteration force the zero
trajectory and zero function values, already included by `a=b=0`.

## Quantitative stability of the two strict branches

The estimates here are dimension independent and explicit in the same
certificate multipliers. They concern small deficit from the sharp bound;
they do not claim global closeness of the objective to an extremal function.

For `H_N<h<2`, put

```math
r=h-1,\quad t=r^{-N},\quad \beta=h-\delta\gt 0,\quad
\mathcal D=R^2-t^2\|g_N\|^2,\quad
E_i=f_i-\tfrac12\|g_i\|^2\geq0.
```
The exact upper certificate gives

**(E8)**

```math
\|x_N-g_N\|^2\leq\mathcal D,\qquad
2\beta E_i\leq\mathcal D\quad(i\lt N),\qquad
\lambda_{ij}Q_{ij}\leq\mathcal D.
```
Define the deviation from quadratic oscillation by
`e_i=g_{i+1}+r g_i`. Since `e_i=z_i-z_{i+1}`, direct expansion of the
two adjacent interpolation quantities gives the exact identity

**(E9)**

```math
\|e_i\|^2
=h(E_i-E_{i+1})+\tfrac r2 Q_{i+1,i}-\tfrac12Q_{i,i+1}.
```
Dropping nonpositive terms and retaining the corresponding two summands
in the deficit certificate yields

**(E10)**

```math
\boxed{\quad
\|g_{i+1}+r g_i\|^2\leq C_i\mathcal D,\qquad
C_i=\max\left\{\frac h{2\beta},\frac r{2\lambda_{i+1,i}}\right\}.
\quad}
```
For example, induction immediately gives the full gradient-path estimate

**(E11)**

```math
\|g_i-(-r)^i g_0\|
\leq\sqrt{\mathcal D}\sum_{j=0}^{i-1}r^{i-1-j}\sqrt{C_j}.
```
Also `||z_i||<=sqrt(D)(1+sum_{j=i}^{N-1}sqrt(C_j))`, by summing
`z_i-z_{i+1}=e_i`. This controls the distance of each point from its
gradient as well. If `||g_N||>=(1-epsilon)R r^N` for
`0<=epsilon<=1`, then `D<=(2epsilon-epsilon^2)R^2`.
Thus these are explicit square-root stability bounds. Their constants
may diverge at balance, where the additional extremal family (E5) exists.

For `0<h<H_N`, set `s=h/H_N`, `T=1+Nh`, and
`D_-=R^2-T^2||g_N||^2`. The decomposition (E3) gives

```math
\|x_N-g_N\|^2\leq D_-,\qquad
\|g_i-g_N\|^2\leq D_-/\kappa_i\quad(i\lt N),
```
**(E12)**

```math
\kappa_i=s(1-s)(\lambda^H_{iN}+\lambda^H_{Ni})\gt 0.
```
In particular, the whole point trajectory stays close to the constant
gradient extremal path with terminal gradient `g_N`:

**(E13)**

```math
\boxed{\quad
\|x_i-(1+(N-i)h)g_N\|
\leq\sqrt{D_-}\left(1+h\sum_{j=i}^{N-1}\kappa_j^{-1/2}\right).
\quad}
```
This follows by writing the vector on the left as
`(x_N-g_N)+h sum_{j=i}^{N-1}(g_j-g_N)` and applying (E12).
All these statements hold for finite data satisfying the interpolation inequalities of Part I, and hence for the
actual Hilbert-space optimization problem through the proved bridge.

The loss of uniform stability at balance is necessary. The orthogonal
Huber-plus-quadratic construction (E5), with `H_N` replaced by any `h>1`
and `r=h-1`, remains an admissible trajectory. Its two branch deficits are

```math
R^2-r^{-2N}\|g_N\|^2=((1+Nh)^2-r^{-2N})\|b\|^2
\quad(h\gt H_N),
```
```math
R^2-(1+Nh)^2\|g_N\|^2
=(1-(1+Nh)^2r^{2N})\|a\|^2
\quad(1\lt h\lt H_N).
```
Each tends to zero at balance while the component incompatible with its
strict-branch equality class can stay nonzero. Consequently a modulus of
distance to that pure equality class which tends to zero with the deficit
cannot be uniform in `h` near the transition.

## Why pairwise cocoercivity is not enough

The convex interpolation assumption has real mathematical content beyond
gradient-norm monotonicity or pairwise cocoercivity. On `R^2`, let

```math
G=\tfrac12\begin{pmatrix}1&-1\\1&1\end{pmatrix}.
```
For every vector `v`,

```math
\langle Gv,v\rangle=\|Gv\|^2=\tfrac12\|v\|^2.
```
Thus `G` is 1-cocoercive and `G(0)=0`. Nevertheless with `h=1`,
`N=2`, and `x_0=(1,0)`, the iteration gives

```math
x_1=(1/2,-1/2),\quad x_2=(0,-1/2),\quad
Gx_2=(1/4,-1/4).
```
Its squared terminal residual is `1/8`, exceeding the proposed smooth
convex coefficient `1/9`. There cannot be scalar function values making
these three gradient samples satisfy all the interpolation inequalities: regardless of the assigned
values, direct calculation gives

```math
Q_{01}+Q_{12}+Q_{20}=-1/4\lt 0.
```
Equivalently, `I-G` is the resolvent `(I+A)^(-1)` of the skew matrix
`A=[[0,-1],[1,0]]`, a maximal monotone operator. To see maximality without
an external theorem, a point `(u,v)` monotonically related to its graph
must satisfy `<v-Au,w>=0` for every `w`, by testing `x=u+t w` for both
signs of `t`; hence `v=Au`. Therefore the convex-function residual curve
cannot be promoted unchanged to arbitrary maximal-monotone resolvents.
The finite convex/cyclic interpolation relations are essential.


## Part III. Direct proximal minimization

## 1. A concrete algorithm contract with real-valued objectives

Let `E` be a real inner-product space, let `C` be a nonempty convex subset
of `E`, and let `F : C -> R` be convex. Equivalently, `F` may be a
real-valued function on `E` assumed convex only on `C`; values outside
`C` are irrelevant. Choose `x* in C` satisfying

```math
F(x_*)\le F(u)\qquad(u\in C),
```
and fix `lambda>0`, an integer `N>=0`, and a constant `h>=0`.
Take `x_0,...,x_N in E` and `z_0,...,z_N in C` such that, for every
`0<=i<=N`, `z_i` is an actual minimizer over `C`:

**(P1)**

```math
\lambda F(z_i)+\tfrac12\|z_i-x_i\|^2
\le\lambda F(u)+\tfrac12\|u-x_i\|^2
\qquad(u\in C).
```
For `0<=i<N`, require the relaxed proximal-point update

**(P2)**

```math
x_{i+1}=(1-h)x_i+h z_i=x_i-h e_i,
\qquad e_i:=x_i-z_i.
```
These are mathematical definitions of the algorithm, not assumed
certificate inequalities. No smoothness, subgradient oracle, Moreau
envelope, or finite interpolation hypothesis is part of the public
contract. Existence of the `z_i` is assumed here because the sequence is
supplied. General proximal existence is a separate issue; the statement here applies
to supplied minimizers.

The final residual is `e_N`: there are `N` updates and `N+1` proximal
evaluations, including the terminal evaluation at `x_N`. Neither
`x_0` nor later `x_i` must lie in `C`. Each proximal minimizer is unique
whenever it exists: midpoint convexity of the objective in (P1) gives
strict convexity from its squared-distance term.

Write `R=||x_0-x*||` and `F*=F(x*)`. Then

**(P3)**

```math
\boxed{\quad
\|e_N\|\le R\,c_N(h),\qquad
c_N(h):=\max\{(1+Nh)^{-1},\ |1-h|^N\}.
\quad}
```
The theorem holds for every `h>=0`, including `h=0,2`. When `N=0`,
powers of exponent zero use the empty-product convention, including
`0^0=1`. Both branches in (P3) are attained by one-dimensional examples,
so `c_N(h)` is the exact universal constant. For `h>2` the second branch
is a growth bound, with a matching divergent example.

## 2. Actual minimization implies the required finite inequalities

Fix `x in E` and a minimizer `z in C` in (P1), and put `e=x-z`.
For any `u in C` and `0<t<=1`, the point `z+t(u-z)` belongs to `C`.
Convexity of `F`, optimality of `z`, and expansion of the squared norm
give

```math
0\le t\{\lambda(F(u)-F(z))-\langle e,u-z\rangle\}
       +\tfrac12t^2\|u-z\|^2.
```
Dividing by `t` and letting `t` decrease to zero proves

**(P4)**

```math
\boxed{\quad
\lambda(F(u)-F(z))\ge\langle e,u-z\rangle
\qquad(u\in C).
\quad}
```
No differentiability or continuity of `F` was used. A purely algebraic
alternative to this limit is useful for formalization. If the bracket
were `-b<0`, let `B=||u-z||^2` and choose
`t=min{1,b/(B+1)}>0`. Then `t B/2<=b/2`, so the divided inequality
would imply `0<=-b/2`, a contradiction.

The converse also holds: (P4), plus the norm expansion, implies for
every `u in C` that the objective in (P1) at `u` is at least its value
at `z` plus `||u-z||^2/2`. Thus (P4) is a derived, equivalent
optimality condition and also establishes uniqueness directly.

Introduce the starred data

```math
z_*=x_*,\qquad e_*=0,\qquad a_*=0,
```
and, for `0<=i<=N`, set

**(P5)**

```math
a_i:=\lambda(F(z_i)-F_*)+\tfrac12\|e_i\|^2.
```
The point `x*` is itself the proximal minimizer at input `x*`, because
`F(u)>=F*` and squared distances are nonnegative. Hence (P4) applies
to every index in `{*,0,...,N}`. For any two such indices, expand
`x_i=z_i+e_i` to obtain the exact identity

**(P6)**

```math
\begin{aligned}
Q_{ij}
&:=2(a_i-a_j)-2\langle e_j,x_i-x_j\rangle
                           -\|e_i-e_j\|^2\\
&=2\lambda(F(z_i)-F(z_j))
                         -2\langle e_j,z_i-z_j\rangle
\ge0.
\end{aligned}
```
The final inequality is exactly (P4) at `z_j`, tested with `u=z_i`.
This includes both orders of each starred inequality; in particular

**(P7)**

```math
2a_i\ge\|e_i\|^2,
\qquad
\langle e_i,x_i-x_*\rangle\ge\|e_i\|^2,
\qquad
\|e_i\|\le\|x_i-x_*\|.
```
The middle inequality follows by adding `Q_i*` and `Q_*i`; the last
uses Cauchy--Schwarz and includes `e_i=0` without division.

The certificate proof in Part I
now applies with data `(x_i,e_i,a_i)`. Its coefficient identities use
only finitely many inner products, the update (P2), and (P6). Its
lower-branch scaling step also works directly on the data: replacing
`(e_i,a_i)` by `(s e_i,s a_i)`, for `0<s<=1`, gives

**(P8)**

```math
Q^{(s)}_{ij}=sQ_{ij}+s(1-s)\|e_i-e_j\|^2\ge0.
```
In particular, no globally defined smooth function realizing these
data has to be constructed. All arguments remain valid in `E`; no
compactness, basis, dimension bound, or Hilbert-space completeness is
needed for this finite-data step. This proves (P3) when `0<h<2`.

For `h>=2`, (P7) gives

**(P9)**

```math
\begin{aligned}
\|x_{i+1}-x_*\|^2
&\le\|x_i-x_*\|^2+h(h-2)\|e_i\|^2\\
&\le(h-1)^2\|x_i-x_*\|^2.
\end{aligned}
```
Thus `||e_N||<=(h-1)^N R`, which is (P3) in this range. For `h=0`,
every `x_i=x_0`, so (P7) proves the claim. For `N=0`, (P7) alone
proves it for all `h`.

## 3. Attainment of the full residual curve

Both examples below satisfy the actual minimization contract (P1).
Fix `R>0`, work in `E=R`, and set `x*=0`, `x_0=R`.

For the progress branch, let `C=R` and

**(P10)**

```math
a=\frac{R}{1+Nh},\qquad F(z)=\frac a\lambda|z|.
```
The proximal map is soft thresholding:
`z=sign(x) max{|x|-a,0}`, and `e=clip(x,-a,a)`.
Indeed the candidate satisfies (P4), since `|e|<=a` and
`e z=a|z|`; the converse proved above certifies its actual
optimality. Induction gives

```math
x_i=R-ih a\ge a,\qquad e_i=a\quad(0\le i\le N),
\qquad x_N=a,\quad z_N=0.
```
Consequently `||e_N||/R=1/(1+Nh)`. The boundary `x_N=a` causes no
ambiguity: the proximal minimizer is uniquely zero.

For the oscillation branch, take `C={0}` and `F(0)=0`. Then `z_i=0`
is the only feasible point, so

**(P11)**

```math
e_i=x_i=(1-h)^i R,
\qquad \|e_N\|/R=|1-h|^N.
```
In extended-real notation this is the singleton indicator
`F=indicator_{ {0} }`. The same example supplies exactness at `h=2`
and the sharp growth rate for `h>2`.

These witnesses also work in any fixed nonzero real Hilbert space by
choosing a unit vector `v` and placing the first example on the convex
set `span{v}`. The zero space has only the trivial case `R=0`.

## 4. A stronger terminal inequality on the lower branch

For `N>=1`, let `H_N` be the unique number in `(1,2)` satisfying

**(P12)**

```math
(H_N-1)^N(1+NH_N)=1.
```
Suppose `0<=h<=H_N` and put `m=Nh`. Then

**(P13)**

```math
\boxed{\quad
R^2\ge\|x_N-x_*\|^2
       +2m\lambda\bigl(F(z_N)-F_*\bigr)
       +m(m+2)\|e_N\|^2.
\quad}
```
For `h>0`, this is precisely the lower-branch joint potential in
Section 8 of Part I, applied
to the data (P5)--(P6): its term `2m a_N` supplies the extra
`m||e_N||^2`, changing the coefficient `m(m+1)` to `m(m+2)`.
For `h=0`, the assertion reduces to equality of the initial and final
distances. For `N=0`, the same statement with `m=0` holds for any `h`.

Let `Delta=F(z_N)-F*>=0`, `y=z_N-x*`, and `q=||e_N||`. Applying (P4)
with `u=x*` gives

**(P14)**

```math
\lambda\Delta\le\langle e_N,y\rangle.
```
If `q=0`, (P14) forces `Delta=0`. If `q>0`, expand `x_N-x*=y+e_N`
in (P13), use (P14) and `||y||>=lambda Delta/q`, and obtain

```math
R^2\ge
\left(\frac{\lambda\Delta}{q}+(m+1)q\right)^2.
```
Taking square roots and multiplying by `q` therefore proves, including
the zero-residual case,

**(P15)**

```math
\boxed{\quad
\lambda\bigl(F(z_N)-F_*\bigr)+(Nh+1)\|e_N\|^2
\le R\|e_N\|.
\quad}
```
This simultaneously bounds the original nonsmooth objective at the
terminal proximal point and the measured residual. Completing the
square gives the sharp objective estimate

**(P16)**

```math
\boxed{\quad
F(z_N)-F_*\le\frac{R^2}{4\lambda(Nh+1)}.
\quad}
```
Its scope here is `N>=1, 0<=h<=H_N`, together with `N=0` for all
`h`. No upper-branch objective theorem is asserted. In particular,
the objective is evaluated at `z_N`; in the extended-real formulation
the value at the relaxed point `x_N` may be infinite.

The tradeoff (P15), not just the maximum gap (P16), is attained for
every prescribed `q in [0,R/(Nh+1)]`. In the absolute-value example,
replace the threshold in (P10) by `a=q`. Then

**(P17)**

```math
e_N=q,\qquad z_N=R-(Nh+1)q\ge0,
\qquad \lambda\Delta=q\{R-(Nh+1)q\}.
```
All iterates remain in the nonnegative affine regime of soft
thresholding. The choice `q=R/[2(Nh+1)]` gives `z_N=R/2` and
attains (P16); the choice `q=R/(Nh+1)` attains the residual branch.
For these examples equality also holds in the joint potential (P13),
as follows by substituting `x_N=R-Nh q` and (P17).

## 5. Interpretation as a subgradient bound

For the feasible-set formulation, define the constrained subdifferential

```math
\partial_C F(z):=\{v\in E:
 F(u)\ge F(z)+\langle v,u-z\rangle\text{ for every }u\in C\}.
```
Equation (P4) proves `e_N/lambda in partial_C F(z_N)`. Thus (P3)
also supplies a certified subgradient with norm at most
`R c_N(h)/lambda`. The infimum of the norms of all constrained
subgradients is at most this quantity.

Exact attainment in Section 3 refers to the proximal residual and its
selected subgradient `e_N/lambda`. It does not assert that this
selected subgradient has minimum norm: for example, the singleton
indicator has a zero subgradient at its proximal point even when
`e_N` is nonzero.

The convex optimization hypothesis is essential. One cannot replace
`partial F` by an arbitrary monotone operator and keep (P3). For a
concrete check, let `E=R^2`, let `A(x,y)=(-y,x)`, and take
`lambda=h=1`, `N=2`, and `x_0=(1,0)`. This linear operator is
monotone, since `<Av,v>=0`. Its resolvent is

```math
J=(I+A)^{-1}=\tfrac12
\begin{pmatrix}1&1\\-1&1\end{pmatrix}.
```
With `x_{i+1}=Jx_i` and `e_i=x_i-Jx_i`, direct calculation gives
`x_2=(0,-1/2)` and `e_2=(1/4,-1/4)`. Thus
`||e_2||^2=1/8>1/9=R^2 c_2(1)^2`. The finite inequalities (P6)
use a common convex objective; monotonicity alone does not supply them.
