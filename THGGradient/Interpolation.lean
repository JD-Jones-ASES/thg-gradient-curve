module
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic

public section
set_option backward.isDefEq.respectTransparency false
namespace THGGradient
open scoped InnerProductSpace
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {g : E → E} {L : ℝ}

/-- Derivative of the restriction of a function with its actual gradient to an affine line. -/
theorem hasDerivAt_line (hg : ∀ x, HasGradientAt f (g x) x) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) ⟪g (x + t • v), v⟫_ℝ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
  simpa only [InnerProductSpace.toDual_apply_apply, Function.comp_def] using
    (hg (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline

/-- First-order support for an actual differentiable convex function. -/
theorem firstOrderSupport (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (x y : E) :
    f x + ⟪g x, y - x⟫_ℝ ≤ f y := by
  have hc : ConvexOn ℝ Set.univ (f ∘ AffineMap.lineMap (k := ℝ) x y) := by
    simpa using hf.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
  have hd : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x y) ⟪g x, y - x⟫_ℝ 0 := by
    simpa using (hg ((AffineMap.lineMap (k := ℝ) x y) 0)).hasFDerivAt.comp_hasDerivAt 0
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have hs := hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) hd
  simp [slope] at hs
  linarith

/-- The sharp descent estimate, derived from the ordinary pairwise gradient Lipschitz bound. -/
theorem smoothDescent (hg : ∀ x, HasGradientAt f (g x) x) (_hL : 0 < L)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪g x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2 := by
  let v := y - x
  let P : ℝ → ℝ := fun t => f (x + t • v) - f x - t * ⟪g x, v⟫_ℝ
    - (L / 2) * t ^ 2 * ‖v‖ ^ 2
  have hd (t : ℝ) : HasDerivAt P
      (⟪g (x + t • v) - g x, v⟫_ℝ - L * t * ‖v‖ ^ 2) t := by
    convert (((hasDerivAt_line hg x v t).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const ⟪g x, v⟫_ℝ)).sub
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖v‖ ^ 2)) using 1 <;>
      simp only [P, inner_sub_left, id_eq, Pi.pow_apply] <;>
      first | rfl | ring
  have hnonpos (t : ℝ) (ht : t ∈ interior (Set.Icc (0 : ℝ) 1)) :
      deriv P t ≤ 0 := by
    rw [(hd t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hb := hLip (x + t • v) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hb
    have hc := real_inner_le_norm (g (x + t • v) - g x) v
    have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
    nlinarith
  have hanti : AntitoneOn P (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt) hnonpos
  have hh := hanti (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [P, v] at hh
  simp only [zero_smul, one_smul, add_zero, add_sub_cancel, zero_mul, one_mul,
    one_pow, mul_one, sub_zero] at hh
  linarith

/-- Smooth-convex interpolation from convexity, actual gradients, and their Lipschitz estimate. -/
theorem smoothConvexInterpolation (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (hL : 0 < L)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖g x - g y‖ ^ 2 ≤ 2 * L * (f x - f y - ⟪g y, x - y⟫_ℝ) := by
  let d := g x - g y
  let z := x - L⁻¹ • d
  have hs := firstOrderSupport hf hg y z
  have hd := smoothDescent hg hL hLip x z
  have hzx : z - x = -(L⁻¹ • d) := by dsimp [z]; abel
  have hzy : z - y = (x - y) - L⁻¹ • d := by dsimp [z]; abel
  rw [hzy, inner_sub_right, inner_smul_right] at hs
  rw [hzx, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), mul_pow] at hd
  have hcoef : L / 2 * (L⁻¹ ^ 2 * ‖d‖ ^ 2) = (L⁻¹ / 2) * ‖d‖ ^ 2 := by
    field_simp
  rw [hcoef] at hd
  have hi : ⟪g x, d⟫_ℝ - ⟪g y, d⟫_ℝ = ‖d‖ ^ 2 := by
    rw [← inner_sub_left, ← real_inner_self_eq_norm_sq]
  have hh : (‖d‖ ^ 2 / 2) / L ≤ f x - f y - ⟪g y, x - y⟫_ℝ := by
    rw [div_eq_mul_inv]
    have hie := congrArg (fun a : ℝ => L⁻¹ * a) hi
    nlinarith [le_trans hs hd]
  rw [div_le_iff₀ hL] at hh
  dsimp [d] at hh
  nlinarith

/-- At an ordinary global minimizer the supplied actual gradient is zero. -/
theorem gradient_eq_zero_of_minimizer (hg : ∀ x, HasGradientAt f (g x) x)
    {xstar : E} (hmin : ∀ x, f xstar ≤ f x) : g xstar = 0 := by
  have hm : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
  have hz := hm.hasFDerivAt_eq_zero (hg xstar).hasFDerivAt
  have he := congrArg (fun A : E →L[ℝ] ℝ => A (g xstar)) hz
  simp only [InnerProductSpace.toDual_apply_apply, zero_apply,
    real_inner_self_eq_norm_sq] at he
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (g xstar)])

/-- Cocoercivity with the prescribed Lipschitz constant, derived by adding interpolation. -/
theorem gradientCocoercive (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (hL : 0 < L)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖g x - g y‖ ^ 2 ≤ L * ⟪g x - g y, x - y⟫_ℝ := by
  have hxy := smoothConvexInterpolation hf hg hL hLip x y
  have hyx := smoothConvexInterpolation hf hg hL hLip y x
  rw [norm_sub_rev (g y) (g x)] at hyx
  have hi : ⟪g x, y - x⟫_ℝ = -⟪g x, x - y⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  rw [hi] at hyx
  rw [inner_sub_left]
  nlinarith

/-- The ordinary Lipschitz gradient bound relative to a genuine minimizer. -/
theorem gradient_norm_le_distance (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {xstar : E} (hmin : ∀ x, f xstar ≤ f x) (x : E) :
    ‖g x‖ ≤ L * ‖x - xstar‖ := by
  simpa [gradient_eq_zero_of_minimizer hg hmin] using hLip x xstar

/-- Translation and division by the smoothness constant produce normalized interpolation data. -/
theorem normalizedInterpolation (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (hL : 0 < L)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (xstar x y : E) :
    0 ≤ 2 * ((f x - f xstar) / L - (f y - f xstar) / L)
      - 2 * ⟪L⁻¹ • g y, (x - xstar) - (y - xstar)⟫_ℝ
      - ‖L⁻¹ • g x - L⁻¹ • g y‖ ^ 2 := by
  have hh := smoothConvexInterpolation hf hg hL hLip x y
  have hpos : 0 < L ^ 2 := sq_pos_of_pos hL
  have hdiff : (x - xstar) - (y - xstar) = x - y := by abel
  rw [hdiff, real_inner_smul_left, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hL), mul_pow]
  have hid : 2 * ((f x - f xstar) / L - (f y - f xstar) / L)
      - 2 * (L⁻¹ * ⟪g y, x - y⟫_ℝ) - L⁻¹ ^ 2 * ‖g x - g y‖ ^ 2 =
      (2 * L * (f x - f y - ⟪g y, x - y⟫_ℝ) - ‖g x - g y‖ ^ 2) / L ^ 2 := by
    field_simp
    ring
  rw [hid]
  exact div_nonneg (sub_nonneg.mpr hh) hpos.le

end THGGradient
