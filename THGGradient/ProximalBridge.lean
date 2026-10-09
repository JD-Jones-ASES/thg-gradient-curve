module

public import THGGradient.FactorIdentity

/-! Finite interpolation follows from actual constrained proximal minimization.
No differentiability or continuity of the original objective is assumed. -/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace

namespace THGGradient

/-- An algebraic right-derivative argument requiring no limit machinery. -/
theorem nonneg_of_quadratic_nonneg {A B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t * A + t ^ 2 * B / 2) : 0 ≤ A := by
  by_contra hn
  have hA : A < 0 := lt_of_not_ge hn
  let t := min 1 (-A / (B + 1))
  have ht : 0 < t := lt_min zero_lt_one (div_pos (by linarith) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htd : t * (B + 1) ≤ -A :=
    (le_div_iff₀ (show 0 < B + 1 by positivity)).mp (min_le_right _ _)
  have hp := h t ht ht1
  have hp' : 0 ≤ t * (A + t * B / 2) := by nlinarith [hp]
  have hinside : 0 ≤ A + t * B / 2 := nonneg_of_mul_nonneg_right hp' ht
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The variational inequality is derived from actual minimization over a convex set. -/
theorem proximal_variational {C : Set E} {F : E → ℝ} (hF : ConvexOn ℝ C F)
    {lam : ℝ} (hlam : 0 < lam) (x z : E) (hz : z ∈ C)
    (hmin : ∀ u ∈ C, lam * F z + ‖x - z‖ ^ 2 / 2 ≤
      lam * F u + ‖x - u‖ ^ 2 / 2) (u : E) (hu : u ∈ C) :
    ⟪x - z, u - z⟫_ℝ ≤ lam * (F u - F z) := by
  have hA : 0 ≤ lam * (F u - F z) - ⟪x - z, u - z⟫_ℝ := by
    apply nonneg_of_quadratic_nonneg (sq_nonneg ‖u - z‖)
    intro t ht ht1
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hw := hF.1 hz hu h1t ht.le (by ring : 1 - t + t = 1)
    have hcv := hF.2 hz hu h1t ht.le (by ring : 1 - t + t = 1)
    have hm := hmin ((1 - t) • z + t • u) hw
    have hcv' := mul_le_mul_of_nonneg_left hcv hlam.le
    have hwx : x - ((1 - t) • z + t • u) = (x - z) - t • (u - z) := by module
    rw [hwx, norm_sub_sq_real (x - z) (t • (u - z))] at hm
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      smul_eq_mul] at hm hcv'
    nlinarith
  linarith

/-- The variational inequality gives the full quadratic growth of the proximal objective. -/
theorem proximal_quadratic_growth {C : Set E} {F : E → ℝ} {lam : ℝ}
    (x z : E)
    (hvar : ∀ u ∈ C, ⟪x - z, u - z⟫_ℝ ≤ lam * (F u - F z))
    (u : E) (hu : u ∈ C) :
    lam * F z + ‖x - z‖ ^ 2 / 2 + ‖u - z‖ ^ 2 / 2 ≤
      lam * F u + ‖x - u‖ ^ 2 / 2 := by
  have hv := hvar u hu
  have he : x - u = (x - z) - (u - z) := by abel
  rw [he, norm_sub_sq_real (x - z) (u - z)]
  nlinarith

/-- Thus the actual proximal minimizer, when supplied, is unique. -/
theorem proximal_minimizer_unique {C : Set E} {F : E → ℝ}
    (hF : ConvexOn ℝ C F) {lam : ℝ} (hlam : 0 < lam)
    (x z w : E) (hz : z ∈ C) (hw : w ∈ C)
    (hzmin : ∀ u ∈ C, lam * F z + ‖x - z‖ ^ 2 / 2 ≤
      lam * F u + ‖x - u‖ ^ 2 / 2)
    (hwmin : ∀ u ∈ C, lam * F w + ‖x - w‖ ^ 2 / 2 ≤
      lam * F u + ‖x - u‖ ^ 2 / 2) : z = w := by
  have hg := proximal_quadratic_growth x z
    (proximal_variational hF hlam x z hz hzmin) w hw
  have hm := hwmin z hz
  have hn : ‖w - z‖ = 0 := by nlinarith [norm_nonneg (w - z)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

/-- The residual/value data of two actual proximal points satisfy smooth interpolation. -/
theorem proximal_interpolation {C : Set E} {F : E → ℝ}
    (hF : ConvexOn ℝ C F) {lam : ℝ} (hlam : 0 < lam)
    (x y z w : E) (hz : z ∈ C) (hw : w ∈ C)
    (hwmin : ∀ u ∈ C, lam * F w + ‖y - w‖ ^ 2 / 2 ≤
      lam * F u + ‖y - u‖ ^ 2 / 2) :
    0 ≤ 2 * ((lam * F z + ‖x - z‖ ^ 2 / 2) -
        (lam * F w + ‖y - w‖ ^ 2 / 2)) -
      2 * ⟪y - w, x - y⟫_ℝ - ‖(x - z) - (y - w)‖ ^ 2 := by
  have hv := proximal_variational hF hlam y w hw hwmin z hz
  rw [norm_sub_sq_real (x - z) (y - w)]
  simp only [inner_sub_left, inner_sub_right] at *
  rw [real_inner_comm y x, real_inner_comm w x, real_inner_comm y z,
    real_inner_comm w z, norm_sub_sq_real y w, real_inner_comm y w]
  simp only [real_inner_self_eq_norm_sq] at *
  nlinarith

/-- Objective-plus-residual data, normalized at the actual minimizer. -/
def proximalDataValue (lam : ℝ) (F : E → ℝ) (xstar : E) (x z : ℕ → E)
    (i : ℕ) : ℝ := lam * (F (z i) - F xstar) + ‖x i - z i‖ ^ 2 / 2

/-- Every finite actual proximal trajectory supplies the certificate's ordinary data.
The final proximal evaluation at index `N` is included. -/
theorem proximal_finite_data (N : ℕ) {C : Set E} {F : E → ℝ}
    (hF : ConvexOn ℝ C F) {lam h : ℝ} (hlam : 0 < lam)
    (xstar : E) (hxstar : xstar ∈ C)
    (hmin : ∀ u ∈ C, F xstar ≤ F u)
    (x z : ℕ → E) (hz : ∀ i ≤ N, z i ∈ C)
    (hprox : ∀ i ≤ N, ∀ u ∈ C,
      lam * F (z i) + ‖x i - z i‖ ^ 2 / 2 ≤
      lam * F u + ‖x i - u‖ ^ 2 / 2)
    (hrec : ∀ i < N, x (i + 1) = x i - h • (x i - z i)) :
    (∀ i ≤ N, ∀ j ≤ N,
      0 ≤ interpolationQ (fun i => x i - xstar) (fun i => x i - z i)
        (proximalDataValue lam F xstar x z) i j) ∧
    (∀ i ≤ N, 0 ≤ starQ (fun i => x i - xstar) (fun i => x i - z i)
        (proximalDataValue lam F xstar x z) i) ∧
    (∀ i ≤ N, 0 ≤ toStarQ (fun i => x i - z i)
        (proximalDataValue lam F xstar x z) i) ∧
    (∀ i < N, x (i + 1) - xstar = (x i - xstar) - h • (x i - z i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    have hp := proximal_interpolation hF hlam (x i) (x j) (z i) (z j)
      (hz i hi) (hz j hj) (hprox j hj)
    have he : (x i - xstar) - (x j - xstar) = x i - x j := by abel
    dsimp only [interpolationQ, proximalDataValue]
    rw [he]
    nlinarith [hp]
  · intro i hi
    have hv := proximal_variational hF hlam (x i) (z i) (hz i hi)
      (hprox i hi) xstar hxstar
    have he : xstar - z i = (x i - z i) - (x i - xstar) := by abel
    rw [he, inner_sub_right, real_inner_self_eq_norm_sq] at hv
    dsimp only [starQ, proximalDataValue]
    nlinarith [hv]
  · intro i hi
    have hv := mul_nonneg hlam.le (sub_nonneg.mpr (hmin (z i) (hz i hi)))
    dsimp only [toStarQ, proximalDataValue]
    nlinarith [hv]
  · intro i hi
    rw [hrec i hi]
    abel

end THGGradient
