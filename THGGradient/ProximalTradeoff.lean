module
public import THGGradient.ProximalBridge
public import THGGradient.LowerBranch

/-! The sharp terminal objective-residual tradeoff from the progress potential. -/

public section
open scoped BigOperators InnerProductSpace
namespace THGGradient

theorem scalar_tradeoff {R q a d T : ℝ} (hR : 0 ≤ R) (hq : 0 ≤ q)
    (_ha : 0 ≤ a) (hd : 0 ≤ d) (_hT : 0 ≤ T)
    (hda : d ≤ q * a)
    (hpot : a ^ 2 + 2 * T * d + T ^ 2 * q ^ 2 ≤ R ^ 2) :
    d + T * q ^ 2 ≤ R * q := by
  have hdsq : d ^ 2 ≤ q ^ 2 * a ^ 2 := by
    nlinarith [mul_nonneg hq _ha]
  have hp := mul_le_mul_of_nonneg_left hpot (sq_nonneg q)
  have hs : (d + T * q ^ 2) ^ 2 ≤ (R * q) ^ 2 := by nlinarith
  have hz : 0 ≤ R * q := mul_nonneg hR hq
  nlinarith

theorem objective_bound_of_tradeoff {R q d T : ℝ}
    (hT : 0 < T) (hbound : d + T * q ^ 2 ≤ R * q) :
    d ≤ R ^ 2 / (4 * T) := by
  apply (le_div_iff₀ (by positivity : 0 < 4 * T)).mpr
  have hh := mul_le_mul_of_nonneg_left hbound hT.le
  nlinarith [sq_nonneg (R - 2 * T * q)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem proximal_tradeoff_of_joint (N : ℕ) {h lam : ℝ} (hh : 0 ≤ h)
    (hlam : 0 < lam) {C : Set E} {F : E → ℝ} (hF : ConvexOn ℝ C F)
    (xstar : E) (hxstar : xstar ∈ C) (hmin : ∀ u ∈ C, F xstar ≤ F u)
    (x z : ℕ → E) (hz : z N ∈ C)
    (hprox : ∀ u ∈ C, lam * F (z N) + ‖x N - z N‖ ^ 2 / 2 ≤
      lam * F u + ‖x N - u‖ ^ 2 / 2)
    (hjoint : ‖x N - xstar‖ ^ 2 +
      2 * (N : ℝ) * h * proximalDataValue lam F xstar x z N +
      (N : ℝ) * h * (1 + (N : ℝ) * h) * ‖x N - z N‖ ^ 2 ≤
        ‖x 0 - xstar‖ ^ 2) :
    lam * (F (z N) - F xstar) + (1 + (N : ℝ) * h) * ‖x N - z N‖ ^ 2 ≤
      ‖x 0 - xstar‖ * ‖x N - z N‖ := by
  let e := x N - z N
  let y := z N - xstar
  let d := lam * (F (z N) - F xstar)
  let T := 1 + (N : ℝ) * h
  have hd : 0 ≤ d := mul_nonneg hlam.le (sub_nonneg.mpr (hmin _ hz))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hvar := proximal_variational hF hlam (x N) (z N) hz hprox xstar hxstar
  have hv : d ≤ ⟪e, y⟫_ℝ := by
    have he : xstar - z N = -y := by dsimp [y]; abel
    rw [he, inner_neg_right] at hvar
    dsimp [d, e]
    linarith
  have heq : x N - xstar = y + e := by dsimp [y, e]; abel
  rw [heq, norm_add_sq_real] at hjoint
  dsimp [proximalDataValue] at hjoint
  have hc : ⟪y, e⟫_ℝ = ⟪e, y⟫_ℝ := real_inner_comm _ _
  rw [hc] at hjoint
  have hpot : ‖y‖ ^ 2 + 2 * T * d + T ^ 2 * ‖e‖ ^ 2 ≤
      ‖x 0 - xstar‖ ^ 2 := by
    dsimp [T, d, e] at *
    nlinarith
  exact scalar_tradeoff (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hd hT
    (hv.trans (real_inner_le_norm _ _)) hpot

end THGGradient
