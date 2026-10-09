module
public import THGGradient.FactorIdentity
public import THGGradient.LowerBranch

/-! Exact coefficient equations and nonnegative weights imply the upper and balanced bounds.
The scalar factor construction discharges these internal certificate hypotheses. -/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace
open Finset
namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Nonnegative interpolation data give a nonnegative weighted sum. -/
theorem weighted_interpolation_nonneg (N : ℕ) (w : ℕ → ℕ → ℝ)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hw : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ w i j)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j) :
    0 ≤ ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j := by
  apply sum_nonneg
  intro i hi
  apply sum_nonneg
  intro j hj
  exact mul_nonneg (hw i (by simpa using hi) j (by simpa using hj))
    (hQ i (by simpa using hi) j (by simpa using hj))

/-- Exact completion yields the upper bound once the coefficients and signs have been proved. -/
theorem upper_norm_of_coefficients (N : ℕ) {h t : ℝ} (hh : 0 ≤ h) (ht : 0 < t)
    (w : ℕ → ℕ → ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i)
    (hto : ∀ i ≤ N, 0 ≤ toStarQ g f i)
    (hw : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ w i j)
    (hoff : ∀ i ≤ N, ∀ j ≤ N, i ≠ j →
      gradientCoefficient N h w i j + gradientCoefficient N h w j i = 0)
    (hdiag : ∀ i ≤ N, 2 * gradientCoefficient N h w i i
      - (∑ j ∈ range (N + 1), (w i j + w j i)) =
        -weightDivergence N w i + if i < N then 1 - (h - 1) ^ 2 else -(t ^ 2 - 1))
    (hdiv : ∀ i < N, weightDivergence N w i ≤ h)
    (hsum : -1 ≤ ∑ i ∈ range N, weightDivergence N w i) :
    ‖g N‖ ≤ ‖x 0‖ / t := by
  have hW := trajectory_weighted_decomposition N h t w f x g hx hoff hdiag
  have heq := certificate_completion N h t _ (weightDivergence N w) f x g hx hW
  have hnonneg := weighted_interpolation_nonneg N w x g f hw hQ
  have hs : 0 ≤ h * ∑ i ∈ range N, starQ x g f i := by
    apply mul_nonneg hh
    exact sum_nonneg (fun i hi => hstar i (by have := mem_range.mp hi; omega))
  have hts : 0 ≤ ∑ i ∈ range N, (h - weightDivergence N w i) * toStarQ g f i := by
    apply sum_nonneg
    intro i hi
    exact mul_nonneg (sub_nonneg.mpr (hdiv i (mem_range.mp hi)))
      (hto i (by have := mem_range.mp hi; omega))
  have htn : 0 ≤ (1 + ∑ i ∈ range N, weightDivergence N w i) * toStarQ g f N :=
    mul_nonneg (by linarith) (hto N le_rfl)
  have hb : t ^ 2 * ‖g N‖ ^ 2 ≤ ‖x 0‖ ^ 2 := by
    nlinarith [hstar N le_rfl, sq_nonneg ‖x N - g N‖]
  apply (le_div_iff₀ ht).mpr
  nlinarith [norm_nonneg (x 0), norm_nonneg (g N)]

/-- A common divergence bounded by the step supplies all scalar sign conditions. -/
theorem upper_norm_of_uniform_coefficients (N : ℕ) {h t δ : ℝ}
    (hh : 0 ≤ h) (ht : 0 < t) (hδ : 0 ≤ δ) (hδh : δ ≤ h)
    (w : ℕ → ℕ → ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i)
    (hto : ∀ i ≤ N, 0 ≤ toStarQ g f i)
    (hw : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ w i j)
    (hoff : ∀ i ≤ N, ∀ j ≤ N, i ≠ j →
      gradientCoefficient N h w i j + gradientCoefficient N h w j i = 0)
    (hdiag : ∀ i ≤ N, 2 * gradientCoefficient N h w i i
      - (∑ j ∈ range (N + 1), (w i j + w j i)) =
        -weightDivergence N w i + if i < N then 1 - (h - 1) ^ 2 else -(t ^ 2 - 1))
    (hdiv : ∀ i < N, weightDivergence N w i = δ) :
    ‖g N‖ ≤ ‖x 0‖ / t := by
  apply upper_norm_of_coefficients N hh ht w x g f hx hQ hstar hto hw hoff hdiag
  · intro i hi
    rw [hdiv i hi]
    exact hδh
  · have hnonneg : 0 ≤ ∑ i ∈ range N, weightDivergence N w i := by
      apply sum_nonneg
      intro i hi
      rw [hdiv i (mem_range.mp hi)]
      exact hδ
    linarith

/-- At balance, pairwise interpolation alone proves the retained certificate. -/
theorem balanced_retained_of_coefficients (N : ℕ) (h : ℝ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ w i j)
    (hoff : ∀ i ≤ N, ∀ j ≤ N, i ≠ j →
      gradientCoefficient N h w i j + gradientCoefficient N h w j i = 0)
    (hdiag : ∀ i ≤ N, 2 * gradientCoefficient N h w i i
      - (∑ j ∈ range (N + 1), (w i j + w j i)) =
        -weightDivergence N w i + if i < N then 1 - (h - 1) ^ 2
          else -((1 + N * h) ^ 2 - 1))
    (hdiv : ∀ i < N, weightDivergence N w i = h) :
    BalancedRetainedCertificate E N h := by
  intro x g f hx hQ
  have hW := trajectory_weighted_decomposition N h (1 + N * h) w f x g hx hoff hdiag
  have he : (∑ i ∈ range N, 2 * weightDivergence N w i *
      ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2))) =
      ∑ i ∈ range N, 2 * h *
      ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2)) := by
    apply sum_congr rfl
    intro i hi
    rw [hdiv i (mem_range.mp hi)]
  rw [he] at hW
  have heq := balanced_certificate_completion N h _ f x g hx hW
  have hnonneg := weighted_interpolation_nonneg N w x g f hw hQ
  linarith

end THGGradient
