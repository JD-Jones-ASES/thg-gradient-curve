module
public import Mathlib

/-! Independent ordinary mathematical statements for the THG gradient curve.
The principal gradient bound covers all horizons and nonnegative steps on real
Hilbert spaces. Equality classifies sampled data after normalization. The proximal
statements concern actual minimizers, including the terminal evaluation.
Only the ten independent statement placeholders are intentional. -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The full sharp final-gradient bound, for every horizon and nonnegative step. -/
theorem last_gradient_bound (N : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (f : E → ℝ) (g : E → E) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ y, HasGradientAt f (g y) y)
    (hLip : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - (h / L) • g (x i)) :
    ‖g (x N)‖ ≤ L * ‖x 0 - xstar‖ *
      max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
  sorry

/-- Both terms in the sharp curve are attained by actual smooth convex real functions.
The function is selected between the Huber primitive and the quadratic. The supplied
trajectory satisfies the gradient recurrence for every natural index. -/
theorem scalar_attainment (N : ℕ) {h L R : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (hR : 0 < R) :
    ∃ (f : ℝ → ℝ) (g : ℝ → ℝ) (x : ℕ → ℝ),
      ConvexOn ℝ Set.univ f ∧
      (∀ y, HasGradientAt f (g y) y) ∧
      (∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) ∧
      (∀ y, f 0 ≤ f y) ∧
      x 0 = R ∧
      (∀ i, x (i + 1) = x i - (h / L) * g (x i)) ∧
      ‖g (x N)‖ = L * R * max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
  sorry

/-- The complete progress-branch potential, with the original smoothness normalization. -/
theorem progress_joint_bound (N : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (hbranch : |1 - h| ^ N ≤ (1 + (N : ℝ) * h)⁻¹)
    (f : E → ℝ) (g : E → E) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ y, HasGradientAt f (g y) y)
    (hLip : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - (h / L) • g (x i)) :
    ‖x N - xstar‖ ^ 2 + (2 * (N : ℝ) * h / L) * (f (x N) - f xstar) +
      ((N : ℝ) * h * (1 + (N : ℝ) * h) / L ^ 2) * ‖g (x N)‖ ^ 2 ≤
        ‖x 0 - xstar‖ ^ 2 := by
  sorry

/-- In the strict progress branch, equality holds exactly for the constant-gradient
sampled trajectory with its forced Huber values. -/
theorem progress_equality (N : ℕ) (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (hbranch : |1 - h| ^ N < (1 + (N : ℝ) * h)⁻¹)
    (f : E → ℝ) (g : E → E) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ y, HasGradientAt f (g y) y)
    (hLip : ∀ y z, ‖g y - g z‖ ≤ ‖y - z‖)
    (hf0 : f 0 = 0) (hmin : ∀ y, f 0 ≤ f y) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - h • g (x i)) :
    ‖g (x N)‖ = ‖x 0‖ * (1 + (N : ℝ) * h)⁻¹ ↔
      ∀ i ≤ N, g (x i) = g (x N) ∧
        x i = (1 + ((N : ℝ) - i) * h) • g (x N) ∧
        f (x i) = (((N : ℝ) - i) * h + 1 / 2) * ‖g (x N)‖ ^ 2 := by
  sorry

/-- In the strict oscillation branch, equality holds exactly for the quadratic
sampled trajectory, including the endpoint `h = 2` and all larger steps. -/
theorem oscillation_equality (N : ℕ) (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (hbranch : (1 + (N : ℝ) * h)⁻¹ < |1 - h| ^ N)
    (f : E → ℝ) (g : E → E) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ y, HasGradientAt f (g y) y)
    (hLip : ∀ y z, ‖g y - g z‖ ≤ ‖y - z‖)
    (hf0 : f 0 = 0) (hmin : ∀ y, f 0 ≤ f y) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - h • g (x i)) :
    ‖g (x N)‖ = ‖x 0‖ * |1 - h| ^ N ↔
      ∀ i ≤ N, x i = (1 - h) ^ i • x 0 ∧
        g (x i) = x i ∧ f (x i) = ‖x i‖ ^ 2 / 2 := by
  sorry

/-- At the literal crossing of the rates, equality holds exactly for an orthogonal
sum of the constant-gradient and quadratic sampled trajectories. -/
theorem balance_equality (N : ℕ) (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (hbranch : |1 - h| ^ N = (1 + (N : ℝ) * h)⁻¹)
    (f : E → ℝ) (g : E → E) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ y, HasGradientAt f (g y) y)
    (hLip : ∀ y z, ‖g y - g z‖ ≤ ‖y - z‖)
    (hf0 : f 0 = 0) (hmin : ∀ y, f 0 ≤ f y) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - h • g (x i)) :
    ‖g (x N)‖ = ‖x 0‖ * (1 + (N : ℝ) * h)⁻¹ ↔
      ∃ a b : E, ⟪a, b⟫_ℝ = 0 ∧ ∀ i ≤ N,
        g (x i) = b + (1 - h) ^ i • a ∧
        x i = (1 + ((N : ℝ) - i) * h) • b + (1 - h) ^ i • a ∧
        f (x i) = (((N : ℝ) - i) * h + 1 / 2) * ‖b‖ ^ 2 +
          ((1 - h) ^ i) ^ 2 / 2 * ‖a‖ ^ 2 := by
  sorry

/-- Exact residual rate for a trajectory of actual proximal minimizers. -/
theorem proximal_residual_bound (N : ℕ) {h lam : ℝ} (hh : 0 ≤ h) (hlam : 0 < lam)
    (C : Set E) (F : E → ℝ) (hF : ConvexOn ℝ C F)
    (xstar : E) (hxstar : xstar ∈ C) (hmin : ∀ u ∈ C, F xstar ≤ F u)
    (x z : ℕ → E) (hz : ∀ i ≤ N, z i ∈ C)
    (hprox : ∀ i ≤ N, ∀ u ∈ C, lam * F (z i) + ‖x i - z i‖ ^ 2 / 2 ≤
      lam * F u + ‖x i - u‖ ^ 2 / 2)
    (hrec : ∀ i < N, x (i + 1) = x i - h • (x i - z i)) :
    ‖x N - z N‖ ≤ ‖x 0 - xstar‖ *
      max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
  sorry

/-- Actual constrained proximal examples attain the full residual curve. -/
theorem proximal_residual_attainment (N : ℕ) {h lam R : ℝ}
    (hh : 0 ≤ h) (hlam : 0 < lam) (hR : 0 < R) :
    ∃ (C : Set ℝ) (F : ℝ → ℝ) (x z : ℕ → ℝ),
      ConvexOn ℝ C F ∧ (0 : ℝ) ∈ C ∧
      (∀ u ∈ C, F 0 ≤ F u) ∧ x 0 = R ∧
      (∀ i, z i ∈ C) ∧
      (∀ i, ∀ u ∈ C, lam * F (z i) + ‖x i - z i‖ ^ 2 / 2 ≤
        lam * F u + ‖x i - u‖ ^ 2 / 2) ∧
      (∀ i, x (i + 1) = x i - h * (x i - z i)) ∧
      ‖x N - z N‖ = R * max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
  sorry

/-- Sharp progress-branch objective-residual tradeoff and its objective-gap consequence. -/
theorem proximal_progress_tradeoff (N : ℕ) {h lam : ℝ} (hh : 0 ≤ h) (hlam : 0 < lam)
    (hbranch : |1 - h| ^ N ≤ (1 + (N : ℝ) * h)⁻¹)
    (C : Set E) (F : E → ℝ) (hF : ConvexOn ℝ C F)
    (xstar : E) (hxstar : xstar ∈ C) (hmin : ∀ u ∈ C, F xstar ≤ F u)
    (x z : ℕ → E) (hz : ∀ i ≤ N, z i ∈ C)
    (hprox : ∀ i ≤ N, ∀ u ∈ C, lam * F (z i) + ‖x i - z i‖ ^ 2 / 2 ≤
      lam * F u + ‖x i - u‖ ^ 2 / 2)
    (hrec : ∀ i < N, x (i + 1) = x i - h • (x i - z i)) :
    (lam * (F (z N) - F xstar) + (1 + (N : ℝ) * h) * ‖x N - z N‖ ^ 2 ≤
      ‖x 0 - xstar‖ * ‖x N - z N‖) ∧
    F (z N) - F xstar ≤ ‖x 0 - xstar‖ ^ 2 / (4 * lam * (1 + (N : ℝ) * h)) := by
  sorry

/-- The objective coefficient is attained by an actual convex absolute-value problem.
The construction exists at every nonnegative step; the matching universal upper
bound is asserted only in its separately proved progress range. -/
theorem proximal_objective_attainment (N : ℕ) {h lam R : ℝ}
    (hh : 0 ≤ h) (hlam : 0 < lam) (hR : 0 < R) :
    ∃ (F : ℝ → ℝ) (x z : ℕ → ℝ),
      ConvexOn ℝ Set.univ F ∧ (∀ u, F 0 ≤ F u) ∧ x 0 = R ∧
      (∀ i u, lam * F (z i) + ‖x i - z i‖ ^ 2 / 2 ≤
        lam * F u + ‖x i - u‖ ^ 2 / 2) ∧
      (∀ i, x (i + 1) = x i - h * (x i - z i)) ∧
      F (z N) - F 0 = R ^ 2 / (4 * lam * (1 + (N : ℝ) * h)) := by
  sorry

end THGGradient
