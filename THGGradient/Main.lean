module
public import THGGradient.UniformCertificate
public import THGGradient.WitnessLift
public import THGGradient.ProximalTradeoff
public import THGGradient.ProximalObjectiveWitness

/-! Principal theorems for actual smooth convex functions and proximal minimizers. -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace THGGradient

section Gradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The full sharp final-gradient bound, for every horizon and nonnegative step. -/
theorem last_gradient_bound (N : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (f : E → ℝ) (g : E → E) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ y, HasGradientAt f (g y) y)
    (hLip : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - (h / L) • g (x i)) :
    ‖g (x N)‖ ≤ L * ‖x 0 - xstar‖ *
      max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) :=
  actual_gradient_of_data_bound N h (normalized_bound N hh) hL f g hf hg hLip
    xstar hmin x hrec

/-- Canonical Mathlib gradient version; differentiability is explicit. -/
theorem canonical_last_gradient_bound (N : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hLip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - (h / L) • gradient f (x i)) :
    ‖gradient f (x N)‖ ≤ L * ‖x 0 - xstar‖ *
      max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) :=
  last_gradient_bound N hh hL f (gradient f) hf (fun y => (hdiff y).hasGradientAt)
    hLip xstar hmin x hrec

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
  obtain ⟨hr, hQ, hs, _ht⟩ := actual_finite_data N h hL f g hf hg hLip xstar hmin x hrec
  have hp := normalized_progress_joint N hh hbranch
    (fun i => x i - xstar) (fun i => L⁻¹ • g (x i))
    (fun i => (f (x i) - f xstar) / L) hr hQ hs
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), mul_pow] at hp
  convert hp using 1; ring

end Gradient

/-- Explicit Euclidean specialization; the norm is the Euclidean Hilbert norm. -/
theorem euclidean_last_gradient_bound (d N : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ y, HasGradientAt f (g y) y)
    (hLip : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖)
    (xstar : EuclideanSpace ℝ (Fin d)) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (hrec : ∀ i < N, x (i + 1) = x i - (h / L) • g (x i)) :
    ‖g (x N)‖ ≤ L * ‖x 0 - xstar‖ *
      max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) :=
  last_gradient_bound N hh hL f g hf hg hLip xstar hmin x hrec

section Proximal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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
  obtain ⟨hQ, hs, ht, hr⟩ := proximal_finite_data N hF hlam xstar hxstar hmin x z hz hprox hrec
  exact normalized_bound N hh (fun i => x i - xstar) (fun i => x i - z i)
    (proximalDataValue lam F xstar x z) hr hQ hs ht

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
  obtain ⟨hQ, hs, _ht, hr⟩ := proximal_finite_data N hF hlam xstar hxstar hmin x z hz hprox hrec
  have hj := normalized_progress_joint N hh hbranch
    (fun i => x i - xstar) (fun i => x i - z i)
    (proximalDataValue lam F xstar x z) hr hQ hs
  have hb := proximal_tradeoff_of_joint N hh hlam hF xstar hxstar hmin x z
    (hz N le_rfl) (hprox N le_rfl) hj
  refine ⟨hb, ?_⟩
  have hc := objective_bound_of_tradeoff (show 0 < 1 + (N : ℝ) * h by positivity) hb
  have hd : 0 < 4 * (1 + (N : ℝ) * h) := by positivity
  rw [le_div_iff₀ hd] at hc
  apply (le_div_iff₀ (by positivity : 0 < 4 * lam * (1 + (N : ℝ) * h))).mpr
  nlinarith [hc]

end Proximal
end THGGradient
