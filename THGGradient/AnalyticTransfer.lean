module
public import THGGradient.Interpolation
public import THGGradient.FactorIdentity

/-! Transfer from the proved finite interpolation bound to actual functions.
The data estimate is an internal interface, discharged by the certificate. -/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace
namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def DataBound (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : ℕ) (h : ℝ) : Prop :=
  ∀ (x g : ℕ → E) (f : ℕ → ℝ),
    (∀ i < N, x (i + 1) = x i - h • g i) →
    (∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j) →
    (∀ i ≤ N, 0 ≤ starQ x g f i) →
    (∀ i ≤ N, 0 ≤ toStarQ g f i) →
    ‖g N‖ ≤ ‖x 0‖ * max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N)

/-- Actual gradients and the minimizer supply every finite-data hypothesis. -/
theorem actual_finite_data (N : ℕ) (h : ℝ) {L : ℝ} (hL : 0 < L)
    (f : E → ℝ) (g : E → E) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (xstar : E) (hmin : ∀ x, f xstar ≤ f x) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - (h / L) • g (x i)) :
    (∀ i < N, x (i + 1) - xstar = (x i - xstar) - h • (L⁻¹ • g (x i))) ∧
    (∀ i ≤ N, ∀ j ≤ N,
      0 ≤ interpolationQ (fun i => x i - xstar) (fun i => L⁻¹ • g (x i))
        (fun i => (f (x i) - f xstar) / L) i j) ∧
    (∀ i ≤ N, 0 ≤ starQ (fun i => x i - xstar) (fun i => L⁻¹ • g (x i))
      (fun i => (f (x i) - f xstar) / L) i) ∧
    (∀ i ≤ N, 0 ≤ toStarQ (fun i => L⁻¹ • g (x i))
      (fun i => (f (x i) - f xstar) / L) i) := by
  let X := fun i => x i - xstar
  let G := fun i => L⁻¹ • g (x i)
  let F := fun i => (f (x i) - f xstar) / L
  have hzero := gradient_eq_zero_of_minimizer hg hmin
  have hr : ∀ i < N, X (i + 1) = X i - h • G i := by
    intro i hi
    dsimp [X, G]
    rw [hrec i hi, smul_smul, div_eq_mul_inv]
    abel
  have hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ X G F i j := by
    intro i _ j _
    exact normalizedInterpolation hf hg hL hLip xstar (x i) (x j)
  have hs : ∀ i ≤ N, 0 ≤ starQ X G F i := by
    intro i _
    have hi := normalizedInterpolation hf hg hL hLip xstar xstar (x i)
    simp only [hzero, smul_zero, sub_self, zero_div, zero_sub, zero_sub,
      norm_neg, inner_neg_right, inner_sub_right] at hi
    dsimp [starQ, X, G, F]
    rw [inner_sub_right]
    linarith
  have ht : ∀ i ≤ N, 0 ≤ toStarQ G F i := by
    intro i _
    have hi := normalizedInterpolation hf hg hL hLip xstar (x i) xstar
    simpa [toStarQ, X, G, F, hzero] using hi
  exact ⟨hr, hQ, hs, ht⟩

theorem actual_gradient_of_data_bound (N : ℕ) (h : ℝ)
    (dataBound : DataBound E N h)
    {L : ℝ} (hL : 0 < L) (f : E → ℝ) (g : E → E)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (xstar : E) (hmin : ∀ x, f xstar ≤ f x) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - (h / L) • g (x i)) :
    ‖g (x N)‖ ≤ L * ‖x 0 - xstar‖ *
      max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
  let X := fun i => x i - xstar
  let G := fun i => L⁻¹ • g (x i)
  let F := fun i => (f (x i) - f xstar) / L
  have hzero := gradient_eq_zero_of_minimizer hg hmin
  have hr : ∀ i < N, X (i + 1) = X i - h • G i := by
    intro i hi
    dsimp [X, G]
    rw [hrec i hi, smul_smul, div_eq_mul_inv]
    abel
  have hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ X G F i j := by
    intro i _ j _
    exact normalizedInterpolation hf hg hL hLip xstar (x i) (x j)
  have hs : ∀ i ≤ N, 0 ≤ starQ X G F i := by
    intro i _
    have hi := normalizedInterpolation hf hg hL hLip xstar xstar (x i)
    simp only [hzero, smul_zero, sub_self, zero_div, zero_sub, zero_sub,
      norm_neg, inner_neg_right, inner_sub_right] at hi
    dsimp [starQ, X, G, F]
    rw [inner_sub_right]
    linarith
  have ht : ∀ i ≤ N, 0 ≤ toStarQ G F i := by
    intro i _
    have hi := normalizedInterpolation hf hg hL hLip xstar (x i) xstar
    simpa [toStarQ, X, G, F, hzero] using hi
  have hb := dataBound X G F hr hQ hs ht
  change ‖L⁻¹ • g (x N)‖ ≤ ‖x 0 - xstar‖ * _ at hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at hb
  have hm := mul_le_mul_of_nonneg_left hb hL.le
  calc
    ‖g (x N)‖ = L * (L⁻¹ * ‖g (x N)‖) := by field_simp
    _ ≤ L * (‖x 0 - xstar‖ * max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N)) := hm
    _ = _ := by ring

end THGGradient
