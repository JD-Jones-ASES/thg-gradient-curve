module

public import THGGradient.EqualityAux
public import THGGradient.NormalizedEquality
public import THGGradient.FarEquality

/-! Complete equality classifications for actual normalized smooth convex functions.
Only the trajectory and its sampled values are classified. -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Ordinary normalized smooth convex functions supply every interpolation inequality. -/
theorem normalized_actual_data (N : ℕ) (h : ℝ)
    (f : E → ℝ) (g : E → E) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ y, HasGradientAt f (g y) y)
    (hLip : ∀ y z, ‖g y - g z‖ ≤ ‖y - z‖)
    (hf0 : f 0 = 0) (hmin : ∀ y, f 0 ≤ f y) (x : ℕ → E)
    (hrec : ∀ i < N, x (i + 1) = x i - h • g (x i)) :
    (∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x (fun i => g (x i)) (fun i => f (x i)) i j) ∧
    (∀ i ≤ N, 0 ≤ starQ x (fun i => g (x i)) (fun i => f (x i)) i) ∧
    (∀ i ≤ N, 0 ≤ toStarQ (fun i => g (x i)) (fun i => f (x i)) i) := by
  have hd := actual_finite_data N h (L := 1) zero_lt_one f g hf hg
    (by simpa using hLip) 0 hmin x (by simpa using hrec)
  simpa only [hf0, sub_zero, div_one, inv_one, one_smul] using hd.2

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
  constructor
  · intro heq
    obtain ⟨hQ, hs, ht⟩ := normalized_actual_data N h f g hf hg hLip hf0 hmin x hrec
    exact normalized_progress_equality N hN hh (lt_balance_of_strict_progress hN hh hbranch)
      x (fun i => g (x i)) (fun i => f (x i)) hrec hQ hs ht heq
  · intro hform
    apply progress_formula_attains N hh.le x (fun i => g (x i))
    simpa using (hform 0 (by omega)).2.1

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
  constructor
  · intro heq
    obtain ⟨hQ, hs, ht⟩ := normalized_actual_data N h f g hf hg hLip hf0 hmin x hrec
    obtain ⟨h1, hupper⟩ := upper_guards_of_strict_oscillation hN hh hbranch
    have habs : |1 - h| = h - 1 := by rw [abs_of_nonpos (by linarith)]; ring
    rw [habs] at heq
    by_cases hfar : 2 ≤ h
    · exact far_equality_quadratic N hfar x (fun i => g (x i)) (fun i => f (x i))
        hrec hQ hs ht (by simpa only [mul_comm] using heq)
    · exact normalized_oscillation_equality N hN h1 (lt_of_not_ge hfar) hupper
        x (fun i => g (x i)) (fun i => f (x i)) hrec hQ hs ht heq
  · intro hform
    exact quadratic_formula_attains N h x (fun i => g (x i))
      (hform N le_rfl).1 (hform N le_rfl).2.1

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
  constructor
  · intro heq
    obtain ⟨hQ, hs, ht⟩ := normalized_actual_data N h f g hf hg hLip hf0 hmin x hrec
    have hbal := eq_balance_of_rate_eq hN hh hbranch
    subst h
    exact normalized_balance_equality N hN x (fun i => g (x i)) (fun i => f (x i))
      hrec hQ hs ht heq
  · rintro ⟨a, b, hab, hform⟩
    apply balanced_formula_attains N hh.le hbranch x (fun i => g (x i)) a b hab
    · simpa using (hform 0 (by omega)).2.1
    · exact (hform N le_rfl).1

end THGGradient
