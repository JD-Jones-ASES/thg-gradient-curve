module

public import THGGradient.UniformDivergence
public import THGGradient.UpperBranch
public import THGGradient.RateAssembly

/-! The explicit scalar factors discharge every internal certificate hypothesis.
The final finite-data results here are unconditional in all step regimes. -/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace
open Finset
namespace THGGradient

/-- Product recurrence for the actual constructed factors, including index zero. -/
theorem uniform_product_recurrence {N : ℕ} {h : ℝ} (h1 : 1 < h) (h2 : h < 2)
    (i : ℕ) (hi : i < N) :
    2 * ((h - 1) ^ 2 * uniformU N h (i + 1) * uniformD N h (i + 1) -
      uniformU N h i * uniformD N h i) = 1 - (h - 1) ^ 2 := by
  rw [mul_assoc, uniform_product_all (by omega : i + 1 ≤ N) h1 h2,
    uniform_product_all (by omega : i ≤ N) h1 h2]
  exact uniformMoment_recurrence h1 i

/-- The final product is exactly the squared reciprocal quadratic rate. -/
theorem uniform_product_terminal {N : ℕ} {h : ℝ} (h1 : 1 < h) (h2 : h < 2) :
    2 * uniformU N h N * uniformD N h N = (((h - 1)⁻¹) ^ N) ^ 2 - 1 := by
  rw [mul_assoc, uniform_product_all le_rfl h1 h2]
  simp only [uniformMoment, geometricMoment, uniformRatio, ← pow_mul, Nat.mul_comm]
  ring

theorem uniformWeight_mixed {N : ℕ} {h : ℝ} :
    ∀ i ≤ N, ∀ j ≤ N, i ≠ j →
      gradientCoefficient N h (uniformWeight N h) i j +
        gradientCoefficient N h (uniformWeight N h) j i = 0 :=
  factor_mixed_cancellation N h _ _ (uniformU_zero N h) (uniformD_terminal N h)

theorem uniformWeight_diagonal {N : ℕ} {h : ℝ} (h1 : 1 < h) (h2 : h < 2) :
    ∀ i ≤ N, 2 * gradientCoefficient N h (uniformWeight N h) i i -
      (∑ j ∈ range (N + 1), (uniformWeight N h i j + uniformWeight N h j i)) =
        -weightDivergence N (uniformWeight N h) i +
          if i < N then 1 - (h - 1) ^ 2 else -((((h - 1)⁻¹) ^ N) ^ 2 - 1) :=
  factor_diagonal_completion N h _ _ _ (uniformU_zero N h) (uniformD_terminal N h)
    (uniform_product_recurrence h1 h2) (uniform_product_terminal h1 h2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The entire upper branch follows from the explicitly constructed nonnegative multipliers. -/
theorem normalized_upper (N : ℕ) {h : ℝ} (hN : 0 < N) (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) : UpperDataBound E N h := by
  intro x g f hrec hQ hstar hto
  have ht : 0 < ((h - 1)⁻¹) ^ N := by positivity
  have hb := upper_norm_of_uniform_coefficients N (by linarith : 0 ≤ h) ht
    (uniformDelta_pos hN h1 h2).le (uniformDelta_le_step hN h1 h2 hupper)
    (uniformWeight N h) x g f hrec hQ hstar hto (uniformWeight_nonneg h1 h2 hupper)
    uniformWeight_mixed (uniformWeight_diagonal h1 h2) (uniformWeight_divergence h1 h2)
  simpa only [div_eq_mul_inv, inv_pow, inv_inv] using hb

/-- The genuine balancing step satisfies the retained balanced certificate. -/
theorem normalized_balanced (N : ℕ) (hN : 0 < N) :
    BalancedRetainedCertificate E N (balanceStep N) := by
  have hs := balanceStep_spec hN
  have heq := balanceStep_upper_condition hN
  have hdiag := uniformWeight_diagonal (N := N) hs.1 hs.2.1
  rw [heq] at hdiag
  apply balanced_retained_of_coefficients N (balanceStep N) (uniformWeight N (balanceStep N))
    (uniformWeight_nonneg hs.1 hs.2.1 heq.le) uniformWeight_mixed hdiag
  intro i hi
  rw [uniformWeight_divergence hs.1 hs.2.1 i hi, uniformDelta_eq_step hN hs.1 heq]

/-- Universal normalized interpolation-data bound, with no certificate premises. -/
theorem normalized_bound (N : ℕ) {h : ℝ} (hh : 0 ≤ h) : DataBound E N h :=
  data_bound_of_certificates N hh (fun _ hN h1 h2 hu => normalized_upper N hN h1 h2 hu)
    (normalized_balanced N)

/-- The stronger progress potential, including the zero horizon and zero step. -/
theorem normalized_progress_joint (N : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (hbranch : |1 - h| ^ N ≤ (1 + (N : ℝ) * h)⁻¹)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hrec : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i) :
    ‖x N‖ ^ 2 + 2 * (N : ℝ) * h * f N +
      (N : ℝ) * h * (1 + (N : ℝ) * h) * ‖g N‖ ^ 2 ≤ ‖x 0‖ ^ 2 :=
  progress_joint_of_certificates N hh hbranch (normalized_balanced N) x g f hrec hQ hstar

end THGGradient
