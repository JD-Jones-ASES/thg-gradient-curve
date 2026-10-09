module

public import THGGradient.FreeFactors
public import THGGradient.UniformConstruction

/-! Prefix cuts convert the scalar factor construction into uniform divergence. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Finset
namespace THGGradient

/-- The internal contributions of a prefix cancel, leaving only its outgoing cut. -/
theorem divergence_prefix_cut (N k : ℕ) (hk : k ≤ N) (w : ℕ → ℕ → ℝ) :
    (∑ i ∈ range (k + 1), weightDivergence N w i) =
      ∑ j ∈ Ico (k + 1) (N + 1), ∑ i ∈ range (k + 1), (w i j - w j i) := by
  have hrow (i : ℕ) : weightDivergence N w i =
      (∑ j ∈ range (k + 1), (w i j - w j i)) +
      ∑ j ∈ Ico (k + 1) (N + 1), (w i j - w j i) := by
    exact (sum_range_add_sum_Ico _ (by omega : k + 1 ≤ N + 1)).symm
  simp_rw [hrow]
  rw [sum_add_distrib]
  have hin : (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), (w i j - w j i)) = 0 :=
    sum_weightDivergence k w
  rw [hin, zero_add, sum_comm]

/-- Free-factor prefix divergence is a bilinear expression in the two tails. -/
theorem factor_prefix_divergence (N k : ℕ) (hk : k < N) (h : ℝ) (U D : ℕ → ℝ)
    (hU : U 0 = 0) (hD : D (N + 1) = 0) :
    (∑ i ∈ range (k + 1), weightDivergence N (factorWeight h U D) i) =
      (2 - h) * (U (k + 1) * D (k + 1)) +
      h * (U (k + 1) * (∑ j ∈ Ico (k + 2) (N + 1), D j) -
        D (k + 1) * (∑ i ∈ range k, U (i + 1))) := by
  rw [divergence_prefix_cut N k (by omega)]
  have hUsum : (∑ i ∈ range (k + 1), (U i + (h - 1) * U (i + 1))) =
      h * (∑ i ∈ range k, U (i + 1)) + (h - 1) * U (k + 1) := by
    rw [sum_add_distrib, ← mul_sum, sum_range_succ' U k,
      sum_range_succ (fun i => U (i + 1)), hU]
    ring
  have hcol (j : ℕ) (hj : j ∈ Ico (k + 1) (N + 1)) :
      (∑ i ∈ range (k + 1), (factorWeight h U D i j - factorWeight h U D j i)) =
        U (k + 1) * (D j + (h - 1) * D (j + 1)) -
          (h * (∑ i ∈ range k, U (i + 1)) + (h - 1) * U (k + 1)) *
            (D j - D (j + 1)) := by
    rw [sum_sub_distrib, factor_prefix h U D hU (k + 1) j (mem_Ico.mp hj).1]
    congr 1
    calc
      _ = ∑ i ∈ range (k + 1), (U i + (h - 1) * U (i + 1)) * (D j - D (j + 1)) := by
        apply sum_congr rfl
        intro i hi
        exact factorWeight_below h U D (by have := mem_range.mp hi; have := mem_Ico.mp hj; omega)
      _ = _ := by rw [← sum_mul, hUsum]
  rw [sum_congr rfl hcol]
  have hDsum : (∑ j ∈ Ico (k + 1) (N + 1), (D j - D (j + 1))) = D (k + 1) := by
    rw [sum_Ico_eq_sub _ (by omega : k + 1 ≤ N + 1), sum_range_sub', sum_range_sub', hD]
    ring
  have htail := sum_Ico_sub_bot D (by omega : k + 1 < N + 1)
  have hDs : (∑ j ∈ Ico (k + 1) (N + 1), (D j + (h - 1) * D (j + 1))) =
      D (k + 1) + h * (∑ j ∈ Ico (k + 2) (N + 1), D j) := by
    have he : (∑ j ∈ Ico (k + 1) (N + 1), (D j + (h - 1) * D (j + 1))) =
        h * (∑ j ∈ Ico (k + 1) (N + 1), D j) -
        (h - 1) * (∑ j ∈ Ico (k + 1) (N + 1), (D j - D (j + 1))) := by
      simp only [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      ring
    rw [he, hDsum]
    have ht : (∑ j ∈ Ico (k + 1) (N + 1), D j) =
        D (k + 1) + ∑ j ∈ Ico (k + 2) (N + 1), D j := by
      change (∑ j ∈ Ico (k + 1) (N + 1), D j) - D (k + 1) =
        ∑ j ∈ Ico (k + 2) (N + 1), D j at htail
      linarith
    rw [ht]
    ring
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hDs, hDsum]
  ring

/-- Constant linear prefix sums characterize a uniform divergence on the nonterminal data. -/
theorem uniform_divergence_of_prefix (N : ℕ) (δ : ℝ) (w : ℕ → ℕ → ℝ)
    (hp : ∀ k < N, (∑ i ∈ range (k + 1), weightDivergence N w i) = (k + 1 : ℝ) * δ) :
    ∀ i < N, weightDivergence N w i = δ := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simpa using hp 0 hi
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0.ne'
    have hprev := hp k (by omega)
    have hnext := hp (k + 1) hi
    rw [sum_range_succ] at hnext
    push_cast at hnext hprev
    linarith

/-- Explicit directed weights from the universally admissible scalar factors. -/
def uniformWeight (N : ℕ) (h : ℝ) : ℕ → ℕ → ℝ :=
  factorWeight h (uniformU N h) (uniformD N h)

/-- The constructed multipliers have exactly one common nonterminal divergence. -/
theorem uniformWeight_divergence {N : ℕ} {h : ℝ} (h1 : 1 < h) (h2 : h < 2) :
    ∀ i < N, weightDivergence N (uniformWeight N h) i = uniformDelta N h := by
  apply uniform_divergence_of_prefix
  intro k hk
  rw [uniformWeight, factor_prefix_divergence N k hk h (uniformU N h) (uniformD N h)
    (uniformU_zero N h) (uniformD_terminal N h),
    uniform_product_all (by omega : k + 1 ≤ N) h1 h2]
  simpa only [mul_comm] using uniform_prefix_cut hk h1 h2

/-- Every off-diagonal constructed multiplier is strictly positive. -/
theorem uniformWeight_pos {N : ℕ} {h : ℝ} (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h)
    (i : ℕ) (hi : i ≤ N) (j : ℕ) (hj : j ≤ N) (hne : i ≠ j) :
    0 < uniformWeight N h i j := by
  have hr : 0 < h - 1 := by linarith
  rcases lt_or_gt_of_ne hne with hij | hji
  · rw [uniformWeight, factorWeight_above h _ _ hij]
    apply mul_pos (sub_pos.mpr (uniformU_strict_step (by omega) h1 h2 hupper))
    exact add_pos_of_pos_of_nonneg (uniformD_pos (by omega) hj h1 h2)
      (mul_nonneg hr.le (uniformD_nonneg h1 h2))
  · rw [uniformWeight, factorWeight_below h _ _ hji]
    apply mul_pos _ (sub_pos.mpr (uniformD_strict_step (by omega) hi h1 h2 hupper))
    exact add_pos_of_nonneg_of_pos (uniformU_nonneg hj h1 h2)
      (mul_pos hr (uniformU_pos (by omega) h1 h2))

theorem uniformWeight_nonneg {N : ℕ} {h : ℝ} (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) :
    ∀ i ≤ N, ∀ j ≤ N, 0 ≤ uniformWeight N h i j := by
  intro i hi j hj
  by_cases hij : i = j
  · subst j
    simp [uniformWeight]
  · exact (uniformWeight_pos h1 h2 hupper i hi j hj hij).le

end THGGradient
