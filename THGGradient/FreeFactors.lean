module

public import THGGradient.FactorIdentity

/-! Free-factor mixed cancellation and exact diagonal coefficients.
These identities require no positivity or root construction. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Finset

namespace THGGradient

/-- The two directed triangular factor weights; the diagonal is zero. -/
def factorWeight (h : ℝ) (U D : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i < j then (U (i + 1) - U i) * (D j + (h - 1) * D (j + 1))
  else if j < i then (U j + (h - 1) * U (j + 1)) * (D i - D (i + 1))
  else 0

@[simp] theorem factorWeight_self (h : ℝ) (U D : ℕ → ℝ) (i : ℕ) :
    factorWeight h U D i i = 0 := by simp [factorWeight]

theorem factorWeight_above (h : ℝ) (U D : ℕ → ℝ) {i j : ℕ} (hij : i < j) :
    factorWeight h U D i j = (U (i + 1) - U i) * (D j + (h - 1) * D (j + 1)) := by
  simp only [factorWeight, ite_eq_left hij]

theorem factorWeight_below (h : ℝ) (U D : ℕ → ℝ) {i j : ℕ} (hji : j < i) :
    factorWeight h U D i j = (U j + (h - 1) * U (j + 1)) * (D i - D (i + 1)) := by
  simp only [factorWeight, ite_eq_right (by omega : ¬i < j), ite_eq_left hji]

/-- Incoming upper-triangular weights telescope in their first factor. -/
theorem factor_prefix (h : ℝ) (U D : ℕ → ℝ) (hU : U 0 = 0)
    (m b : ℕ) (hmb : m ≤ b) :
    (∑ k ∈ range m, factorWeight h U D k b) =
      U m * (D b + (h - 1) * D (b + 1)) := by
  calc
    _ = ∑ k ∈ range m, (U (k + 1) - U k) * (D b + (h - 1) * D (b + 1)) := by
      apply sum_congr rfl
      intro k hk
      exact factorWeight_above h U D (by have := mem_range.mp hk; omega)
    _ = _ := by rw [← sum_mul, sum_range_sub, hU, sub_zero]

/-- Incoming lower-triangular weights telescope in their second factor. -/
theorem factor_suffix_Ico (N : ℕ) (h : ℝ) (U D : ℕ → ℝ)
    (hD : D (N + 1) = 0) (a m : ℕ) (ham : a < m) (hm : m ≤ N + 1) :
    (∑ k ∈ Ico m (N + 1), factorWeight h U D k a) =
      (U a + (h - 1) * U (a + 1)) * D m := by
  calc
    _ = ∑ k ∈ Ico m (N + 1), (U a + (h - 1) * U (a + 1)) * (D k - D (k + 1)) := by
      apply sum_congr rfl
      intro k hk
      exact factorWeight_below h U D (by have := mem_Ico.mp hk; omega)
    _ = _ := by
      rw [← mul_sum, sum_Ico_eq_sub _ hm, sum_range_sub', sum_range_sub', hD]
      ring

/-- Filtered suffix form, used in the trajectory's coefficient matrix. -/
theorem factor_suffix (N : ℕ) (h : ℝ) (U D : ℕ → ℝ)
    (hD : D (N + 1) = 0) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    (∑ k ∈ range (N + 1), if b < k then factorWeight h U D k a else 0) =
      (U a + (h - 1) * U (a + 1)) * D (b + 1) := by
  rw [← sum_filter]
  have he : (range (N + 1)).filter (fun k => b < k) = Ico (b + 1) (N + 1) := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [he]
  exact factor_suffix_Ico N h U D hD a (b + 1) (by omega) (by omega)

/-- The coefficient above the diagonal is a single terminal suffix. -/
theorem factor_coefficient_above (N : ℕ) (h : ℝ) (U D : ℕ → ℝ)
    (hD : D (N + 1) = 0) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ N) :
    gradientCoefficient N h (factorWeight h U D) i j = factorWeight h U D i j +
      h * ((U i + (h - 1) * U (i + 1)) * D (j + 1)) := by
  rw [gradientCoefficient]
  simp only [ite_eq_right (by omega : ¬j < i), sub_zero, mul_ite, mul_one, mul_zero]
  rw [factor_suffix N h U D hD i j hij hj]

/-- The coefficient below the diagonal is a single initial prefix. -/
theorem factor_coefficient_below (N : ℕ) (h : ℝ) (U D : ℕ → ℝ)
    (hU : U 0 = 0) (i j : ℕ) (hji : j < i) (hi : i ≤ N) :
    gradientCoefficient N h (factorWeight h U D) i j = factorWeight h U D i j -
      h * (U (j + 1) * (D i + (h - 1) * D (i + 1))) := by
  rw [gradientCoefficient, ite_eq_left hji]
  have hs : (∑ k ∈ range (N + 1), factorWeight h U D k i *
      ((if j < k then (1 : ℝ) else 0) - 1)) =
      -(∑ k ∈ range (j + 1), factorWeight h U D k i) := by
    calc
      _ = -(∑ k ∈ range (N + 1), if k ≤ j then factorWeight h U D k i else 0) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro k _
        by_cases hk : j < k
        · simp [hk, not_le.mpr hk]
        · simp [hk, le_of_not_gt hk]
      _ = _ := by
        rw [← sum_filter]
        congr 2
        ext k
        simp only [mem_filter, mem_range]
        omega
  rw [hs, factor_prefix h U D hU (j + 1) i (by omega)]
  ring

/-- Every off-diagonal inner-product coefficient cancels, for arbitrary free factors. -/
theorem factor_mixed_cancellation (N : ℕ) (h : ℝ) (U D : ℕ → ℝ)
    (hU : U 0 = 0) (hD : D (N + 1) = 0)
    (i : ℕ) (hi : i ≤ N) (j : ℕ) (hj : j ≤ N) (hne : i ≠ j) :
    gradientCoefficient N h (factorWeight h U D) i j +
      gradientCoefficient N h (factorWeight h U D) j i = 0 := by
  wlog hij : i < j generalizing i j
  · rw [add_comm]
    exact this j hj i hi hne.symm (by omega)
  rw [factor_coefficient_above N h U D hD i j (by omega) hj,
    factor_coefficient_below N h U D hU j i hij hj,
    factorWeight_above h U D hij, factorWeight_below h U D hij]
  ring

/-- Full incoming mass is the sum of its telescoped prefix and suffix. -/
theorem factor_incoming_sum (N : ℕ) (h : ℝ) (U D : ℕ → ℝ)
    (hU : U 0 = 0) (hD : D (N + 1) = 0) (i : ℕ) (hi : i ≤ N) :
    (∑ j ∈ range (N + 1), factorWeight h U D j i) =
      U i * (D i + (h - 1) * D (i + 1)) +
        (U i + (h - 1) * U (i + 1)) * D (i + 1) := by
  rw [← sum_range_add_sum_Ico (fun j => factorWeight h U D j i)
    (show i + 1 ≤ N + 1 by omega), sum_range_succ, factorWeight_self, add_zero,
    factor_prefix h U D hU i i le_rfl,
    factor_suffix_Ico N h U D hD i (i + 1) (by omega) (by omega)]

/-- The diagonal identity before imposing the prescribed product recurrence. -/
theorem factor_diagonal_identity (N : ℕ) (h : ℝ) (U D : ℕ → ℝ)
    (hU : U 0 = 0) (hD : D (N + 1) = 0) (i : ℕ) (hi : i ≤ N) :
    2 * gradientCoefficient N h (factorWeight h U D) i i -
      (∑ j ∈ range (N + 1), (factorWeight h U D i j + factorWeight h U D j i)) =
        -weightDivergence N (factorWeight h U D) i +
          2 * ((h - 1) ^ 2 * U (i + 1) * D (i + 1) - U i * D i) := by
  rw [factor_coefficient_above N h U D hD i i le_rfl hi,
    factorWeight_self, zero_add]
  simp only [weightDivergence, sum_add_distrib, sum_sub_distrib]
  rw [factor_incoming_sum N h U D hU hD i hi]
  ring

/-- The product recurrence and terminal product fix all diagonal coefficients. -/
theorem factor_diagonal_completion (N : ℕ) (h t : ℝ) (U D : ℕ → ℝ)
    (hU : U 0 = 0) (hD : D (N + 1) = 0)
    (hp : ∀ i < N, 2 * ((h - 1) ^ 2 * U (i + 1) * D (i + 1) - U i * D i) =
      1 - (h - 1) ^ 2)
    (hterminal : 2 * U N * D N = t ^ 2 - 1) (i : ℕ) (hi : i ≤ N) :
    2 * gradientCoefficient N h (factorWeight h U D) i i -
      (∑ j ∈ range (N + 1), (factorWeight h U D i j + factorWeight h U D j i)) =
        -weightDivergence N (factorWeight h U D) i +
          if i < N then 1 - (h - 1) ^ 2 else -(t ^ 2 - 1) := by
  rw [factor_diagonal_identity N h U D hU hD i hi]
  by_cases hiN : i < N
  · rw [ite_eq_left hiN, hp i hiN]
  · have hiN' : i = N := by omega
    subst i
    rw [ite_eq_right (by omega : ¬N < N), hD]
    nlinarith [hterminal]

end THGGradient
