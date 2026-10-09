module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Tactic

/-! # Geometric moments and exact prefix averages -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace THGGradient

def geometricMoment (a : ℝ) (n : ℕ) : ℝ := (a ^ n - 1) / 2

def momentSum (a : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, geometricMoment a (j + 1)

@[simp] theorem geometricMoment_zero (a : ℝ) : geometricMoment a 0 = 0 := by
  simp [geometricMoment]

@[simp] theorem momentSum_zero (a : ℝ) : momentSum a 0 = 0 := by
  simp [momentSum]

theorem momentSum_succ (a : ℝ) (n : ℕ) :
    momentSum a (n + 1) = momentSum a n + geometricMoment a (n + 1) := by
  simp [momentSum, Finset.sum_range_succ]

theorem geometricMoment_pos {a : ℝ} (ha : 1 < a) {n : ℕ} (hn : 0 < n) :
    0 < geometricMoment a n := by
  have hp : 1 < a ^ n := one_lt_pow₀ ha (by omega)
  unfold geometricMoment
  linarith

theorem geometricMoment_strictMono {a : ℝ} (ha : 1 < a) :
    StrictMono (geometricMoment a) := by
  intro m n hmn
  have hp : a ^ m < a ^ n := pow_lt_pow_right₀ ha hmn
  unfold geometricMoment
  linarith

theorem geometricMoment_nonneg {a : ℝ} (ha : 1 < a) (n : ℕ) :
    0 ≤ geometricMoment a n := by
  simpa using (geometricMoment_strictMono ha).monotone (Nat.zero_le n)

theorem momentSum_pos {a : ℝ} (ha : 1 < a) {n : ℕ} (hn : 0 < n) :
    0 < momentSum a n := by
  unfold momentSum
  apply Finset.sum_pos
  · intro i hi
    exact geometricMoment_pos ha (by omega)
  · exact Finset.nonempty_range_iff.mpr (by omega)

/-- Each term in a geometric prefix is strictly smaller than its next endpoint. -/
theorem geometric_sum_lt_last {a : ℝ} (ha : 1 < a) {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ Finset.range n, a ^ i) < (n : ℝ) * a ^ n := by
  calc
    (∑ i ∈ Finset.range n, a ^ i) < ∑ _i ∈ Finset.range n, a ^ n := by
      apply Finset.sum_lt_sum
      · intro i hi
        exact (pow_lt_pow_right₀ ha (Finset.mem_range.mp hi)).le
      · exact ⟨0, Finset.mem_range.mpr hn, pow_lt_pow_right₀ ha hn⟩
    _ = (n : ℝ) * a ^ n := by simp

/-- The quotient `(a^n-1)/n` increases strictly at every positive integer. -/
theorem geometric_quotient_step {a : ℝ} (ha : 1 < a) {n : ℕ} (hn : 0 < n) :
    (n + 1 : ℝ) * (a ^ n - 1) < (n : ℝ) * (a ^ (n + 1) - 1) := by
  have hs := geometric_sum_lt_last ha hn
  have hmul := mul_lt_mul_of_pos_right hs (show 0 < a - 1 by linarith)
  rw [geom_sum_mul] at hmul
  rw [pow_succ]
  nlinarith

theorem geometricMoment_ratio_strictMono {a : ℝ} (ha : 1 < a) :
    StrictMono (fun n : ℕ => geometricMoment a (n + 1) / (n + 1 : ℝ)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs := geometric_quotient_step ha (Nat.succ_pos n)
  have hd : (0 : ℝ) < n + 1 := by positivity
  have hd' : (0 : ℝ) < n + 1 + 1 := by positivity
  push_cast
  rw [div_lt_div_iff₀ hd hd']
  simp only [geometricMoment]
  simp only [Nat.succ_eq_add_one] at hs
  push_cast at hs ⊢
  nlinarith

theorem geometricMoment_ratio_lt {a : ℝ} (ha : 1 < a) {j k : ℕ}
    (hj : 0 < j) (hjk : j < k) :
    (k : ℝ) * geometricMoment a j < (j : ℝ) * geometricMoment a k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hh := geometricMoment_ratio_strictMono ha (show i < l by omega)
  have hi : (0 : ℝ) < i + 1 := by positivity
  have hl : (0 : ℝ) < l + 1 := by positivity
  rw [div_lt_div_iff₀ hi hl] at hh
  simpa [mul_comm] using hh

/-- A weighted prefix average lies strictly below the following moment ratio. -/
theorem momentSum_lt_next {a : ℝ} (ha : 1 < a) {n : ℕ} (hn : 0 < n) :
    2 * momentSum a n < (n : ℝ) * geometricMoment a (n + 1) := by
  have hs : (∑ i ∈ Finset.range n, (n + 1 : ℝ) * geometricMoment a (i + 1)) <
      ∑ i ∈ Finset.range n, (i + 1 : ℝ) * geometricMoment a (n + 1) := by
    apply Finset.sum_lt_sum
    · intro i hi
      have hi' : i + 1 < n + 1 := by have := Finset.mem_range.mp hi; omega
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        (geometricMoment_ratio_lt ha (Nat.succ_pos i) hi').le
    · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
      simpa using geometricMoment_ratio_lt ha (by omega : 0 < 1) (by omega : 1 < n + 1)
  have hsum : (∑ i ∈ Finset.range n, (i + 1 : ℝ)) = (n : ℝ) * (n + 1) / 2 := by
    clear hn hs
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [← Finset.mul_sum, ← Finset.sum_mul, hsum] at hs
  change (n + 1 : ℝ) * momentSum a n < _ at hs
  have hd : (0 : ℝ) < n + 1 := by positivity
  nlinarith

/-- Twice the moment sum divided by the triangular-index denominator. -/
def momentAverage (a : ℝ) (n : ℕ) : ℝ :=
  2 * momentSum a n / ((n : ℝ) * (n + 1))

theorem momentAverage_strictMono {a : ℝ} (ha : 1 < a) :
    StrictMono (fun n : ℕ => momentAverage a (n + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hh := momentSum_lt_next ha (Nat.succ_pos n)
  unfold momentAverage
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  rw [momentSum_succ a (n + 1)]
  simp only [Nat.succ_eq_add_one] at hh
  push_cast at hh ⊢
  have hp := mul_lt_mul_of_pos_left hh (show (0 : ℝ) < 2 * (n + 1 + 1) by positivity)
  nlinarith

theorem momentAverage_lt {a : ℝ} (ha : 1 < a) {j k : ℕ}
    (hj : 0 < j) (hjk : j < k) : momentAverage a j < momentAverage a k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact momentAverage_strictMono ha (by omega)

/-- Closed geometric sum; this identity does not require a sign hypothesis. -/
theorem momentSum_identity (a : ℝ) (n : ℕ) :
    2 * (a - 1) * momentSum a n = a * (a ^ n - 1) - (n : ℝ) * (a - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [momentSum_succ]
    simp only [geometricMoment, pow_succ]
    push_cast
    nlinarith

end THGGradient
