module

public import THGGradient.UniformFactors

/-! # Positive factors with uniform prefix divergence -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace THGGradient

/-- Shifted increasing factor: `U 0 = 0` and `U 1 = 1`. -/
def uniformU (N : ℕ) (h : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | k + 2 => uniformU N h (k + 1) * (1 + uniformRoot h (uniformDelta N h) k) /
      uniformRoot h (uniformDelta N h) (k + 1)

/-- Decreasing factor with an explicit zero at the terminal sentinel. -/
def uniformD (N : ℕ) (h : ℝ) (k : ℕ) : ℝ :=
  if k ≤ N then uniformMoment h k / uniformU N h k else 0

/-- The normalized tail variable. -/
def uniformV (N : ℕ) (h : ℝ) (k : ℕ) : ℝ :=
  uniformRoot h (uniformDelta N h) k + uniformW h (uniformDelta N h) k

@[simp] theorem uniformU_zero (N : ℕ) (h : ℝ) : uniformU N h 0 = 0 := rfl
@[simp] theorem uniformU_one (N : ℕ) (h : ℝ) : uniformU N h 1 = 1 := rfl

@[simp] theorem uniformD_terminal (N : ℕ) (h : ℝ) : uniformD N h (N + 1) = 0 := by
  simp [uniformD]

theorem uniformU_pos {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) : 0 < uniformU N h (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hu := uniformRoot_nonneg (show k < N by omega) h1 h2 (le_refl (uniformDelta N h))
    have hu' := uniformRoot_pos (show 0 < k + 1 by omega) (show k + 1 < N by omega)
      h1 h2 (le_refl (uniformDelta N h))
    rw [show k + 1 + 1 = k + 2 by omega, uniformU]
    exact div_pos (mul_pos (ih (by omega)) (by linarith)) hu'

theorem uniformU_recurrence {N k : ℕ} (hkN : k + 1 < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) :
    uniformU N h (k + 2) * uniformRoot h (uniformDelta N h) (k + 1) =
      uniformU N h (k + 1) * (1 + uniformRoot h (uniformDelta N h) k) := by
  have hu' := uniformRoot_pos (show 0 < k + 1 by omega) hkN
    h1 h2 (le_refl (uniformDelta N h))
  rw [uniformU, div_mul_cancel₀ _ hu'.ne']

theorem uniformU_strict_step {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) :
    uniformU N h k < uniformU N h (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hu := uniformRoot_nonneg (show j + 1 < N by omega) h1 h2 (le_refl (uniformDelta N h))
  have hc := uniformRoot_comparison (show j + 1 < N by omega) h1 h2 hupper
  have hp := uniformMoment_pos h1 h2 (show 0 < j + 1 by omega)
  have hpp := geometricMoment_strictMono (uniformRatio_gt_one h1 h2) (show j + 1 < j + 2 by omega)
  change uniformMoment h (j + 1) < uniformMoment h (j + 2) at hpp
  have humul := mul_le_mul_of_nonneg_right hpp.le hu
  have hroot : uniformRoot h (uniformDelta N h) (j + 1) <
      1 + uniformRoot h (uniformDelta N h) j := by nlinarith
  have hU := uniformU_pos (show j < N by omega) h1 h2
  have hrec := uniformU_recurrence (show j + 1 < N by omega) h1 h2
  have hmul := mul_lt_mul_of_pos_left hroot hU
  have hrootpos := uniformRoot_pos (show 0 < j + 1 by omega) (show j + 1 < N by omega)
    h1 h2 (le_refl (uniformDelta N h))
  have : uniformU N h (j + 1) < uniformU N h (j + 2) := by nlinarith
  simpa only [Nat.succ_eq_add_one] using this

theorem uniform_product {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) : uniformU N h k * uniformD N h k = uniformMoment h k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hp := uniformU_pos (show j < N by omega) h1 h2
  unfold uniformD
  rw [ite_eq_left hkN]
  exact mul_div_cancel₀ _ hp.ne'

theorem uniformD_pos {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) : 0 < uniformD N h k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  unfold uniformD
  rw [ite_eq_left hkN]
  exact div_pos (uniformMoment_pos h1 h2 (by omega)) (uniformU_pos (by omega) h1 h2)

theorem uniformD_strict_step {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) :
    uniformD N h (k + 1) < uniformD N h k := by
  rcases lt_or_eq_of_le hkN with hlt | rfl
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hU := uniformU_pos (show j < N by omega) h1 h2
    have hU' := uniformU_pos (show j + 1 < N by omega) h1 h2
    have hrec := uniformU_recurrence (show j + 1 < N by omega) h1 h2
    have hcomp := uniformRoot_comparison (show j + 1 < N by omega) h1 h2 hupper
    have hroot := uniformRoot_pos (show 0 < j + 1 by omega) (show j + 1 < N by omega)
      h1 h2 (le_refl (uniformDelta N h))
    have hm := mul_lt_mul_of_pos_right hcomp hU
    have heq := congrArg (fun z : ℝ => uniformMoment h (j + 1) * z) hrec
    have hpcomp : uniformMoment h (j + 2) * uniformU N h (j + 1) <
        uniformMoment h (j + 1) * uniformU N h (j + 2) := by
      nlinarith
    unfold uniformD
    rw [ite_eq_left (by omega : j.succ + 1 ≤ N), ite_eq_left (by omega : j.succ ≤ N)]
    exact (div_lt_div_iff₀ hU' hU).2 hpcomp
  · rw [uniformD_terminal]
    exact uniformD_pos hk le_rfl h1 h2

theorem uniformU_prefix {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) :
    (∑ i ∈ Finset.range k, uniformU N h (i + 1)) =
      uniformU N h (k + 1) * uniformRoot h (uniformDelta N h) k := by
  induction k with
  | zero =>
    simp [uniformRoot_zero h1 h2 (uniformDelta_pos (by omega) h1 h2).le]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hrec := uniformU_recurrence (show k + 1 < N by omega) h1 h2
    simpa only [Nat.succ_eq_add_one] using (by linarith :
      uniformU N h (k + 1) * uniformRoot h (uniformDelta N h) k + uniformU N h (k + 1) =
        uniformU N h (k + 2) * uniformRoot h (uniformDelta N h) (k + 1))

theorem uniformV_root_identity {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) :
    (1 + uniformRoot h (uniformDelta N h) k) * uniformV N h k =
      uniformZ h (uniformDelta N h) k + uniformW h (uniformDelta N h) k := by
  have heq := positiveRoot_equation (B := 1 + uniformW h (uniformDelta N h) k)
    (uniformZ_nonneg hkN h1 h2 (le_refl (uniformDelta N h)))
  change rootPolynomial (1 + uniformW h (uniformDelta N h) k)
    (uniformZ h (uniformDelta N h) k) (uniformRoot h (uniformDelta N h) k) = 0 at heq
  unfold rootPolynomial at heq
  unfold uniformV
  nlinarith

theorem uniformV_terminal {N k : ℕ} (hkN : k + 1 = N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) : uniformV N h k = 0 := by
  have hN : 0 < N := by omega
  have hh : h ≠ 0 := by linarith
  have hp : uniformMoment h (k + 1) ≠ 0 := (uniformMoment_pos h1 h2 (by omega)).ne'
  have hk : k < N := by omega
  have hden : (N : ℝ) * (N + 1) ≠ 0 := by positivity
  have hz : uniformZ h (uniformDelta N h) k + uniformW h (uniformDelta N h) k = 0 := by
    unfold uniformZ uniformW uniformDelta
    have hs : uniformSum h N = uniformSum h k + uniformMoment h (k + 1) := by
      rw [← hkN]
      exact momentSum_succ _ _
    rw [hs, ← hkN]
    push_cast
    field_simp
    ring
  have heq := uniformV_root_identity hk h1 h2
  have hu := uniformRoot_nonneg hk h1 h2 (le_refl (uniformDelta N h))
  rw [hz] at heq
  exact (mul_eq_zero.mp heq).resolve_left (by linarith)

theorem uniformV_nonneg {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) : 0 ≤ uniformV N h k := by
  rcases lt_or_eq_of_le (show k + 1 ≤ N by omega) with hlt | heq
  · have hZ := uniformZ_nonneg hlt h1 h2 (le_refl (uniformDelta N h))
    have hp := uniformMoment_pos h1 h2 (show 0 < k + 1 by omega)
    have hp' := uniformMoment_pos h1 h2 (show 0 < k + 2 by omega)
    have hrec := uniformZ_recurrence h1 h2 (uniformDelta N h) k
    have hz : 0 ≤ uniformZ h (uniformDelta N h) k + uniformW h (uniformDelta N h) k := by
      nlinarith [mul_nonneg hp'.le hZ]
    have hid := uniformV_root_identity hkN h1 h2
    have hu := uniformRoot_nonneg hkN h1 h2 (le_refl (uniformDelta N h))
    nlinarith
  · rw [uniformV_terminal heq h1 h2]

theorem uniformU_nonneg {N k : ℕ} (hkN : k ≤ N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) : 0 ≤ uniformU N h k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact (uniformU_pos (by omega) h1 h2).le

@[simp] theorem uniformD_zero (N : ℕ) (h : ℝ) : uniformD N h 0 = 0 := by
  simp [uniformD, uniformMoment]

theorem uniformD_nonneg {N k : ℕ} {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) : 0 ≤ uniformD N h k := by
  by_cases hkN : k ≤ N
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exact (uniformD_pos hk hkN h1 h2).le
  · simp [uniformD, hkN]

theorem uniform_product_all {N k : ℕ} (hkN : k ≤ N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) : uniformU N h k * uniformD N h k = uniformMoment h k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [uniformMoment]
  · exact uniform_product hk hkN h1 h2

theorem uniformV_root_equation {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) :
    uniformRoot h (uniformDelta N h) k * (1 + uniformV N h k) =
      uniformZ h (uniformDelta N h) k := by
  have heq := positiveRoot_equation (B := 1 + uniformW h (uniformDelta N h) k)
    (uniformZ_nonneg hkN h1 h2 (le_refl (uniformDelta N h)))
  change rootPolynomial (1 + uniformW h (uniformDelta N h) k)
    (uniformZ h (uniformDelta N h) k) (uniformRoot h (uniformDelta N h) k) = 0 at heq
  unfold rootPolynomial at heq
  unfold uniformV
  nlinarith

/-- Backward recurrence of the normalized suffix. -/
theorem uniformD_V_recurrence {N k : ℕ} (hkN : k + 1 < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) :
    uniformD N h (k + 2) * (1 + uniformV N h (k + 1)) =
      uniformD N h (k + 1) * uniformV N h k := by
  have hU := uniformU_pos (show k < N by omega) h1 h2
  have hU' := uniformU_pos hkN h1 h2
  have hu := uniformRoot_pos (show 0 < k + 1 by omega) hkN h1 h2 (le_refl (uniformDelta N h))
  have hrec := uniformZ_recurrence h1 h2 (uniformDelta N h) k
  have heq := uniformV_root_equation hkN h1 h2
  have heq' := uniformV_root_identity (show k < N by omega) h1 h2
  have hUrec := uniformU_recurrence hkN h1 h2
  unfold uniformD
  rw [ite_eq_left (by omega : k + 2 ≤ N), ite_eq_left (by omega : k + 1 ≤ N),
    div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_eq_div_iff hU'.ne' hU.ne').2
  apply mul_right_cancel₀ hu.ne'
  linear_combination uniformU N h (k + 1) * hrec +
    uniformMoment h (k + 2) * uniformU N h (k + 1) * heq -
    uniformMoment h (k + 1) * uniformU N h (k + 1) * heq' -
    uniformMoment h (k + 1) * uniformV N h k * hUrec

/-- Every suffix is represented by the tail variable from the scalar root. -/
theorem uniformD_suffix {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) :
    (∑ j ∈ Finset.Ico (k + 2) (N + 1), uniformD N h j) =
      uniformD N h (k + 1) * uniformV N h k := by
  have hN : 0 < N := by omega
  have hbase : (∑ j ∈ Finset.Ico (N - 1 + 2) (N + 1), uniformD N h j) =
      uniformD N h (N - 1 + 1) * uniformV N h (N - 1) := by
    rw [uniformV_terminal (by omega : N - 1 + 1 = N) h1 h2]
    simp [show N - 1 + 2 = N + 1 by omega]
  apply Nat.decreasingInduction' (n := N - 1) (P := fun k =>
    (∑ j ∈ Finset.Ico (k + 2) (N + 1), uniformD N h j) =
      uniformD N h (k + 1) * uniformV N h k) ?_ (by omega) hbase
  intro j hj _ ih
  have hrec := uniformD_V_recurrence (show j + 1 < N by omega) h1 h2
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : j + 2 < N + 1)]
  rw [show j + 2 + 1 = j + 1 + 2 by omega, ih]
  nlinarith [hrec]

/-- The exact prefix-cut value produced by the factor construction. -/
theorem uniform_prefix_cut {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) :
    (2 - h) * uniformMoment h (k + 1) + h *
      (uniformU N h (k + 1) *
        (∑ j ∈ Finset.Ico (k + 2) (N + 1), uniformD N h j) -
      uniformD N h (k + 1) * (∑ i ∈ Finset.range k, uniformU N h (i + 1))) =
      uniformDelta N h * (k + 1) := by
  rw [uniformD_suffix hkN h1 h2, uniformU_prefix hkN h1 h2]
  have hp := uniform_product (show 0 < k + 1 by omega) (show k + 1 ≤ N by omega) h1 h2
  have hpn : uniformMoment h (k + 1) ≠ 0 := (uniformMoment_pos h1 h2 (by omega)).ne'
  have hh : h ≠ 0 := by linarith
  have hw : h * uniformMoment h (k + 1) * uniformW h (uniformDelta N h) k =
      uniformDelta N h * (k + 1) - (2 - h) * uniformMoment h (k + 1) := by
    unfold uniformW
    field_simp
  unfold uniformV
  linear_combination (h * uniformW h (uniformDelta N h) k) * hp + hw

end THGGradient
