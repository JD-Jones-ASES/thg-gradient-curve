module
public import THGGradient.UpperBranch
public import THGGradient.EqualityData

/-! Rigidity extraction from nonnegative certificate remainders. -/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace
open Finset
namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem interpolationQ_self (x g : ℕ → E) (f : ℕ → ℝ) (i : ℕ) :
    interpolationQ x g f i i = 0 := by simp [interpolationQ]

/-- A zero weighted history sum with positive off-diagonal weights makes all history remainders zero. -/
theorem weighted_zero_history (N : ℕ) (w : ℕ → ℕ → ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hw : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ w i j)
    (hwpos : ∀ i ≤ N, ∀ j ≤ N, i ≠ j → 0 < w i j)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hW : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      w i j * interpolationQ x g f i j) = 0) :
    ∀ i ≤ N, ∀ j ≤ N, interpolationQ x g f i j = 0 := by
  intro i hi j hj
  by_cases hij : i = j
  · subst j
    exact interpolationQ_self x g f i
  have hn (i : ℕ) (hi : i ∈ range (N + 1)) (j : ℕ) (hj : j ∈ range (N + 1)) :
      0 ≤ w i j * interpolationQ x g f i j :=
    mul_nonneg (hw i (by simpa using hi) j (by simpa using hj))
      (hQ i (by simpa using hi) j (by simpa using hj))
  have hrow : (∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j) = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun k hk => sum_nonneg (hn k hk))).mp hW i (by simpa)
  have hterm := (sum_eq_zero_iff_of_nonneg (hn i (by simpa))).mp hrow j (by simpa)
  exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hwpos i hi j hj hij))

/-- The full history surplus under objective scaling. -/
theorem weighted_interpolation_scale (N : ℕ) (w : ℕ → ℕ → ℝ) (s : ℝ)
    (x g : ℕ → E) (f : ℕ → ℝ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      w i j * interpolationQ x (fun k => s • g k) (fun k => s * f k) i j) =
    s * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j)
      + s * (1 - s) * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        w i j * ‖g i - g j‖ ^ 2) := by
  simp only [interpolationQ_scale, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- Exact deficit identity with every scaled interpolation surplus retained. -/
theorem progress_deficit_identity (N : ℕ) (H h s : ℝ) (hsH : H * s = h)
    (w : ℕ → ℕ → ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hbalanced : ‖x 0‖ ^ 2 - ‖x N‖ ^ 2 - 2 * N * H * (s * f N)
      - N * H * (1 + N * H) * ‖s • g N‖ ^ 2 =
      (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        w i j * interpolationQ x (fun k => s • g k) (fun k => s * f k) i j)
      + H * ∑ i ∈ range N, starQ x (fun k => s • g k) (fun k => s * f k) i) :
    ‖x 0‖ ^ 2 - (1 + N * h) ^ 2 * ‖g N‖ ^ 2 =
      s * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j)
      + h * (∑ i ∈ range N, starQ x g f i)
      + s * (1 - s) * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        w i j * ‖g i - g j‖ ^ 2)
      + h * (1 - s) * (∑ i ∈ range N, (‖g i‖ ^ 2 - ‖g N‖ ^ 2))
      + starQ x g f N + (1 + N * h) * toStarQ g f N + ‖x N - g N‖ ^ 2 := by
  rw [weighted_interpolation_scale] at hbalanced
  have hstarScale : (∑ i ∈ range N,
      starQ x (fun k => s • g k) (fun k => s * f k) i) =
      s * (∑ i ∈ range N, starQ x g f i) + s * (1 - s) * ∑ i ∈ range N, ‖g i‖ ^ 2 := by
    simp only [starQ_scale, sum_add_distrib, mul_sum]
  rw [hstarScale, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hbalanced
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [← hsH]
  simp only [starQ, toStarQ, norm_sub_sq_real] at hbalanced ⊢
  have hi : ⟪g N, x N⟫_ℝ = ⟪x N, g N⟫_ℝ := real_inner_comm _ _
  nlinarith

/-- Strict scaling turns equality into a constant gradient history. -/
theorem progress_equality_remainders (N : ℕ) {h s : ℝ} (hh : 0 < h)
    (hs : 0 < s) (hs1 : s < 1)
    (w : ℕ → ℕ → ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i)
    (hto : ∀ i ≤ N, 0 ≤ toStarQ g f i)
    (hw : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ w i j)
    (hwpos : ∀ i ≤ N, ∀ j ≤ N, i ≠ j → 0 < w i j)
    (hmono : ∀ i < N, ‖g N‖ ^ 2 ≤ ‖g i‖ ^ 2)
    (hdef : ‖x 0‖ ^ 2 - (1 + N * h) ^ 2 * ‖g N‖ ^ 2 =
      s * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j)
      + h * (∑ i ∈ range N, starQ x g f i)
      + s * (1 - s) * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        w i j * ‖g i - g j‖ ^ 2)
      + h * (1 - s) * (∑ i ∈ range N, (‖g i‖ ^ 2 - ‖g N‖ ^ 2))
      + starQ x g f N + (1 + N * h) * toStarQ g f N + ‖x N - g N‖ ^ 2)
    (heq : ‖x 0‖ ^ 2 = (1 + N * h) ^ 2 * ‖g N‖ ^ 2) :
    x N = g N ∧ (∀ i ≤ N, starQ x g f i = 0) ∧ (∀ i ≤ N, g i = g N) := by
  have hWn := mul_nonneg hs.le (weighted_interpolation_nonneg N w x g f hw hQ)
  have hsn : 0 ≤ ∑ i ∈ range N, starQ x g f i :=
    sum_nonneg (fun i hi => hstar i (by have := mem_range.mp hi; omega))
  have hsd : 0 ≤ h * ∑ i ∈ range N, starQ x g f i := mul_nonneg hh.le hsn
  have hn (i : ℕ) (hi : i ∈ range (N + 1)) (j : ℕ) (hj : j ∈ range (N + 1)) :
      0 ≤ w i j * ‖g i - g j‖ ^ 2 :=
    mul_nonneg (hw i (by simpa using hi) j (by simpa using hj)) (sq_nonneg _)
  have hdiff : 0 ≤ ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), w i j * ‖g i - g j‖ ^ 2 :=
    sum_nonneg (fun i hi => sum_nonneg (hn i hi))
  have hss : 0 < s * (1 - s) := mul_pos hs (sub_pos.mpr hs1)
  have hdn := mul_nonneg hss.le hdiff
  have hmonosum : 0 ≤ ∑ i ∈ range N, (‖g i‖ ^ 2 - ‖g N‖ ^ 2) :=
    sum_nonneg (fun i hi => sub_nonneg.mpr (hmono i (mem_range.mp hi)))
  have hmn := mul_nonneg (mul_nonneg hh.le (sub_nonneg.mpr hs1.le)) hmonosum
  have hT : 0 ≤ 1 + (N : ℝ) * h := by positivity
  have ht := mul_nonneg hT (hto N le_rfl)
  have hNz := hstar N le_rfl
  have hnorm := sq_nonneg ‖x N - g N‖
  have hres : x N = g N := by
    have hz : ‖x N - g N‖ = 0 := by nlinarith [norm_nonneg (x N - g N)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hs0 : (∑ i ∈ range N, starQ x g f i) = 0 := by nlinarith
  have hNz0 : starQ x g f N = 0 := by nlinarith
  have hdiff0 : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), w i j * ‖g i - g j‖ ^ 2) = 0 := by
    nlinarith
  refine ⟨hres, ?_, ?_⟩
  · intro i hi
    by_cases hiN : i = N
    · simpa [hiN] using hNz0
    exact (sum_eq_zero_iff_of_nonneg
      (fun i hi => hstar i (by have := mem_range.mp hi; omega))).mp hs0 i (by simp; omega)
  · intro i hi
    by_cases hiN : i = N
    · simp [hiN]
    have hrow := (sum_eq_zero_iff_of_nonneg (fun k hk => sum_nonneg (hn k hk))).mp
      hdiff0 i (by simpa)
    have hterm := (sum_eq_zero_iff_of_nonneg (hn i (by simpa))).mp hrow N (by simp)
    have hz := (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hwpos i hi N le_rfl hiN))
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (g i - g N)]))

/-- Equality in an upper certificate forces the terminal square, all starred
remainders, and every history remainder to vanish. -/
theorem upper_equality_remainders (N : ℕ) {h t : ℝ} (hh : 0 < h)
    (w : ℕ → ℕ → ℝ) (d f : ℕ → ℝ) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i)
    (hto : ∀ i ≤ N, 0 ≤ toStarQ g f i)
    (hw : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ w i j)
    (hwpos : ∀ i ≤ N, ∀ j ≤ N, i ≠ j → 0 < w i j)
    (hdiv : ∀ i < N, d i ≤ h) (hsum : -1 ≤ ∑ i ∈ range N, d i)
    (hW : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j) =
      (∑ i ∈ range N, 2 * d i *
        ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2)))
      + (1 - (h - 1) ^ 2) * (∑ i ∈ range N, ‖g i‖ ^ 2)
      - (t ^ 2 - 1) * ‖g N‖ ^ 2)
    (heq : ‖x 0‖ ^ 2 = t ^ 2 * ‖g N‖ ^ 2) :
    x N = g N ∧ (∀ i ≤ N, starQ x g f i = 0) ∧
      (∀ i ≤ N, ∀ j ≤ N, interpolationQ x g f i j = 0) ∧
      (∀ i < N, d i < h → toStarQ g f i = 0) := by
  have hc := certificate_completion N h t _ d f x g hx hW
  have hWn := weighted_interpolation_nonneg N w x g f hw hQ
  have hsn : 0 ≤ ∑ i ∈ range N, starQ x g f i :=
    sum_nonneg (fun i hi => hstar i (by have := mem_range.mp hi; omega))
  have hsd : 0 ≤ h * ∑ i ∈ range N, starQ x g f i := mul_nonneg hh.le hsn
  have htn : 0 ≤ ∑ i ∈ range N, (h - d i) * toStarQ g f i := by
    apply sum_nonneg
    intro i hi
    exact mul_nonneg (sub_nonneg.mpr (hdiv i (mem_range.mp hi)))
      (hto i (by have := mem_range.mp hi; omega))
  have hNt : 0 ≤ (1 + ∑ i ∈ range N, d i) * toStarQ g f N :=
    mul_nonneg (by linarith) (hto N le_rfl)
  have hNz := hstar N le_rfl
  have hnorm := sq_nonneg ‖x N - g N‖
  have hres : x N = g N := by
    have hs : ‖x N - g N‖ = 0 := by nlinarith [norm_nonneg (x N - g N)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hs)
  have hs0 : (∑ i ∈ range N, starQ x g f i) = 0 := by nlinarith
  have hNz0 : starQ x g f N = 0 := by nlinarith
  have hW0 : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      w i j * interpolationQ x g f i j) = 0 := by nlinarith
  have ht0 : (∑ i ∈ range N, (h - d i) * toStarQ g f i) = 0 := by nlinarith
  refine ⟨hres, ?_, weighted_zero_history N w x g f hw hwpos hQ hW0, ?_⟩
  · intro i hi
    by_cases hiN : i = N
    · simpa [hiN] using hNz0
    exact (sum_eq_zero_iff_of_nonneg
      (fun i hi => hstar i (by have := mem_range.mp hi; omega))).mp hs0 i (by simp; omega)
  · intro i hi hstrict
    have hz := (sum_eq_zero_iff_of_nonneg (fun j hj =>
      mul_nonneg (sub_nonneg.mpr (hdiv j (mem_range.mp hj)))
        (hto j (by have := mem_range.mp hj; omega)))).mp ht0 i (mem_range.mpr hi)
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr hstrict))

end THGGradient
