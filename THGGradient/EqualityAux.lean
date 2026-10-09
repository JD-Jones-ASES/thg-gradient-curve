module

public import THGGradient.UniformCertificate

/-! Literal branch comparisons and converse directions for the equality classifications. -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace THGGradient

/-- Every positive step at most one lies strictly in the progress branch. -/
theorem small_step_strict_progress {N : ℕ} (hN : 0 < N) {h : ℝ}
    (hh : 0 < h) (h1 : h ≤ 1) :
    |1 - h| ^ N < (1 + (N : ℝ) * h)⁻¹ := by
  have hD : 0 < 1 + (N : ℝ) * h := by positivity
  rcases lt_or_eq_of_le h1 with hlt | rfl
  · have ha : 0 < 1 - h := by linarith
    have hfrac : h < h / (1 - h) := by
      apply (lt_div_iff₀ ha).mpr
      nlinarith [sq_pos_of_pos hh]
    have hber := one_add_mul_le_pow (show (-2 : ℝ) ≤ h / (1 - h) by have hp := div_pos hh ha; linarith) N
    have hid : 1 + h / (1 - h) = (1 - h)⁻¹ := by field_simp; ring
    rw [hid, inv_pow] at hber
    have hstrict : 1 + (N : ℝ) * h < ((1 - h) ^ N)⁻¹ := by
      have hm := mul_lt_mul_of_pos_left hfrac (Nat.cast_pos.mpr hN : (0 : ℝ) < N)
      linarith
    rw [abs_of_pos ha]
    exact (lt_inv_comm₀ (pow_pos ha _) hD).mpr hstrict
  · simpa [Nat.ne_of_gt hN] using inv_pos.mpr hD

/-- At the balancing step the two literal rates coincide. -/
theorem balanceStep_rate_eq {N : ℕ} (hN : 0 < N) :
    |1 - balanceStep N| ^ N = (1 + (N : ℝ) * balanceStep N)⁻¹ := by
  have hs := balanceStep_spec hN
  have he := congrArg (fun t : ℝ => t⁻¹) (balanceStep_upper_condition hN)
  rw [inv_pow, inv_inv] at he
  rw [abs_of_nonpos (by linarith [hs.1])]
  convert he using 1; ring

/-- A strict literal progress comparison is strictly below the balancing step. -/
theorem lt_balance_of_strict_progress {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (hb : |1 - h| ^ N < (1 + (N : ℝ) * h)⁻¹) : h < balanceStep N := by
  have hl := le_balance_of_progress hN hh.le hb.le
  rcases lt_or_eq_of_le hl with hl | rfl
  · exact hl
  · rw [balanceStep_rate_eq hN] at hb
    exact (lt_irrefl _ hb).elim

/-- A positive literal equality of the two rates identifies the unique balancing step. -/
theorem eq_balance_of_rate_eq {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (hb : |1 - h| ^ N = (1 + (N : ℝ) * h)⁻¹) : h = balanceStep N := by
  have h1 : 1 < h := by
    by_contra hn
    have hs := small_step_strict_progress hN hh (le_of_not_gt hn)
    rw [hb] at hs
    exact lt_irrefl _ hs
  apply balance_unique hN h1.le
  have hD : 0 < 1 + (N : ℝ) * h := by positivity
  unfold balancePolynomial
  rw [abs_of_nonpos (by linarith)] at hb
  have hp : (h - 1) ^ N = (1 + (N : ℝ) * h)⁻¹ := by convert hb using 1; ring
  rw [hp, inv_mul_cancel₀ hD.ne']

/-- A strict oscillation comparison yields the reciprocal-power upper-branch guard. -/
theorem upper_guards_of_strict_oscillation {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (hb : (1 + (N : ℝ) * h)⁻¹ < |1 - h| ^ N) :
    1 < h ∧ ((h - 1)⁻¹) ^ N < 1 + (N : ℝ) * h := by
  have h1 : 1 < h := by
    by_contra hn
    have hs := small_step_strict_progress hN hh (le_of_not_gt hn)
    linarith
  refine ⟨h1, ?_⟩
  have hD : 0 < 1 + (N : ℝ) * h := by positivity
  have hp : 0 < (h - 1) ^ N := pow_pos (by linarith) _
  have habs : |1 - h| = h - 1 := by rw [abs_of_nonpos (by linarith)]; ring
  rw [habs] at hb
  rw [inv_pow]
  exact (inv_lt_comm₀ hD hp).mp hb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The progress trajectory formula itself certifies attainment. -/
theorem progress_formula_attains (N : ℕ) {h : ℝ} (hh : 0 ≤ h) (x g : ℕ → E)
    (hx0 : x 0 = (1 + (N : ℝ) * h) • g N) :
    ‖g N‖ = ‖x 0‖ * (1 + (N : ℝ) * h)⁻¹ := by
  have hD : 0 < 1 + (N : ℝ) * h := by positivity
  rw [hx0, norm_smul, Real.norm_of_nonneg hD.le]
  field_simp

/-- The quadratic trajectory formula itself certifies attainment. -/
theorem quadratic_formula_attains (N : ℕ) (h : ℝ) (x g : ℕ → E)
    (hxN : x N = (1 - h) ^ N • x 0) (hgN : g N = x N) :
    ‖g N‖ = ‖x 0‖ * |1 - h| ^ N := by
  rw [hgN, hxN, norm_smul, norm_pow, Real.norm_eq_abs, mul_comm]

/-- Orthogonal mixtures attain the crossing rate exactly. -/
theorem balanced_formula_attains (N : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (hb : |1 - h| ^ N = (1 + (N : ℝ) * h)⁻¹) (x g : ℕ → E)
    (a b : E) (hab : ⟪a, b⟫_ℝ = 0)
    (hx0 : x 0 = (1 + (N : ℝ) * h) • b + a)
    (hgN : g N = b + (1 - h) ^ N • a) :
    ‖g N‖ = ‖x 0‖ * (1 + (N : ℝ) * h)⁻¹ := by
  have hba : ⟪b, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact hab
  have hD : 0 < 1 + (N : ℝ) * h := by positivity
  have hxsq : ‖x 0‖ ^ 2 = (1 + (N : ℝ) * h) ^ 2 * ‖b‖ ^ 2 + ‖a‖ ^ 2 := by
    rw [hx0, norm_add_sq_real, real_inner_smul_left, hba]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_zero, add_zero]
  have hgsq : ‖g N‖ ^ 2 = ‖b‖ ^ 2 + ((1 - h) ^ N) ^ 2 * ‖a‖ ^ 2 := by
    rw [hgN, norm_add_sq_real, inner_smul_right, hba]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_zero, add_zero]
  have hcoeff : (1 + (N : ℝ) * h) ^ 2 * ((1 - h) ^ N) ^ 2 = 1 := by
    rw [← sq_abs ((1 - h) ^ N), abs_pow, hb]
    field_simp
  have heq : ((1 + (N : ℝ) * h) * ‖g N‖) ^ 2 = ‖x 0‖ ^ 2 := by
    rw [mul_pow, hgsq, mul_add, ← mul_assoc, hcoeff, one_mul, hxsq]
  have hnorm : (1 + (N : ℝ) * h) * ‖g N‖ = ‖x 0‖ := by
    exact (sq_eq_sq₀ (mul_nonneg hD.le (norm_nonneg (g N))) (norm_nonneg (x 0))).mp heq
  rw [← hnorm]
  field_simp

end THGGradient
