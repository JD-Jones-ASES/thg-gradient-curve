module
public import THGGradient.AnalyticTransfer
public import THGGradient.Balance
public import THGGradient.LowerBranch

/-! Assembly of the step regimes from the two internal certificate interfaces. -/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace
namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def UpperDataBound (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : ℕ) (h : ℝ) : Prop :=
  ∀ (x g : ℕ → E) (f : ℕ → ℝ),
    (∀ i < N, x (i + 1) = x i - h • g i) →
    (∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j) →
    (∀ i ≤ N, 0 ≤ starQ x g f i) →
    (∀ i ≤ N, 0 ≤ toStarQ g f i) →
    ‖g N‖ ≤ ‖x 0‖ * (h - 1) ^ N

theorem data_bound_of_certificates (N : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (upper : ∀ (h : ℝ), 0 < N → 1 < h → h < 2 →
      ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h → UpperDataBound E N h)
    (balanced : 0 < N → BalancedRetainedCertificate E N (balanceStep N)) :
    DataBound E N h := by
  intro x g f hrec hQ hs ht
  have hc : ∀ i ≤ N, ‖g i‖ ^ 2 ≤ ⟪g i, x i⟫_ℝ := by
    intro i hi
    exact starred_cocoercive _ _ _ (hs i hi) (ht i hi)
  by_cases hz : N = 0
  · subst N
    simpa using norm_le_of_cocoercive_zero _ _ (hc 0 le_rfl)
  have hN : 0 < N := by omega
  by_cases hfar : 2 ≤ h
  · have hb := far_step_bound N hfar x g hrec hc
    have habs : |1 - h| = h - 1 := by rw [abs_of_nonpos (by linarith)]; ring
    calc
      ‖g N‖ ≤ ‖x 0‖ * (h - 1) ^ N := by simpa [mul_comm] using hb
      _ ≤ ‖x 0‖ * max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
        rw [habs]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
  have hlt2 : h < 2 := lt_of_not_ge hfar
  have hH := balanceStep_spec hN
  by_cases hlo : h ≤ balanceStep N
  · have hj := progress_joint_of_balanced N (by linarith [hH.1]) hH.2.1.le hh hlo
      (balanced hN) x g f hrec hQ hs
    have hb := progress_norm_of_joint N hh x g f hj (hs N le_rfl) (ht N le_rfl)
    exact hb.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _))
  · have hHh : balanceStep N ≤ h := (lt_of_not_ge hlo).le
    have h1 : 1 < h := lt_of_lt_of_le hH.1 hHh
    have hpoly := (balanceStep_le_iff hN h1.le).mp hHh
    have hpow : 0 < (h - 1) ^ N := pow_pos (by linarith) _
    have hu : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h := by
      rw [inv_pow]
      apply (inv_le_iff_one_le_mul₀ hpow).mpr
      simpa [balancePolynomial, mul_comm] using hpoly
    have hb := upper h hN h1 hlt2 hu x g f hrec hQ hs ht
    have habs : |1 - h| = h - 1 := by rw [abs_of_nonpos (by linarith)]; ring
    exact hb.trans (mul_le_mul_of_nonneg_left (by rw [habs]; exact le_max_right _ _)
      (norm_nonneg _))

theorem le_balance_of_progress {N : ℕ} (hN : 0 < N) {h : ℝ} (_hh : 0 ≤ h)
    (hbranch : |1 - h| ^ N ≤ (1 + (N : ℝ) * h)⁻¹) : h ≤ balanceStep N := by
  by_cases h1 : 1 ≤ h
  · apply (le_balanceStep_iff hN h1).mpr
    have hD : 0 < 1 + (N : ℝ) * h := by positivity
    have habs : |1 - h| = h - 1 := by rw [abs_of_nonpos (by linarith)]; ring
    calc
      balancePolynomial N h = |1 - h| ^ N * (1 + (N : ℝ) * h) := by
        rw [habs]; rfl
      _ ≤ (1 + (N : ℝ) * h)⁻¹ * (1 + (N : ℝ) * h) :=
        mul_le_mul_of_nonneg_right hbranch hD.le
      _ = 1 := inv_mul_cancel₀ hD.ne'
  · exact (le_of_not_ge h1).trans (balanceStep_spec hN).1.le

theorem progress_joint_of_certificates (N : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (hbranch : |1 - h| ^ N ≤ (1 + (N : ℝ) * h)⁻¹)
    (balanced : 0 < N → BalancedRetainedCertificate E N (balanceStep N))
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hrec : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i) :
    ‖x N‖ ^ 2 + 2 * (N : ℝ) * h * f N +
      (N : ℝ) * h * (1 + (N : ℝ) * h) * ‖g N‖ ^ 2 ≤ ‖x 0‖ ^ 2 := by
  by_cases hz : N = 0
  · subst N; simp
  have hN : 0 < N := by omega
  have hs := balanceStep_spec hN
  exact progress_joint_of_balanced N (by linarith [hs.1]) hs.2.1.le hh
    (le_balance_of_progress hN hh hbranch) (balanced hN) x g f hrec hQ hstar

end THGGradient
