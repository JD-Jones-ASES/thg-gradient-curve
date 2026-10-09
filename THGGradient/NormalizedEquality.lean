module
public import THGGradient.UniformCertificate
public import THGGradient.EqualityCertificates

/-! Unconditional normalized trajectory rigidity in the two certificate branches. -/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace
open Finset
namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact balanced weighted identity, retaining all multipliers. -/
theorem normalized_balanced_identity (N : ℕ) (hN : 0 < N)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - balanceStep N • g i) :
    ‖x 0‖ ^ 2 - ‖x N‖ ^ 2 - 2 * N * balanceStep N * f N
      - N * balanceStep N * (1 + N * balanceStep N) * ‖g N‖ ^ 2 =
      (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        uniformWeight N (balanceStep N) i j * interpolationQ x g f i j)
      + balanceStep N * ∑ i ∈ range N, starQ x g f i := by
  have hs := balanceStep_spec hN
  have heq := balanceStep_upper_condition hN
  have hdiag := uniformWeight_diagonal (N := N) hs.1 hs.2.1
  rw [heq] at hdiag
  have hW := trajectory_weighted_decomposition N (balanceStep N) (1 + N * balanceStep N)
    (uniformWeight N (balanceStep N)) f x g hx uniformWeight_mixed hdiag
  have he : (∑ i ∈ range N, 2 * weightDivergence N (uniformWeight N (balanceStep N)) i *
      ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2))) =
      ∑ i ∈ range N, 2 * balanceStep N *
      ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2)) := by
    apply sum_congr rfl
    intro i hi
    rw [uniformWeight_divergence hs.1 hs.2.1 i (mem_range.mp hi),
      uniformDelta_eq_step hN hs.1 heq]
  rw [he] at hW
  exact balanced_certificate_completion N (balanceStep N) _ f x g hx hW

/-- Equality in the strict progress branch forces the Huber sampled trajectory. -/
theorem normalized_progress_equality (N : ℕ) (hN : 0 < N) {h : ℝ}
    (hh : 0 < h) (hbranch : h < balanceStep N)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i)
    (hto : ∀ i ≤ N, 0 ≤ toStarQ g f i)
    (heq : ‖g N‖ = ‖x 0‖ * (1 + N * h)⁻¹) :
    ∀ i ≤ N, g i = g N ∧ x i = (1 + ((N : ℝ) - i) * h) • g N ∧
      f i = (((N : ℝ) - i) * h + 1 / 2) * ‖g N‖ ^ 2 := by
  let H := balanceStep N
  let s := h / H
  have hH := balanceStep_spec hN
  have hH0 : 0 < H := by dsimp [H]; linarith [hH.1]
  have hs : 0 < s := div_pos hh hH0
  have hs1 : s < 1 := (div_lt_one hH0).mpr hbranch
  have hsH : H * s = h := by dsimp [s]; field_simp
  have hxS : ∀ i < N, x (i + 1) = x i - H • (s • g i) := by
    intro i hi
    rw [smul_smul, hsH]
    exact hx i hi
  have hb := normalized_balanced_identity N hN x (fun i => s • g i) (fun i => s * f i) hxS
  have hdef := progress_deficit_identity N H h s hsH (uniformWeight N H) x g f hb
  have hupper := balanceStep_upper_condition hN
  have hcoco : ∀ i < N, ‖g i - g (i + 1)‖ ^ 2 ≤
      ⟪g i - g (i + 1), x i - x (i + 1)⟫_ℝ := by
    intro i hi
    exact interpolation_cocoercive _ _ _ _ _ _
      (hQ i (by omega) (i + 1) (by omega))
      (hQ (i + 1) (by omega) i (by omega))
  have hm := gradient_norm_antitone N hh.le (by linarith [hH.2.1]) x g hx hcoco
  have hmono (i : ℕ) (hi : i < N) : ‖g N‖ ^ 2 ≤ ‖g i‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hm i (by omega))
  have hT : 0 < 1 + (N : ℝ) * h := by positivity
  have he : ‖g N‖ * (1 + N * h) = ‖x 0‖ := by
    rw [heq]
    field_simp
  have he2 : ‖x 0‖ ^ 2 = (1 + N * h) ^ 2 * ‖g N‖ ^ 2 := by
    rw [← he]
    ring
  obtain ⟨hres, hsz, hgc⟩ := progress_equality_remainders N hh hs hs1
    (uniformWeight N H) x g f hQ hstar hto
    (uniformWeight_nonneg hH.1 hH.2.1 hupper.le)
    (uniformWeight_pos hH.1 hH.2.1 hupper.le) hmono hdef he2
  have hf := constant_gradient_decomposition N h x g f hx hgc hsz hres
  exact fun i hi => ⟨hgc i hi, hf i hi⟩

/-- Equality in the balanced branch admits exactly two orthogonal components. -/
theorem normalized_balance_equality (N : ℕ) (hN : 0 < N)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - balanceStep N • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i)
    (hto : ∀ i ≤ N, 0 ≤ toStarQ g f i)
    (heq : ‖g N‖ = ‖x 0‖ * (1 + N * balanceStep N)⁻¹) :
    ∃ a b : E, ⟪a, b⟫_ℝ = 0 ∧ ∀ i ≤ N,
      g i = b + (1 - balanceStep N) ^ i • a ∧
      x i = (1 + ((N : ℝ) - i) * balanceStep N) • b + (1 - balanceStep N) ^ i • a ∧
      f i = (((N : ℝ) - i) * balanceStep N + 1 / 2) * ‖b‖ ^ 2
        + ((1 - balanceStep N) ^ i) ^ 2 / 2 * ‖a‖ ^ 2 := by
  have hs := balanceStep_spec hN
  have hupper := balanceStep_upper_condition hN
  have hW := trajectory_weighted_decomposition N (balanceStep N) (((balanceStep N - 1)⁻¹) ^ N)
    (uniformWeight N (balanceStep N)) f x g hx uniformWeight_mixed
    (uniformWeight_diagonal hs.1 hs.2.1)
  have hd (i : ℕ) (hi : i < N) : weightDivergence N (uniformWeight N (balanceStep N)) i = balanceStep N := by
    rw [uniformWeight_divergence hs.1 hs.2.1 i hi, uniformDelta_eq_step hN hs.1 hupper]
  have hsum : -1 ≤ ∑ i ∈ range N, weightDivergence N (uniformWeight N (balanceStep N)) i := by
    have hn : 0 ≤ ∑ i ∈ range N, weightDivergence N (uniformWeight N (balanceStep N)) i := by
      apply sum_nonneg
      intro i hi
      rw [hd i (mem_range.mp hi)]
      linarith [hs.1]
    linarith
  have hT : 0 < 1 + (N : ℝ) * balanceStep N := by
    have hHpos : 0 < balanceStep N := by linarith [hs.1]
    positivity
  have he : ‖g N‖ * (1 + N * balanceStep N) = ‖x 0‖ := by rw [heq]; field_simp
  have he2 : ‖x 0‖ ^ 2 = (((balanceStep N - 1)⁻¹) ^ N) ^ 2 * ‖g N‖ ^ 2 := by
    rw [hupper, ← he]
    ring
  obtain ⟨hres, hsz, hqz, _⟩ := upper_equality_remainders N (by linarith [hs.1])
    (uniformWeight N (balanceStep N)) (weightDivergence N (uniformWeight N (balanceStep N))) f x g
    hx hQ hstar hto (uniformWeight_nonneg hs.1 hs.2.1 hupper.le)
    (uniformWeight_pos hs.1 hs.2.1 hupper.le) (fun i hi => (hd i hi).le) hsum hW he2
  exact zero_interpolation_decomposition N hN (by linarith [hs.1]) x g f hx hsz hqz hres

/-- Equality in the strict oscillation branch is purely quadratic. -/
theorem normalized_oscillation_equality (N : ℕ) (hN : 0 < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2)
    (hbranch : ((h - 1)⁻¹) ^ N < 1 + (N : ℝ) * h)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i)
    (hto : ∀ i ≤ N, 0 ≤ toStarQ g f i)
    (heq : ‖g N‖ = ‖x 0‖ * (h - 1) ^ N) :
    ∀ i ≤ N, x i = (1 - h) ^ i • x 0 ∧ g i = x i ∧ f i = ‖x i‖ ^ 2 / 2 := by
  have hW := trajectory_weighted_decomposition N h (((h - 1)⁻¹) ^ N)
    (uniformWeight N h) f x g hx uniformWeight_mixed (uniformWeight_diagonal h1 h2)
  have hd := uniformWeight_divergence (N := N) h1 h2
  have hδ := uniformDelta_lt_step hN h1 h2 hbranch
  have hsum : -1 ≤ ∑ i ∈ range N, weightDivergence N (uniformWeight N h) i := by
    have hn : 0 ≤ ∑ i ∈ range N, weightDivergence N (uniformWeight N h) i := by
      apply sum_nonneg
      intro i hi
      rw [hd i (mem_range.mp hi)]
      exact (uniformDelta_pos hN h1 h2).le
    linarith
  have hr : (h - 1) ≠ 0 := by linarith
  have he : ‖g N‖ * ((h - 1)⁻¹) ^ N = ‖x 0‖ := by
    rw [heq, mul_assoc, ← mul_pow]
    simp [hr]
  have he2 : ‖x 0‖ ^ 2 = (((h - 1)⁻¹) ^ N) ^ 2 * ‖g N‖ ^ 2 := by rw [← he]; ring
  obtain ⟨hres, hsz, hqz, htz⟩ := upper_equality_remainders N (by linarith : 0 < h)
    (uniformWeight N h) (weightDivergence N (uniformWeight N h)) f x g
    hx hQ hstar hto (uniformWeight_nonneg h1 h2 hbranch.le)
    (uniformWeight_pos h1 h2 hbranch.le) (fun i hi => by rw [hd i hi]; exact hδ.le) hsum hW he2
  apply zero_interpolation_quadratic N hN (by linarith) x g f hx hsz hqz hres
  exact htz 0 hN (by rw [hd 0 hN]; exact hδ)

end THGGradient
