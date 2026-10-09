module

public import THGGradient.FactorIdentity
public import THGGradient.Elementary

/-! Scaling with the retained starred interpolation surplus.
The balanced certificate is an explicit internal hypothesis in this module. -/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace
open Finset

namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact interpolation surplus under scalar objective/gradient scaling. -/
theorem interpolationQ_scale (s : ℝ) (x g : ℕ → E) (f : ℕ → ℝ) (i j : ℕ) :
    interpolationQ x (fun k => s • g k) (fun k => s * f k) i j =
      s * interpolationQ x g f i j + s * (1 - s) * ‖g i - g j‖ ^ 2 := by
  simp only [interpolationQ, ← smul_sub, inner_smul_left, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, RCLike.conj_to_real]
  ring

/-- The starred surplus is essential for the progress coefficient. -/
theorem starQ_scale (s : ℝ) (x g : ℕ → E) (f : ℕ → ℝ) (i : ℕ) :
    starQ x (fun k => s • g k) (fun k => s * f k) i =
      s * starQ x g f i + s * (1 - s) * ‖g i‖ ^ 2 := by
  simp only [starQ, inner_smul_left, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, RCLike.conj_to_real]
  ring

theorem toStarQ_scale (s : ℝ) (g : ℕ → E) (f : ℕ → ℝ) (i : ℕ) :
    toStarQ (fun k => s • g k) (fun k => s * f k) i =
      s * toStarQ g f i + s * (1 - s) * ‖g i‖ ^ 2 := by
  simp only [toStarQ, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Internal balanced-step certificate retaining all starred interpolation terms. -/
def BalancedRetainedCertificate (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (N : ℕ) (H : ℝ) : Prop :=
  ∀ (x g : ℕ → E) (f : ℕ → ℝ),
    (∀ i < N, x (i + 1) = x i - H • g i) →
    (∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j) →
    ‖x N‖ ^ 2 + 2 * (N : ℝ) * H * f N +
      (N : ℝ) * H * (1 + (N : ℝ) * H) * ‖g N‖ ^ 2 +
      H * ∑ i ∈ range N, starQ x g f i ≤ ‖x 0‖ ^ 2

/-- The full progress potential follows from the balanced certificate, with no loss
in the gradient coefficient because the scaled starred remainder is retained. -/
theorem progress_joint_of_balanced (N : ℕ) {h H : ℝ}
    (hH : 0 < H) (hH2 : H ≤ 2) (hh : 0 ≤ h) (hhH : h ≤ H)
    (balanced : BalancedRetainedCertificate E N H)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hrec : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i) :
    ‖x N‖ ^ 2 + 2 * (N : ℝ) * h * f N +
      (N : ℝ) * h * (1 + (N : ℝ) * h) * ‖g N‖ ^ 2 ≤ ‖x 0‖ ^ 2 := by
  let s := h / H
  have hs : 0 ≤ s := div_nonneg hh hH.le
  have hs1 : s ≤ 1 := (div_le_one hH).mpr hhH
  have hsH : H * s = h := by dsimp [s]; field_simp
  have hc : ∀ i < N, ‖g i - g (i + 1)‖ ^ 2 ≤
      ⟪g i - g (i + 1), x i - x (i + 1)⟫_ℝ := by
    intro i hi
    exact interpolation_cocoercive _ _ _ _ _ _
      (hQ i (by omega) (i + 1) (by omega))
      (hQ (i + 1) (by omega) i (by omega))
  have hmono := gradient_norm_antitone N hh (hhH.trans hH2) x g hrec hc
  have hscaledrec : ∀ i < N, x (i + 1) = x i - H • (s • g i) := by
    intro i hi
    rw [smul_smul, hsH]
    exact hrec i hi
  have hscaledQ : ∀ i ≤ N, ∀ j ≤ N,
      0 ≤ interpolationQ x (fun k => s • g k) (fun k => s * f k) i j := by
    intro i hi j hj
    rw [interpolationQ_scale]
    exact add_nonneg (mul_nonneg hs (hQ i hi j hj))
      (mul_nonneg (mul_nonneg hs (sub_nonneg.mpr hs1)) (sq_nonneg _))
  have hb := balanced x (fun i => s • g i) (fun i => s * f i) hscaledrec hscaledQ
  have hsum : (N : ℝ) * (s * (1 - s) * ‖g N‖ ^ 2) ≤
      ∑ i ∈ range N, starQ x (fun k => s • g k) (fun k => s * f k) i := by
    calc
      (N : ℝ) * (s * (1 - s) * ‖g N‖ ^ 2) =
          ∑ _i ∈ range N, (s * (1 - s) * ‖g N‖ ^ 2) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        have hiN : i ≤ N := Nat.le_of_lt (mem_range.mp hi)
        rw [starQ_scale]
        have hiG : ‖g N‖ ^ 2 ≤ ‖g i‖ ^ 2 := by
          nlinarith [hmono i hiN, norm_nonneg (g N), norm_nonneg (g i)]
        have hm := mul_le_mul_of_nonneg_left hiG (mul_nonneg hs (sub_nonneg.mpr hs1))
        have hz := mul_nonneg hs (hstar i hiN)
        linarith
  have hsumH := mul_le_mul_of_nonneg_left hsum hH.le
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hb
  have hcoefficient :
      (N : ℝ) * H * (1 + (N : ℝ) * H) * s ^ 2 +
        H * ((N : ℝ) * (s * (1 - s))) =
        (N : ℝ) * h * (1 + (N : ℝ) * h) := by
    rw [← hsH]
    ring
  have hval : 2 * (N : ℝ) * H * (s * f N) = 2 * (N : ℝ) * h * f N := by
    rw [← hsH]
    ring
  rw [hval] at hb
  nlinarith [hsumH, hcoefficient]

/-- The progress potential gives the exact terminal gradient coefficient. -/
theorem progress_norm_of_joint (N : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hjoint : ‖x N‖ ^ 2 + 2 * (N : ℝ) * h * f N +
      (N : ℝ) * h * (1 + (N : ℝ) * h) * ‖g N‖ ^ 2 ≤ ‖x 0‖ ^ 2)
    (hstar : 0 ≤ starQ x g f N) (hto : 0 ≤ toStarQ g f N) :
    ‖g N‖ ≤ ‖x 0‖ * (1 + (N : ℝ) * h)⁻¹ := by
  have hc := starred_cocoercive (x N) (g N) (f N) hstar hto
  have hg := norm_le_of_cocoercive_zero (x N) (g N) hc
  have hsq : ‖g N‖ ^ 2 ≤ ‖x N‖ ^ 2 := by
    nlinarith [norm_nonneg (g N), norm_nonneg (x N)]
  have hf : ‖g N‖ ^ 2 ≤ 2 * f N := by simpa only [toStarQ, sub_nonneg] using hto
  have hfg := mul_le_mul_of_nonneg_left hf (show 0 ≤ (N : ℝ) * h by positivity)
  have hD : 0 < 1 + (N : ℝ) * h := by positivity
  have hsq' : ((1 + (N : ℝ) * h) * ‖g N‖) ^ 2 ≤ ‖x 0‖ ^ 2 := by
    nlinarith [hjoint, hsq, hfg]
  have hbound : (1 + (N : ℝ) * h) * ‖g N‖ ≤ ‖x 0‖ := by
    nlinarith [norm_nonneg (x 0), norm_nonneg (g N)]
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ hD).mpr (by nlinarith)

end THGGradient
