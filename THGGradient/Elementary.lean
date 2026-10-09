module
public import Mathlib

/-! Elementary interpolation consequences and the zero-step and far-step regimes. -/

public section
open scoped BigOperators InnerProductSpace
open Finset
namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem interpolation_cocoercive (x y g k : E) (a b : ℝ)
    (hxy : 0 ≤ 2 * (a - b) - 2 * ⟪k, x - y⟫_ℝ - ‖g - k‖ ^ 2)
    (hyx : 0 ≤ 2 * (b - a) - 2 * ⟪g, y - x⟫_ℝ - ‖k - g‖ ^ 2) :
    ‖g - k‖ ^ 2 ≤ ⟪g - k, x - y⟫_ℝ := by
  rw [norm_sub_rev k g] at hyx
  simp only [inner_sub_right, inner_sub_left] at *
  linarith

theorem norm_le_of_cocoercive_zero (x g : E)
    (hc : ‖g‖ ^ 2 ≤ ⟪g, x⟫_ℝ) : ‖g‖ ≤ ‖x‖ := by
  by_contra hn
  have hlt : ‖x‖ < ‖g‖ := lt_of_not_ge hn
  have hpos : 0 < ‖g‖ := lt_of_le_of_lt (norm_nonneg x) hlt
  have hh := mul_lt_mul_of_pos_left hlt hpos
  nlinarith [real_inner_le_norm g x]

theorem starred_cocoercive (x g : E) (f : ℝ)
    (hs : 0 ≤ -2 * f + 2 * ⟪g, x⟫_ℝ - ‖g‖ ^ 2)
    (ht : 0 ≤ 2 * f - ‖g‖ ^ 2) : ‖g‖ ^ 2 ≤ ⟪g, x⟫_ℝ := by
  linarith

theorem gradient_step_norm_le {h : ℝ} (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (g k : E) (hc : ‖g - k‖ ^ 2 ≤ h * ⟪g - k, g⟫_ℝ) :
    ‖k‖ ≤ ‖g‖ := by
  have he : ‖g - k‖ ^ 2 = ‖g‖ ^ 2 + ‖k‖ ^ 2 - 2 * ⟪g, k⟫_ℝ := by
    nlinarith [norm_sub_sq_real g k]
  simp only [inner_sub_left, real_inner_self_eq_norm_sq] at hc
  rw [real_inner_comm g k] at hc
  have hn : 0 ≤ ‖g - k‖ ^ 2 := sq_nonneg _
  have hrem := mul_nonneg (show 0 ≤ 2 - h by linarith) hn
  by_cases hz : h = 0
  · subst h
    have : g - k = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (g - k)])
    simp [sub_eq_zero.mp this]
  · have hp : 0 < h := lt_of_le_of_ne hh (Ne.symm hz)
    have hs : h * ‖k‖ ^ 2 ≤ h * ‖g‖ ^ 2 := by nlinarith
    have hs' := le_of_mul_le_mul_left hs hp
    nlinarith [norm_nonneg g, norm_nonneg k]

theorem gradient_norm_antitone (N : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hc : ∀ i < N, ‖g i - g (i + 1)‖ ^ 2 ≤
      ⟪g i - g (i + 1), x i - x (i + 1)⟫_ℝ) :
    ∀ i ≤ N, ‖g N‖ ≤ ‖g i‖ := by
  have step (i : ℕ) (hi : i < N) : ‖g (i + 1)‖ ≤ ‖g i‖ := by
    apply gradient_step_norm_le hh hh2
    have hp := hc i hi
    rw [hx i hi, sub_sub_cancel, inner_smul_right] at hp
    exact hp
  intro i hi
  have aux : ∀ j, j ≤ N → ∀ i, i ≤ j → ‖g j‖ ≤ ‖g i‖ := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      have : i = 0 := by omega
      subst i
      exact le_rfl
    | succ j ih =>
      intro hj i hi
      rcases eq_or_lt_of_le hi with heq | hlt
      · subst i; exact le_rfl
      · exact (step j (by omega)).trans (ih (by omega) i (by omega))
  exact aux N le_rfl i hi

theorem far_step_distance {h : ℝ} (hh : 2 ≤ h) (x g : E)
    (hc : ‖g‖ ^ 2 ≤ ⟪g, x⟫_ℝ) : ‖x - h • g‖ ≤ (h - 1) * ‖x‖ := by
  have hn := norm_le_of_cocoercive_zero x g hc
  have hs : ‖g‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg g, norm_nonneg x]
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ h * (h - 2) by positivity)
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * h by linarith)
  have he := norm_sub_sq_real x (h • g)
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ h by linarith), mul_pow] at he
  rw [real_inner_comm g x] at he
  have hsq : ‖x - h • g‖ ^ 2 ≤ ((h - 1) * ‖x‖) ^ 2 := by nlinarith
  have hnn : 0 ≤ (h - 1) * ‖x‖ := mul_nonneg (by linarith) (norm_nonneg x)
  nlinarith [norm_nonneg (x - h • g)]

theorem far_step_bound (N : ℕ) {h : ℝ} (hh : 2 ≤ h) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hc : ∀ i ≤ N, ‖g i‖ ^ 2 ≤ ⟪g i, x i⟫_ℝ) :
    ‖g N‖ ≤ (h - 1) ^ N * ‖x 0‖ := by
  have hd : ∀ i ≤ N, ‖x i‖ ≤ (h - 1) ^ i * ‖x 0‖ := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      rw [hx i (by omega)]
      calc
        ‖x i - h • g i‖ ≤ (h - 1) * ‖x i‖ :=
          far_step_distance hh _ _ (hc i (by omega))
        _ ≤ (h - 1) * ((h - 1) ^ i * ‖x 0‖) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
        _ = (h - 1) ^ (i + 1) * ‖x 0‖ := by rw [pow_succ]; ring
  exact (norm_le_of_cocoercive_zero _ _ (hc N le_rfl)).trans (hd N le_rfl)

end THGGradient
