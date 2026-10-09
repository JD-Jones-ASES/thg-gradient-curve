module

public import THGGradient.Elementary
public import THGGradient.FactorIdentity

/-!
# Equality in the far-step regime

The quadratic trajectory is forced by equality for every normalized stepsize
`h ≥ 2`. At `h = 2`, the proof uses interpolation between successive iterates;
for larger steps, equality in the distance recursion is already rigid.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace THGGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Equality in the norm consequence of cocoercivity identifies the two vectors. -/
theorem eq_of_cocoercive_norm_eq (x g : E)
    (hc : ‖g‖ ^ 2 ≤ ⟪g, x⟫_ℝ) (hn : ‖g‖ = ‖x‖) : g = x := by
  have hs := norm_sub_sq_real g x
  rw [hn] at hc hs
  have hsq : ‖g - x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖g - x‖]
  have hh : ‖g - x‖ = 0 := (sq_eq_zero_iff).mp hsq
  exact sub_eq_zero.mp (norm_eq_zero.mp hh)

/-- A strict far step attaining its distance expansion has `g = x`. -/
theorem far_step_equality {h : ℝ} (hh : 2 < h) (x g : E)
    (hc : ‖g‖ ^ 2 ≤ ⟪g, x⟫_ℝ)
    (heq : ‖x - h • g‖ = (h - 1) * ‖x‖) : g = x := by
  have hn := norm_le_of_cocoercive_zero x g hc
  have hgap : 0 ≤ ‖x‖ ^ 2 - ‖g‖ ^ 2 := by nlinarith [norm_nonneg x, norm_nonneg g]
  have hcoef : 0 < h * (h - 2) := by positivity
  have hinter : 0 ≤ 2 * h * (⟪g, x⟫_ℝ - ‖g‖ ^ 2) := by positivity
  have hs := norm_sub_sq_real x (h • g)
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (show 0 < h by linarith), mul_pow] at hs
  rw [real_inner_comm g x, heq] at hs
  have hz : h * (h - 2) * (‖x‖ ^ 2 - ‖g‖ ^ 2) = 0 := by
    nlinarith [mul_nonneg hcoef.le hgap]
  have he : ‖x‖ ^ 2 - ‖g‖ ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hcoef.ne'
  apply eq_of_cocoercive_norm_eq x g hc
  nlinarith [norm_nonneg x, norm_nonneg g]

/-- The elementary distance bound for every prefix of a far-step trajectory. -/
theorem far_iterate_distance (N : ℕ) {h : ℝ} (hh : 2 ≤ h) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hc : ∀ i ≤ N, ‖g i‖ ^ 2 ≤ ⟪g i, x i⟫_ℝ) :
    ∀ i ≤ N, ‖x i‖ ≤ (h - 1) ^ i * ‖x 0‖ := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    rw [hx i (by omega)]
    calc
      ‖x i - h • g i‖ ≤ (h - 1) * ‖x i‖ := far_step_distance hh _ _ (hc i (by omega))
      _ ≤ (h - 1) * ((h - 1) ^ i * ‖x 0‖) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
      _ = (h - 1) ^ (i + 1) * ‖x 0‖ := by rw [pow_succ]; ring

/-- Terminal sharpness forces equality at every distance recursion. -/
theorem far_equality_distances (N : ℕ) {h : ℝ} (hh : 2 ≤ h) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hc : ∀ i ≤ N, ‖g i‖ ^ 2 ≤ ⟪g i, x i⟫_ℝ)
    (heq : ‖g N‖ = (h - 1) ^ N * ‖x 0‖) :
    ∀ i ≤ N, ‖x i‖ = (h - 1) ^ i * ‖x 0‖ := by
  have hd := far_iterate_distance N hh x g hx hc
  have hterminal : ‖x N‖ = (h - 1) ^ N * ‖x 0‖ := by
    have hg := norm_le_of_cocoercive_zero _ _ (hc N le_rfl)
    linarith [hd N le_rfl]
  intro i hi
  apply Nat.decreasingInduction' (n := N) (P := fun j =>
    ‖x j‖ = (h - 1) ^ j * ‖x 0‖) ?_ hi hterminal
  intro j hj _ ih
  have hs := far_step_distance hh (x j) (g j) (hc j (by omega))
  rw [← hx j hj, ih, pow_succ] at hs
  have hu := hd j (by omega)
  have hr : 0 < h - 1 := by linarith
  nlinarith

/-- Equality characterizes the entire sampled quadratic trajectory for `h ≥ 2`.
The statement includes zero initial distance and even the zero horizon. -/
theorem far_equality_quadratic (N : ℕ) {h : ℝ} (hh : 2 ≤ h)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ interpolationQ x g f i j)
    (hstar : ∀ i ≤ N, 0 ≤ starQ x g f i)
    (hto : ∀ i ≤ N, 0 ≤ toStarQ g f i)
    (heq : ‖g N‖ = (h - 1) ^ N * ‖x 0‖) :
    ∀ i ≤ N, x i = (1 - h) ^ i • x 0 ∧ g i = x i ∧ f i = ‖x i‖ ^ 2 / 2 := by
  have hc (i : ℕ) (hi : i ≤ N) : ‖g i‖ ^ 2 ≤ ⟪g i, x i⟫_ℝ := by
    exact starred_cocoercive _ _ _ (hstar i hi) (hto i hi)
  have hd := far_equality_distances N hh x g hx hc heq
  have hgnorm : ‖g N‖ = ‖x N‖ := by rw [heq, hd N le_rfl]
  have hgN : g N = x N := eq_of_cocoercive_norm_eq _ _ (hc N le_rfl) hgnorm
  have hgi (i : ℕ) (hi : i ≤ N) : g i = x i := by
    rcases eq_or_lt_of_le hh with htwo | hstrict
    · have htwo' : h = 2 := htwo.symm
      have hmono := gradient_norm_antitone N (show 0 ≤ h by linarith) (show h ≤ 2 by linarith)
        x g hx (fun j hj => interpolation_cocoercive (x j) (x (j + 1))
          (g j) (g (j + 1)) (f j) (f (j + 1))
          (hQ j (by omega) (j + 1) (by omega)) (hQ (j + 1) (by omega) j (by omega)))
      have hupper := norm_le_of_cocoercive_zero _ _ (hc i hi)
      have hxi : ‖x i‖ = ‖x 0‖ := by simpa only [htwo', show (2 : ℝ) - 1 = 1 by norm_num, one_pow, one_mul] using hd i hi
      have hgterm : ‖g N‖ = ‖x 0‖ := by simpa only [htwo', show (2 : ℝ) - 1 = 1 by norm_num, one_pow, one_mul] using heq
      exact eq_of_cocoercive_norm_eq _ _ (hc i hi) (by linarith [hmono i hi])
    · rcases lt_or_eq_of_le hi with hlt | rfl
      · apply far_step_equality hstrict _ _ (hc i hi)
        rw [← hx i hlt, hd (i + 1) (by omega), hd i hi, pow_succ]
        ring
      · exact hgN
  have hxformula (i : ℕ) (hi : i ≤ N) : x i = (1 - h) ^ i • x 0 := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [hx i (by omega), hgi i (by omega), ih (by omega), pow_succ]
      module
  intro i hi
  refine ⟨hxformula i hi, hgi i hi, ?_⟩
  have hs := hstar i hi
  have ht := hto i hi
  unfold starQ at hs
  unfold toStarQ at ht
  rw [hgi i hi, real_inner_self_eq_norm_sq] at hs
  rw [hgi i hi] at ht
  linarith

end THGGradient
