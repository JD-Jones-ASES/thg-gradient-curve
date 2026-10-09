module
public import THGGradient.ProximalWitnesses

/-! Actual scalar minimizers attaining the terminal objective coefficient. -/

@[expose] public section
noncomputable section
namespace THGGradient

theorem clipped_trajectory_affine (N : ℕ) {h R a : ℝ}
    (hh : 0 ≤ h) (ha : 0 ≤ a) (hRa : (1 + (N : ℝ) * h) * a ≤ R) :
    ∀ i ≤ N, scalarGD h (clippedGradient a) R i = R - (i : ℝ) * h * a := by
  intro i hi
  induction i with
  | zero => simp [scalarGD]
  | succ i ih =>
    have hiN : i ≤ N := by omega
    have hiz : (i : ℝ) * h ≤ (N : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hiN) hh
    have hxa : a ≤ R - (i : ℝ) * h * a := by
      nlinarith [mul_le_mul_of_nonneg_right hiz ha]
    rw [scalarGD, ih hiN]
    rw [clippedGradient, min_eq_right hxa, max_eq_right (by linarith : -a ≤ a)]
    push_cast
    ring

/-- The objective coefficient is attained by an actual convex absolute-value problem.
The construction exists at every nonnegative step; the matching universal upper
bound is asserted only in its separately proved progress range. -/
theorem proximal_objective_attainment (N : ℕ) {h lam R : ℝ}
    (hh : 0 ≤ h) (hlam : 0 < lam) (hR : 0 < R) :
    ∃ (F : ℝ → ℝ) (x z : ℕ → ℝ),
      ConvexOn ℝ Set.univ F ∧ (∀ u, F 0 ≤ F u) ∧ x 0 = R ∧
      (∀ i u, lam * F (z i) + ‖x i - z i‖ ^ 2 / 2 ≤
        lam * F u + ‖x i - u‖ ^ 2 / 2) ∧
      (∀ i, x (i + 1) = x i - h * (x i - z i)) ∧
      F (z N) - F 0 = R ^ 2 / (4 * lam * (1 + (N : ℝ) * h)) := by
  let T := 1 + (N : ℝ) * h
  have hT : 0 < T := by dsimp [T]; positivity
  let a := R / (2 * T)
  have ha : 0 < a := by dsimp [a]; positivity
  have hTa : T * a = R / 2 := by dsimp [a]; field_simp
  have hRa : (1 + (N : ℝ) * h) * a ≤ R := by change T * a ≤ R; rw [hTa]; linarith
  let x := scalarGD h (clippedGradient a) R
  let z := fun i => x i - clippedGradient a (x i)
  refine ⟨(fun t => (a / lam) * |t|), x, z, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs, smul_eq_mul] using
      (convexOn_norm convex_univ : ConvexOn ℝ Set.univ (fun t : ℝ => ‖t‖)).smul
        (div_nonneg ha.le hlam.le)
  · intro u
    simp only [abs_zero, mul_zero]
    positivity
  · intro i u
    exact absolute_proximal_minimizer ha.le hlam (x i) u
  · intro i
    dsimp [z]
    rw [sub_sub_cancel]
    rfl
  · have hxN : x N = R - (N : ℝ) * h * a := clipped_trajectory_affine N hh ha.le hRa N le_rfl
    have hxa : a ≤ x N := by rw [hxN]; nlinarith [hRa]
    have hc : clippedGradient a (x N) = a := by
      rw [clippedGradient, min_eq_right hxa, max_eq_right (by linarith)]
    have hzN : z N = R / 2 := by
      dsimp [z]
      rw [hc, hxN]
      dsimp [T] at hTa
      nlinarith
    change (a / lam) * |z N| - (a / lam) * |(0 : ℝ)| = _
    rw [hzN, abs_of_pos (by positivity : 0 < R / 2), abs_zero, mul_zero, sub_zero]
    dsimp [a, T]
    field_simp
    ring

end THGGradient
