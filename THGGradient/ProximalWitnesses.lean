module

public import THGGradient.Witnesses
public import THGGradient.ProximalBridge

/-! Actual proximal minimizers attaining both branches of the residual curve. -/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace

namespace THGGradient

theorem clippedGradient_abs_le {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    |clippedGradient a x| ≤ a := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

/-- Complementarity identity certifying soft thresholding. -/
theorem clippedGradient_complementarity {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    clippedGradient a x * (x - clippedGradient a x) =
      a * |x - clippedGradient a x| := by
  by_cases hx : x ≤ a
  · by_cases hnx : -a ≤ x
    · simp [clippedGradient, min_eq_left hx, max_eq_right hnx]
    · have hn : x - -a ≤ 0 := by linarith
      simp only [clippedGradient, min_eq_left hx, max_eq_left (le_of_not_ge hnx),
        abs_of_nonpos hn]
      ring
  · have hx' : a ≤ x := le_of_not_ge hx
    simp only [clippedGradient, min_eq_right hx', max_eq_right (by linarith : -a ≤ a),
      abs_of_nonneg (sub_nonneg.mpr hx')]

/-- The soft-threshold point is an actual global proximal minimizer. -/
theorem absolute_proximal_minimizer {a lam : ℝ} (ha : 0 ≤ a) (hlam : 0 < lam)
    (x u : ℝ) :
    lam * ((a / lam) * |x - clippedGradient a x|) +
        ‖x - (x - clippedGradient a x)‖ ^ 2 / 2 ≤
      lam * ((a / lam) * |u|) + ‖x - u‖ ^ 2 / 2 := by
  have he : lam * (a / lam) = a := by field_simp
  have hvar : ∀ u ∈ (Set.univ : Set ℝ),
      ⟪x - (x - clippedGradient a x), u - (x - clippedGradient a x)⟫ ≤
        lam * ((a / lam) * |u| - (a / lam) * |x - clippedGradient a x|) := by
    intro u _
    have heU : clippedGradient a x * u ≤ a * |u| := calc
      clippedGradient a x * u ≤ |clippedGradient a x * u| := le_abs_self _
      _ = |clippedGradient a x| * |u| := abs_mul _ _
      _ ≤ a * |u| := mul_le_mul_of_nonneg_right (clippedGradient_abs_le ha x) (abs_nonneg _)
    have hc := clippedGradient_complementarity ha x
    simp only [sub_sub_cancel, RCLike.inner_apply, conj_trivial, mul_sub]
    rw [← mul_assoc, he, ← mul_assoc, he]
    nlinarith
  have hg := proximal_quadratic_growth (C := Set.univ) (F := fun t => (a / lam) * |t|)
    x (x - clippedGradient a x) hvar u (Set.mem_univ _)
  nlinarith [sq_nonneg ‖u - (x - clippedGradient a x)‖]

/-- Actual constrained proximal examples attain the full residual curve. -/
theorem proximal_residual_attainment (N : ℕ) {h lam R : ℝ}
    (hh : 0 ≤ h) (hlam : 0 < lam) (hR : 0 < R) :
    ∃ (C : Set ℝ) (F : ℝ → ℝ) (x z : ℕ → ℝ),
      ConvexOn ℝ C F ∧ (0 : ℝ) ∈ C ∧
      (∀ u ∈ C, F 0 ≤ F u) ∧ x 0 = R ∧
      (∀ i, z i ∈ C) ∧
      (∀ i, ∀ u ∈ C, lam * F (z i) + ‖x i - z i‖ ^ 2 / 2 ≤
        lam * F u + ‖x i - u‖ ^ 2 / 2) ∧
      (∀ i, x (i + 1) = x i - h * (x i - z i)) ∧
      ‖x N - z N‖ = R * max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
  by_cases hb : |1 - h| ^ N ≤ (1 + (N : ℝ) * h)⁻¹
  · let a := R / (1 + (N : ℝ) * h)
    have ha : 0 ≤ a := by dsimp [a]; positivity
    let x := scalarGD h (clippedGradient a) R
    refine ⟨Set.univ, (fun t => (a / lam) * |t|), x,
      (fun i => x i - clippedGradient a (x i)), ?_, Set.mem_univ _, ?_, rfl,
      (fun _ => Set.mem_univ _), ?_, ?_, ?_⟩
    · simpa only [Real.norm_eq_abs, smul_eq_mul] using (convexOn_norm convex_univ : ConvexOn ℝ Set.univ (fun t : ℝ => ‖t‖)).smul (div_nonneg ha hlam.le)
    · intro u _
      simp only [abs_zero, mul_zero]
      positivity
    · intro i u _
      exact absolute_proximal_minimizer ha hlam (x i) u
    · intro i
      simp only [sub_sub_cancel]
      rfl
    · dsimp only
      rw [sub_sub_cancel, max_eq_left hb]
      simpa only [one_mul] using huber_terminal_gradient N (L := 1) hh zero_lt_one hR
  · let x := scalarGD h id R
    refine ⟨{0}, (fun _ => 0), x, (fun _ => 0), ?_, Set.mem_singleton _, ?_,
      rfl, (fun _ => Set.mem_singleton _), ?_, ?_, ?_⟩
    · exact convexOn_const 0 (convex_singleton _)
    · intro u _
      rfl
    · intro i u hu
      have hu0 : u = 0 := Set.mem_singleton_iff.mp hu
      subst u
      rfl
    · intro i
      dsimp [x, scalarGD]
      simp only [sub_zero]
    · dsimp only
      rw [sub_zero, max_eq_right (le_of_not_ge hb)]
      simpa only [one_mul] using quadratic_terminal_gradient N (h := h) (L := 1) zero_lt_one hR

end THGGradient
