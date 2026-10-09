module

public import Mathlib

@[expose] public section

namespace THGGradient

/-- The clipped identity used as the derivative of the Huber witness. -/
def clippedGradient (a x : ℝ) : ℝ := max (-a) (min x a)

/-- The Huber primitive, including both junctions in its derivative theorem. -/
noncomputable def huberFunction (a x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, clippedGradient a t

theorem clippedGradient_lipschitz (a : ℝ) : LipschitzWith 1 (clippedGradient a) := by
  exact (LipschitzWith.id.min_const a).const_max (-a)

theorem clippedGradient_monotone (a : ℝ) : Monotone (clippedGradient a) := by
  intro x y hxy
  exact max_le_max_left _ (min_le_min_right _ hxy)

theorem huberFunction_hasDerivAt (a x : ℝ) :
    HasDerivAt (huberFunction a) (clippedGradient a x) x := by
  have hc := (clippedGradient_lipschitz a).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem huberFunction_convex (a : ℝ) : ConvexOn ℝ Set.univ (huberFunction a) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (huberFunction_hasDerivAt a x).differentiableAt)
  intro x y hxy
  rw [(huberFunction_hasDerivAt a x).deriv, (huberFunction_hasDerivAt a y).deriv]
  exact clippedGradient_monotone a hxy

theorem clippedGradient_zero {a : ℝ} (ha : 0 ≤ a) : clippedGradient a 0 = 0 := by
  simp [clippedGradient, min_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]

theorem scalar_minimum_of_convex_of_deriv_zero {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : HasDerivAt f 0 0) (x : ℝ) : f 0 ≤ f x := by
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · have hs := hf.le_slope_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hx hd
    rw [slope_def_field, sub_zero] at hs
    have ht := (le_div_iff₀ hx).mp hs
    linarith
  · rfl
  · have hs := hf.slope_le_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hx hd
    rw [slope_def_field, zero_sub] at hs
    have := (div_le_iff₀ (neg_pos.mpr hx)).mp hs
    linarith

theorem huberFunction_minimum {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    huberFunction a 0 ≤ huberFunction a x := by
  apply scalar_minimum_of_convex_of_deriv_zero (huberFunction_convex a)
  simpa only [clippedGradient_zero ha] using huberFunction_hasDerivAt a 0

/-- Scaling the objective prescribes the gradient Lipschitz constant. -/
noncomputable def scaledHuber (L a x : ℝ) : ℝ := L * huberFunction a x

theorem scaledHuber_hasGradientAt (L a x : ℝ) :
    HasGradientAt (scaledHuber L a) (L * clippedGradient a x) x :=
  ((huberFunction_hasDerivAt a x).const_mul L).hasGradientAt'

theorem scaledHuber_convex {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    ConvexOn ℝ Set.univ (scaledHuber L a) :=
  (huberFunction_convex a).smul hL

theorem scaledHuber_lipschitz {L : ℝ} (hL : 0 ≤ L) (a x y : ℝ) :
    ‖L * clippedGradient a x - L * clippedGradient a y‖ ≤ L * ‖x - y‖ := by
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg hL]
  apply mul_le_mul_of_nonneg_left _ hL
  simpa only [Real.dist_eq, Real.norm_eq_abs, NNReal.coe_one, one_mul] using (clippedGradient_lipschitz a).dist_le_mul x y

theorem scaledHuber_minimum {L a : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (x : ℝ) :
    scaledHuber L a 0 ≤ scaledHuber L a x :=
  mul_le_mul_of_nonneg_left (huberFunction_minimum ha x) hL

/-- Actual quadratic objective for the oscillatory branch. -/
noncomputable def quadraticFunction (L x : ℝ) : ℝ := L * x ^ 2 / 2

theorem quadraticFunction_hasDerivAt (L x : ℝ) :
    HasDerivAt (quadraticFunction L) (L * x) x := by
  have hd := (((hasDerivAt_id x).pow 2).const_mul L).div_const 2
  convert hd using 1
  · funext y
    rfl
  · norm_num
    ring

theorem quadraticFunction_hasGradientAt (L x : ℝ) :
    HasGradientAt (quadraticFunction L) (L * x) x :=
  (quadraticFunction_hasDerivAt L x).hasGradientAt'

theorem quadraticFunction_convex {L : ℝ} (hL : 0 ≤ L) :
    ConvexOn ℝ Set.univ (quadraticFunction L) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (quadraticFunction_hasDerivAt L x).differentiableAt)
  intro x y hxy
  rw [(quadraticFunction_hasDerivAt L x).deriv, (quadraticFunction_hasDerivAt L y).deriv]
  exact mul_le_mul_of_nonneg_left hxy hL

theorem quadraticFunction_lipschitz {L : ℝ} (hL : 0 ≤ L) (x y : ℝ) :
    ‖L * x - L * y‖ ≤ L * ‖x - y‖ := by
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg hL]

theorem quadraticFunction_minimum {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    quadraticFunction L 0 ≤ quadraticFunction L x := by
  simp only [quadraticFunction, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
  positivity

/-- Unrestricted real gradient iteration; sharpness checks its first `N` steps. -/
noncomputable def scalarGD (h : ℝ) (g : ℝ → ℝ) (R : ℝ) : ℕ → ℝ
  | 0 => R
  | n + 1 => scalarGD h g R n - h * g (scalarGD h g R n)

theorem scalarGD_scaled_recurrence {L : ℝ} (hL : L ≠ 0) (h R : ℝ)
    (g : ℝ → ℝ) (i : ℕ) :
    scalarGD h g R (i + 1) = scalarGD h g R i -
      (h / L) * (L * g (scalarGD h g R i)) := by
  rw [scalarGD]
  field_simp

/-- The progress witness stays in the constant-gradient region through the final point. -/
theorem huber_trajectory_formula (N : ℕ) {h R : ℝ} (hh : 0 ≤ h) (hR : 0 < R)
    (i : ℕ) (hi : i ≤ N) :
    scalarGD h (clippedGradient (R / (1 + (N : ℝ) * h))) R i =
      R - (i : ℝ) * h * (R / (1 + (N : ℝ) * h)) := by
  have hD : 0 < 1 + (N : ℝ) * h := by positivity
  have ha : 0 < R / (1 + (N : ℝ) * h) := div_pos hR hD
  have hRa : (1 + (N : ℝ) * h) * (R / (1 + (N : ℝ) * h)) = R := by
    field_simp
  induction i with
  | zero => simp [scalarGD]
  | succ i ih =>
      have hiN : i ≤ N := by omega
      have hih := ih hiN
      have hiz : (i : ℝ) * h ≤ (N : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hiN) hh
      have hxa : R / (1 + (N : ℝ) * h) ≤
          R - (i : ℝ) * h * (R / (1 + (N : ℝ) * h)) := by
        have := mul_le_mul_of_nonneg_right hiz ha.le
        nlinarith [hRa]
      rw [scalarGD, hih]
      rw [clippedGradient, min_eq_right hxa, max_eq_right (by linarith :
        -(R / (1 + (N : ℝ) * h)) ≤ R / (1 + (N : ℝ) * h))]
      push_cast
      ring

theorem huber_terminal_gradient (N : ℕ) {h L R : ℝ} (hh : 0 ≤ h)
    (hL : 0 < L) (hR : 0 < R) :
    ‖L * clippedGradient (R / (1 + (N : ℝ) * h))
      (scalarGD h (clippedGradient (R / (1 + (N : ℝ) * h))) R N)‖ =
        L * R * (1 + (N : ℝ) * h)⁻¹ := by
  have hD : 0 < 1 + (N : ℝ) * h := by positivity
  have ha : 0 < R / (1 + (N : ℝ) * h) := div_pos hR hD
  have heq : R - (N : ℝ) * h * (R / (1 + (N : ℝ) * h)) =
      R / (1 + (N : ℝ) * h) := by field_simp; ring
  rw [huber_trajectory_formula N hh hR N le_rfl, heq]
  rw [clippedGradient, min_self, max_eq_right (by linarith),
    Real.norm_of_nonneg (mul_nonneg hL.le ha.le)]
  simp only [div_eq_mul_inv]
  ring

theorem quadratic_trajectory_formula (h R : ℝ) (i : ℕ) :
    scalarGD h id R i = (1 - h) ^ i * R := by
  induction i with
  | zero => simp [scalarGD]
  | succ i ih =>
      rw [scalarGD, ih, pow_succ]
      simp only [id_eq]
      ring

theorem quadratic_terminal_gradient (N : ℕ) {h L R : ℝ}
    (hL : 0 < L) (hR : 0 < R) :
    ‖L * scalarGD h id R N‖ = L * R * |1 - h| ^ N := by
  rw [quadratic_trajectory_formula, norm_mul, norm_mul, Real.norm_of_nonneg hL.le,
    Real.norm_of_nonneg hR.le, norm_pow, Real.norm_eq_abs]
  ring

/-- Both terms in the sharp curve are attained by actual smooth convex real functions.
The function is selected between the Huber primitive and the quadratic. The supplied
trajectory satisfies the gradient recurrence for every natural index. -/
theorem scalar_attainment (N : ℕ) {h L R : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (hR : 0 < R) :
    ∃ (f : ℝ → ℝ) (g : ℝ → ℝ) (x : ℕ → ℝ),
      ConvexOn ℝ Set.univ f ∧
      (∀ y, HasGradientAt f (g y) y) ∧
      (∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) ∧
      (∀ y, f 0 ≤ f y) ∧
      x 0 = R ∧
      (∀ i, x (i + 1) = x i - (h / L) * g (x i)) ∧
      ‖g (x N)‖ = L * R * max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
  by_cases hb : |1 - h| ^ N ≤ (1 + (N : ℝ) * h)⁻¹
  · let a := R / (1 + (N : ℝ) * h)
    have ha : 0 ≤ a := by dsimp [a]; positivity
    refine ⟨scaledHuber L a, (fun y => L * clippedGradient a y),
      scalarGD h (clippedGradient a) R, scaledHuber_convex hL.le a,
      scaledHuber_hasGradientAt L a, scaledHuber_lipschitz hL.le a,
      scaledHuber_minimum hL.le ha, rfl, ?_, ?_⟩
    · exact scalarGD_scaled_recurrence hL.ne' h R (clippedGradient a)
    · rw [max_eq_left hb]
      exact huber_terminal_gradient N hh hL hR
  · refine ⟨quadraticFunction L, (fun y => L * y), scalarGD h id R,
      quadraticFunction_convex hL.le, quadraticFunction_hasGradientAt L,
      quadraticFunction_lipschitz hL.le, quadraticFunction_minimum hL.le,
      rfl, ?_, ?_⟩
    · exact scalarGD_scaled_recurrence hL.ne' h R id
    · rw [max_eq_right (le_of_not_ge hb)]
      exact quadratic_terminal_gradient N hL hR

end THGGradient
