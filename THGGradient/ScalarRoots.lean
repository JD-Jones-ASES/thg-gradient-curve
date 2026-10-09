module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-!
# Nonnegative quadratic roots

The scalar root used by the uniform certificate is handled by its polynomial
identity and order properties. No downstream argument needs to unfold a square
root. All results in this file are exact real statements.
-/

@[expose] public section

namespace THGGradient

/-- The nonnegative root of `z² + B*z - Z`, when `B > 0` and `Z ≥ 0`. -/
noncomputable def positiveRoot (B Z : ℝ) : ℝ :=
  (Real.sqrt (B ^ 2 + 4 * Z) - B) / 2

/-- The scalar quadratic whose distinguished root is `positiveRoot`. -/
def rootPolynomial (B Z z : ℝ) : ℝ := z ^ 2 + B * z - Z

theorem positiveRoot_nonneg {B Z : ℝ} (hB : 0 < B) (hZ : 0 ≤ Z) :
    0 ≤ positiveRoot B Z := by
  have hs := Real.sq_sqrt (show 0 ≤ B ^ 2 + 4 * Z by positivity)
  have hn := Real.sqrt_nonneg (B ^ 2 + 4 * Z)
  unfold positiveRoot
  nlinarith [sq_nonneg (Real.sqrt (B ^ 2 + 4 * Z) - B)]

theorem positiveRoot_equation {B Z : ℝ} (hZ : 0 ≤ Z) :
    rootPolynomial B Z (positiveRoot B Z) = 0 := by
  have hs := Real.sq_sqrt (show 0 ≤ B ^ 2 + 4 * Z by positivity)
  unfold positiveRoot rootPolynomial
  nlinarith

theorem rootPolynomial_strictMonoOn {B Z : ℝ} (hB : 0 < B) :
    StrictMonoOn (rootPolynomial B Z) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hprod : 0 < (y - x) * (y + x + B) := by
    apply mul_pos <;> linarith [hx, hy]
  unfold rootPolynomial
  nlinarith

theorem positiveRoot_unique {B Z z : ℝ} (hB : 0 < B) (hZ : 0 ≤ Z)
    (hz : 0 ≤ z) (heq : rootPolynomial B Z z = 0) : z = positiveRoot B Z := by
  apply (rootPolynomial_strictMonoOn hB).injOn hz (positiveRoot_nonneg hB hZ)
  rw [heq, positiveRoot_equation hZ]

theorem positiveRoot_pos {B Z : ℝ} (hB : 0 < B) (hZ : 0 < Z) :
    0 < positiveRoot B Z := by
  have hnon := positiveRoot_nonneg hB hZ.le
  have heq := positiveRoot_equation (B := B) hZ.le
  unfold rootPolynomial at heq
  rcases lt_or_eq_of_le hnon with h | h
  · exact h
  · rw [← h] at heq
    linarith

@[simp] theorem positiveRoot_zero {B : ℝ} (hB : 0 < B) :
    positiveRoot B 0 = 0 := by
  exact (positiveRoot_unique hB le_rfl le_rfl (by simp [rootPolynomial])).symm

theorem positiveRoot_lt_iff {B Z z : ℝ} (hB : 0 < B) (hZ : 0 ≤ Z)
    (hz : 0 ≤ z) : positiveRoot B Z < z ↔ 0 < rootPolynomial B Z z := by
  have hm := rootPolynomial_strictMonoOn (Z := Z) hB
  have hr := positiveRoot_nonneg hB hZ
  constructor
  · intro h
    simpa [positiveRoot_equation hZ] using hm hr hz h
  · intro h
    by_contra hn
    have hh := hm.monotoneOn hz hr (le_of_not_gt hn)
    rw [positiveRoot_equation hZ] at hh
    linarith

theorem le_positiveRoot_iff {B Z z : ℝ} (hB : 0 < B) (hZ : 0 ≤ Z)
    (hz : 0 ≤ z) : z ≤ positiveRoot B Z ↔ rootPolynomial B Z z ≤ 0 := by
  rw [← not_lt, positiveRoot_lt_iff hB hZ hz, not_lt]

theorem positiveRoot_le_iff {B Z z : ℝ} (hB : 0 < B) (hZ : 0 ≤ Z)
    (hz : 0 ≤ z) : positiveRoot B Z ≤ z ↔ 0 ≤ rootPolynomial B Z z := by
  have hm := rootPolynomial_strictMonoOn (Z := Z) hB
  have hr := positiveRoot_nonneg hB hZ
  constructor
  · intro h
    simpa [positiveRoot_equation hZ] using hm.monotoneOn hr hz h
  · intro h
    by_contra hn
    have hh := hm hz hr (lt_of_not_ge hn)
    rw [positiveRoot_equation hZ] at hh
    linarith

theorem lt_positiveRoot_iff {B Z z : ℝ} (hB : 0 < B) (hZ : 0 ≤ Z)
    (hz : 0 ≤ z) : z < positiveRoot B Z ↔ rootPolynomial B Z z < 0 := by
  rw [← not_le, positiveRoot_le_iff hB hZ hz, not_le]

/-- Root comparison using the value of a second polynomial at the first root. -/
theorem positiveRoot_le_of_polynomial_le {B₁ Z₁ B₂ Z₂ : ℝ}
    (hB₁ : 0 < B₁) (hZ₁ : 0 ≤ Z₁) (hB₂ : 0 < B₂) (hZ₂ : 0 ≤ Z₂)
    (hp : rootPolynomial B₂ Z₂ (positiveRoot B₁ Z₁) ≤ 0) :
    positiveRoot B₁ Z₁ ≤ positiveRoot B₂ Z₂ :=
  (le_positiveRoot_iff hB₂ hZ₂ (positiveRoot_nonneg hB₁ hZ₁)).2 hp

end THGGradient
