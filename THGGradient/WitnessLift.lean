module

public import THGGradient.Witnesses

@[expose] public section

namespace THGGradient

open scoped RealInnerProductSpace

section Lift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Composition with a linear coordinate has the expected actual Hilbert gradient. -/
theorem scalar_lift_hasGradientAt {f g : ℝ → ℝ}
    (hg : ∀ t, HasGradientAt f (g t) t) (u x : E) :
    HasGradientAt (fun y => f ⟪u, y⟫) (g ⟪u, x⟫ • u) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (hg ⟪u, x⟫).hasDerivAt'.comp_hasFDerivAt x (innerSL ℝ u).hasFDerivAt
  have he : (InnerProductSpace.toDual ℝ E) (g ⟪u, x⟫ • u) =
      g ⟪u, x⟫ • innerSL ℝ u := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply]
  rw [he]
  exact hd

/-- Every unit direction carries a sharp actual smooth convex example. -/
theorem unit_vector_attainment (N : ℕ) {h L R : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (hR : 0 < R) (u : E) (hu : ‖u‖ = 1) :
    ∃ (f : E → ℝ) (g : E → E) (x : ℕ → E),
      ConvexOn ℝ Set.univ f ∧
      (∀ y, HasGradientAt f (g y) y) ∧
      (∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) ∧
      (∀ y, f 0 ≤ f y) ∧
      x 0 = R • u ∧ ‖x 0‖ = R ∧
      (∀ i, x (i + 1) = x i - (h / L) • g (x i)) ∧
      ‖g (x N)‖ = L * R * max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
  obtain ⟨f, g, x, hf, hg, hlip, hmin, hx0, hrec, hnorm⟩ :=
    scalar_attainment N hh hL hR
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  refine ⟨(fun y => f ⟪u, y⟫), (fun y => g ⟪u, y⟫ • u), (fun i => x i • u),
    ?_, scalar_lift_hasGradientAt hg u, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Set.preimage_univ, Function.comp_def,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply] using
      hf.comp_linearMap (innerSL ℝ u).toLinearMap
  · intro y z
    rw [← sub_smul, norm_smul, hu, mul_one]
    apply (hlip _ _).trans
    apply mul_le_mul_of_nonneg_left _ hL.le
    rw [← inner_sub_right]
    exact (norm_inner_le_norm u (y - z)).trans_eq (by rw [hu, one_mul])
  · intro y
    simpa only [inner_zero_right] using hmin ⟪u, y⟫
  · dsimp only
    rw [hx0]
  · dsimp only
    rw [hx0, norm_smul, hu, mul_one, Real.norm_of_nonneg hR.le]
  · intro i
    dsimp only
    rw [hrec i, sub_smul, real_inner_smul_right, huu, mul_one, smul_smul]
  · simpa only [real_inner_smul_right, huu, mul_one, norm_smul, hu] using hnorm

/-- Sharpness holds in every positive finite Euclidean dimension. -/
theorem euclidean_attainment (d N : ℕ) (hd : 0 < d) {h L R : ℝ}
    (hh : 0 ≤ h) (hL : 0 < L) (hR : 0 < R) :
    ∃ (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (x : ℕ → EuclideanSpace ℝ (Fin d)),
      ConvexOn ℝ Set.univ f ∧
      (∀ y, HasGradientAt f (g y) y) ∧
      (∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) ∧
      (∀ y, f 0 ≤ f y) ∧
      ‖x 0‖ = R ∧
      (∀ i, x (i + 1) = x i - (h / L) • g (x i)) ∧
      ‖g (x N)‖ = L * R * max ((1 + (N : ℝ) * h)⁻¹) (|1 - h| ^ N) := by
  let u : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ 1
  have hu : ‖u‖ = 1 := by simp [u]
  obtain ⟨f, g, x, hf, hg, hlip, hmin, _, hx0, hrec, hnorm⟩ :=
    unit_vector_attainment N hh hL hR u hu
  exact ⟨f, g, x, hf, hg, hlip, hmin, hx0, hrec, hnorm⟩

end Lift
end THGGradient
