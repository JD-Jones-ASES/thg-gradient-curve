module

public import Mathlib

/-! Exact finite interpolation identities, independent of multiplier signs. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace
open Finset

namespace THGGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def interpolationQ (x g : ℕ → E) (f : ℕ → ℝ) (i j : ℕ) : ℝ :=
  2 * (f i - f j) - 2 * ⟪g j, x i - x j⟫_ℝ - ‖g i - g j‖ ^ 2

def starQ (x g : ℕ → E) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  -2 * f i + 2 * ⟪g i, x i⟫_ℝ - ‖g i‖ ^ 2

def toStarQ (g : ℕ → E) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  2 * f i - ‖g i‖ ^ 2

theorem trajectory_closed (N : ℕ) (h : ℝ) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i) :
    ∀ i ≤ N, x i = x 0 - h • ∑ k ∈ range i, g k := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    rw [hx i (by omega), ih (by omega), sum_range_succ, smul_add]
    abel

theorem distance_telescope (N : ℕ) (h : ℝ) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i) :
    ‖x 0‖ ^ 2 - ‖x N‖ ^ 2 =
      ∑ i ∈ range N, (2 * h * ⟪g i, x i⟫_ℝ - h ^ 2 * ‖g i‖ ^ 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ← ih (fun i hi => hx i (by omega)), hx N (by omega)]
    simp only [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    rw [real_inner_comm (x N) (g N)]
    ring

theorem symmetric_bilinear_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (g : ι → E)
    (hoff : ∀ i j, i ≠ j → M i j + M j i = 0) :
    ∑ i, ∑ j, M i j * ⟪g i, g j⟫_ℝ = ∑ i, M i i * ‖g i‖ ^ 2 := by
  have htranspose : (∑ i, ∑ j, M j i * ⟪g i, g j⟫_ℝ) =
      ∑ i, ∑ j, M i j * ⟪g i, g j⟫_ℝ := by
    rw [sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    rw [real_inner_comm]
  have hdouble : 2 * (∑ i, ∑ j, M i j * ⟪g i, g j⟫_ℝ) =
      ∑ i, ∑ j, (M i j + M j i) * ⟪g i, g j⟫_ℝ := by
    simp only [add_mul, sum_add_distrib]
    rw [htranspose]
    ring
  have hdiag : (∑ i, ∑ j, (M i j + M j i) * ⟪g i, g j⟫_ℝ) =
      2 * ∑ i, M i i * ‖g i‖ ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [sum_eq_single i]
    · rw [real_inner_self_eq_norm_sq]
      ring
    · intro j _ hji
      rw [hoff i j (Ne.symm hji), zero_mul]
    · simp
  linarith

/-- Weighted differences collect into the outgoing-minus-incoming divergence. -/
theorem sum_weighted_difference {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (v : ι → ℝ) :
    (∑ i, ∑ j, w i j * (v i - v j)) =
      ∑ i, (∑ j, (w i j - w j i)) * v i := by
  simp only [mul_sub, sum_sub_distrib, sub_mul, sum_mul]
  rw [sum_comm (f := fun i j => w i j * v j)]

/-- The two diagonal norm contributions collect into row-plus-column sums. -/
theorem sum_weighted_pair {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (v : ι → ℝ) :
    (∑ i, ∑ j, w i j * (v i + v j)) =
      ∑ i, (∑ j, (w i j + w j i)) * v i := by
  simp only [mul_add, sum_add_distrib, add_mul, sum_mul]
  rw [sum_comm (f := fun i j => w i j * v j)]

/-- General finite-data expansion before any mixed coefficient cancellation. -/
theorem weighted_interpolation_expansion {ι : Type*} [Fintype ι]
    (w a : ι → ι → ℝ) (f : ι → ℝ) (x g : ι → E) (X : E) (h : ℝ)
    (hx : ∀ i, x i = X - h • ∑ j, (a i j) • g j) :
    (∑ i, ∑ j, w i j *
      (2 * (f i - f j) - 2 * ⟪g j, x i - x j⟫_ℝ - ‖g i - g j‖ ^ 2)) =
      (∑ i, 2 * (∑ j, (w i j - w j i)) * f i)
      + 2 * (∑ i, ∑ j,
        (w i j + h * ∑ k, w k i * (a k j - a i j)) * ⟪g i, g j⟫_ℝ)
      - ∑ i, (∑ j, (w i j + w j i)) * ‖g i‖ ^ 2 := by
  have hipos (i j : ι) : ⟪g j, x i - x j⟫_ℝ =
      -h * ∑ k, (a i k - a j k) * ⟪g j, g k⟫_ℝ := by
    rw [hx i, hx j]
    have hv : (X - h • ∑ k, a i k • g k) - (X - h • ∑ k, a j k • g k) =
        -h • ∑ k, (a i k - a j k) • g k := by
      simp only [sub_smul, sum_sub_distrib, neg_smul, smul_sub]
      abel
    rw [hv, inner_smul_right, inner_sum]
    simp_rw [inner_smul_right]
  have hpos : (∑ i, ∑ j, w i j * ⟪g j, x i - x j⟫_ℝ) =
      -h * ∑ i, ∑ j, (∑ k, w k i * (a k j - a i j)) * ⟪g i, g j⟫_ℝ := by
    simp_rw [hipos, mul_sum, sum_mul]
    calc
      _ = ∑ i, ∑ j, ∑ k, -h * (w i j * (a i k - a j k) * ⟪g j, g k⟫_ℝ) := by
        apply sum_congr rfl; intro i _
        apply sum_congr rfl; intro j _
        apply sum_congr rfl; intro k _
        ring
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl; intro i _
        rw [sum_comm]
        simp only [mul_sum]
  have hraw : (∑ i, ∑ j, w i j *
      (2 * (f i - f j) - 2 * ⟪g j, x i - x j⟫_ℝ - ‖g i - g j‖ ^ 2)) =
      2 * (∑ i, ∑ j, w i j * (f i - f j))
      - 2 * (∑ i, ∑ j, w i j * ⟪g j, x i - x j⟫_ℝ)
      - (∑ i, ∑ j, w i j * (‖g i‖ ^ 2 + ‖g j‖ ^ 2))
      + 2 * (∑ i, ∑ j, w i j * ⟪g i, g j⟫_ℝ) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    rw [norm_sub_sq_real]
    ring
  rw [hraw, hpos, sum_weighted_difference, sum_weighted_pair]
  simp only [add_mul, sum_add_distrib, ← mul_sum, mul_assoc]
  ring

/-- Vanishing mixed coefficients leave precisely the stated diagonal coefficients. -/
theorem weighted_interpolation_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w a : ι → ι → ℝ) (c f : ι → ℝ) (x g : ι → E) (X : E) (h : ℝ)
    (hx : ∀ i, x i = X - h • ∑ j, (a i j) • g j)
    (hoff : ∀ i j, i ≠ j →
      (w i j + h * ∑ k, w k i * (a k j - a i j))
      + (w j i + h * ∑ k, w k j * (a k i - a j i)) = 0)
    (hdiag : ∀ i, 2 * (w i i + h * ∑ k, w k i * (a k i - a i i))
      - (∑ j, (w i j + w j i)) = c i) :
    (∑ i, ∑ j, w i j *
      (2 * (f i - f j) - 2 * ⟪g j, x i - x j⟫_ℝ - ‖g i - g j‖ ^ 2)) =
      (∑ i, 2 * (∑ j, (w i j - w j i)) * f i)
      + ∑ i, c i * ‖g i‖ ^ 2 := by
  rw [weighted_interpolation_expansion w a f x g X h hx,
    symmetric_bilinear_sum (fun i j => w i j + h * ∑ k, w k i * (a k j - a i j)) g hoff]
  rw [add_sub_assoc]
  congr 1
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← hdiag i]
  ring

/-- The scalar coefficient matrix obtained after substituting a gradient trajectory. -/
def gradientCoefficient (N : ℕ) (h : ℝ) (w : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  w i j + h * ∑ k ∈ range (N + 1), w k i *
    ((if j < k then 1 else 0) - (if j < i then 1 else 0))

/-- Outgoing-minus-incoming weight at a datum. -/
def weightDivergence (N : ℕ) (w : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range (N + 1), (w i j - w j i)

/-- Total divergence vanishes for every finite weight matrix. -/
theorem sum_weightDivergence (N : ℕ) (w : ℕ → ℕ → ℝ) :
    (∑ i ∈ range (N + 1), weightDivergence N w i) = 0 := by
  simp only [weightDivergence, sum_sub_distrib]
  rw [sum_comm (f := fun i j => w j i)]
  exact sub_self _

private theorem sum_fin_prefix (N k : ℕ) (hk : k ≤ N + 1) (g : ℕ → E) :
    (∑ j : Fin (N + 1), (if (j : ℕ) < k then (1 : ℝ) else 0) • g j) =
      ∑ j ∈ range k, g j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (if j < k then (1 : ℝ) else 0) • g j)]
  simp only [ite_smul, one_smul, zero_smul]
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  omega

/-- For a gradient trajectory, the only obstructions to a diagonal decomposition are
its explicitly displayed mixed coefficient equations. -/
theorem trajectory_weighted_diagonal (N : ℕ) (h : ℝ) (w : ℕ → ℕ → ℝ)
    (c f : ℕ → ℝ) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hoff : ∀ i ≤ N, ∀ j ≤ N, i ≠ j →
      gradientCoefficient N h w i j + gradientCoefficient N h w j i = 0)
    (hdiag : ∀ i ≤ N, 2 * gradientCoefficient N h w i i
      - (∑ j ∈ range (N + 1), (w i j + w j i)) = c i) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j) =
      (∑ i ∈ range (N + 1), 2 * weightDivergence N w i * f i)
      + ∑ i ∈ range (N + 1), c i * ‖g i‖ ^ 2 := by
  have hxf (i : Fin (N + 1)) : x i = x 0 - h •
      ∑ j : Fin (N + 1), (if (j : ℕ) < (i : ℕ) then (1 : ℝ) else 0) • g j := by
    rw [sum_fin_prefix N i (by omega)]
    exact trajectory_closed N h x g hx i (by omega)
  have hoff' (i j : Fin (N + 1)) (hij : i ≠ j) :
      ((w i j) + h * ∑ k : Fin (N + 1), w k i *
        ((if (j : ℕ) < k then (1 : ℝ) else 0) - (if (j : ℕ) < i then 1 else 0)))
      + ((w j i) + h * ∑ k : Fin (N + 1), w k j *
        ((if (i : ℕ) < k then (1 : ℝ) else 0) - (if (i : ℕ) < j then 1 else 0))) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => w k i *
      ((if (j : ℕ) < k then (1 : ℝ) else 0) - (if (j : ℕ) < i then 1 else 0))),
      Fin.sum_univ_eq_sum_range (fun k => w k j *
      ((if (i : ℕ) < k then (1 : ℝ) else 0) - (if (i : ℕ) < j then 1 else 0)))]
    exact hoff i (by omega) j (by omega) (fun he => hij (Fin.ext he))
  have hdiag' (i : Fin (N + 1)) :
      2 * (w i i + h * ∑ k : Fin (N + 1), w k i *
        ((if (i : ℕ) < k then (1 : ℝ) else 0) - (if (i : ℕ) < i then 1 else 0)))
        - (∑ j : Fin (N + 1), (w i j + w j i)) = c i := by
    rw [Fin.sum_univ_eq_sum_range (fun k => w k i *
      ((if (i : ℕ) < k then (1 : ℝ) else 0) - (if (i : ℕ) < i then 1 else 0))),
      Fin.sum_univ_eq_sum_range (fun j => w i j + w j i)]
    exact hdiag i (by omega)
  have hh := weighted_interpolation_diagonal
    (fun i j : Fin (N + 1) => w i j)
    (fun i j : Fin (N + 1) => if (j : ℕ) < i then (1 : ℝ) else 0)
    (fun i : Fin (N + 1) => c i) (fun i : Fin (N + 1) => f i)
    (fun i : Fin (N + 1) => x i) (fun i : Fin (N + 1) => g i)
    (x 0) h hxf hoff' hdiag'
  have hq (i : ℕ) : (∑ j : Fin (N + 1), w i j *
      (2 * (f i - f j) - 2 * ⟪g j, x i - x j⟫_ℝ - ‖g i - g j‖ ^ 2)) =
      ∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j :=
    Fin.sum_univ_eq_sum_range (fun j => w i j * interpolationQ x g f i j) _
  have hd (i : ℕ) : (∑ j : Fin (N + 1), (w i j - w j i)) =
      weightDivergence N w i :=
    Fin.sum_univ_eq_sum_range (fun j => w i j - w j i) _
  simp_rw [hq, hd] at hh
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j),
    Fin.sum_univ_eq_sum_range (fun i => 2 * weightDivergence N w i * f i),
    Fin.sum_univ_eq_sum_range (fun i => c i * ‖g i‖ ^ 2)] at hh
  exact hh

/-- The coefficient equations imply the exact weighted interpolation decomposition. -/
theorem trajectory_weighted_decomposition (N : ℕ) (h t : ℝ) (w : ℕ → ℕ → ℝ)
    (f : ℕ → ℝ) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hoff : ∀ i ≤ N, ∀ j ≤ N, i ≠ j →
      gradientCoefficient N h w i j + gradientCoefficient N h w j i = 0)
    (hdiag : ∀ i ≤ N, 2 * gradientCoefficient N h w i i
      - (∑ j ∈ range (N + 1), (w i j + w j i)) =
        -weightDivergence N w i + if i < N then 1 - (h - 1) ^ 2 else -(t ^ 2 - 1)) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), w i j * interpolationQ x g f i j) =
      (∑ i ∈ range N, 2 * weightDivergence N w i *
        ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2)))
      + (1 - (h - 1) ^ 2) * (∑ i ∈ range N, ‖g i‖ ^ 2)
      - (t ^ 2 - 1) * ‖g N‖ ^ 2 := by
  rw [trajectory_weighted_diagonal N h w _ f x g hx hoff hdiag]
  have hdiv := sum_weightDivergence N w
  rw [sum_range_succ] at hdiv
  rw [sum_range_succ, sum_range_succ]
  simp only [lt_self_iff_false, ite_false]
  have hsum : (∑ i ∈ range N, 2 * weightDivergence N w i * f i)
      + (∑ i ∈ range N, (-weightDivergence N w i +
        if i < N then 1 - (h - 1) ^ 2 else -(t ^ 2 - 1)) * ‖g i‖ ^ 2) =
      (∑ i ∈ range N, 2 * weightDivergence N w i *
        ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2)))
      + (1 - (h - 1) ^ 2) * (∑ i ∈ range N, ‖g i‖ ^ 2)
      + (∑ i ∈ range N, weightDivergence N w i) * (2 * f N - ‖g N‖ ^ 2) := by
    simp only [mul_sum, sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [ite_eq_left (mem_range.mp hi)]
    ring
  have hc := congrArg (fun q : ℝ => q * (2 * f N - ‖g N‖ ^ 2)) hdiv
  nlinarith

/-- The weighted interpolation identity completes exactly against a zero minimizer.
The sole algebraic premise is the preceding weighted decomposition; no signs are needed. -/
theorem certificate_completion (N : ℕ) (h t W : ℝ) (d f : ℕ → ℝ) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hW : W = (∑ i ∈ range N, 2 * d i *
        ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2)))
      + (1 - (h - 1) ^ 2) * (∑ i ∈ range N, ‖g i‖ ^ 2)
      - (t ^ 2 - 1) * ‖g N‖ ^ 2) :
    ‖x 0‖ ^ 2 - t ^ 2 * ‖g N‖ ^ 2 =
      W + h * (∑ i ∈ range N, starQ x g f i) + starQ x g f N
      + (∑ i ∈ range N, (h - d i) * toStarQ g f i)
      + (1 + ∑ i ∈ range N, d i) * toStarQ g f N
      + ‖x N - g N‖ ^ 2 := by
  have hterm (i : ℕ) :
      2 * d i * ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2))
        + (1 - (h - 1) ^ 2) * ‖g i‖ ^ 2 + h * starQ x g f i
        + (h - d i) * toStarQ g f i + d i * toStarQ g f N =
      2 * h * ⟪g i, x i⟫_ℝ - h ^ 2 * ‖g i‖ ^ 2 := by
    dsimp [starQ, toStarQ]
    ring
  have hsum := sum_congr rfl (fun i (_ : i ∈ range N) => hterm i)
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul] at hsum
  have hterminal : starQ x g f N + toStarQ g f N + ‖x N - g N‖ ^ 2 =
      ‖x N‖ ^ 2 - ‖g N‖ ^ 2 := by
    simp only [starQ, toStarQ, norm_sub_sq_real]
    rw [real_inner_comm (x N) (g N)]
    ring
  have htel := distance_telescope N h x g hx
  rw [hW]
  nlinarith

/-- At balance, the common divergence is the step and the exact stronger potential is retained. -/
theorem balanced_certificate_completion (N : ℕ) (h W : ℝ) (f : ℕ → ℝ) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hW : W = (∑ i ∈ range N, 2 * h *
        ((f i - ‖g i‖ ^ 2 / 2) - (f N - ‖g N‖ ^ 2 / 2)))
      + (1 - (h - 1) ^ 2) * (∑ i ∈ range N, ‖g i‖ ^ 2)
      - ((1 + N * h) ^ 2 - 1) * ‖g N‖ ^ 2) :
    ‖x 0‖ ^ 2 - ‖x N‖ ^ 2 - 2 * N * h * f N
      - N * h * (1 + N * h) * ‖g N‖ ^ 2 =
      W + h * ∑ i ∈ range N, starQ x g f i := by
  have hh := certificate_completion N h (1 + N * h) W (fun _ => h) f x g hx hW
  simp only [sub_self, zero_mul, sum_const_zero, add_zero, sum_const, card_range,
    nsmul_eq_mul, starQ, toStarQ, norm_sub_sq_real] at hh
  rw [real_inner_comm (x N) (g N)] at hh
  dsimp [starQ]
  nlinarith

end THGGradient
