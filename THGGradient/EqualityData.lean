module
public import THGGradient.FactorIdentity

/-! Exact trajectory rigidity from vanishing interpolation remainders.
These lemmas classify the sampled data once the certificate has forced its remainders to vanish. -/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace
open Finset
namespace THGGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Vanishing starred and history interpolation implies residual orthogonality. -/
theorem zero_interpolation_residual_orthogonal (x g : ℕ → E) (f : ℕ → ℝ)
    (i j : ℕ) (hi : starQ x g f i = 0) (hj : starQ x g f j = 0)
    (hij : interpolationQ x g f i j = 0) :
    ⟪g i - g j, x i - g i⟫_ℝ = 0 := by
  dsimp [starQ] at hi hj
  dsimp [interpolationQ] at hij
  rw [norm_sub_sq_real] at hij
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
  have hcomm : ⟪g i, g j⟫_ℝ = ⟪g j, g i⟫_ℝ := real_inner_comm _ _
  simp only [inner_sub_right] at hij
  nlinarith [hcomm]

/-- Every residual is orthogonal to every sampled gradient difference. -/
theorem zero_interpolation_all_differences (N : ℕ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hstar : ∀ i ≤ N, starQ x g f i = 0)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, interpolationQ x g f i j = 0)
    (i j k : ℕ) (hi : i ≤ N) (hj : j ≤ N) (hk : k ≤ N) :
    ⟪g j - g k, x i - g i⟫_ℝ = 0 := by
  have hij := zero_interpolation_residual_orthogonal x g f i j
    (hstar i hi) (hstar j hj) (hQ i hi j hj)
  have hik := zero_interpolation_residual_orthogonal x g f i k
    (hstar i hi) (hstar k hk) (hQ i hi k hk)
  simp only [inner_sub_left] at hij hik ⊢
  linarith

/-- Vanishing interpolation and a terminal zero residual give the complete
orthogonal constant-plus-oscillating decomposition. -/
theorem zero_interpolation_decomposition (N : ℕ) (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hstar : ∀ i ≤ N, starQ x g f i = 0)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, interpolationQ x g f i j = 0)
    (hterminal : x N = g N) :
    ∃ a b : E, ⟪a, b⟫_ℝ = 0 ∧ ∀ i ≤ N,
      g i = b + (1 - h) ^ i • a ∧
      x i = (1 + ((N : ℝ) - i) * h) • b + (1 - h) ^ i • a ∧
      f i = (((N : ℝ) - i) * h + 1 / 2) * ‖b‖ ^ 2
        + ((1 - h) ^ i) ^ 2 / 2 * ‖a‖ ^ 2 := by
  let z : ℕ → E := fun i => x i - g i
  let c : ℕ → E := fun i => z i - z (i + 1)
  have hzN : z N = 0 := by simp [z, hterminal]
  have hzorth (i j k : ℕ) (hi : i ≤ N) (hj : j ≤ N) (hk : k ≤ N) :
      ⟪g j - g k, z i⟫_ℝ = 0 :=
    zero_interpolation_all_differences N x g f hstar hQ i j k hi hj hk
  have hcg (i : ℕ) (hi : i < N) : c i = (h - 1) • g i + g (i + 1) := by
    dsimp [c, z]
    rw [hx i hi]
    module
  have hcd (i j : ℕ) (hi : i < N) (hj : j ≤ N) : ⟪c i - c 0, z j⟫_ℝ = 0 := by
    rw [hcg i hi, hcg 0 hN]
    have he : ((h - 1) • g i + g (i + 1)) - ((h - 1) • g 0 + g (0 + 1)) =
        (h - 1) • (g i - g 0) + (g (i + 1) - g 1) := by module
    rw [he, inner_add_left, real_inner_smul_left, hzorth j i 0 hj (by omega) (by omega),
      hzorth j (i + 1) 1 hj (by omega) (by omega)]
    ring
  have hc (i : ℕ) (hi : i < N) : c i = c 0 := by
    have he : ⟪c i - c 0, c i - c 0⟫_ℝ = 0 := by
      have h1 := hcd i i hi (by omega)
      have h2 := hcd i (i + 1) hi (by omega)
      have h3 := hcd i 0 hi (by omega)
      have h4 := hcd i 1 hi (by omega)
      simp only [c, inner_sub_right] at h1 h2 h3 h4 ⊢
      linarith
    exact sub_eq_zero.mp (inner_self_eq_zero.mp he)
  have hzrec (i : ℕ) (hi : i < N) : z (i + 1) = z i - (1 : ℝ) • c 0 := by
    have he := hc i hi
    change z i - z (i + 1) = c 0 at he
    simp only [one_smul]
    calc
      z (i + 1) = z i - (z i - z (i + 1)) := by abel
      _ = z i - c 0 := by rw [he]
  have hzclosed (i : ℕ) (hi : i ≤ N) : z i = z 0 - (i : ℝ) • c 0 := by
    simpa only [sum_const, card_range, nsmul_eq_mul, one_smul, Nat.cast_smul_eq_nsmul] using
      trajectory_closed N 1 z (fun _ => c 0) hzrec i hi
  have hz0 : z 0 = (N : ℝ) • c 0 := by
    have he := hzclosed N le_rfl
    rw [hzN] at he
    exact sub_eq_zero.mp he.symm
  have hzformula (i : ℕ) (hi : i ≤ N) : z i = ((N : ℝ) - i) • c 0 := by
    rw [hzclosed i hi, hz0, sub_smul]
  let b : E := h⁻¹ • c 0
  let a : E := g 0 - b
  have hcb : c 0 = h • b := by simp [b, smul_smul, ne_of_gt hh]
  have hgr (i : ℕ) (hi : i < N) : g (i + 1) = (1 - h) • g i + h • b := by
    have he := hcg i hi
    rw [hc i hi, hcb] at he
    calc
      g (i + 1) = ((h - 1) • g i + g (i + 1)) - (h - 1) • g i := by abel
      _ = h • b - (h - 1) • g i := by rw [← he]
      _ = (1 - h) • g i + h • b := by module
  have hgformula (i : ℕ) (hi : i ≤ N) : g i = b + (1 - h) ^ i • a := by
    induction i with
    | zero => simp [a]
    | succ i ih =>
      rw [hgr i (by omega), ih (by omega), pow_succ]
      module
  have hxformula (i : ℕ) (hi : i ≤ N) :
      x i = (1 + ((N : ℝ) - i) * h) • b + (1 - h) ^ i • a := by
    have he := hzformula i hi
    rw [hcb, smul_smul] at he
    dsimp [z] at he
    rw [hgformula i hi] at he
    calc
      x i = (((N : ℝ) - i) * h) • b + (b + (1 - h) ^ i • a) :=
        (sub_eq_iff_eq_add).mp he
      _ = _ := by module
  have horth : ⟪a, b⟫_ℝ = 0 := by
    have he : ⟪g 0 - g 1, c 0⟫_ℝ = 0 := by
      dsimp [c]
      rw [inner_sub_right, hzorth 0 0 1 (by omega) (by omega) (by omega),
        hzorth 1 0 1 (by omega) (by omega) (by omega)]
      ring
    rw [hgformula 0 (by omega), hgformula 1 (by omega), hcb] at he
    have hv : (b + (1 - h) ^ 0 • a) - (b + (1 - h) ^ 1 • a) = h • a := by
      simp only [pow_zero, pow_one, one_smul]
      module
    rw [hv, real_inner_smul_left, inner_smul_right] at he
    have hne := ne_of_gt hh
    exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hne)).resolve_left hne
  refine ⟨a, b, horth, ?_⟩
  intro i hi
  refine ⟨hgformula i hi, hxformula i hi, ?_⟩
  have hs := hstar i hi
  dsimp [starQ] at hs
  rw [hgformula i hi, hxformula i hi] at hs
  simp only [inner_add_left, inner_add_right, inner_smul_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, horth, mul_zero, add_zero] at hs
  nlinarith

/-- A zero initial value-to-minimizer remainder removes the constant component. -/
theorem zero_interpolation_quadratic (N : ℕ) (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hstar : ∀ i ≤ N, starQ x g f i = 0)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, interpolationQ x g f i j = 0)
    (hterminal : x N = g N) (hzero : toStarQ g f 0 = 0) :
    ∀ i ≤ N, x i = (1 - h) ^ i • x 0 ∧ g i = x i ∧ f i = ‖x i‖ ^ 2 / 2 := by
  obtain ⟨a, b, hab, hform⟩ := zero_interpolation_decomposition N hN hh x g f hx hstar hQ hterminal
  have hform0 := hform 0 (by omega)
  have hg0 : g 0 = b + a := by simpa using hform0.1
  have hx0 : x 0 = (1 + N * h) • b + a := by simpa using hform0.2.1
  have hf0 : f 0 = (N * h + 1 / 2) * ‖b‖ ^ 2 + ‖a‖ ^ 2 / 2 := by
    convert hform0.2.2 using 1
    simp
    ring
  have hba : ⟪b, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact hab
  dsimp [toStarQ] at hzero
  rw [hg0, hf0, norm_add_sq_real, hba] at hzero
  have hNh : 0 < (N : ℝ) * h := mul_pos (Nat.cast_pos.mpr hN) hh
  have hb : b = 0 := by
    have hn : ‖b‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖b‖]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg b])
  subst b
  simp only [smul_zero, zero_add] at hx0
  intro i hi
  obtain ⟨hgi, hxi, hfi⟩ := hform i hi
  simp only [zero_add, smul_zero, norm_zero] at hgi hxi hfi
  refine ⟨by rw [hxi, hx0], by rw [hgi, hxi], ?_⟩
  rw [hxi, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hfi]
  ring

/-- A constant sampled gradient and vanishing starred remainders give the Huber trajectory. -/
theorem constant_gradient_decomposition (N : ℕ) (h : ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i)
    (hg : ∀ i ≤ N, g i = g N)
    (hstar : ∀ i ≤ N, starQ x g f i = 0) (hterminal : x N = g N) :
    ∀ i ≤ N, x i = (1 + ((N : ℝ) - i) * h) • g N ∧
      f i = (((N : ℝ) - i) * h + 1 / 2) * ‖g N‖ ^ 2 := by
  have hsum (i : ℕ) (hi : i ≤ N) : (∑ k ∈ range i, g k) = (i : ℝ) • g N := by
    calc
      _ = ∑ _k ∈ range i, g N := by
        apply sum_congr rfl
        intro k hk
        exact hg k (by have := mem_range.mp hk; omega)
      _ = _ := by simp [Nat.cast_smul_eq_nsmul]
  have hclosed (i : ℕ) (hi : i ≤ N) : x i = x 0 - (h * i) • g N := by
    rw [trajectory_closed N h x g hx i hi, hsum i hi, smul_smul]
  have hx0 : x 0 = (1 + N * h) • g N := by
    have he := hclosed N le_rfl
    rw [hterminal] at he
    calc
      x 0 = g N + (h * N) • g N := by exact (eq_sub_iff_add_eq).mp he |>.symm
      _ = _ := by module
  intro i hi
  have hxi : x i = (1 + ((N : ℝ) - i) * h) • g N := by
    rw [hclosed i hi, hx0]
    module
  refine ⟨hxi, ?_⟩
  have hs := hstar i hi
  dsimp [starQ] at hs
  rw [hg i hi, hxi, inner_smul_right, real_inner_self_eq_norm_sq] at hs
  nlinarith

end THGGradient
