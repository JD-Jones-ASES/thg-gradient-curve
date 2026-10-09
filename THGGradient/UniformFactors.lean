module

public import THGGradient.ScalarRoots
public import THGGradient.ScalarGeometric

/-!
# Uniform-divergence scalar construction

The definitions in this module use the exact real parameter `r = h - 1`.
They are independent of the optimization trajectory and the ambient dimension.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace THGGradient

def uniformRatio (h : ℝ) : ℝ := ((h - 1)⁻¹) ^ 2

def uniformMoment (h : ℝ) (n : ℕ) : ℝ := geometricMoment (uniformRatio h) n

def uniformSum (h : ℝ) (n : ℕ) : ℝ := momentSum (uniformRatio h) n

def uniformDelta (N : ℕ) (h : ℝ) : ℝ :=
  2 * (2 - h) * uniformSum h N / ((N : ℝ) * (N + 1))

theorem uniformRatio_gt_one {h : ℝ} (h1 : 1 < h) (h2 : h < 2) :
    1 < uniformRatio h := by
  have hr : 0 < h - 1 := by linarith
  have hr' : h - 1 < 1 := by linarith
  have hi : 1 < (h - 1)⁻¹ := (one_lt_inv₀ hr).2 hr'
  exact one_lt_pow₀ hi (by decide : 2 ≠ 0)

theorem uniformMoment_pos {h : ℝ} (h1 : 1 < h) (h2 : h < 2)
    {n : ℕ} (hn : 0 < n) : 0 < uniformMoment h n :=
  geometricMoment_pos (uniformRatio_gt_one h1 h2) hn

theorem uniformDelta_pos {N : ℕ} (hN : 0 < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2) : 0 < uniformDelta N h := by
  have hs : 0 < uniformSum h N := momentSum_pos (uniformRatio_gt_one h1 h2) hN
  unfold uniformDelta
  exact div_pos (by positivity) (by positivity)

theorem uniformRatio_mul {h : ℝ} (h1 : 1 < h) :
    uniformRatio h * (h - 1) ^ 2 = 1 := by
  unfold uniformRatio
  have hr : h - 1 ≠ 0 := by linarith
  field_simp

theorem uniformMoment_recurrence {h : ℝ} (h1 : 1 < h) (k : ℕ) :
    2 * ((h - 1) ^ 2 * uniformMoment h (k + 1) - uniformMoment h k) =
      1 - (h - 1) ^ 2 := by
  have ha := uniformRatio_mul h1
  unfold uniformMoment geometricMoment
  rw [pow_succ (uniformRatio h) k]
  have hh : uniformRatio h ^ k * (uniformRatio h * (h - 1) ^ 2) = uniformRatio h ^ k := by rw [ha, mul_one]
  nlinarith [hh]

theorem uniformSum_identity {h : ℝ} (h1 : 1 < h) (n : ℕ) :
    2 * (1 - (h - 1) ^ 2) * uniformSum h n =
      uniformRatio h ^ n - 1 - (n : ℝ) * (1 - (h - 1) ^ 2) := by
  have hs := momentSum_identity (uniformRatio h) n
  have ha := uniformRatio_mul h1
  have hh := congrArg (fun z : ℝ => z * (h - 1) ^ 2) hs
  change 2 * (uniformRatio h - 1) * uniformSum h n = _ at hs
  change (2 * (uniformRatio h - 1) * uniformSum h n) * (h - 1) ^ 2 = _ at hh
  linear_combination hh - (2 * uniformSum h n - uniformRatio h ^ n + 1 + n) * ha

theorem uniformDelta_identity {N : ℕ} (hN : 0 < N) {h : ℝ}
    (h1 : 1 < h) :
    h * uniformDelta N h * (N : ℝ) * (N + 1) =
      uniformRatio h ^ N - 1 - (N : ℝ) * (1 - (h - 1) ^ 2) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hn1 : (N + 1 : ℝ) ≠ 0 := by positivity
  have hs := uniformSum_identity h1 N
  unfold uniformDelta
  field_simp
  nlinarith

theorem uniformDelta_le_step {N : ℕ} (hN : 0 < N) {h : ℝ}
    (h1 : 1 < h) (_h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) : uniformDelta N h ≤ h := by
  have hi := uniformDelta_identity hN h1
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : 0 ≤ ((h - 1)⁻¹) ^ N := by positivity
  have hpow : uniformRatio h ^ N = (((h - 1)⁻¹) ^ N) ^ 2 := by
    simp only [uniformRatio, ← pow_mul, Nat.mul_comm]
  rw [hpow] at hi
  have hs : (((h - 1)⁻¹) ^ N) ^ 2 ≤ (1 + (N : ℝ) * h) ^ 2 := by
    exact sq_le_sq₀ ht (by positivity) |>.2 hupper
  have hd : 0 < h * (N : ℝ) * (N + 1) := by positivity
  have hp : (uniformDelta N h - h) * (h * (N : ℝ) * (N + 1)) ≤ 0 := by
    nlinarith
  by_contra hn
  have hpos := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hd
  linarith

/-- The strict upper branch leaves positive value-to-minimizer slack. -/
theorem uniformDelta_lt_step {N : ℕ} (hN : 0 < N) {h : ℝ}
    (h1 : 1 < h) (_h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N < 1 + (N : ℝ) * h) : uniformDelta N h < h := by
  have hi := uniformDelta_identity hN h1
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : 0 ≤ ((h - 1)⁻¹) ^ N := by positivity
  have hpow : uniformRatio h ^ N = (((h - 1)⁻¹) ^ N) ^ 2 := by
    simp only [uniformRatio, ← pow_mul, Nat.mul_comm]
  rw [hpow] at hi
  have hsq : (((h - 1)⁻¹) ^ N) ^ 2 < (1 + (N : ℝ) * h) ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hupper)
      (show 0 < 1 + (N : ℝ) * h + ((h - 1)⁻¹) ^ N by positivity)
    nlinarith
  have hd : 0 < h * (N : ℝ) * (N + 1) := by positivity
  have hp : (uniformDelta N h - h) * (h * (N : ℝ) * (N + 1)) < 0 := by nlinarith
  by_contra hge
  have hnon := mul_nonneg (show 0 ≤ uniformDelta N h - h by linarith) hd.le
  linarith

theorem uniformDelta_eq_step {N : ℕ} (hN : 0 < N) {h : ℝ}
    (h1 : 1 < h)
    (hbalance : ((h - 1)⁻¹) ^ N = 1 + (N : ℝ) * h) : uniformDelta N h = h := by
  have hi := uniformDelta_identity hN h1
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : uniformRatio h ^ N = (((h - 1)⁻¹) ^ N) ^ 2 := by
    simp only [uniformRatio, ← pow_mul, Nat.mul_comm]
  rw [hpow, hbalance] at hi
  have hd : h * (N : ℝ) * (N + 1) ≠ 0 := by positivity
  apply mul_right_cancel₀ hd
  nlinarith

/-- Coefficient `w_k(c)` in the auxiliary polynomial. -/
def uniformW (h c : ℝ) (k : ℕ) : ℝ :=
  (c * (k + 1) / uniformMoment h (k + 1) - (2 - h)) / h

/-- Constant `Z_k(c)` in the auxiliary polynomial. -/
def uniformZ (h c : ℝ) (k : ℕ) : ℝ :=
  (c * k * (k + 1) / 2 - (2 - h) * uniformSum h k) /
    (h * uniformMoment h (k + 1))

def uniformRoot (h c : ℝ) (k : ℕ) : ℝ :=
  positiveRoot (1 + uniformW h c k) (uniformZ h c k)

/-- The numerator polynomial, with all geometric denominators removed. -/
def uniformPolynomial (h c : ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  h * uniformMoment h (k + 1) * z ^ 2 +
    (2 * (h - 1) * uniformMoment h (k + 1) + c * (k + 1)) * z -
    c * k * (k + 1) / 2 + (2 - h) * uniformSum h k

theorem uniformPolynomial_eq {h : ℝ} (h1 : 1 < h) (h2 : h < 2)
    (c : ℝ) (k : ℕ) (z : ℝ) :
    uniformPolynomial h c k z = h * uniformMoment h (k + 1) *
      rootPolynomial (1 + uniformW h c k) (uniformZ h c k) z := by
  have hh : h ≠ 0 := by linarith
  have hp : uniformMoment h (k + 1) ≠ 0 := (uniformMoment_pos h1 h2 (by omega)).ne'
  unfold uniformPolynomial rootPolynomial uniformW uniformZ
  field_simp
  ring

theorem uniformB_pos {h c : ℝ} (h1 : 1 < h) (h2 : h < 2)
    (hc : 0 ≤ c) (k : ℕ) : 0 < 1 + uniformW h c k := by
  have hh : 0 < h := by linarith
  have hp : 0 < uniformMoment h (k + 1) := uniformMoment_pos h1 h2 (by omega)
  have hcp : 0 ≤ c * (k + 1) / uniformMoment h (k + 1) := by positivity
  unfold uniformW
  nth_rw 1 [← div_self hh.ne']
  rw [← add_div]
  exact div_pos (by linarith) hh

@[simp] theorem uniformZ_zero (h c : ℝ) : uniformZ h c 0 = 0 := by
  simp [uniformZ, uniformSum]

theorem uniformZ_pos {N k : ℕ} (hk : 0 < k) (hkN : k < N) {h c : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc : uniformDelta N h ≤ c) :
    0 < uniformZ h c k := by
  have ha := uniformRatio_gt_one h1 h2
  have havg := momentAverage_lt ha hk hkN
  have hmul := mul_lt_mul_of_pos_left havg (show 0 < 2 - h by linarith)
  have hd : (0 : ℝ) < (k : ℝ) * (k + 1) := by positivity
  have hh : 0 < h := by linarith
  have hp : 0 < uniformMoment h (k + 1) := uniformMoment_pos h1 h2 (by omega)
  have hcmp : (2 - h) * (2 * uniformSum h k / ((k : ℝ) * (k + 1))) < c := by
    apply lt_of_lt_of_le _ hc
    unfold momentAverage at hmul
    change (2 - h) * (2 * uniformSum h k / ((k : ℝ) * (k + 1))) <
      (2 - h) * (2 * uniformSum h N / ((N : ℝ) * (N + 1))) at hmul
    convert hmul using 1
    unfold uniformDelta
    ring
  have hcmp' : (2 - h) * (2 * uniformSum h k) < c * ((k : ℝ) * (k + 1)) := by
    apply (div_lt_iff₀ hd).mp
    convert hcmp using 1
    ring
  unfold uniformZ
  apply div_pos _ (mul_pos hh hp)
  nlinarith

theorem uniformZ_nonneg {N k : ℕ} (hkN : k < N) {h c : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc : uniformDelta N h ≤ c) :
    0 ≤ uniformZ h c k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [uniformZ_zero]
  · exact (uniformZ_pos hk hkN h1 h2 hc).le

theorem uniformRoot_nonneg {N k : ℕ} (hkN : k < N) {h c : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc : uniformDelta N h ≤ c) :
    0 ≤ uniformRoot h c k := by
  have hc0 : 0 ≤ c := (uniformDelta_pos (by omega) h1 h2).le.trans hc
  exact positiveRoot_nonneg (uniformB_pos h1 h2 hc0 k) (uniformZ_nonneg hkN h1 h2 hc)

theorem uniformRoot_pos {N k : ℕ} (hk : 0 < k) (hkN : k < N) {h c : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc : uniformDelta N h ≤ c) :
    0 < uniformRoot h c k := by
  have hc0 : 0 ≤ c := (uniformDelta_pos (by omega) h1 h2).le.trans hc
  exact positiveRoot_pos (uniformB_pos h1 h2 hc0 k) (uniformZ_pos hk hkN h1 h2 hc)

theorem uniformRoot_equation {N k : ℕ} (hkN : k < N) {h c : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc : uniformDelta N h ≤ c) :
    uniformPolynomial h c k (uniformRoot h c k) = 0 := by
  rw [uniformPolynomial_eq h1 h2]
  exact mul_eq_zero_of_right _ (positiveRoot_equation (uniformZ_nonneg hkN h1 h2 hc))

theorem uniformRoot_zero {h c : ℝ} (h1 : 1 < h) (h2 : h < 2) (hc : 0 ≤ c) :
    uniformRoot h c 0 = 0 := by
  unfold uniformRoot
  rw [uniformZ_zero, positiveRoot_zero (uniformB_pos h1 h2 hc 0)]

theorem uniformRoot_lt_iff {N k : ℕ} (hkN : k < N) {h c z : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc : uniformDelta N h ≤ c) (hz : 0 ≤ z) :
    uniformRoot h c k < z ↔ 0 < uniformPolynomial h c k z := by
  have hc0 : 0 ≤ c := (uniformDelta_pos (by omega) h1 h2).le.trans hc
  rw [uniformPolynomial_eq h1 h2, mul_pos_iff_of_pos_left
    (mul_pos (by linarith) (uniformMoment_pos h1 h2 (by omega)))]
  exact positiveRoot_lt_iff (uniformB_pos h1 h2 hc0 k) (uniformZ_nonneg hkN h1 h2 hc) hz

theorem uniformRoot_lt_half {N k : ℕ} (hk : 0 < k) (hkN : k < N) {h c : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc : uniformDelta N h ≤ c) :
    uniformRoot h c k < (k : ℝ) / 2 := by
  apply (uniformRoot_lt_iff hkN h1 h2 hc (by positivity)).2
  have hp := uniformMoment_pos h1 h2 (show 0 < k + 1 by omega)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 ≤ uniformSum h k := (momentSum_pos (uniformRatio_gt_one h1 h2) hk).le
  have hpos : 0 < h * uniformMoment h (k + 1) * (k : ℝ) ^ 2 / 4 +
      (k : ℝ) * (h - 1) * uniformMoment h (k + 1) + (2 - h) * uniformSum h k := by
    positivity
  unfold uniformPolynomial
  nlinarith

theorem uniformRoot_mono_parameter {N k : ℕ} (hkN : k < N) {h c₁ c₂ : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc₁ : uniformDelta N h ≤ c₁) (hcc : c₁ ≤ c₂) :
    uniformRoot h c₁ k ≤ uniformRoot h c₂ k := by
  have hc₂ := hc₁.trans hcc
  have hc₁0 : 0 ≤ c₁ := (uniformDelta_pos (by omega) h1 h2).le.trans hc₁
  have hc₂0 : 0 ≤ c₂ := hc₁0.trans hcc
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [uniformRoot_zero h1 h2 hc₁0, uniformRoot_zero h1 h2 hc₂0]
  have heq := uniformRoot_equation hkN h1 h2 hc₁
  have hhalf := uniformRoot_lt_half hk hkN h1 h2 hc₁
  have hdiff : uniformPolynomial h c₂ k (uniformRoot h c₁ k) ≤ 0 := by
    have hsign : (c₂ - c₁) * (k + 1 : ℝ) * (uniformRoot h c₁ k - (k : ℝ) / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    unfold uniformPolynomial at heq ⊢
    nlinarith
  have hden : 0 < h * uniformMoment h (k + 1) :=
    mul_pos (by linarith) (uniformMoment_pos h1 h2 (by omega))
  rw [uniformPolynomial_eq h1 h2] at hdiff
  exact positiveRoot_le_of_polynomial_le (uniformB_pos h1 h2 hc₁0 k)
    (uniformZ_nonneg hkN h1 h2 hc₁) (uniformB_pos h1 h2 hc₂0 k)
    (uniformZ_nonneg hkN h1 h2 hc₂) (by
      apply (mul_le_mul_iff_right₀ hden).mp
      simpa [uniformRoot] using hdiff)

theorem uniform_power_eq (h : ℝ) (k : ℕ) :
    uniformRatio h ^ k = (((h - 1)⁻¹) ^ k) ^ 2 := by
  simp only [uniformRatio, ← pow_mul, Nat.mul_comm]

theorem uniformSum_weighted {h : ℝ} (h1 : 1 < h) (k : ℕ) :
    (2 - h) * uniformSum h k =
      (uniformRatio h ^ k - 1 - (k : ℝ) * (1 - (h - 1) ^ 2)) / (2 * h) := by
  have hs := uniformSum_identity h1 k
  apply (eq_div_iff (by positivity : 2 * h ≠ 0)).2
  nlinarith

theorem inverse_power_prefix_lt {N k : ℕ} (hk : 0 < k) (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) :
    ((h - 1)⁻¹) ^ k < 1 + (k : ℝ) * h := by
  have hb : 1 < (h - 1)⁻¹ := (one_lt_inv₀ (by linarith)).2 (by linarith)
  have havg := geometricMoment_ratio_lt hb hk hkN
  unfold geometricMoment at havg
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hh := mul_le_mul_of_nonneg_left hupper hk'.le
  nlinarith

/-- The explicit comparison root at artificial parameter `c = h`. -/
def uniformEndpoint (h : ℝ) (k : ℕ) : ℝ :=
  (1 + (k : ℝ) * h - ((h - 1)⁻¹) ^ k) /
    (h * (1 + ((h - 1)⁻¹) ^ (k + 1)))

@[simp] theorem uniformEndpoint_zero (h : ℝ) : uniformEndpoint h 0 = 0 := by
  simp [uniformEndpoint]

theorem uniformEndpoint_nonneg {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) :
    0 ≤ uniformEndpoint h k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hh := inverse_power_prefix_lt hk hkN h1 h2 hupper
    unfold uniformEndpoint
    positivity

theorem uniformEndpoint_polynomial {h : ℝ} (h1 : 1 < h) (k : ℕ) :
    uniformPolynomial h h k (uniformEndpoint h k) = 0 := by
  have hr : h - 1 ≠ 0 := by linarith
  have hh : h ≠ 0 := by linarith
  have hp : 1 + ((h - 1)⁻¹) ^ (k + 1) ≠ 0 := by positivity
  unfold uniformPolynomial
  rw [uniformSum_weighted h1]
  unfold uniformMoment geometricMoment
  rw [uniform_power_eq h k, uniform_power_eq h (k + 1)]
  unfold uniformEndpoint
  rw [pow_succ ((h - 1)⁻¹) k]
  generalize hz : ((h - 1)⁻¹) ^ k = z
  have hz0 : 0 ≤ z := hz ▸ (show 0 ≤ ((h - 1)⁻¹) ^ k by positivity)
  have hsum : h - 1 + z ≠ 0 := by positivity
  field_simp [hr, hh, hsum]
  ring

theorem uniformRoot_endpoint {N k : ℕ} (hkN : k < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) :
    uniformRoot h h k = uniformEndpoint h k := by
  have hN : 0 < N := by omega
  have hc := uniformDelta_le_step hN h1 h2 hupper
  have hz := uniformEndpoint_nonneg hkN h1 h2 hupper
  have heq := uniformEndpoint_polynomial h1 k
  have hden : h * uniformMoment h (k + 1) ≠ 0 :=
    mul_ne_zero (by linarith) (uniformMoment_pos h1 h2 (by omega)).ne'
  rw [uniformPolynomial_eq h1 h2] at heq
  exact (positiveRoot_unique (uniformB_pos h1 h2 (by linarith) k)
    (uniformZ_nonneg hkN h1 h2 hc) hz ((mul_eq_zero.mp heq).resolve_left hden)).symm

theorem uniformZ_recurrence {h : ℝ} (h1 : 1 < h) (h2 : h < 2)
    (c : ℝ) (k : ℕ) :
    uniformMoment h (k + 2) * uniformZ h c (k + 1) =
      uniformMoment h (k + 1) * (uniformZ h c k + uniformW h c k) := by
  have hh : h ≠ 0 := by linarith
  have hp : uniformMoment h (k + 1) ≠ 0 := (uniformMoment_pos h1 h2 (by omega)).ne'
  have hp' : uniformMoment h (k + 2) ≠ 0 := (uniformMoment_pos h1 h2 (by omega)).ne'
  have hs : uniformSum h (k + 1) = uniformSum h k + uniformMoment h (k + 1) :=
    momentSum_succ _ _
  unfold uniformZ uniformW
  rw [hs]
  simp only [show k + 1 + 1 = k + 2 by omega]
  push_cast
  field_simp
  ring

/-- Margin whose positivity gives strict monotonicity of both factors. -/
def uniformMargin (h c : ℝ) (k : ℕ) : ℝ :=
  uniformMoment h (k + 1) / uniformMoment h (k + 2) + 1 +
    uniformW h c (k + 1) - uniformW h c k -
    (1 - uniformMoment h (k + 1) / uniformMoment h (k + 2)) * uniformRoot h c k

theorem uniform_comparison_identity {N k : ℕ} (hkN : k + 1 < N) {h c : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc : uniformDelta N h ≤ c) :
    rootPolynomial (1 + uniformW h c (k + 1)) (uniformZ h c (k + 1))
      (uniformMoment h (k + 1) / uniformMoment h (k + 2) * (1 + uniformRoot h c k)) =
    (uniformMoment h (k + 1) / uniformMoment h (k + 2) * (1 + uniformRoot h c k)) *
      uniformMargin h c k := by
  have heq := positiveRoot_equation (B := 1 + uniformW h c k)
    (uniformZ_nonneg (show k < N by omega) h1 h2 hc)
  change rootPolynomial (1 + uniformW h c k) (uniformZ h c k) (uniformRoot h c k) = 0 at heq
  have hrec := uniformZ_recurrence h1 h2 c k
  have hp : uniformMoment h (k + 2) ≠ 0 := (uniformMoment_pos h1 h2 (by omega)).ne'
  unfold uniformMargin rootPolynomial at *
  field_simp
  linear_combination uniformMoment h (k + 1) * uniformMoment h (k + 2) * heq -
    uniformMoment h (k + 2) * hrec

theorem uniformW_difference_antitone {h c₁ c₂ : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hcc : c₁ ≤ c₂) (k : ℕ) :
    uniformW h c₂ (k + 1) - uniformW h c₂ k ≤
      uniformW h c₁ (k + 1) - uniformW h c₁ k := by
  have hh : 0 < h := by linarith
  have hp : 0 < uniformMoment h (k + 1) := uniformMoment_pos h1 h2 (by omega)
  have hp' : 0 < uniformMoment h (k + 2) := uniformMoment_pos h1 h2 (by omega)
  have hratio := geometricMoment_ratio_lt (uniformRatio_gt_one h1 h2)
    (show 0 < k + 1 by omega) (show k + 1 < k + 2 by omega)
  change ((k + 2 : ℕ) : ℝ) * uniformMoment h (k + 1) <
    ((k + 1 : ℕ) : ℝ) * uniformMoment h (k + 2) at hratio
  push_cast at hratio
  have hd : (k + 2 : ℝ) / uniformMoment h (k + 2) -
      (k + 1 : ℝ) / uniformMoment h (k + 1) < 0 := by
    apply sub_neg.mpr
    apply (div_lt_div_iff₀ hp' hp).2
    exact hratio
  have hsign : (c₂ - c₁) / h * ((k + 2 : ℝ) / uniformMoment h (k + 2) -
      (k + 1 : ℝ) / uniformMoment h (k + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hd.le
  have heq : uniformW h c₂ (k + 1) - uniformW h c₂ k -
      (uniformW h c₁ (k + 1) - uniformW h c₁ k) =
      (c₂ - c₁) / h * ((k + 2 : ℝ) / uniformMoment h (k + 2) -
        (k + 1 : ℝ) / uniformMoment h (k + 1)) := by
    unfold uniformW
    simp only [show k + 1 + 1 = k + 2 by omega]
    push_cast
    field_simp
    ring
  linarith

theorem uniformMargin_antitone {N k : ℕ} (hkN : k + 1 < N) {h c₁ c₂ : ℝ}
    (h1 : 1 < h) (h2 : h < 2) (hc₁ : uniformDelta N h ≤ c₁) (hcc : c₁ ≤ c₂) :
    uniformMargin h c₂ k ≤ uniformMargin h c₁ k := by
  have hw := uniformW_difference_antitone h1 h2 hcc k
  have hu := uniformRoot_mono_parameter (show k < N by omega) h1 h2 hc₁ hcc
  have hpp := geometricMoment_strictMono (uniformRatio_gt_one h1 h2) (show k + 1 < k + 2 by omega)
  have hp' : 0 < uniformMoment h (k + 2) := uniformMoment_pos h1 h2 (by omega)
  have hr : uniformMoment h (k + 1) / uniformMoment h (k + 2) < 1 :=
    (div_lt_one hp').2 hpp
  have hmul := mul_le_mul_of_nonneg_left hu (show 0 ≤ 1 - uniformMoment h (k + 1) /
      uniformMoment h (k + 2) by linarith)
  unfold uniformMargin
  linarith

theorem inverse_power_bernoulli_strict {h : ℝ} (h1 : 1 < h) (h2 : h < 2)
    {k : ℕ} (hk : 0 < k) : 1 + (k : ℝ) * (2 - h) < ((h - 1)⁻¹) ^ k := by
  have hr : 0 < h - 1 := by linarith
  have hh : (2 - h) < (2 - h) / (h - 1) := by
    apply (lt_div_iff₀ hr).2
    nlinarith
  have hbase : 1 + (2 - h) / (h - 1) = (h - 1)⁻¹ := by field_simp; ring
  have hn : (0 : ℝ) < k := by exact_mod_cast hk
  have hmul := mul_lt_mul_of_pos_left hh hn
  have hb := one_add_mul_le_pow (show -2 ≤ (2 - h) / (h - 1) by
    have : 0 ≤ (2 - h) / (h - 1) := by positivity
    linarith) k
  rw [hbase] at hb
  linarith

theorem uniformEndpoint_difference {h : ℝ} (h1 : 1 < h) (k : ℕ) :
    uniformMoment h (k + 1) * (1 + uniformEndpoint h k) -
      uniformMoment h (k + 2) * uniformEndpoint h (k + 1) =
      ((h - 1)⁻¹) ^ (k + 1) *
        (((h - 1)⁻¹) ^ (k + 1) - 1 - (k + 1 : ℝ) * (2 - h)) / (2 * (h - 1)) := by
  have hr : h - 1 ≠ 0 := by linarith
  have hh : h ≠ 0 := by linarith
  unfold uniformMoment geometricMoment
  rw [uniform_power_eq h (k + 1), uniform_power_eq h (k + 2)]
  unfold uniformEndpoint
  simp only [show k + 2 = k + 1 + 1 by omega, pow_succ ((h - 1)⁻¹)]
  push_cast
  generalize hz : ((h - 1)⁻¹) ^ k = z
  have hz0 : 0 < z := hz ▸ (show 0 < ((h - 1)⁻¹) ^ k by positivity)
  have hs1 : h - 1 + z ≠ 0 := by positivity
  have hs2 : (h - 1) ^ 2 + z ≠ 0 := by positivity
  field_simp [hr, hh, hs1, hs2]
  ring

theorem uniformEndpoint_comparison {h : ℝ} (h1 : 1 < h) (h2 : h < 2) (k : ℕ) :
    uniformMoment h (k + 2) * uniformEndpoint h (k + 1) <
      uniformMoment h (k + 1) * (1 + uniformEndpoint h k) := by
  have hbern := inverse_power_bernoulli_strict h1 h2 (show 0 < k + 1 by omega)
  have hid := uniformEndpoint_difference h1 k
  have hpos : 0 < ((h - 1)⁻¹) ^ (k + 1) *
        (((h - 1)⁻¹) ^ (k + 1) - 1 - (k + 1 : ℝ) * (2 - h)) / (2 * (h - 1)) := by
    push_cast at hbern
    have : 0 < ((h - 1)⁻¹) ^ (k + 1) - 1 - (k + 1 : ℝ) * (2 - h) := by linarith
    positivity
  linarith

theorem uniformMargin_endpoint_pos {N k : ℕ} (hkN : k + 1 < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) :
    0 < uniformMargin h h k := by
  have hc := uniformDelta_le_step (by omega : 0 < N) h1 h2 hupper
  have hp : 0 < uniformMoment h (k + 1) := uniformMoment_pos h1 h2 (by omega)
  have hp' : 0 < uniformMoment h (k + 2) := uniformMoment_pos h1 h2 (by omega)
  have hu := uniformRoot_nonneg (show k < N by omega) h1 h2 hc
  have hB : 0 < uniformMoment h (k + 1) / uniformMoment h (k + 2) *
      (1 + uniformRoot h h k) := by positivity
  have hcomp : uniformRoot h h (k + 1) <
      uniformMoment h (k + 1) / uniformMoment h (k + 2) * (1 + uniformRoot h h k) := by
    rw [uniformRoot_endpoint hkN h1 h2 hupper,
      uniformRoot_endpoint (show k < N by omega) h1 h2 hupper]
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ hp').2
    simpa [mul_comm] using uniformEndpoint_comparison h1 h2 k
  have hpoly := (positiveRoot_lt_iff (uniformB_pos h1 h2 (by linarith) (k + 1))
    (uniformZ_nonneg hkN h1 h2 hc) hB.le).1 hcomp
  rw [uniform_comparison_identity hkN h1 h2 hc] at hpoly
  exact (mul_pos_iff_of_pos_left hB).1 hpoly

/-- The decisive strict comparison; it simultaneously orders the two factors. -/
theorem uniformRoot_comparison {N k : ℕ} (hkN : k + 1 < N) {h : ℝ}
    (h1 : 1 < h) (h2 : h < 2)
    (hupper : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h) :
    uniformMoment h (k + 2) * uniformRoot h (uniformDelta N h) (k + 1) <
      uniformMoment h (k + 1) * (1 + uniformRoot h (uniformDelta N h) k) := by
  have hc := uniformDelta_le_step (by omega : 0 < N) h1 h2 hupper
  have hm := uniformMargin_endpoint_pos hkN h1 h2 hupper
  have hma := uniformMargin_antitone hkN h1 h2 (le_refl (uniformDelta N h)) hc
  have hm0 : 0 < uniformMargin h (uniformDelta N h) k := hm.trans_le hma
  have hp : 0 < uniformMoment h (k + 1) := uniformMoment_pos h1 h2 (by omega)
  have hp' : 0 < uniformMoment h (k + 2) := uniformMoment_pos h1 h2 (by omega)
  have hu := uniformRoot_nonneg (show k < N by omega) h1 h2 (le_refl (uniformDelta N h))
  have hB : 0 < uniformMoment h (k + 1) / uniformMoment h (k + 2) *
      (1 + uniformRoot h (uniformDelta N h) k) := by positivity
  have hid := uniform_comparison_identity hkN h1 h2 (le_refl (uniformDelta N h))
  have hpoly : 0 < rootPolynomial (1 + uniformW h (uniformDelta N h) (k + 1))
      (uniformZ h (uniformDelta N h) (k + 1))
      (uniformMoment h (k + 1) / uniformMoment h (k + 2) *
        (1 + uniformRoot h (uniformDelta N h) k)) := by
    rw [hid]
    exact mul_pos hB hm0
  have hr := (positiveRoot_lt_iff (uniformB_pos h1 h2
    (uniformDelta_pos (by omega) h1 h2).le (k + 1))
    (uniformZ_nonneg hkN h1 h2 (le_refl (uniformDelta N h))) hB.le).2 hpoly
  change uniformRoot h (uniformDelta N h) (k + 1) < _ at hr
  have hh := mul_lt_mul_of_pos_left hr hp'
  field_simp at hh
  nlinarith

end THGGradient
