module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# The balancing stepsize

For each positive horizon the two explicit rates meet at one step in `(1,2)`.
The construction uses only the intermediate value theorem for a polynomial.
-/

@[expose] public section

namespace THGGradient

def balancePolynomial (N : ℕ) (h : ℝ) : ℝ :=
  (h - 1) ^ N * (1 + (N : ℝ) * h)

theorem balancePolynomial_continuous (N : ℕ) : Continuous (balancePolynomial N) := by
  unfold balancePolynomial
  fun_prop

theorem balancePolynomial_strictMonoOn {N : ℕ} (hN : 0 < N) :
    StrictMonoOn (balancePolynomial N) (Set.Ici 1) := by
  intro a ha b hb hab
  change 1 ≤ a at ha
  change 1 ≤ b at hb
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (a - 1) ^ N < (b - 1) ^ N := by
    exact pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)
  have hmul := mul_lt_mul_of_pos_right hpow (show 0 < 1 + (N : ℝ) * a by positivity)
  have hmul' : (b - 1) ^ N * (1 + (N : ℝ) * a) ≤
      (b - 1) ^ N * (1 + (N : ℝ) * b) := by
    gcongr
  exact hmul.trans_le hmul'

theorem exists_balance {N : ℕ} (hN : 0 < N) :
    ∃ H : ℝ, 1 < H ∧ H < 2 ∧ balancePolynomial N H = 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hleft : balancePolynomial N 1 = 0 := by
    simp [balancePolynomial, Nat.ne_of_gt hN]
  have hright : 1 < balancePolynomial N 2 := by
    simp only [balancePolynomial]
    norm_num
    positivity
  have hf := intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num)
    (balancePolynomial_continuous N).continuousOn
  obtain ⟨H, hH, heq⟩ := hf (show (1 : ℝ) ∈
      Set.Icc (balancePolynomial N 1) (balancePolynomial N 2) by
    rw [hleft]
    exact ⟨by norm_num, hright.le⟩)
  refine ⟨H, ?_, ?_, heq⟩
  · rcases lt_or_eq_of_le hH.1 with h | h
    · exact h
    · rw [← h, hleft] at heq
      norm_num at heq
  · rcases lt_or_eq_of_le hH.2 with h | h
    · exact h
    · rw [h] at heq
      linarith

/-- The unique crossing step for a positive horizon. The zero-horizon value is 1. -/
noncomputable def balanceStep (N : ℕ) : ℝ :=
  if hN : 0 < N then Classical.choose (exists_balance hN) else 1

theorem balanceStep_spec {N : ℕ} (hN : 0 < N) :
    1 < balanceStep N ∧ balanceStep N < 2 ∧ balancePolynomial N (balanceStep N) = 1 := by
  rw [balanceStep, dite_eq_left hN]
  exact Classical.choose_spec (exists_balance hN)

theorem balance_unique {N : ℕ} (hN : 0 < N) {H : ℝ}
    (hH : 1 ≤ H) (heq : balancePolynomial N H = 1) : H = balanceStep N := by
  apply (balancePolynomial_strictMonoOn hN).injOn hH (balanceStep_spec hN).1.le
  rw [heq, (balanceStep_spec hN).2.2]

theorem balanceStep_le_iff {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 1 ≤ h) :
    balanceStep N ≤ h ↔ 1 ≤ balancePolynomial N h := by
  have hm := balancePolynomial_strictMonoOn hN
  have hb := balanceStep_spec hN
  constructor
  · intro hle
    have := hm.monotoneOn hb.1.le hh hle
    rwa [hb.2.2] at this
  · intro hle
    by_contra hn
    have := hm hh hb.1.le (lt_of_not_ge hn)
    rw [hb.2.2] at this
    linarith

theorem le_balanceStep_iff {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 1 ≤ h) :
    h ≤ balanceStep N ↔ balancePolynomial N h ≤ 1 := by
  have hm := balancePolynomial_strictMonoOn hN
  have hb := balanceStep_spec hN
  constructor
  · intro hle
    have := hm.monotoneOn hh hb.1.le hle
    rwa [hb.2.2] at this
  · intro hle
    by_contra hn
    have := hm hb.1.le hh (lt_of_not_ge hn)
    rw [hb.2.2] at this
    linarith

theorem balanceStep_upper_condition {N : ℕ} (hN : 0 < N) :
    ((balanceStep N - 1)⁻¹) ^ N = 1 + (N : ℝ) * balanceStep N := by
  have hs := balanceStep_spec hN
  have hp : (balanceStep N - 1) ^ N ≠ 0 := pow_ne_zero _ (by linarith [hs.1])
  rw [inv_pow]
  rw [inv_eq_one_div]
  apply (div_eq_iff hp).2
  simpa [balancePolynomial, mul_comm] using hs.2.2.symm

theorem inverse_power_le_iff_balance (N : ℕ) {h : ℝ} (h1 : 1 < h) :
    ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h ↔ 1 ≤ balancePolynomial N h := by
  rw [inv_pow, inv_eq_one_div, div_le_iff₀ (pow_pos (by linarith : 0 < h - 1) N)]
  simp only [balancePolynomial, mul_comm]

theorem inverse_power_lt_iff_balance (N : ℕ) {h : ℝ} (h1 : 1 < h) :
    ((h - 1)⁻¹) ^ N < 1 + (N : ℝ) * h ↔ 1 < balancePolynomial N h := by
  rw [inv_pow, inv_eq_one_div, div_lt_iff₀ (pow_pos (by linarith : 0 < h - 1) N)]
  simp only [balancePolynomial, mul_comm]

theorem balanceStep_upper_condition_of_le {N : ℕ} (hN : 0 < N) {h : ℝ}
    (hh : balanceStep N ≤ h) : ((h - 1)⁻¹) ^ N ≤ 1 + (N : ℝ) * h := by
  have h1 : 1 < h := (balanceStep_spec hN).1.trans_le hh
  exact (inverse_power_le_iff_balance N h1).2 ((balanceStep_le_iff hN h1.le).1 hh)

theorem balanceStep_upper_condition_of_lt {N : ℕ} (hN : 0 < N) {h : ℝ}
    (hh : balanceStep N < h) : ((h - 1)⁻¹) ^ N < 1 + (N : ℝ) * h := by
  have hb := balanceStep_spec hN
  have h1 : 1 < h := hb.1.trans hh
  apply (inverse_power_lt_iff_balance N h1).2
  have hp := balancePolynomial_strictMonoOn hN hb.1.le h1.le hh
  rwa [hb.2.2] at hp

end THGGradient
