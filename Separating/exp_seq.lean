import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Basic

open Filter Real BigOperators Set Finset

-- In this file, we show that the following sequence converges to the exponential function pointwise
noncomputable
def exp_seq (x : ℝ) (n : ℕ) := (1 + x / n) ^ n

-- some lemmas on properties of 1 + x / n
lemma zero_lt_one_plus_div {n : ℕ} {x : ℝ} (h : -n < x) : 0 < (1 + x / n) := by
  by_cases hn : n = 0
  simp [hn]
  rw [← Real.add_lt_add_iff_left (-1), add_zero, ← add_assoc, add_left_neg, zero_add, neg_lt, ← neg_div]
  exact (div_lt_one (Nat.cast_pos.2 (Nat.zero_lt_of_ne_zero hn))).2 (neg_lt.1 h)

lemma zero_le_one_plus_div {n : ℕ} {x : ℝ} (h : -n ≤ x) : 0 ≤ (1 + x / n) := by
  by_cases hn : n=0
  simp [hn]
  rw [← add_le_add_iff_left (-1), add_zero, ← add_assoc, add_left_neg, zero_add, neg_le, ← neg_div]
  apply (div_le_one (Nat.cast_pos.2 (Nat.zero_lt_of_ne_zero hn))).2 (neg_le.1 h)

lemma exp_seq_bound {x : ℝ} (n : ℕ) (h₁ : x ≤ 0) (h₂ : -n ≤ x) : abs ((1 + x / n) ^ n) ≤ 1 := by
  by_cases h : n = 0
  · simp only [h, CharP.cast_eq_zero, div_zero, add_zero, pow_zero, abs_one, le_refl]
  · rw [abs_pow]
    apply pow_le_one n (abs_nonneg (1 + x / n))
    rw [abs_le]
    constructor
    · exact le_trans (Left.neg_nonpos_iff.2 zero_le_one) (zero_le_one_plus_div h₂)
    · rw [add_le_iff_nonpos_right]
      refine div_nonpos_of_nonpos_of_nonneg h₁ (Nat.cast_nonneg n)

lemma log_lim (t : ℝ) : Tendsto (fun (n : ℕ) ↦ ((1 + t/n) ^ n).log) atTop (nhds t) := by
  have : (fun (n : ℕ) ↦ ((1 + t/n) ^ n).log) = fun (n : ℕ) ↦ n * (1 + t/n).log := by
    ext n; exact log_pow (1 + t/n) n
  rw [this]
  change Tendsto ((fun n ↦ n * (1 + t / n).log) ∘ Nat.cast) atTop (nhds t)
  refine Tendsto.comp (tendsto_mul_log_one_plus_div_atTop t) tendsto_natCast_atTop_atTop

lemma exp_seq_lim (x : ℝ) : Tendsto (fun (n : ℕ) ↦ (1 + x/n) ^ n) atTop (nhds (x.exp)) := by
  --choose N big enough, s.t. 1 + x / n > 0
  let h := exists_nat_gt (abs x)
  cases' h with N h
  have hloglim : Tendsto (fun (n : ℕ) ↦ ((1 + x/n) ^ n).log) atTop (nhds x) := log_lim x
  rw [tendsto_atTop_nhds] at *
  intro U hxU hU
  let V := exp⁻¹' U
  specialize hloglim V (Set.mem_preimage.2 hxU) (IsOpen.preimage continuous_exp hU)
  cases' hloglim with NV hloglim
  -- if N ≤ n, then the sequence is in V.
  -- If NV ≤ n, then the sequence is nonnegative, i.e. we can apply exp_log.
  use (max N NV)
  intro n hn
  rw [max_le_iff] at hn
  specialize hloglim n hn.2
  have : 0 < (1 + x / n) :=
    (zero_lt_one_plus_div (lt_of_le_of_lt (neg_le_neg_iff.mpr (Nat.cast_le.2 hn.1)) (abs_lt.1 h).1))
  rw [← exp_log (pow_pos this n), ← Set.mem_preimage]
  exact hloglim
