import Mathlib.Topology.MetricSpace.CauSeqFilter
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
--import Separating.exp_seq
import Separating.xexp2_onE

open Filter MeasureTheory BigOperators

variable {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E] { P : FiniteMeasure E}

lemma zero_le_one_plus_div {n : ℕ} {x : ℝ} (h : -n ≤ x) : 0 ≤ (1 + x / n) := by
  by_cases hn : n=0
  simp [hn]
  rw [← add_le_add_iff_left (-1), add_zero, ← add_assoc, add_left_neg, zero_add, neg_le, ← neg_div]
  apply (div_le_one (Nat.cast_pos.2 (Nat.zero_lt_of_ne_zero hn))).2 (neg_le.1 h)

--the following sequence converges to the exponential function
noncomputable
def exp_seq (x : ℝ) (n : ℕ) := (1 + x / n) ^ n

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


theorem Plimexp (g : BoundedContinuousFunction E ℝ) (ε : ℝ) (hε : ε > 0)
    : Filter.Tendsto (fun (n : ℕ) => ∫ (x : E), (g x) * exp_seq (-(ε * g x * g x)) n ∂ P)
    Filter.atTop (nhds (∫ (x : E), expeps2 g.continuous ε x ∂ P)) := by
  let h := exists_nat_ge (ε * (norm g * norm g))
  cases' h with N h
  rw [← tendsto_add_atTop_iff_nat N]
  apply tendstoIntegral_of_boundedPointwise
-- measurability
  · intro n
    apply StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable _)
    continuity
  · refine { h_bound := ?h_bound, h_lim := ?h_lim }
-- uniform boundedness
    · use norm g; intro n
      apply eventually_of_forall
      intro x
      rw [norm_mul (g x) (exp_seq (-(ε * g x * g x)) (n + N)), ← mul_one (norm g)]
      apply mul_le_mul (BoundedContinuousFunction.norm_coe_le_norm g x) _
          (norm_nonneg (exp_seq (-(ε * g x * g x)) (n + N))) (norm_nonneg g)
      have : -(ε * g x * g x) ≤ 0 := by
        rw [neg_le, neg_zero, mul_assoc]
        apply Left.mul_nonneg (le_of_lt hε) (mul_self_nonneg (g x))
      apply exp_seq_bound (n + N) this
      simp only [Nat.cast_add, neg_add_rev, add_neg_le_iff_le_add, le_neg_add_iff_add_le]
      refine le_trans (le_trans ?_ h) ((le_add_iff_nonneg_left (N : ℝ)).2 (Nat.cast_nonneg n))
      rw [mul_assoc]
      apply mul_le_mul (Preorder.le_refl ε) _ (mul_self_nonneg (g x)) (le_of_lt hε)
      rw [← abs_le_iff_mul_self_le, abs_norm]
      exact BoundedContinuousFunction.norm_coe_le_norm g x
-- pointwise convergence
    · apply eventually_of_forall
      intro x
      rw [@tendsto_add_atTop_iff_nat _ (fun n ↦ g x * exp_seq (-(ε * g x * g x)) (n)) _ N]
      apply Filter.Tendsto.const_mul (g x)
      exact tendsto_one_plus_div_pow_exp (-(ε * g x * g x))
