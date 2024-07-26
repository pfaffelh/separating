import Mathlib.Topology.MetricSpace.CauSeqFilter
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Separating.xexp2_onE


/-
approximation of expeps2 by the exponential sequence. Convergence of integrals

move this to the file xexp2_onE ?!
-/

open Filter MeasureTheory BigOperators BoundedContinuousFunction

variable {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E] { P : FiniteMeasure E}

lemma zero_le_one_sub_div {n : ℕ} {x : ℝ} (h : x ≤ n) : 0 ≤ 1 - x / n := by
  by_cases hn : n=0
  · simp only [hn, CharP.cast_eq_zero, div_zero, sub_zero, zero_le_one]
  · rw [sub_nonneg, div_le_one ((Nat.cast_pos).mpr (Nat.zero_lt_of_ne_zero hn))]
    exact h

--the following sequence converges to the exponential function
noncomputable
def exp_seq (x : ℝ) (n : ℕ) := (1 + x / n) ^ n

lemma exp_seq_bound {x : ℝ} (n : ℕ) (h₁ : 0 ≤ x) (h₂ : x ≤ n) : abs ((1 + -((n : ℝ)⁻¹ * x)) ^ n) ≤ 1 := by
  by_cases hn : n = 0
  · simp only [hn, pow_zero, abs_one, le_refl]
  · rw [abs_pow]
    apply pow_le_one n (abs_nonneg _)
    rw [inv_mul_eq_div, abs_le]
    constructor
    · apply le_trans (Left.neg_nonpos_iff.2 zero_le_one) (zero_le_one_sub_div h₂)
    · rw [add_le_iff_nonpos_right, Left.neg_nonpos_iff]
      apply div_nonneg h₁ (Nat.cast_nonneg n)

theorem Plimexp (g : BoundedContinuousFunction E ℝ) {ε : ℝ} (hε : ε > 0) (P : Measure E) [IsFiniteMeasure P]
    : Filter.Tendsto (fun (n : ℕ) => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂ P)
    Filter.atTop (nhds (∫ (x : E), expeps2 g.continuous ε x ∂ P)) := by
  obtain ⟨N, hgN⟩ := exists_nat_ge (ε * (norm g * norm g))
  apply tendstoIntegral_of_eventually_boundedPointwise
-- measurability
  · apply eventually_of_forall
    intro n
    apply StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable _)
    continuity
  · refine { h_bound := ?h_bound, h_lim := ?h_lim }
-- uniform boundedness
    · use norm g
      rw [eventually_atTop]
      use N
      intro n hn
      apply eventually_of_forall
      intro x
      simp only [Algebra.smul_mul_assoc, smul_neg, coe_mul, coe_pow, coe_add, coe_one,
        coe_neg, coe_smul, Pi.mul_apply, smul_eq_mul, Pi.pow_apply, Pi.add_apply, Pi.one_apply,
        Pi.neg_apply, norm_mul, Real.norm_eq_abs]
      rw [← mul_one (norm g)]
      apply mul_le_mul (BoundedContinuousFunction.norm_coe_le_norm g x) _ (abs_nonneg _) (norm_nonneg _)
      apply exp_seq_bound n (Left.mul_nonneg (le_of_lt hε) (mul_self_nonneg (g x)))
      apply le_trans (le_trans _ hgN) (Nat.cast_le.mpr hn)
      apply mul_le_mul (Preorder.le_refl ε) _ (mul_self_nonneg (g x)) (le_of_lt hε)
      rw [← abs_le_iff_mul_self_le, abs_norm]
      exact BoundedContinuousFunction.norm_coe_le_norm g x
-- pointwise convergence
    · apply eventually_of_forall
      intro x
      apply Filter.Tendsto.const_mul (g x)
      simp only [Algebra.smul_mul_assoc, smul_neg, pow_apply, coe_add, coe_one, coe_neg, coe_smul,
        coe_mul, Pi.mul_apply, smul_eq_mul, Pi.add_apply, Pi.one_apply, Pi.neg_apply]
      simp only [mul_assoc, inv_mul_eq_div, ← neg_div]
      exact tendsto_one_plus_div_pow_exp (-(ε * (g x * g x)))
