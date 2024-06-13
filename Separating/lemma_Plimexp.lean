import «Separating».xexp2
import «Separating».boundedPointwiseConvergence
import «Separating».exp_seq
import Mathlib.Topology.MetricSpace.CauSeqFilter
import Mathlib.Topology.ContinuousFunction.Bounded

open Filter MeasureTheory BigOperators

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] {μ : FiniteMeasure E}

--gexpepsg from the file xexp2, but defined on E instead of R
noncomputable
def gexpepsgE (g : E → ℝ) (hg: Continuous g) (ε : ℝ) (hε : ε > 0)
    := (fun x => (g x) * (- (ε * (g x * g x))).exp)

theorem Plimexp (g : BoundedContinuousFunction E ℝ) (ε : ℝ) (hε : ε > 0)
    : Filter.Tendsto (fun (n : ℕ) => ∫ (x : E), (g x) * exp_seq (-(ε * (g x * g x))) n ∂μ)
    Filter.atTop (nhds (∫ (x : E), gexpepsgE g (map_continuous g) ε hε x ∂μ)) := by
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
      rw [norm_mul (g x) (exp_seq (-(ε * (g x * g x))) (n + N)), ← mul_one (norm g)]
      apply mul_le_mul (BoundedContinuousFunction.norm_coe_le_norm g x) _
          (norm_nonneg (exp_seq (-(ε * (g x * g x))) (n + N))) (norm_nonneg g)
      have : -(ε * (g x * g x)) ≤ 0 := by
        rw [neg_le, neg_zero]
        apply Left.mul_nonneg (le_of_lt hε) (mul_self_nonneg (g x))
      apply exp_seq_bound (n + N) this; simp
      refine le_trans (le_trans ?_ h) ((le_add_iff_nonneg_left (N : ℝ)).2 (Nat.cast_nonneg n))
      apply mul_le_mul (Preorder.le_refl ε) _ (mul_self_nonneg (g x)) (le_of_lt hε)
      rw [← abs_le_iff_mul_self_le, abs_norm]
      exact BoundedContinuousFunction.norm_coe_le_norm g x
-- pointwise convergence
    · apply eventually_of_forall
      intro x
      rw [@tendsto_add_atTop_iff_nat _ (fun n ↦ g x * exp_seq (-(ε * (g x * g x))) (n)) _ N]
      apply Filter.Tendsto.const_mul (g x) (exp_seq_lim (-(ε * (g x * g x))))
