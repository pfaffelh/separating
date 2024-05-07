import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Order.Bounded

lemma l1 {f : ℝ → ℝ} (hf : ∃ C : ℝ, ∀ x, f x ∈ Set.Icc (-C) C) : ∃ (C : ℝ), ∀ (x y : ℝ ), dist (f x)  (f y) ≤ C := by
  cases' hf with C hC
  refine Metric.isBounded_range_iff.mp ?_
  have h1 : Set.range f ⊆ Set.Icc (-C) C := by
    intro y hy
    cases' hy with x hx
    rw [← hx]
    exact hC x
  exact Bornology.IsBounded.subset (Metric.isBounded_Icc (-C) C) h1

-- We are going to show that the following is continuous and bounded
noncomputable
def xexp2 := fun x => x * (Real.exp (-x*x))

lemma xexp2_symm (x : ℝ) : - xexp2 (-x) = xexp2 x  := by
  simp only [xexp2, neg_mul, neg_neg, mul_neg]

lemma bounded_above_of_xexpx2 : ∀ (x : ℝ), xexp2 x ≤ 1 := by
  intros x
  simp [xexp2]
  rw [← le_div_iff (Real.exp_pos (-(x * x)))]
  rw [Real.exp_neg]
  simp only [div_inv_eq_mul, one_mul]
  obtain hx2 : (x * x) + 1 ≤ Real.exp (x * x):= by
    apply Real.add_one_le_exp
  apply le_trans _ hx2
  nlinarith

lemma bounded_of_xexpx2' : ∃ (C : ℝ), ∀ (x : ℝ), xexp2 x ∈ Set.Icc (-C) C := by
  simp_rw [Set.mem_Icc, ← abs_le]
  use 1
  intro x
  rw [abs_le]
  constructor
  swap
  · exact bounded_above_of_xexpx2 x
  · rw [← xexp2_symm, neg_le_neg_iff]
    exact bounded_above_of_xexpx2 (-x)

noncomputable
def xexpx2' : BoundedContinuousFunction ℝ ℝ where
  toFun := xexp2
  continuous_toFun := Continuous.mul continuous_id' (Continuous.comp' Real.continuous_exp (Continuous.mul continuous_neg continuous_id'))
  map_bounded' := l1 bounded_of_xexpx2'
