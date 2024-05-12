import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Order.Bounded

lemma l1 {f : ℝ → ℝ} (hf : ∃ C : ℝ, ∀ x, f x ∈ Set.Icc (-C) C) : ∃ (C : ℝ), ∀ (x y : ℝ ), dist (f x)  (f y) ≤ C := by
  cases' hf with C hC
  refine Metric.isBounded_range_iff.mp (Bornology.IsBounded.subset (Metric.isBounded_Icc (-C) C) ?_)
  rintro y ⟨x, hx⟩
  rw [← hx]
  exact hC x

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

lemma bounded_xexp2_of_interval: ∀ (x : ℝ), xexp2 x ∈ Set.Icc (-1) 1 := by
  simp_rw [Set.mem_Icc, ← abs_le]
  intro x
  rw [abs_le]
  constructor
  swap
  · exact bounded_above_of_xexpx2 x
  · rw [← xexp2_symm, neg_le_neg_iff]
    exact bounded_above_of_xexpx2 (-x)

lemma bounded_of_xexpx2' : ∃ (C : ℝ), ∀ (x : ℝ), xexp2 x ∈ Set.Icc (-C) C := by
  use 1
  exact bounded_xexp2_of_interval

noncomputable
def xexpx2' : BoundedContinuousFunction ℝ ℝ where
  toFun := xexp2
  continuous_toFun := Continuous.mul continuous_id' (Continuous.comp' Real.continuous_exp (Continuous.mul continuous_neg continuous_id'))
  map_bounded' := l1 bounded_of_xexpx2'

lemma l2 (g : ℝ → ℝ) (ε : ℝ) (hε : ε > 0) (x : ℝ): (g x) * (Real.exp (- (ε * (g x) * (g x)))) = ε.sqrt⁻¹ * xexp2 (Real.sqrt ε * (g x)) := by
  simp only [neg_mul, one_div, xexp2]
  obtain h : ((ε.sqrt * g x * (ε.sqrt * g x))) = ε * (g x) * (g x):= by
    ring_nf
    rw [Real.sq_sqrt hε.le, mul_comm]
  rw [h, eq_inv_mul_iff_mul_eq₀ _]
  · ring_nf
  · intro h
    rw [← pow_eq_zero_iff (Ne.symm (Nat.zero_ne_add_one 1)), Real.sq_sqrt hε.le] at h
    linarith

noncomputable
def gexpepsg (g : ℝ → ℝ) (hf: Continuous g) (ε : ℝ) (hε : ε > 0): BoundedContinuousFunction ℝ ℝ where
  toFun := (fun x => (g x) * (- (ε * (g x) * (g x))).exp)
  continuous_toFun := by continuity
  map_bounded' := by
    dsimp only [ContinuousMap.toFun_eq_coe, ContinuousMap.coe_mk]
    apply l1
    use ε.sqrt⁻¹
    intro x
    rw [Set.mem_Icc, ← abs_le, l2, abs_mul, abs_of_pos]
    nth_rewrite 2 [← mul_one ε.sqrt⁻¹]
    rw [mul_le_mul_iff_of_pos_left]
    · simp_rw [abs_le, ← Set.mem_Icc]
      exact bounded_xexp2_of_interval (ε.sqrt * g x)
    · exact (inv_pos_of_pos (Real.sqrt_pos_of_pos hε))
    · exact (inv_pos_of_pos (Real.sqrt_pos_of_pos hε))
    · exact hε
