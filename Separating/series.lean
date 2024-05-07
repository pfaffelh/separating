import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.NormedSpace.Exponential

noncomputable
def xexp2 (x : ℝ) : ℝ := x * (Real.exp (-x*x))

lemma xexp2_symm (x : ℝ) : - xexp2 (-x) = xexp2 x  := by
  simp only [xexp2, neg_mul, neg_neg, mul_neg]

lemma xexp2_symm' (x : ℝ) : xexp2 (-x) = - xexp2 x  := by
  simp only [xexp2, neg_neg, mul_neg, neg_mul]

lemma xexp2_cont : Continuous (fun x => xexp2 x) := by
  simp [xexp2]
  refine Continuous.mul ?hf ?hg
  continuity
  continuity
  sorry

lemma bounded_above_of_xexpx2'' : ∀ (x : ℝ), x ≥ 0 →  xexp2 x  ≤ 1 := by
  intros x hx
  simp [xexp2]
  rw [← le_div_iff (Real.exp_pos (-(x * x)))]
  rw [Real.exp_neg]
  simp only [div_inv_eq_mul, one_mul]
  obtain hx2 : (x * x) + 1 ≤ Real.exp (x * x):= by
    apply Real.add_one_le_exp
  apply le_trans _ hx2
  nlinarith

lemma bounded_above_of_xexpx2' : ∃ (C : ℝ), ∀ (x : ℝ), x≥0 → xexp2 x ≤ C := by
  use 1
  intros x hx
  exact bounded_above_of_xexpx2'' x hx

lemma bounded_above_of_xexpx2 : ∃ (C : ℝ), ∀ (x : ℝ), |xexp2 x| ≤ C := by
  use 1
  intro x
  by_cases hx : x ≥ 0
  · obtain hx1 : xexp2 x ≥ 0 := by sorry
    simp [hx1]
    exact bounded_above_of_xexpx2'' x hx
  · simp [xexp2]
    simp at hx



lemma bounded_of_xexpx2 :
∃ (C : ℝ), ∀ (x y : ℝ), dist (xexp2 x) (xexp2 y) ≤ C := by
  use 2
  intros x y
  obtain h1 : dist (xexp2 x) 0 ≤ 1 := by sorry
  obtain h2 : dist 0 (xexp2 y) ≤ 1 := by sorry
  apply le_trans (dist_triangle _ 0 _ )
  linarith
