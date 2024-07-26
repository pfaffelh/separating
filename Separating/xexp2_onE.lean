import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Order.Bounded
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Separating.BoundedPointwiseConvergence

/-
# Definition of fun x => g x * Real.exp (-ε * g x * g x) and properties

In this file, we show

* properties of xexp2 := fun x => x * Real.exp (-x * x);
* properties of expeps2 := fun x => g x * Real.exp (-ε * g x * g x );
* convergence of ∫ expeps2 dx to ∫ g dx, as ε → 0, for any g : E →ᵇ ℝ.

The latter is a key ingredient in the proof of 'theorem sep_of_sep_points'.
-/

open MeasureTheory NNReal ENNReal BoundedContinuousFunction Filter

variable {E: Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E]
    {P : Measure E} [IsFiniteMeasure P]

lemma dist_le_of_mem_Icc {f : E → ℝ} (hf : ∃ C : ℝ, ∀ x, f x ∈ Set.Icc (-C) C)
    : ∃ (C : ℝ), ∀ (x y : E ), dist (f x) (f y) ≤ C := by
  cases' hf with C hC
  refine Metric.isBounded_range_iff.mp
      (Bornology.IsBounded.subset (Metric.isBounded_Icc (-C) C) ?_)
  rintro y ⟨x, hx⟩
  rw [← hx]
  exact hC x

-- We are going to show that the following is continuous and bounded
noncomputable
def xexp2 := fun x => x * (Real.exp (-x*x))

lemma xexp2_symm (x : ℝ) : - xexp2 (-x) = xexp2 x  := by
  simp only [xexp2, neg_mul, neg_neg, mul_neg]

lemma bounded_above_of_xexpx2 : ∀ (x : ℝ), xexp2 x ≤ 1 := by
  intro x
  simp [xexp2]
  rw [← le_div_iff (Real.exp_pos (-(x * x))), Real.exp_neg]
  simp only [div_inv_eq_mul, one_mul]
  apply le_trans _ (Real.add_one_le_exp (x * x))
  nlinarith

lemma bounded_of_xexp2 : ∀ (x : ℝ), abs (xexp2 x) ≤ 1 := by
  intro x
  rw [abs_le]
  constructor
  · rw [← xexp2_symm, neg_le_neg_iff]
    exact bounded_above_of_xexpx2 (-x)
  · exact bounded_above_of_xexpx2 x

lemma bounded_xexp2_of_interval: ∀ (x : ℝ), xexp2 x ∈ Set.Icc (-1) 1 := by
  simp_rw [Set.mem_Icc, ← abs_le]
  exact bounded_of_xexp2

lemma bounded_of_xexp2' : ∃ (C : ℝ), ∀ (x : ℝ), xexp2 x ∈ Set.Icc (-C) C := by
  use 1
  exact bounded_xexp2_of_interval

lemma deriv_of_exp2 : ∀ y, deriv (fun (x : ℝ) => (-x * x).exp) y = -2 * y * (-y * y).exp := by
  intro y
  simp only [neg_mul, differentiableAt_neg_iff, differentiableAt_id', DifferentiableAt.mul,
    deriv_exp, deriv.neg', deriv_mul, deriv_id'', one_mul, mul_one, neg_add_rev]
  ring

lemma differentiable_of_exp2 : ∀ y : ℝ, DifferentiableAt ℝ (fun (x : ℝ) => (-x * x).exp) y := by
  simp only [neg_mul, differentiableAt_neg_iff, differentiableAt_id', DifferentiableAt.mul,
    DifferentiableAt.exp, implies_true]

lemma deriv_of_xexp2 : ∀ x, deriv xexp2 x = (-x * x).exp + x * (-2 * x * (-x * x).exp) := by
  intro x
  have : deriv xexp2 x = deriv (fun x => x * (-x * x).exp) x := by
    apply congrFun (congrArg deriv _) x
    rfl
  rw [this]
  nth_rw 1 [← one_mul (-x * x).exp, ← (deriv_id x)]
  rw [← deriv_of_exp2 x]
  apply deriv_mul differentiableAt_id' (differentiable_of_exp2 x)

lemma mul_le_one_of_le_inv {x y : ℝ} (hx : x ≥ 0) (hy : y > 0) : x ≤ y⁻¹ → y * x ≤ 1 := by
  intro h
  have := mul_le_mul_of_nonneg_left h (le_of_lt hy)
  rw [CommGroupWithZero.mul_inv_cancel y (ne_of_gt hy)] at this
  exact this

lemma emulx_le_expx {x : ℝ} (hx : x ≥ 0) : Real.exp 1 * x ≤ x.exp := by
  by_cases hx0 : x = 0
  · rw [hx0]; simp only [mul_zero, Real.exp_zero, zero_le_one]
  · have hxgt0 : 0 < x := lt_of_le_of_ne hx (fun a ↦ hx0 (id a.symm))
    have := Real.add_one_le_exp (Real.log x)
    rwa [← Real.exp_le_exp, Real.exp_add, Real.exp_log hxgt0, mul_comm] at this

lemma lipschitz_of_xexp2 : LipschitzWith 1 xexp2 := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · apply Differentiable.mul differentiable_id'
    simp only [neg_mul, differentiable_neg_iff, differentiable_id', Differentiable.mul,
      Differentiable.exp]
  · intro x
    have h : ∀ x : ℝ, abs x ≤ 1 → ‖x‖₊ ≤ 1 := by
      intro x
      exact fun a => a
    apply h _
    rw [deriv_of_xexp2 x]
    have : (-x * x).exp + x * (-2 * x * (-x * x).exp) = (-x * x).exp * (1 + 2 * -x * x) := by ring
    rw [this, abs_mul, Real.abs_exp]
    let y := x * x
    have hy : y = x * x := by rfl
    have hy_nonneg : 0 ≤ y := mul_self_nonneg x
    rw [neg_mul, ← hy, mul_assoc, neg_mul, ← hy]
    apply mul_le_one_of_le_inv (abs_nonneg _) (Real.exp_pos _)
    simp [← Real.exp_neg (-y), abs_le]
    constructor
    · have : 2 * y ≤ y.exp := by
        apply le_trans _ (emulx_le_expx hy_nonneg)
        have : 2 ≤ Real.exp 1 := by
          apply le_of_lt (lt_trans _ Real.exp_one_gt_d9)
          norm_num
        apply mul_le_mul_of_nonneg_right this hy_nonneg
      apply le_trans this _
      simp only [le_add_iff_nonneg_right, zero_le_one]
    · apply le_trans (Real.one_le_exp hy_nonneg) _
      simp [hy_nonneg]

lemma lipschitz_of_xexp2' : ∀ x y, abs (xexp2 x - xexp2 y) ≤ abs (x - y) := by
  intro x y
  rw [← Real.dist_eq, ← Real.dist_eq]
  have lipschitz := (lipschitz_of_xexp2 x y)
  simp only [ENNReal.coe_one, one_mul] at lipschitz
  rw [dist_edist, dist_edist]
  exact (toReal_le_toReal (edist_ne_top _ _) (edist_ne_top _ _)).mpr lipschitz

-- not used anymore
noncomputable
def xexpx2' : BoundedContinuousFunction ℝ ℝ where
  toFun := xexp2
  continuous_toFun := Continuous.mul continuous_id'
      (Continuous.comp' Real.continuous_exp (Continuous.mul continuous_neg continuous_id'))
  map_bounded' := dist_le_of_mem_Icc bounded_of_xexp2'

noncomputable
def expeps2 {g : E → ℝ} (hg: Continuous g) (ε : ℝ): ContinuousMap E ℝ where
  toFun := (fun x => (g x) * (- (ε * (g x) * (g x))).exp)
  continuous_toFun := by continuity

lemma expeps2_eq_sqrt_mul_xexp2 {g : E → ℝ} {x : E} {ε : ℝ} (hε : ε > 0)
    : (g x) * (Real.exp (- (ε * (g x) * (g x)))) = ε.sqrt⁻¹ * xexp2 (Real.sqrt ε * (g x)) := by
  simp only [neg_mul, one_div, xexp2]
  have h : ((ε.sqrt * g x * (ε.sqrt * g x))) = ε * (g x) * (g x) := by
    ring_nf
    rw [Real.sq_sqrt hε.le, mul_comm]
  rw [h, eq_inv_mul_iff_mul_eq₀ _]
  · ring_nf
  · intro h
    rw [← pow_eq_zero_iff (Ne.symm (Nat.zero_ne_add_one 1)), Real.sq_sqrt hε.le] at h
    linarith

--if ε ≥ 0, then expeps2 is bounded by ε.sqrt⁻¹
lemma bounded_of_expeps2 {g : E → ℝ} (hg: Continuous g) {ε : ℝ} (hε : ε > 0)
    : ∀ (x : E), abs (expeps2 hg ε x) ≤ ε.sqrt⁻¹ := by
  intro x
  simp [expeps2]
  rw [expeps2_eq_sqrt_mul_xexp2 hε, abs_mul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos_of_pos hε))]
  nth_rw 2 [← mul_one ε.sqrt⁻¹]
  rw [mul_le_mul_left (inv_pos.mpr (Real.sqrt_pos_of_pos hε))]
  exact bounded_of_xexp2 (ε.sqrt * g x)

lemma bounded'_of_expeps2 {g : E → ℝ} (hg: Continuous g) {ε : ℝ} (hε : ε > 0)
    : ∀ (x y : E), dist (expeps2 hg ε x) (expeps2 hg ε y) ≤ 2 * ε.sqrt⁻¹ := by
  intro x y
  apply le_trans (dist_triangle (expeps2 hg ε x) 0 (expeps2 hg ε y))
  simp only [dist_zero_right, Real.norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (bounded_of_expeps2 hg hε x) (bounded_of_expeps2 hg hε y)

-- boundedness of expeps2 by norm g, which does not depend on ε. We need this in order to have
-- bounded pointwise convergence in 'lemma tendsto_integral_expeps2' below
lemma bounded_bynorm_of_expeps2 (g : BoundedContinuousFunction E ℝ) {ε : ℝ} (hε : ε ≥ 0)
    : ∀ (x : E), abs ((expeps2 g.continuous ε) x) ≤ norm g := by
  intro x
  simp only [expeps2, ContinuousMap.coe_mk, abs_mul, Real.abs_exp]
  apply le_trans (mul_le_of_le_one_right (abs_nonneg (g x)) _) (g.norm_coe_le_norm x)
  rw [Real.exp_le_one_iff, Left.neg_nonpos_iff, mul_assoc]
  apply mul_nonneg hε (mul_self_nonneg (g x))

lemma lipschitz_of_expeps2 {f g : E → ℝ} (hf: Continuous f) (hg: Continuous g) {ε : ℝ} (hε : ε > 0)
    : ∀ x, dist (expeps2 hg ε x) (expeps2 hf ε x) ≤ dist (g x) (f x) := by
  have hxexp2 : ∀ x, |xexp2 (ε.sqrt * g x) - xexp2 (ε.sqrt * f x)| ≤ ε.sqrt * abs (g x - f x) := by
    intro x
    apply le_trans (lipschitz_of_xexp2' (ε.sqrt * g x) (ε.sqrt * f x)) _
    rw [← mul_sub_left_distrib ε.sqrt _ _, abs_mul, abs_of_pos (Real.sqrt_pos_of_pos hε)]
  intro x
  simp [expeps2]
  rw [expeps2_eq_sqrt_mul_xexp2 hε, expeps2_eq_sqrt_mul_xexp2 hε, Real.dist_eq, Real.dist_eq]
  rw [← mul_sub_left_distrib ε.sqrt⁻¹ _ _, abs_mul, abs_of_pos (inv_pos_of_pos (Real.sqrt_pos_of_pos hε))]
  rw [← one_mul (abs ((g x) - (f x)))]
  rw [← inv_mul_cancel (ne_of_gt (Real.sqrt_pos_of_pos hε)), mul_assoc]
  rw [mul_le_mul_left (inv_pos_of_pos (Real.sqrt_pos_of_pos hε))]
  apply le_trans (hxexp2 x) _
  rw [mul_le_mul_left (Real.sqrt_pos_of_pos hε)]

-- not used anymore
noncomputable
def expeps2' {g : E → ℝ} (hg: Continuous g) {ε : ℝ} (pos : ε > 0): BoundedContinuousFunction E ℝ where
  toFun := (fun x => (g x) * (- (ε * (g x) * (g x))).exp)
  continuous_toFun := by continuity
  map_bounded' := by
    use 2 * ε.sqrt⁻¹
    exact bounded'_of_expeps2 hg pos

lemma tendsto_expeps2 {g : E → ℝ} (hg: Continuous g) (x : E)
    : Tendsto (fun ε => expeps2 hg ε x) (nhds 0) (nhds (g x)) := by
  have : g x = (fun ε : ℝ => expeps2 hg ε x) 0 := by
    simp only [expeps2, zero_mul, neg_zero, Real.exp_zero, mul_one, ContinuousMap.coe_mk]
  rw [this]
  apply Continuous.tendsto
  simp [expeps2]
  continuity

lemma tendsto_integral_expeps2 (g : BoundedContinuousFunction E ℝ) (P : FiniteMeasure E)
    : Tendsto (fun ε => ∫ (x : E), (expeps2 g.continuous ε x) ∂P)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ (x : E), g x ∂P)) := by
  apply tendsto_of_seq_tendsto
  intro u hu
  -- how to compress this into one line
  obtain ⟨_, hupos⟩ := tendsto_nhdsWithin_iff.mp hu
  obtain ⟨N, hupos⟩ := eventually_atTop.mp hupos
  have hbound : ∀ᶠ (n : ℕ) in Filter.atTop, ∀ᵐ (x : E) ∂P, abs ((expeps2 g.continuous (u n)) x) ≤ norm g := by
    rw [eventually_atTop]
    use N
    intro n hn
    exact eventually_of_forall
        (bounded_bynorm_of_expeps2 g (le_of_lt (Set.mem_Ioi.mp (hupos n hn))))
  have hlim : ∀ᵐ (x : E) ∂P, Filter.Tendsto (fun (n : ℕ) => (expeps2 g.continuous (u n)) x)
      Filter.atTop (nhds (g x)) := by
    apply eventually_of_forall
    intro x
    exact (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_expeps2 g.continuous x)).comp hu
  have hbp: eventually_boundedPointwise P (fun (n : ℕ) (x : E) => (expeps2 g.continuous (u n)) x) g := by
    refine { h_bound := ?h_bound, h_lim := hlim }
    · use norm g
      exact hbound
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => expeps2 g.continuous (u n) x) P := by
    intro n
    apply StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable _)
    continuity
  exact tendstoIntegral_of_eventually_boundedPointwise (eventually_of_forall hmeas) hbp
