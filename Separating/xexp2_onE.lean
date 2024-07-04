import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Order.Bounded
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Separating.BoundedPointwiseConvergence

open MeasureTheory NNReal ENNReal BoundedContinuousFunction Filter

variable {E: Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E]
    {P : Measure E} [IsFiniteMeasure P]

--was previously named l1, and stated for functions defined on ℝ instead of E
lemma dist_le_of_mem_Icc {f : E → ℝ} (hf : ∃ C : ℝ, ∀ x, f x ∈ Set.Icc (-C) C)
    : ∃ (C : ℝ), ∀ (x y : E ), dist (f x) (f y) ≤ C := by
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

lemma bounded_of_xexp2 : ∀ (x : ℝ), abs (xexp2 x) ≤ 1 := by
  intro x
  rw [abs_le]
  constructor
  swap
  · exact bounded_above_of_xexpx2 x
  · rw [← xexp2_symm, neg_le_neg_iff]
    exact bounded_above_of_xexpx2 (-x)

lemma bounded_xexp2_of_interval: ∀ (x : ℝ), xexp2 x ∈ Set.Icc (-1) 1 := by
  simp_rw [Set.mem_Icc, ← abs_le]
  exact bounded_of_xexp2

lemma bounded_of_xexpx2' : ∃ (C : ℝ), ∀ (x : ℝ), xexp2 x ∈ Set.Icc (-C) C := by
  use 1
  exact bounded_xexp2_of_interval

noncomputable
def xexpx2' : BoundedContinuousFunction ℝ ℝ where
  toFun := xexp2
  continuous_toFun := Continuous.mul continuous_id' (Continuous.comp' Real.continuous_exp (Continuous.mul continuous_neg continuous_id'))
  map_bounded' := dist_le_of_mem_Icc bounded_of_xexpx2'


noncomputable
def expeps2 {g : E → ℝ} (hg: Continuous g) (ε : ℝ): ContinuousMap E ℝ where
  toFun := (fun x => (g x) * (- (ε * (g x) * (g x))).exp)
  continuous_toFun := by continuity

--this is l2 in xexp2
lemma l_expeps2 {g : E → ℝ} {x : E} {ε : ℝ} (hε : ε > 0)
    : (g x) * (Real.exp (- (ε * (g x) * (g x)))) = ε.sqrt⁻¹ * xexp2 (Real.sqrt ε * (g x)) := by
  simp only [neg_mul, one_div, xexp2]
  obtain h : ((ε.sqrt * g x * (ε.sqrt * g x))) = ε * (g x) * (g x):= by
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
  rw [l_expeps2 hε, abs_mul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos_of_pos hε))]
  nth_rw 2 [← mul_one ε.sqrt⁻¹]
  rw [mul_le_mul_left (inv_pos.mpr (Real.sqrt_pos_of_pos hε))]
  exact bounded_of_xexp2 (ε.sqrt * g x)

lemma bounded'_of_expeps2 {g : E → ℝ} (hg: Continuous g) {ε : ℝ} (hε : ε > 0)
    : ∀ (x y : E), dist (expeps2 hg ε x) (expeps2 hg ε y) ≤ 2 * ε.sqrt⁻¹ := by
  intro x y
  apply le_trans (dist_triangle (expeps2 hg ε x) 0 (expeps2 hg ε y))
  simp only [dist_zero_right, Real.norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (bounded_of_expeps2 hg hε x) (bounded_of_expeps2 hg hε y)

lemma bounded_bynorm_of_expeps2 (g : BoundedContinuousFunction E ℝ) {ε : ℝ} (hε : ε ≥ 0)
    : ∀ (x : E), abs ((expeps2 g.continuous ε) x) ≤ norm g := by
  intro x
  simp only [expeps2, ContinuousMap.coe_mk, abs_mul, Real.abs_exp]
  apply le_trans _ (g.norm_coe_le_norm x)
  apply mul_le_of_le_one_right (abs_nonneg (g x))
  apply Real.exp_le_one_iff.mpr
  rw [Left.neg_nonpos_iff, mul_assoc]
  apply mul_nonneg hε (mul_self_nonneg (g x))

noncomputable
def expeps2' {g : E → ℝ} (hg: Continuous g) {ε : ℝ} (pos : ε > 0): BoundedContinuousFunction E ℝ where
  toFun := (fun x => (g x) * (- (ε * (g x) * (g x))).exp)
  continuous_toFun := by continuity
  map_bounded' := by
    dsimp only [ContinuousMap.toFun_eq_coe, ContinuousMap.coe_mk]
    apply dist_le_of_mem_Icc
    use ε.sqrt⁻¹
    intro x
    rw [Set.mem_Icc, ← abs_le]
    exact bounded_of_expeps2 hg pos x

lemma tendsto_expeps2 {g : E → ℝ} (hg: Continuous g) (x : E)
    : Tendsto (fun ε => expeps2 hg ε x) (nhds 0) (nhds (g x)) := by
  have : g x = (fun ε : ℝ => expeps2 hg ε x) 0 := by
    simp only [expeps2, zero_mul, neg_zero, Real.exp_zero, mul_one, ContinuousMap.coe_mk]
  rw [this]
  apply Continuous.tendsto
  simp [expeps2]
  continuity

theorem tendsto_nhdsWithin_iff_seq_tendsto [TopologicalSpace X] [TopologicalSpace Y]
    [FrechetUrysohnSpace X] {f : X → Y} {a : X} {b : Y} :
    Tendsto f (nhdsWithin a s) (nhds b) ↔ ∀ u : ℕ → X, (∀ n, u n ∈ s)
        → Tendsto u atTop (nhdsWithin a s) → Tendsto (f ∘ u) atTop (nhds b) := by
  -- similar to tendsto_nhds_iff_seq_tendsto
  sorry

lemma tendsto_integral_expeps2 (g : BoundedContinuousFunction E ℝ) (P : FiniteMeasure E)
    : Tendsto (fun ε => ∫ (x : E), (expeps2 g.continuous ε x) ∂P)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ (x : E), g x ∂P)) := by
  rw [tendsto_nhdsWithin_iff_seq_tendsto]
  intro u hupos hulim
  have hbound : ∀ (n : ℕ), ∀ᵐ (x : E) ∂P, abs ((expeps2 g.continuous (u n)) x) ≤ norm g := by
    intro n
    apply eventually_of_forall
    exact bounded_bynorm_of_expeps2 g (le_of_lt (Set.mem_Ioi.mp (hupos n)))
  have hlim : ∀ᵐ (x : E) ∂P, Filter.Tendsto (fun (n : ℕ) => (expeps2 g.continuous (u n)) x)
      Filter.atTop (nhds (g x)) := by
    apply eventually_of_forall
    intro x
    have : Tendsto (fun ε ↦ (expeps2 g.continuous ε) x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g x)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (tendsto_expeps2 g.continuous x)
    rw [tendsto_nhdsWithin_iff_seq_tendsto] at this
    exact this u hupos hulim
  have hbp: boundedPointwise P (fun (n : ℕ) (x : E) => (expeps2 g.continuous (u n)) x) g := by
    refine { h_bound := ?h_bound, h_lim := ?h_lim }
    · use norm g; exact hbound
    · exact hlim
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => expeps2 g.continuous (u n) x) P := by
    intro n
    apply StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable _)
    continuity
  --change Tendsto (fun n ↦ ∫ (x : E), (expeps2 g.continuous (u n)) x ∂↑P) atTop (nhds (∫ (x : E), g x ∂↑P))
  apply tendstoIntegral_of_boundedPointwise
  · exact hmeas
  · exact hbp
