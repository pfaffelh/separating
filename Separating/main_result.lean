import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.SetIntegral
import Separating.xexp2_onE
import Separating.tight_singleton
import Separating.lemma_Plimexp
import Separating.lemmas

/-
# A subalgebra of functions separates measures if it separates points

We prove that a subalgebra of bounded continuous functions separates measures if it separates
points.

The key ingredient to the proof of 'theorem Subalgebra.separatesMeasures_of_separatesPoints'
is a result ('lemma key_lemma') that the integrals of an exponential transformation of a
BoundedContinuousFunction f wrt measures P, P', respectively are arbitrarily close. It uses a
decomposition into 7 parts, of which the approximation results are derived first, see
line1357_lemma, line26_lemma, line4_lemma.
-/

open scoped BigOperators

open MeasureTheory NNReal ENNReal BoundedContinuousFunction Filter

variable {E 𝕜: Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E] [RCLike 𝕜]
    {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']

lemma line1357_lemma (f : C(E, ℝ)) {K : Set E} (hK : MeasurableSet K)
    {ε : ℝ} (hε : ε > 0)  (hKP : P Kᶜ < ε.toNNReal)
    : abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
    - ∫ x in K, (expeps2 f.continuous ε) x ∂P) < ε.sqrt := by
  have hbound : ∀ᵐ (x : E) ∂P, ‖(expeps2 f.continuous ε) x‖ ≤ ε.sqrt⁻¹ :=
    eventually_of_forall (bounded_of_expeps2 f.continuous hε)
  have hint : Integrable (expeps2 f.continuous ε) P := by
    apply BoundedContinuousFunction.integrable P ⟨(expeps2 f.continuous ε), ⟨2 * ε.sqrt⁻¹, _⟩⟩
    exact bounded'_of_expeps2 f.continuous hε
  apply lt_of_le_of_lt (sub_integral_bounded P hbound hK hint)
  have leps : ε * ε.sqrt⁻¹ = ε.sqrt := by
    nth_rw 1 [← (Real.mul_self_sqrt (le_of_lt hε)), mul_assoc,
        CommGroupWithZero.mul_inv_cancel ε.sqrt (ne_of_gt (Real.sqrt_pos_of_pos hε)), mul_one]
  nth_rw 2 [← leps]
  exact (_root_.mul_lt_mul_right (inv_pos.mpr (Real.sqrt_pos.mpr hε))).mpr
      (ENNReal.toReal_lt_of_lt_ofReal hKP)

lemma line4_lemma {A : Subalgebra ℝ C(E, ℝ)} {ε : ℝ}
    (hε : ε > 0) (hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P')
    : ∀ (g : A), ∫ (x : E), (expeps2 (g : C(E, ℝ)).continuous ε) x ∂P
        = ∫ (x : E), (expeps2 (g : C(E, ℝ)).continuous ε) x ∂P' := by
  rintro ⟨g, hgA⟩
  obtain ⟨C, h⟩ := hbound g hgA
  --redefine g as a BoundedContinuousFunction
  let gb := mkOfBound g C h
  have : ∀ (n : ℕ), g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n ∈ A := by
    intro n
    apply Subalgebra.mul_mem A hgA (Subalgebra.pow_mem A _ n)
    apply Subalgebra.add_mem A (Subalgebra.one_mem A) (Subalgebra.smul_mem A _ n⁻¹)
    exact Subalgebra.neg_mem A (Subalgebra.mul_mem A (Subalgebra.smul_mem A hgA ε) hgA)
  have heqfun : (fun n : ℕ => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂ P)
      = (fun n : ℕ => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂ P') := by
    apply funext (fun n => heq _ (this n))
  have limP : Tendsto (fun n : ℕ => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂ P) atTop
      (nhds (∫ (x : E), (expeps2 (g : C(E, ℝ)).continuous ε) x ∂P')) := by
    rw [heqfun]
    exact Plimexp gb hε P'
  apply tendsto_nhds_unique (Plimexp gb hε P) limP

lemma line26_lemma {K : Set E} (hK : IsCompact K) (h'K : MeasurableSet K) (f g : C(E, ℝ))
    {ε δ : ℝ} (hε : ε > 0) {P : Measure E} [hP : IsFiniteMeasure P]
    (hfg : ∀ x ∈ K, abs (g x - f x) < δ)
    : abs (∫ x in K, (expeps2 g.continuous ε) x ∂P
        - ∫ x in K, (expeps2 f.continuous ε) x ∂P) ≤ δ * (P K).toReal := by
  have : ∀ x ∈ K, norm ((expeps2 g.continuous ε) x - (expeps2 f.continuous ε) x) ≤ δ :=
    fun x hxK => le_trans (lipschitz_of_expeps2 f.continuous g.continuous hε x) (le_of_lt (hfg x hxK))
  have integrable_expeps2 : ∀ f : C(E, ℝ), Integrable (fun x ↦ (expeps2 f.continuous ε) x) (P.restrict K) :=
    fun f => ContinuousOn.integrableOn_compact' hK h'K
        (Continuous.continuousOn (expeps2 f.continuous ε).continuous)
  rw [← (integral_sub (integrable_expeps2 g) (integrable_expeps2 f))]
  · apply norm_setIntegral_le_of_norm_le_const (IsCompact.measure_lt_top hK) this
      (StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable _))
    continuity

-- special case of 'dist_le_range_sum_dist'
lemma dist_triangle8 {a b c d e f g h : ℝ} :   abs (a - h) ≤   abs (a - b) +   abs (b - c) +   abs (c - d)
    +   abs (d - e) +   abs (e - f) +   abs (f - g) +   abs (g - h) := by
  --rw [← distabs, ← distabs, ← distabs, ← distabs, ← distabs, ← distabs, ← distabs, ← distabs]
  apply le_trans (dist_triangle4 a f g h)
  apply add_le_add_right (add_le_add_right _ (dist f g)) (dist g h)
  apply le_trans (dist_triangle4 a d e f)
  apply add_le_add_right (add_le_add_right _ (dist d e)) (dist e f)
  exact dist_triangle4 a b c d

--key lemma for the proof
lemma key_lemma [CompleteSpace E] [SecondCountableTopology E] (f : BoundedContinuousFunction E ℝ)
    {A : Subalgebra ℝ C(E, ℝ)} (hA : A.SeparatesPoints)
    (hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P')
    : ∀ ε > 0, abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
        - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') ≤ 6 * ε.sqrt := by
  intro ε hε
  -- if both measures are zero, the result is trivial
  by_cases hPP' : P = 0 ∧ P' = 0
  · simp only [hPP', integral_zero_measure, sub_self, abs_zero, gt_iff_lt, Nat.ofNat_pos,
    mul_nonneg_iff_of_pos_left, (le_of_lt (Real.sqrt_pos_of_pos hε))]
  -- if not, we use (ε.sqrt * (inverse of the following constant)) in the application of stone-weierstrass
  let const : ℝ := (max (P Set.univ).toReal (P' Set.univ).toReal)
  have pos_of_measure : const > 0 := by
    rw [Mathlib.Tactic.PushNeg.not_and_or_eq] at hPP'
    cases' hPP' with hP0 hP'0
    · exact lt_max_of_lt_left
        (toReal_pos ((Measure.measure_univ_ne_zero).mpr hP0) (measure_ne_top P Set.univ))
    · exact lt_max_of_lt_right
        (toReal_pos ((Measure.measure_univ_ne_zero).mpr hP'0) (measure_ne_top P' Set.univ))
  have pos : ε.sqrt * const⁻¹ > 0 := by
    apply Left.mul_pos (Real.sqrt_pos_of_pos hε) (inv_pos_of_pos pos_of_measure)
  -- obtain K, a compact and closed set, which covers E up to a small area of measure at most ε
  -- wrt to both P and P'
  obtain ⟨KP, hKPc, hKP⟩ := tight_singleton P hε
  obtain ⟨KP', hKP'c, hKP'⟩ := tight_singleton P' hε
  let K := KP ∪ KP'
  have hKco := IsCompact.union hKPc.1 hKP'c.1
  have hKcl := IsClosed.union hKPc.2 hKP'c.2
  have hKPbound : P (KP ∪ KP')ᶜ < ε.toNNReal := lt_of_le_of_lt
        (measure_mono (Set.compl_subset_compl_of_subset (Set.subset_union_left KP KP'))) hKP
  have hKP'bound : P' (KP ∪ KP')ᶜ < ε.toNNReal := lt_of_le_of_lt
        (measure_mono (Set.compl_subset_compl_of_subset (Set.subset_union_right KP KP'))) hKP'
  -- stone-weierstrass approximation of f on K
  obtain ⟨g, hgA, hgapprox⟩ :=
      exists_mem_subalgebra_near_continuous_on_compact_of_separatesPoints f hKco pos hA
  -- collect the results needed in the decomposition at the end of the proof
  have line1 : abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ x in K, (expeps2 f.continuous ε) x ∂P) < ε.sqrt :=
    line1357_lemma f (IsClosed.measurableSet hKcl) hε hKPbound
  have line3 : abs (∫ x in K, (expeps2 g.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 g.continuous ε) x ∂P) < ε.sqrt := by
    rw [abs_sub_comm]
    apply (line1357_lemma g (IsClosed.measurableSet hKcl) hε hKPbound)
  have line5 : abs (∫ (x : E), (expeps2 g.continuous ε) x ∂P'
      - ∫ x in K, (expeps2 g.continuous ε) x ∂P') < ε.sqrt :=
    (line1357_lemma g (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line7 : abs (∫ x in K, (expeps2 f.continuous ε) x ∂P'
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') < ε.sqrt := by
    rw [abs_sub_comm]
    apply (line1357_lemma f (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line2 : abs (∫ x in K, (expeps2 f.continuous ε) x ∂P
      - ∫ x in K, (expeps2 g.continuous ε) x ∂P) ≤ ε.sqrt := by
    rw [abs_sub_comm]
    apply le_trans (line26_lemma hKco (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (Real.sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le (le_max_of_le_left _) (le_of_lt pos_of_measure)
    exact (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mpr
        (measure_mono (Set.subset_univ _))
  have line6 : abs (∫ x in K, (expeps2 g.continuous ε) x ∂P'
      - ∫ x in K, (expeps2 f.continuous ε) x ∂P') ≤ ε.sqrt := by
    apply le_trans (line26_lemma hKco (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (Real.sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le (le_max_of_le_right _) (le_of_lt pos_of_measure)
    exact (ENNReal.toReal_le_toReal (measure_ne_top P' _) (measure_ne_top P' _)).mpr
        (measure_mono (Set.subset_univ _))
  have line4 : abs (∫ (x : E), (expeps2 g.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 g.continuous ε) x ∂P') = 0 := by
    rw [abs_eq_zero, sub_eq_zero]
    apply line4_lemma hε hbound heq ⟨g, hgA⟩
  calc
    abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') ≤
    abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P - ∫ x in K, (expeps2 f.continuous ε) x ∂P)
    + abs (∫ x in K, (expeps2 f.continuous ε) x ∂P - ∫ x in K, (expeps2 g.continuous ε) x ∂P)
    + abs (∫ x in K, (expeps2 g.continuous ε) x ∂P - ∫ (x : E), (expeps2 g.continuous ε) x ∂P)
    + abs (∫ (x : E), (expeps2 g.continuous ε) x ∂P - ∫ (x : E), (expeps2 g.continuous ε) x ∂P')
    + abs (∫ (x : E), (expeps2 g.continuous ε) x ∂P' - ∫ x in K, (expeps2 g.continuous ε) x ∂P')
    + abs (∫ x in K, (expeps2 g.continuous ε) x ∂P' - ∫ x in K, (expeps2 f.continuous ε) x ∂P')
    + abs (∫ x in K, (expeps2 f.continuous ε) x ∂P' - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') :=
      dist_triangle8
    _ ≤ 6 * ε.sqrt := by linarith


theorem Subalgebra.separatesMeasures_of_separatesPoints [CompleteSpace E] [SecondCountableTopology E]
    {A : StarSubalgebra 𝕜 C(E, 𝕜)} (hA : A.SeparatesPoints) {P P' : FiniteMeasure E}
    (hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ (x : E), (g : E → 𝕜) x ∂P = ∫ (x : E), (g : E → 𝕜) x ∂P') : P = P' := by
  --consider the real subalgebra of the purely real-valued elements of A
  let A' := (A.restrictScalars ℝ).comap
      (RCLike.ofRealAm.compLeftContinuous ℝ RCLike.continuous_ofReal)
  --the real subalgebra separates points
  have hA' : A'.SeparatesPoints := Subalgebra.SeparatesPoints.rclike_to_real hA
  --elements of the real subalgebra are bounded
  have hbound' : ∀ g ∈ A', ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C := by
    intro g hgA'
    let G : C(E, 𝕜) := (RCLike.ofRealAm.compLeftContinuous ℝ RCLike.continuous_ofReal) g
    have h : ∀ x, G x = g x := by
      exact fun x ↦ rfl
    obtain ⟨C, hboundC⟩ := hbound ((RCLike.ofRealAm.compLeftContinuous ℝ RCLike.continuous_ofReal) g) hgA'
    use C
    intro x y
    specialize hboundC x y
    rw [NormedAddGroup.dist_eq] at *
    rw [h x, h y, ← RCLike.ofReal_sub _ _, RCLike.norm_ofReal] at hboundC
    exact hboundC
  --integrals of elements of the real subalgebra wrt P, P', respectively, coincide
  have heq' : ∀ g ∈ A', ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P' := by
    intro g hgA'
    rw [← @RCLike.ofReal_inj 𝕜, ← integral_ofReal, ← integral_ofReal]
    exact heq ((RCLike.ofRealAm.compLeftContinuous ℝ RCLike.continuous_ofReal) g) hgA'
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  have key : ∀ (ε : ℝ) (_ : ε > 0),
      abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P - ∫ (x : E), (expeps2 f.continuous ε) x ∂P')
      ≤ 6 * ε.sqrt := by
    apply key_lemma f hA' hbound' heq'
  have lim1 : Tendsto (fun ε => abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P')) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hle : ∀ᶠ ε in (nhdsWithin 0 (Set.Ioi 0)), abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') ≤ 6 * ε.sqrt := by
      apply eventually_nhdsWithin_of_forall
      intro ε hε
      exact key ε (Set.mem_Ioi.1 hε)
    have g0 : Tendsto (fun ε : ℝ => 6 * ε.sqrt) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      nth_rewrite 3 [← mul_zero 6]
      apply tendsto_nhdsWithin_of_tendsto_nhds (Tendsto.const_mul 6 _)
      nth_rewrite 2 [← Real.sqrt_zero]
      apply Continuous.tendsto Real.continuous_sqrt
    apply squeeze_zero' (eventually_nhdsWithin_of_forall (fun x _ => abs_nonneg _)) hle g0
  have lim2 : Tendsto (fun ε => abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P')) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (abs (∫ (x : E), f x ∂↑P - ∫ (x : E), f x ∂↑P'))) :=
    Tendsto.abs (Filter.Tendsto.sub (tendsto_integral_expeps2 f P) (tendsto_integral_expeps2 f P'))
  apply eq_of_abs_sub_eq_zero (tendsto_nhds_unique lim2 lim1)

#lint
