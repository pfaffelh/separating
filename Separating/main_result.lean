import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.SetIntegral
import Separating.xexp2_onE
import Separating.tight_singleton
import Separating.lemma_Plimexp

open scoped BigOperators

open MeasureTheory NNReal ENNReal BoundedContinuousFunction Filter

variable {E 𝕜: Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E] [RCLike 𝕜]
    {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']


lemma eq_of_toReal_eq {x y : ℝ≥0∞} (hx : x < ∞) (hy : y < ∞) : ENNReal.toReal x = ENNReal.toReal y → x = y := by
  rw [lt_top_iff_ne_top] at *
  intro hxy
  rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_toReal hy]
  apply congrArg ENNReal.ofReal hxy

--coercion from BoundedContinuousFunction E ℝ≥0 to BoundedContinuousFunction E ℝ
noncomputable
def coetoreal (g : BoundedContinuousFunction E ℝ≥0) : BoundedContinuousFunction E ℝ where
  toFun := (fun x => (g x))
  continuous_toFun := by continuity
  map_bounded' := g.map_bounded'

--continuous bounded functions are separating
--Similar to FiniteMeasure.ext_of_forall_lintegral_eq, but for integrals instead of lower integrals
theorem FiniteMeasure.ext_of_forall_integral_eq [HasOuterApproxClosed E] [BorelSpace E]
    {P P' : FiniteMeasure E} (h : ∀ (f : E →ᵇ ℝ), ∫ x, f x ∂P = ∫ x, f x ∂P') :
    P = P' := by
  apply FiniteMeasure.ext_of_forall_lintegral_eq
  intro f
  specialize h (coetoreal f)
  apply eq_of_toReal_eq (BoundedContinuousFunction.lintegral_lt_top_of_nnreal P f)
      (BoundedContinuousFunction.lintegral_lt_top_of_nnreal P' f)
  rw [BoundedContinuousFunction.toReal_lintegral_coe_eq_integral f P,
      BoundedContinuousFunction.toReal_lintegral_coe_eq_integral f P']
  exact h


--stone-weierstrass
lemma sw (f : BoundedContinuousFunction E ℝ) {K : Set E} (hK : IsCompact K) {ε : ℝ} (pos : ε > 0)
    {A : Subalgebra ℝ C(E, ℝ)} (hA : A.SeparatesPoints)
    : ∃ g ∈ A, ∀ x : K, ‖(g : E → ℝ) x - f x‖ < ε := by
  --apply Stone-Weierstrass to K.restrict f to obtain a function g' : K → ℝ ∈ A
  --extend g' to a continuous function on E
  sorry

lemma line1357_lemma [CompleteSpace E] [SecondCountableTopology E] (f : C(E, ℝ))
    {K : Set E} (hK : MeasurableSet K) {ε : ℝ} (pos : ε > 0)  (hKP : P Kᶜ < ε.toNNReal)
    : abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
    - ∫ x in K, (expeps2 f.continuous ε) x ∂P) < ε.sqrt := by
  have hbound : ∀ᵐ (x : E) ∂P, ‖(expeps2 f.continuous ε) x‖ ≤ ε.sqrt⁻¹ :=
    eventually_of_forall (bounded_of_expeps2 f.continuous pos)
  have hint : Integrable (expeps2 f.continuous ε) P := by
    apply BoundedContinuousFunction.integrable P ⟨(expeps2 f.continuous ε), ⟨2 * ε.sqrt⁻¹, _⟩⟩
    exact bounded'_of_expeps2 f.continuous pos
  apply lt_of_le_of_lt (sub_integral_bounded P hbound hK hint)
  have leps : ε * ε.sqrt⁻¹ = ε.sqrt := by
    nth_rw 1 [← (Real.mul_self_sqrt (le_of_lt pos)), mul_assoc,
        CommGroupWithZero.mul_inv_cancel ε.sqrt (ne_of_gt (Real.sqrt_pos_of_pos pos)), mul_one]
  nth_rw 2 [← leps]
  exact (_root_.mul_lt_mul_right (inv_pos.mpr (Real.sqrt_pos.mpr pos))).mpr
      (ENNReal.toReal_lt_of_lt_ofReal hKP)


--need boundedness of functions in A here
lemma line4_lemma [CompleteSpace E] [SecondCountableTopology E] {A : Subalgebra ℝ (E →ᵇ ℝ)}
    (hA : Set.SeparatesPoints ((fun f : (E →ᵇ ℝ) => (f : E → ℝ)) '' (A : Set (E →ᵇ ℝ)))) --how do i say this easier?
    (heq : ∀ (g : A), ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P')
    : ∀ (g : A), ∫ (x : E), (expeps2 (g : C(E, ℝ)).continuous ε) x ∂P
        = ∫ (x : E), (expeps2 (g : C(E, ℝ)).continuous ε) x ∂P' := by
  rintro ⟨g, hgA⟩
  have : ∀ n, ∫ (x : E), (g x) * exp_seq (-(ε * g x * g x)) n ∂ P
      = ∫ (x : E), (g x) * exp_seq (-(ε * g x * g x)) n ∂ P' := by
    sorry
  sorry

--key lemma for the proof
lemma key_lemma [CompleteSpace E] [SecondCountableTopology E] (f : BoundedContinuousFunction E ℝ)
    {A : Subalgebra ℝ C(E, ℝ)} (hA : A.SeparatesPoints)
    (heq : ∀ (g : A), ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P')
    : ∀ (ε : ℝ) (pos : ε > 0), abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
        - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') < 6 * ε.sqrt := by
  intro ε pos
  obtain ⟨KP, hKPc, hKP⟩ := tight_singleton P pos
  obtain ⟨KP', hKP'c, hKP'⟩ := tight_singleton P' pos
  -- TODO: compress the following two lines using obtain
  let K := KP ∪ KP'
  have hKco := IsCompact.union hKPc.1 hKP'c.1
  have hKcl := IsClosed.union hKPc.2 hKP'c.2
  have hKPbound : (P Kᶜ) < ε.toNNReal := by
    simp [K]
    apply lt_of_le_of_lt (measure_mono (Set.inter_subset_left KPᶜ KP'ᶜ)) hKP
  have hKP'bound : (P' Kᶜ) < ε.toNNReal := by
    simp [K]
    apply lt_of_le_of_lt (measure_mono (Set.inter_subset_right KPᶜ KP'ᶜ)) hKP'
  obtain ⟨g, hgA, hg⟩ := sw f hKco pos hA
  have line1 : abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ x in K, (expeps2 f.continuous ε) x ∂P) < ε.sqrt :=
    line1357_lemma f (IsClosed.measurableSet hKcl) pos hKPbound
  have line3 : abs (∫ x in K, (expeps2 g.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 g.continuous ε) x ∂P) < ε.sqrt := by
    rw [abs_sub_comm]
    apply (line1357_lemma g (IsClosed.measurableSet hKcl) pos hKPbound)
  have line5 : abs (∫ (x : E), (expeps2 g.continuous ε) x ∂P'
      - ∫ x in K, (expeps2 g.continuous ε) x ∂P') < ε.sqrt :=
    (line1357_lemma g (IsClosed.measurableSet hKcl) pos hKP'bound)
  have line7 : abs (∫ x in K, (expeps2 f.continuous ε) x ∂P'
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') < ε.sqrt := by
    rw [abs_sub_comm]
    apply (line1357_lemma f (IsClosed.measurableSet hKcl) pos hKP'bound)
  have line2 : abs (∫ x in K, (expeps2 f.continuous ε) x ∂P
      - ∫ x in K, (expeps2 g.continuous ε) x ∂P) < ε.sqrt := by
    --use sw together with some strong enough continuity property of x → x * (ε * x ^ 2).exp
    sorry
  have line6 : abs (∫ x in K, (expeps2 g.continuous ε) x ∂P'
      - ∫ x in K, (expeps2 f.continuous ε) x ∂P') < ε.sqrt := by
    --use sw together with some strong enough continuity property of x → x * (ε * x ^ 2).exp
    sorry
  have line4 : abs (∫ (x : E), (expeps2 g.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 g.continuous ε) x ∂P') = 0 := by
    -- use line4_lemma
    sorry
  calc
    abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') ≤
        abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P - ∫ x in K, (expeps2 f.continuous ε) x ∂P)
        + abs (∫ x in K, (expeps2 f.continuous ε) x ∂P - ∫ x in K, (expeps2 g.continuous ε) x ∂P)
        + abs (∫ x in K, (expeps2 g.continuous ε) x ∂P - ∫ (x : E), (expeps2 g.continuous ε) x ∂P)
        --+ abs (∫ (x : E), (expeps2 g.continuous ε) x ∂P - ∫ (x : E), (expeps2 g.continuous ε) x ∂P')
        + abs (∫ (x : E), (expeps2 g.continuous ε) x ∂P' - ∫ x in K, (expeps2 g.continuous ε) x ∂P')
        + abs (∫ x in K, (expeps2 g.continuous ε) x ∂P' - ∫ x in K, (expeps2 f.continuous ε) x ∂P')
        + abs (∫ x in K, (expeps2 f.continuous ε) x ∂P' - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') := by sorry
    _ < 6 * ε.sqrt := by linarith
  --sorry

theorem sep_of_sep_points [CompleteSpace E] [SecondCountableTopology E]
    {A : StarSubalgebra 𝕜 C(E, 𝕜)} (hA : A.SeparatesPoints) {P P' : FiniteMeasure E}
    (heq : ∀ (g : A), ∫ (x : E), (g : E → 𝕜) x ∂P = ∫ (x : E), (g : E → 𝕜) x ∂P') : P = P' := by
  --consider the real subalgebra of the purely real-valued elements of A
  let A' := (A.restrictScalars ℝ).comap
      (RCLike.ofRealAm.compLeftContinuous ℝ RCLike.continuous_ofReal)
  --the real subalgebra separates points
  have hA' : A'.SeparatesPoints := Subalgebra.SeparatesPoints.rclike_to_real hA
  apply FiniteMeasure.ext_of_forall_integral_eq
  --integrals of elements of the real subalgebra wrt P, P', respectively, coincide
  have heq' : ∀ (g : A'), ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P' := by
    sorry
  intro f
  have key : ∀ (ε : ℝ) (hε : 0 < ε),
      abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') < 6 * ε.sqrt := by
    apply key_lemma f hA' heq'
  have lim1 : Tendsto (fun ε => abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P')) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have pos : ∀ᶠ ε in (nhdsWithin 0 (Set.Ioi 0)), 0 ≤ abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P')  := by
      apply eventually_nhdsWithin_of_forall
      intro x hx
      apply abs_nonneg
    have hle : ∀ᶠ ε in (nhdsWithin 0 (Set.Ioi 0)), abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P') ≤ 6 * ε.sqrt := by
      apply eventually_nhdsWithin_of_forall
      intro ε hε
      exact le_of_lt (key ε (Set.mem_Ioi.1 hε))
    have g0 : Tendsto (fun ε : ℝ => 6 * ε.sqrt) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      nth_rewrite 3 [← mul_zero 6]
      apply Tendsto.const_mul 6 --
      apply tendsto_nhdsWithin_of_tendsto_nhds
      nth_rewrite 2 [← Real.sqrt_zero]
      apply Continuous.tendsto Real.continuous_sqrt
    apply squeeze_zero' pos hle g0
  have lim2 : Tendsto (fun ε => abs (∫ (x : E), (expeps2 f.continuous ε) x ∂P
      - ∫ (x : E), (expeps2 f.continuous ε) x ∂P')) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (abs (∫ (x : E), f x ∂↑P - ∫ (x : E), f x ∂↑P'))) :=
    Tendsto.abs (Filter.Tendsto.sub (tendsto_integral_expeps2 f P) (tendsto_integral_expeps2 f P'))
  apply eq_of_abs_sub_eq_zero
  apply tendsto_nhds_unique lim2 lim1
