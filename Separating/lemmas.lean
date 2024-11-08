import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass
import Mathlib.Topology.TietzeExtension
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Collection of results used to prove 'theorem Subalgebra.separatesMeasures_of_separatesPoints'.
Should be moved to an appropriate position in the mathlib
-/

open MeasureTheory NNReal ENNReal BoundedContinuousFunction Filter

variable {Ω : Type*} [MeasurableSpace Ω]

--continuous bounded functions are separating
--Similar to FiniteMeasure.ext_of_forall_lintegral_eq, but for integrals instead of lower integrals
--  -> Mathlib.MeasureTheory.Measure.FiniteMeasure ?
theorem FiniteMeasure.ext_of_forall_integral_eq [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
    {P P' : FiniteMeasure Ω} (h : ∀ (f : Ω →ᵇ ℝ), ∫ x, f x ∂P = ∫ x, f x ∂P') :
    P = P' := by
  apply FiniteMeasure.ext_of_forall_lintegral_eq
  intro f
  apply (toReal_eq_toReal_iff' (ne_of_lt (lintegral_lt_top_of_nnreal P f))
      (ne_of_lt (lintegral_lt_top_of_nnreal P' f))).mp
  rw [toReal_lintegral_coe_eq_integral f P, toReal_lintegral_coe_eq_integral f P']
  exact h ⟨⟨fun x => (f x).toReal, Continuous.comp' NNReal.continuous_coe f.continuous⟩,
      f.map_bounded'⟩


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sub_integral_bounded {X : Ω → E} {C : ℝ} (P : Measure Ω) [IsFiniteMeasure P]
    (hX : ∀ᵐ (ω : Ω) ∂P, ‖X ω‖ ≤ C) {K : Set Ω} (hK : MeasurableSet K) (hX1 : Integrable X P)
    : ‖∫ (ω : Ω), X ω ∂P - ∫ ω in K, X ω ∂P‖ ≤ (P Kᶜ).toReal * C := by
  have : ∫ (ω : Ω), X ω ∂P - ∫ ω in K, X ω ∂P = ∫ ω in Kᶜ, X ω ∂P := by
    rw [sub_eq_iff_eq_add, add_comm, integral_add_compl hK hX1]
  rw [this]
  have h1 : ‖∫ ω in Kᶜ, X ω ∂P‖ ≤ ∫ (ω : Ω), ‖X ω‖ ∂(P.restrict Kᶜ) :=
    norm_integral_le_integral_norm X
  have h2 : ∫ ω in Kᶜ, ‖X ω‖ ∂P ≤ ∫ _ in Kᶜ, C ∂P :=
    integral_mono_ae (Integrable.restrict (Integrable.norm hX1))
        (integrable_const C) (ae_restrict_of_ae hX)
  have h3 : ∫ _ in Kᶜ, C ∂P = (P Kᶜ).toReal * C := by
    rw [setIntegral_const C, smul_eq_mul]
  apply le_trans h1 (le_trans h2 (le_of_eq h3))


variable {E: Type*} [TopologicalSpace E]

--stone-weierstrass approximation on a compact subset
--  -> Mathlib.Topology.ContinuousFunction.StoneWeierstrass
lemma exists_mem_subalgebra_near_continuous_on_compact_of_separatesPoints (f : C(E, ℝ))
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (pos : ε > 0) {A : Subalgebra ℝ C(E, ℝ)}
    (hA : A.SeparatesPoints) --(hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    : ∃ g ∈ A, (∀ x ∈ K, ‖(g : E → ℝ) x - f x‖ < ε) := by --∧ ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C
  --consider the subalgebra AK of functions with domain K
  let restrict_on_K : C(E, ℝ) →⋆ₐ[ℝ] C(K, ℝ) :=
    ContinuousMap.compStarAlgHom' ℝ ℝ ⟨(Subtype.val), continuous_subtype_val⟩
  let AK : Subalgebra ℝ C(K, ℝ) := Subalgebra.map restrict_on_K A
  have hsep : AK.SeparatesPoints := by
    intro x y hxy
    obtain ⟨_, ⟨g, hg1, hg2⟩, hg_sep⟩ := hA (Subtype.coe_ne_coe.mpr hxy)
    simp only [Set.mem_image, SetLike.mem_coe, exists_exists_and_eq_and]
    use restrict_on_K g
    constructor
    · rw [Subalgebra.mem_map]
      use g, hg1
      simp only [AlgHom.coe_coe]
    · change K.restrict (↑g) x ≠ K.restrict (↑g) y
      simp only [Set.restrict_apply, hg2]
      exact hg_sep
  have : CompactSpace ↑K := isCompact_iff_compactSpace.mp hK
  obtain ⟨⟨gK, hgKAK⟩, hgapprox⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      AK hsep (K.restrict f) (ContinuousOn.restrict (Continuous.continuousOn f.continuous)) ε pos
  obtain ⟨g, hgA, hgKAK⟩ := Subalgebra.mem_map.mp hgKAK
  use g, hgA
  intro x hxK
  have eqg : g x = gK ⟨x, hxK⟩ := by
    rw [← hgKAK]
    rfl
  rw [eqg]
  exact hgapprox ⟨x, hxK⟩

#lint
