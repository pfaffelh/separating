import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.SetIntegral

open MeasureTheory NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

--proof tightness of a singleton using lemmas from kolmogorov extension
lemma tight_singleton [PseudoEMetricSpace Ω] [CompleteSpace Ω]
    [SecondCountableTopology Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {ε : ℝ} (pos : ε > 0)
    : ∃ (s : Set Ω), (IsCompact s ∧ IsClosed s) ∧ (P sᶜ < ε.toNNReal) := by
  have innerRegular_isCompact_isClosed_measurableSet_of_complete_countable
      : Measure.InnerRegularWRT P (fun s => IsCompact s ∧ IsClosed s) MeasurableSet := by
    -- import KolmogorovExtension4.RegularityCompacts
    -- innerRegular_isCompact_isClosed_measurableSet_of_complete_countable
    sorry
  /-
  "MeasurableSet.exists_isCompact_diff_lt MeasurableSet.univ (measure_ne_top P Set.univ) pos"
  does not work here, as they assume [T2Space Ω] to ensure a compact set is measurable. Typically,
  pseudometric spaces are not T2. We really need InnerRegularWRT both IsCompact AND IsClosed here.
  -/
  obtain ⟨K, hKuniv, hKcc, hK⟩ := Measure.InnerRegularWRT.exists_subset_lt_add
        innerRegular_isCompact_isClosed_measurableSet_of_complete_countable
        ⟨isCompact_empty, isClosed_empty⟩ (MeasurableSet.univ) (measure_ne_top P Set.univ)
        (pos_iff_ne_zero.mp (ENNReal.ofReal_pos.mpr pos))
  have : P Kᶜ < ε.toNNReal := by
    rw [Set.compl_eq_univ_diff]
    exact measure_diff_lt_of_lt_add (IsClosed.measurableSet hKcc.2) hKuniv (measure_ne_top P K) hK
  exact ⟨K, hKcc, this⟩

--the following result was already stated in the file "Basic", withput proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sub_integral_bounded [MeasurableSpace Ω] {X : Ω → E} {C : ℝ} (P : Measure Ω) [IsFiniteMeasure P]
    (hX : ∀ᵐ (ω : Ω) ∂P, ‖X ω‖ ≤ C) {K : Set Ω} (hK : MeasurableSet K) (hX1 : Integrable X P)
    : ‖∫ (ω : Ω), X ω ∂P - ∫ ω in K, X ω ∂P‖ ≤ (P Kᶜ).toReal * C := by
  have : ∫ (ω : Ω), X ω ∂P - ∫ ω in K, X ω ∂P = ∫ ω in Kᶜ, X ω ∂P := by
    rw [sub_eq_iff_eq_add, add_comm, integral_add_compl hK hX1]
  rw [this]
  have h1 : ‖∫ ω in Kᶜ, X ω ∂P‖ ≤ ∫ (ω : Ω), ‖X ω‖ ∂(P.restrict Kᶜ) :=
    norm_integral_le_integral_norm X
  have h2 : ∫ ω in Kᶜ, ‖X ω‖ ∂P ≤ ∫ ω in Kᶜ, C ∂P :=
    integral_mono_ae (Integrable.restrict (Integrable.norm hX1))
        (integrable_const C) (ae_restrict_of_ae hX)
  have h3 : ∫ ω in Kᶜ, C ∂P = (P Kᶜ).toReal * C := by
    rw [setIntegral_const C, smul_eq_mul]
  apply le_trans h1 (le_trans h2 (le_of_eq h3))
