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
