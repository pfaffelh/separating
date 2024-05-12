import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ContinuousFunction.Compact

open scoped BigOperators

open MeasureTheory NNReal ENNReal

variable {Ω : Type*} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω]

example (X : Ω → E) (C : ℝ) (hX : ∀ᵐ (ω : Ω) ∂P, ‖X ω‖ ≤ C) (K : Set α) (hK : measurable K) (P : FiniteMeasure Ω) (hX1 : Integrable X) : ‖∫ (ω : Ω), X ω ∂P - ∫ (ω : Ω), X ω ∂P‖ ≤ C * P Kᶜ := by
  sorry
