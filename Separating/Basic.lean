import Mathlib

open scoped BigOperators

open MeasureTheory NNReal ENNReal

variable {Ω : Type*} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω]

lemma sub_integral_bounded [MeasurableSpace Ω] {X : Ω → E} {C : ℝ} (P : FiniteMeasure Ω) (hX : ∀ᵐ (ω : Ω) ∂P, ‖X ω‖ ≤ C)
    {K : Set Ω} (hK : MeasurableSet K) (hX1 : Integrable X P)
    : ‖∫ (ω : Ω), X ω ∂P - ∫ ω in K, X ω ∂P‖ ≤ P Kᶜ * C := by
  have : ∫ (ω : Ω), X ω ∂P - ∫ ω in K, X ω ∂P = ∫ ω in Kᶜ, X ω ∂P := by
    rw [sub_eq_iff_eq_add, add_comm, integral_add_compl hK hX1]
  rw [this]
  have h1 : ‖∫ ω in Kᶜ, X ω ∂P‖ ≤ ∫ (ω : Ω), ‖X ω‖ ∂(P.restrict Kᶜ) :=
    norm_integral_le_integral_norm X
  have h2 : ∫ ω in Kᶜ, ‖X ω‖ ∂P ≤ ∫ ω in Kᶜ, C ∂P :=
    integral_mono_ae (Integrable.restrict (Integrable.norm hX1))
        (integrable_const C) (ae_restrict_of_ae hX)
  have h3 : ∫ ω in Kᶜ, C ∂P = P Kᶜ * C := by
    rw [setIntegral_const C, smul_eq_mul]
    exact rfl
  apply le_trans h1 (le_trans h2 (le_of_eq h3))
