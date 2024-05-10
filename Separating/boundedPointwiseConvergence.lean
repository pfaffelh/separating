import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded pointwise convergence

If some f : Ω → ℝ and a sequence f : ℕ → Ω → ℝ, all measurable, is such that ∀ ω, tendsTo N (f n ω) N (f ω) and { f n ω | n ∈ ℕ, ω ∈ Ω } is bounded, almost surely, we say that f n converges to f boundedly pointwise.

This notion is helpful since, for any probability (or finite) measure) P, we then have that ∫ f n ω ∂P dω → ∫ f ω ∂P dω by dominated convergence.

-/

open scoped BigOperators

open MeasureTheory NNReal ENNReal

@[class] structure boundedPointwise {Ω : Type*} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω] (P : FiniteMeasure Ω) (X : ℕ → Ω → E) (Z : Ω → E) where
 h_bound : ∃ C, ∀ (n : ℕ), ∀ᵐ (ω : Ω) ∂P, ‖X n ω‖ ≤ C
 h_lim : ∀ᵐ (ω : Ω) ∂P, Filter.Tendsto (fun (n : ℕ) => X n ω) Filter.atTop (nhds (Z ω))

lemma integral_constant_finite_of_finiteMeasure {Ω : Type*} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω] {P : FiniteMeasure Ω} (c : E) : Integrable (fun _ : Ω => c) (MeasureTheory.FiniteMeasure.toMeasure P) := by
simp only [integrable_const]

lemma tendstoIntegral_of_boundedPointwise {Ω : Type*} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω] {P : FiniteMeasure Ω} (X : ℕ → Ω → E) (Z : Ω → E) (h_meas1 : ∀ n, MeasureTheory.AEStronglyMeasurable (X n) P) (hbp: boundedPointwise P X Z) : Filter.Tendsto (fun (n : ℕ) => ∫ (ω : Ω), X n ω ∂P) Filter.atTop (nhds (∫ (ω : Ω), Z ω ∂P)) := by
  cases' hbp.h_bound with c h
  let C : Ω → ℝ := (fun _ => c)
  refine MeasureTheory.tendsto_integral_of_dominated_convergence C h_meas1 (integral_constant_finite_of_finiteMeasure c) h hbp.h_lim

@[class] structure boundedPointwise' (X : ℕ → Ω → ℝ≥0∞) (Z : Ω → ℝ≥0∞) where
  h_aefinite : ∀ n, ∀ᵐ (ω : Ω) ∂μ, (X n ω) ≠ ⊤
  h_bound: ∃ C : Set ℝ≥0, Bornology.IsBounded C → ∀ n, ∀ᵐ (ω : Ω) ∂μ, (X n ω).toNNReal ∈ C
  h_conv : ∀ᵐ (ω : Ω) ∂μ, Filter.Tendsto (fun n => X n ω) Filter.atTop (nhds (Z ω))
