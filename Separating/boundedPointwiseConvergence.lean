import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded pointwise convergence

If some f : Ω → ℝ and a sequence f : ℕ → Ω → ℝ, all measurable, is such that

∀ ω, (f n ω) → (f ω) as n → ∞, and
{ f n ω | n ∈ ℕ, ω ∈ Ω } is bounded, almost surely,

we say that f n converges to f boundedly pointwise. This notion is helpful since, for any
probability (or finite) measure) P, we then have that

∫ f n ω ∂P dω → ∫ f ω ∂P dω

by dominated convergence.
-/

open scoped BigOperators

open MeasureTheory NNReal ENNReal

variable {Ω : Type*} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω]

/-- docBlame -/
class boundedPointwise (P : Measure Ω) (X : ℕ → Ω → E) (Z : Ω → E) : Prop where
 h_bound : ∃ C, ∀ (n : ℕ), ∀ᵐ (ω : Ω) ∂P, ‖X n ω‖ ≤ C
 h_lim : ∀ᵐ (ω : Ω) ∂P, Filter.Tendsto (fun (n : ℕ) => X n ω) Filter.atTop (nhds (Z ω))

lemma integral_constant_finite_of_finiteMeasure {P : Measure Ω} [IsFiniteMeasure P] (c : E)
    : Integrable (fun _ : Ω => c) P := by
simp only [integrable_const]

lemma tendstoIntegral_of_boundedPointwise {P : Measure Ω} [IsFiniteMeasure P] (X : ℕ → Ω → E) (Z : Ω → E)
    (h_meas : ∀ n, MeasureTheory.AEStronglyMeasurable (X n) P) (hbp: boundedPointwise P X Z)
    : Filter.Tendsto (fun (n : ℕ) => ∫ (ω : Ω), X n ω ∂P) Filter.atTop (nhds (∫ (ω : Ω), Z ω ∂P)) := by
  cases' hbp.h_bound with c h_boundc
  let C : Ω → ℝ := (fun _ => c)
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
      C h_meas (integral_constant_finite_of_finiteMeasure c) h_boundc hbp.h_lim

-- not used ?
/-- docBlame -/
class boundedPointwise' (X : ℕ → Ω → ℝ≥0∞) (Z : Ω → ℝ≥0∞) : Prop where
  h_aefinite : ∀ n, ∀ᵐ (ω : Ω) ∂μ, (X n ω) ≠ ⊤
  h_bound: ∃ C : Set ℝ≥0, Bornology.IsBounded C → ∀ n, ∀ᵐ (ω : Ω) ∂μ, (X n ω).toNNReal ∈ C
  h_conv : ∀ᵐ (ω : Ω) ∂μ, Filter.Tendsto (fun n => X n ω) Filter.atTop (nhds (Z ω))

/-- docBlame -/
class eventually_boundedPointwise (P : Measure Ω) (X : ℕ → Ω → E) (Z : Ω → E) : Prop where
 h_bound : ∃ C, ∀ᶠ (n : ℕ) in Filter.atTop, (∀ᵐ (ω : Ω) ∂P, ‖X n ω‖ ≤ C)
 h_lim : ∀ᵐ (ω : Ω) ∂P, Filter.Tendsto (fun (n : ℕ) => X n ω) Filter.atTop (nhds (Z ω))

lemma eventually_boundedPointwise_of_boundedPointwise {P : Measure Ω} {X : ℕ → Ω → E} {Z : Ω → E}
    (hbp : boundedPointwise P X Z)
    : eventually_boundedPointwise P X Z := by
  cases' hbp.h_bound with c h_boundc
  exact ⟨⟨c, @Filter.eventually_of_forall _ _ Filter.atTop h_boundc⟩, hbp.h_lim⟩

lemma tendstoIntegral_of_eventually_boundedPointwise {P : Measure Ω} [IsFiniteMeasure P] {X : ℕ → Ω → E} {Z : Ω → E}
    (h_meas : ∀ᶠ (n : ℕ) in Filter.atTop, MeasureTheory.AEStronglyMeasurable (X n) P)
    (hbp : eventually_boundedPointwise P X Z)
    : Filter.Tendsto (fun (n : ℕ) => ∫ (ω : Ω), X n ω ∂P) Filter.atTop (nhds (∫ (ω : Ω), Z ω ∂P)) := by
  cases' hbp.h_bound with c h_boundc
  let C : Ω → ℝ := (fun _ => c)
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      C h_meas h_boundc (integral_constant_finite_of_finiteMeasure c) hbp.h_lim

#lint
