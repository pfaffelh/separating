import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic

/-!
# Separating algebras of bounded continuous functions

Bounded continuous functions

These functions are a star-subalgebra of `E →ᵇ ℂ` (see `expPoly`).

The goal of this file is to prove:

Let 𝕜 ∈ {ℝ, ℂ}, (E, r) be a complete and separable extended pseudo-metric space, and M ⊆ Cb (E, k) be a
star-sub-algebra that separates points. Then, M is separating.



-/

open scoped BigOperators

open BoundedContinuousFunction Complex Set MeasureTheory

variable {α 𝕜 : Type*}

noncomputable
def IsSeparatesPoints (M : Set (α → 𝕜)) : Prop :=
∀ x y : α, x≠y → ∃ f ∈ M, f x ≠ f y

example (M : Set (α → 𝕜)) : IsSeparatesPoints M ↔ SeparatesPoints M := by
  rfl

variable [TopologicalSpace α] [MeasurableSpace α] [MetricSpace α] [BorelSpace α] [NormedAddCommGroup 𝕜]

def IsSeparating (M : Set (α → ℝ)) : Prop :=
∀ P Q : Measure α, IsProbabilityMeasure P → IsProbabilityMeasure Q → (∀ f ∈ M, ∫ x, f x ∂P = ∫ x, f x ∂Q) → P = Q

def IsSeparatingContinuousClass (M : Set C(α, ℝ)) : Prop := IsSeparating (DFunLike.coe '' M)

theorem subalgebra_separating_fromSeparatesPoints1 (M : Set C(α, ℝ)) : IsSeparatingContinuousClass M := by
  sorry

theorem subalgebra_separating_fromSeparatesPoints (M : StarSubalgebra ℝ C(α, ℝ)) [MeasurableSpace α] : IsSeparating (DFunLike.coe '' M.carrier) := by
  intros P Q

  simp [IsSeparating]

  sorry

def xexp2 := fun (x : ℝ) => x * (Real.exp (-x*x))

lemma xexpx2_bounded : ∃ (C : ℝ), ∀ (x y : ℝ), xexp2 x < C
