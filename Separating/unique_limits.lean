import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Order.Interval.Set.Basic

open MeasureTheory


namespace ENNReal

open Filter ENNReal NNReal

lemma tendsto_coe_id {a : ℝ≥0∞} (ha : a ≠ ⊤) : Tendsto (fun (x : NNReal) => (x : ENNReal))
    (nhds a.toNNReal) (nhds a) := by
  nth_rewrite 2 [← coe_toNNReal ha]
  exact ContinuousAt.tendsto (Continuous.continuousAt continuous_coe)

lemma coe_of_fun_toNNReal {ι : Type*} {f : ι → ℝ≥0∞} (hf : ∀ x, f x ≠ ⊤) : (fun (x : NNReal) => (x : ENNReal)) ∘ ENNReal.toNNReal ∘ f = f := by
  ext x
  change (ENNReal.toNNReal (f x) : ℝ≥0∞) = f x
  rw [coe_toNNReal]
  exact hf x

theorem tendsto_toNNReal_iff {ι : Type*} {f : ι → ℝ≥0∞} {u : Filter ι} {a : ℝ≥0∞} (ha : a ≠ ⊤) (hf : ∀ x, f x ≠ ⊤): Tendsto f u (nhds a) ↔ Tendsto (ENNReal.toNNReal ∘ f ) u (nhds (ENNReal.toNNReal a)) := by
  constructor
  · exact fun h =>  Filter.Tendsto.comp (ENNReal.tendsto_toNNReal ha) h
  · intro h
    have h2 := Filter.Tendsto.comp (tendsto_coe_id ha) h
    rw [coe_of_fun_toNNReal hf] at h2
    exact h2

theorem tendsto_toNNReal_iff' {ι : Type*} {f : ι → ℝ≥0∞} {u : Filter ι} {a : ℝ≥0} (hf : ∀ x, f x ≠ ⊤): Tendsto f u (nhds a) ↔ Tendsto (ENNReal.toNNReal ∘ f ) u (nhds a) := by
  rw [← @toNNReal_coe a]
  exact tendsto_toNNReal_iff coe_ne_top hf

end ENNReal

namespace MeasureTheory

-- The ae-limit is ae-unique. (This must already be in Mathlib somewhere...)
theorem ae_unique_of_ae_limit {α ι E : Type*} [TopologicalSpace E] [T2Space E] {x : MeasurableSpace α} {μ : Measure α} {Y Z : α → E} {X : ι → α → E} {l : Filter ι} [l.NeBot]
(hY : ∀ᵐ ω ∂μ, Filter.Tendsto (fun i => X i ω) l (nhds (Y ω))) (hZ
: ∀ᵐ ω ∂μ, Filter.Tendsto (fun i => X i ω) l (nhds (Z ω))) : Y =ᵐ[μ] Z := by
  filter_upwards [hY, hZ] with ω hY1 hZ1
  exact tendsto_nhds_unique hY1 hZ1

end MeasureTheory

section

variable {α ι κ E : Type*}

open Filter ENNReal

/-- This notion is helpful for finite measures since we don't have to deal with the possibility that some set measures to ∞ -/
def TendstoInMeasure' [Dist E] {_ : MeasurableSpace α} (μ : Measure α) (f : ι → α → E)
(l : Filter ι) (g : α → E) : Prop :=
  ∀ ε, 0 < ε → Tendsto (ENNReal.toNNReal ∘ (fun i => (μ { x | ε ≤ dist (f i x) (g x) }))) l (nhds 0)

theorem TendstoInMeasure_of_FiniteMeasure [Dist E] {_ : MeasurableSpace α} {μ : Measure α}
[hfin: MeasureTheory.IsFiniteMeasure μ] {f : ι → α → E} {l : Filter ι} {g : α → E} :
TendstoInMeasure μ f l g ↔ TendstoInMeasure' μ f l g := by
  have hfin : ∀ ε, ∀ i, μ { x | ε ≤ dist (f i x) (g x) } ≠ ⊤ := by
    exact fun ε i ↦ (measure_ne_top μ {x | ε ≤ dist (f i x) (g x)})
  constructor
  · intros h ε hε
    rw [← tendsto_toNNReal_iff' (hfin ε)]
    exact h ε hε
  · intros h ε hε
    rw [tendsto_toNNReal_iff zero_ne_top (hfin ε) ]
    exact h ε hε

variable [MetricSpace E] {_ : MeasurableSpace α} {μ : Measure α}

-- Convergence in measure is stable under taking subsequences.
lemma sub_TendstoInMeasure' {X : ι → α → E}  {Y : α → E} {u v: Filter ι} (huv : v ≤ u)
(hY :  TendstoInMeasure μ X u Y) : TendstoInMeasure μ X v Y :=
  fun ε hε => Tendsto.mono_left (hY ε hε) huv

lemma subseqTendsto_of_TendstoInMeasure {X : ℕ → α → E}  {Y : α → E} {ns : ℕ → ℕ} (hns : StrictMono ns)
(hY :  TendstoInMeasure μ X atTop Y) : TendstoInMeasure μ (X ∘ ns) atTop Y :=
  by
  intro ε hε
  apply Filter.Tendsto.comp (hY ε hε) (StrictMono.tendsto_atTop hns)

lemma subseq_TendstoInMeasure' {X : ι → α → E}  {Y : α → E} {u : Filter ι} {v : Filter κ}
    {ns : κ → ι} (hns : Tendsto ns v u) (hY :  TendstoInMeasure μ X u Y) : TendstoInMeasure μ (X ∘ ns) v Y := by
  intro ε hε
  apply Filter.Tendsto.comp (hY ε hε) hns

-- This is slightly stronger (ns ist strictly monotone) than the previous version
theorem exists_seq_tendstoInMeasure_atTop {u : Filter ι} [NeBot u]
    [IsCountablyGenerated u] {f : ι → α → E} {g : α → E} (hfg : TendstoInMeasure μ f u g) :
    ∃ (ns : ℕ → ι) (_ : Tendsto ns atTop u),  TendstoInMeasure μ (fun n => f (ns n)) atTop g := by
  obtain ⟨ns, h_tendsto_ns⟩ : ∃ ns : ℕ → ι, Tendsto ns atTop u := exists_seq_tendsto u
  exact ⟨ns, h_tendsto_ns, fun ε hε => (hfg ε hε).comp h_tendsto_ns⟩

-- The LimitInMeasure is ae unique
theorem ae_unique_of_limitInMeasure' {Y Z : α → E} {X : ℕ → α → E}  (hY : TendstoInMeasure μ X atTop Y) (hZ : TendstoInMeasure μ X atTop Z) : Y =ᵐ[μ] Z := by
  obtain ⟨ns,h1,h1'⟩ := TendstoInMeasure.exists_seq_tendsto_ae hY
  obtain ⟨ns', h2, h2'⟩ := TendstoInMeasure.exists_seq_tendsto_ae (subseqTendsto_of_TendstoInMeasure h1 hZ)
  obtain h4 : ∀ᵐ (x : α) ∂μ, Tendsto (fun i ↦ X (ns (ns' i)) x) atTop (nhds (Y x)) := by
    filter_upwards [h1'] with ω h
    apply Filter.Tendsto.comp h (StrictMono.tendsto_atTop h2)
  filter_upwards [h4, h2'] with ω hY1 hZ1
  refine tendsto_nhds_unique hY1 hZ1

-- Same as above but with a more general filter on ι
theorem ae_unique_of_limitInMeasure {Y Z : α → E} {X : ι → α → E}  {u : Filter ι} [NeBot u]
    [IsCountablyGenerated u] (hY : TendstoInMeasure μ X u Y) (hZ : TendstoInMeasure μ X u Z) : Y =ᵐ[μ] Z := by
  obtain ⟨ns,h1,h1'⟩ := @exists_seq_tendstoInMeasure_atTop α ι _ _ _ μ u _ _ X Y hY
  obtain h2 := @subseq_TendstoInMeasure' α ι ℕ E _ _ μ X Z u atTop ns h1 hZ
  exact @ae_unique_of_limitInMeasure' α E _ _ μ Y Z (X ∘ ns) h1' h2

open Filter ENNReal NNReal

lemma forall_seq_tendstoInMeasure_atTop {u : Filter ι} {v : Filter κ} {f : ι → α → E} {g : α → E} {ns : κ → ι} (hfg : TendstoInMeasure μ f u g) (hns : Tendsto ns v u) :
    TendstoInMeasure μ (fun n => f (ns n)) v g := fun ε hε => (hfg ε hε).comp hns

lemma subseq_of_notTendsto {f : ℕ → NNReal} (h : ¬Tendsto f atTop (nhds (0 : ℝ≥0))) : ∃ ε > 0, ∃ (ns : ℕ → ℕ) (_ : StrictMono ns), ∀ n, ε ≤ (f (ns n)).toReal :=
  by
  rw [Filter.not_tendsto_iff_exists_frequently_nmem] at h
  rcases h with ⟨A, ⟨hA1, hA2⟩⟩
  rw [Metric.mem_nhds_iff] at hA1
  rcases (Filter.extraction_of_frequently_atTop hA2) with ⟨ns, hns, h4⟩
  rcases hA1 with ⟨ε, hε, h3⟩
  use ε, hε, ns, hns
  intro n
  rw [← NNReal.abs_eq, ← Real.norm_eq_abs, ← not_lt, ← mem_ball_zero_iff]
  exact fun a => (h4 n) (h3 a)

lemma false_of_Tendsto_boundBelow (f : ℕ → ℝ) (δ : ℝ) (hδ: (0 : ℝ) < δ) (hf1 : Tendsto f atTop (nhds 0)) (hf2 : ∀ n, δ ≤ (f n) ) : False := by
  revert hf2
  rw [imp_false]
  push_neg
  specialize hf1 (Iio_mem_nhds hδ)
  simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage, Set.mem_Iio] at hf1
  cases' hf1 with a ha
  use a, by exact ha a (le_refl _)

lemma false_of_Tendsto_boundBelow' (f : ℕ → ℝ≥0) (δ : ℝ) (hδ: (0 : ℝ) < δ) (hf1 : Tendsto f atTop (nhds 0)) (hf2 : ∀ n, δ ≤ (f n) ) : False :=
  false_of_Tendsto_boundBelow (fun n => (f n).toReal) δ hδ (Tendsto.comp (tendsto_coe'.mpr ⟨Preorder.le_refl 0, fun ⦃_⦄ a ↦ a ⟩) hf1) hf2

theorem TendstoInMeasure.iff_exists_seq_tendstoInMeasure_atTop
  (hfin : MeasureTheory.IsFiniteMeasure μ) {f : ℕ → α → E} (hf : ∀ (n : ℕ), AEStronglyMeasurable (f n) μ) {g : α → E} : (TendstoInMeasure μ f atTop g) ↔ ∀ (ns : ℕ → ℕ) (_ : StrictMono ns), ∃ (ns' : ℕ → ℕ) (_ : StrictMono ns'), ∀ᵐ (ω : α) ∂μ, Tendsto (fun i ↦ f (ns (ns' i)) ω) atTop (nhds (g ω)) := by
    rw [TendstoInMeasure_of_FiniteMeasure]
    constructor
    · intros hfg ns hns
      have h1 : TendstoInMeasure μ (f ∘ ns)
        atTop g := (subseqTendsto_of_TendstoInMeasure hns (TendstoInMeasure_of_FiniteMeasure.mpr hfg))
      have ⟨ns', hns1, hns2⟩ :=
      TendstoInMeasure.exists_seq_tendsto_ae h1
      use ns', hns1
      filter_upwards [hns2] with x hns3
      exact hns3
    · rw [← not_imp_not]
      intros h1
      push_neg
      obtain h2 : ∃ (ε : ℝ) (_ : 0 < ε), ¬ (Tendsto (fun n => (μ { x | ε ≤ dist (f n x) (g x) }).toNNReal) atTop (nhds 0)) := by
        · by_contra h3
          apply h1
          push_neg at h3
          exact h3
      rcases h2 with ⟨ε, hε, h4⟩
      obtain h5 := @subseq_of_notTendsto (fun n ↦ (μ {x | ε ≤ dist (f n x) (g x)}).toNNReal) h4
      rcases h5 with ⟨δ, hδ, ns, hns, h5⟩
      use ns, hns
      intros ns' _
      by_contra h6
      apply h4
      have h4 : ∀ (n : ℕ), AEStronglyMeasurable ((f ∘ ns ∘ ns') n) μ := by exact fun n ↦
        (hf ((ns ∘ ns') n))
      have h8 := (MeasureTheory.tendstoInMeasure_of_tendsto_ae (f := f ∘ ns ∘ ns') (h4) h6)
      obtain h7 := fun n => h5 (ns' n)
      rw [TendstoInMeasure_of_FiniteMeasure] at h8
      exfalso
      revert h7
      apply false_of_Tendsto_boundBelow' (fun n => (μ {x | ε ≤ dist (f (ns (ns' n)) x) (g x)}).toNNReal) δ hδ (h8 ε hε)


end
