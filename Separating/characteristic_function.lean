import Separating.main_result
import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Fourier.FourierTransform

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

/-!
this file blablabla
-/

/-- The span of a set which contains one and is closed under multiplication is a subalgebra. -/
def Set.toSubalgebra (s : Set A) (h_one_mem : 1 ∈ s)
    (h_mul_mem : ∀ x y : A, x ∈ s → y ∈ s → x * y ∈ s)
    : Subalgebra R A :=
  { Submodule.span R s with
    mul_mem' := by
      intro _ _ hx hy
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid] at *
      rcases (mem_span_set'.mp hx) with ⟨nx, fx, gx, hx⟩
      rcases (mem_span_set'.mp hy) with ⟨ny, fy, gy, hy⟩
      rw [← hx, ← hy, Finset.sum_mul_sum]
      apply Submodule.sum_mem
      intro c _
      apply Submodule.sum_mem
      intro d _
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      apply Submodule.smul_mem _ _ (Submodule.smul_mem _ _ _)
      apply Submodule.subset_span
          (h_mul_mem _ _ (Subtype.coe_prop (gx c)) (Subtype.coe_prop (gy d)))
    one_mem' := Submodule.subset_span (h_one_mem)
    algebraMap_mem' := by
      intro r
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem (Submodule.span R (s : Set A)) _ (Submodule.subset_span h_one_mem) }

/-- docBlame -/
def Submonoid.toSubalgebra (R : Type u) {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
    (s : Submonoid A) : Subalgebra R A :=
  Set.toSubalgebra (s : Set A) s.one_mem (@Submonoid.mul_mem _ _ s)

lemma Submodule.span_starmem [StarRing R] [StarRing A] [StarModule R A] {s : Set A} (h : ∀ x, x ∈ s → star x ∈ s)
    : ∀ x, x ∈ Submodule.span R s → star x ∈ Submodule.span R s := by
  intro x hx
  obtain ⟨n, f, g, hfgx⟩ := mem_span_set'.1 hx
  simp [Submonoid.toSubalgebra, Set.toSubalgebra, mem_span_set']
  let fStar := fun i => star (f i)
  let gStar : Fin n → s
      := fun i => ⟨star (g i), h (g i) (Subtype.coe_prop (g i))⟩
  use n, fStar, gStar
  rw [← hfgx]
  simp only [star_sum, star_smul]

/-- the span of a submonoid which is closed under "star" is a StarSubalgebra -/
def Submonoid.toStarSubalgebra (R : Type u) {A : Type v} [CommSemiring R] [Semiring A]
    [Algebra R A] [StarRing R] [StarRing A] [StarModule R A] (s : Submonoid A)
    (hstar : ∀ x, x ∈ s → star x ∈ s) : StarSubalgebra R A :=
  { Submonoid.toSubalgebra R s with
    star_mem' := fun hx => Submodule.span_starmem hstar _ hx  }


variable {V : Type*} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V] [PseudoEMetricSpace V]
  [BorelSpace V] {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

variable {e : AddChar ℝ circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}

/-- define probabilityChar, as a continuous map from V to ℂ -/
noncomputable def probabilityChar' (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (w : W)
    : ContinuousMap V ℂ where
  toFun := fun (v : V) ↦ e (L v w)
  continuous_toFun := Continuous.subtype_val
      (he.comp (hL.comp (Continuous.Prod.mk_left w)))

lemma probabilityChar'_abs_one   (he : Continuous e)  (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) (v : V) : Complex.abs (probabilityChar' he hL w v) = 1 := by
  exact abs_coe_circle (e (L v w))

lemma probabilityChar'_dist_le_two   (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) (v v' : V) : dist (probabilityChar' he hL w v) (probabilityChar' he hL w v') ≤ 2 := by
  rw [dist_eq_norm_sub]
  apply le_trans (norm_sub_le _ _) _
  simp [Complex.norm_eq_abs, probabilityChar'_abs_one he hL w _]
  norm_num

lemma probabilityChar'_apply (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) (v : V) : probabilityChar' he hL w v = e (L v w) :=
  rfl

lemma probabilityChar'_one_mem   (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    : 1 ∈ {probabilityChar' he hL w | w : W} := by
  use 0
  ext z
  simp only [probabilityChar', map_zero, neg_zero, AddChar.map_zero_one, OneMemClass.coe_one,
    ContinuousMap.coe_mk, ContinuousMap.one_apply]

lemma probabilityChar'_mul_mem   (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    : ∀ x y : C(V, ℂ), x ∈ {probabilityChar' he hL w | w : W}
    → y ∈ {probabilityChar' he hL w | w : W} →x * y ∈ {probabilityChar' he hL w | w : W} := by
  rintro x y ⟨v, hv⟩ ⟨v', hv'⟩
  use v + v'
  ext z
  simp only [probabilityChar', map_add, ContinuousMap.coe_mk, ContinuousMap.mul_apply]
  rw [AddChar.map_add_mul e, Submonoid.coe_mul]
  rw [← congrFun (congrArg DFunLike.coe hv) z, ← congrFun (congrArg DFunLike.coe hv') z]
  simp [probabilityChar']

lemma probabilityChar'_star_mem   (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    : ∀ x, x ∈ {probabilityChar' he hL w | w : W}
    → star x ∈ {probabilityChar' he hL w | w : W} := by
  intro x ⟨w, hw⟩
  use -w
  ext v
  rw [← hw]
  simp only [probabilityChar', map_neg, neg_neg]
  simp [probabilityChar'_apply he hL]
  rw [AddChar.map_neg_inv]
  rw [coe_inv_circle_eq_conj]

lemma probabilityChar'_SeparatesPoints (he : Continuous e) (he' : AddChar.IsNontrivial e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) {v v' : V} (hv : v ≠ v')
    : ∃ w : W, probabilityChar' he hL w v ≠ probabilityChar' he hL w v' := by
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp (hL' (v - v') (sub_ne_zero_of_ne hv))
  obtain ⟨a, ha⟩ := he'
  use (a / (L (v - v') w)) • w
  simp only [probabilityChar', map_sub, LinearMap.sub_apply, LinearMapClass.map_smul, smul_eq_mul,
    ContinuousMap.coe_mk, ne_eq]
  rw [← div_eq_one_iff_eq (ne_zero_of_mem_circle _)]
  rw [div_eq_inv_mul, ← coe_inv_unitSphere]
  rw [← AddChar.map_neg_inv e ((a / ((L v) w - (L v') w) * (L v') w))]
  rw [← Submonoid.coe_mul, ← AddChar.map_add_mul]
  ring_nf
  rw [← sub_mul, ← mul_sub, mul_assoc, mul_inv_cancel _, mul_one]
  · exact fun h => ha (SetLike.coe_eq_coe.mp h)
  · intro h
    apply hw
    simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply, h]

/-- docBlame -/
noncomputable
def probabilityChar'_submonoid (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    : Submonoid C(V, ℂ) where
  carrier := { (probabilityChar' he hL w) | w : W}
  mul_mem' := (fun ha hb => probabilityChar'_mul_mem he hL _ _ ha hb)
  one_mem' := probabilityChar'_one_mem he hL

lemma probabilityChar'_extract_w (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (f : probabilityChar'_submonoid he hL) : ∃ (w : W), probabilityChar' he hL w = f :=
  Set.mem_setOf.1 (Subtype.coe_prop f)

lemma probabilityChar'_dist_le_two' (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (f : probabilityChar'_submonoid he hL) : ∀ (v v' : V), dist ((f : C(V, ℂ)) v) ((f : C(V, ℂ)) v') ≤ 2 := by
  rw [← Exists.choose_spec (probabilityChar'_extract_w he hL f)]
  exact probabilityChar'_dist_le_two he hL _

/-- docBlame -/
noncomputable
def probabilityChar'_starSubalgebra (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    : StarSubalgebra ℂ C(V, ℂ) :=
  Submonoid.toStarSubalgebra ℂ (probabilityChar'_submonoid he hL) (probabilityChar'_star_mem he hL)

lemma probabilityChar'_StarSubalgebra_separatesPoints (he : Continuous e)
    (he' : AddChar.IsNontrivial e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (hL' : ∀ v ≠ 0, L v ≠ 0) : (probabilityChar'_starSubalgebra he hL).SeparatesPoints := by
  intro v v' hvv'
  obtain ⟨w, hw⟩ := probabilityChar'_SeparatesPoints he he' hL hL' hvv'
  use (probabilityChar' he hL w)
  simp only [StarSubalgebra.coe_toSubalgebra, Set.mem_image, SetLike.mem_coe, DFunLike.coe_fn_eq,
    exists_eq_right, ne_eq]
  exact ⟨Submodule.subset_span ⟨w, rfl⟩, hw⟩

lemma probabilityChar'_starSubalgebra_bounded (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    : ∀ g ∈ (probabilityChar'_starSubalgebra he hL), ∃ C, ∀ (v v' : V), dist (g v) (g v') ≤ C := by
  intro g hg
  obtain ⟨n, c, f, hf⟩ := mem_span_set'.1 hg
  by_cases hn : n = 0
  · use 0
    intro x y
    rw [← hf]
    simp only [hn, Fin.isEmpty', Finset.univ_eq_empty, Finset.sum_empty, ContinuousMap.zero_apply,
      dist_self, le_refl]
  have : Nonempty (Fin n) := by
    exact Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero hn)
  let C := Complex.abs (c (Exists.choose (Finite.exists_max (fun i => Complex.abs (c i)))))
  have hC : ∀ i, Complex.abs (c i) ≤ C := Exists.choose_spec (Finite.exists_max (fun i => Complex.abs (c i)))
  use n * (C * 2)
  intro v v'
  rw [dist_eq_norm, Complex.norm_eq_abs, ← hf]
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← Finset.univ.sum_sub_distrib]
  have := AbsoluteValue.sum_le Complex.abs
      Finset.univ fun i ↦ c i * ((f i) : C(V, ℂ)) v - c i * ((f i) : C(V, ℂ)) v'
  apply le_trans this _
  apply le_trans (Finset.sum_le_card_nsmul _
      (fun i => Complex.abs ((c i) * ((f i) : C(V, ℂ)) v - (c i) * ((f i) : C(V, ℂ)) v')) (C * 2) _)
  · simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]
  · intro i _
    simp only
    rw [← mul_sub]
    rw [AbsoluteValue.map_mul Complex.abs (c i) (((f i) : C(V, ℂ)) v - ((f i) : C(V, ℂ)) v')]
    apply mul_le_mul (hC i) (probabilityChar'_dist_le_two' he hL (f i) _ _)
        (AbsoluteValue.nonneg Complex.abs _) (AbsoluteValue.nonneg Complex.abs (_))

lemma probabilityChar'_starSubalgebra_integrable (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) {P : MeasureTheory.FiniteMeasure V}
    : ∀ g ∈ (probabilityChar'_starSubalgebra he hL), MeasureTheory.Integrable g P :=
  fun g hg => BoundedContinuousFunction.integrable P
      ⟨g, probabilityChar'_starSubalgebra_bounded he hL g hg⟩

-- start with characteristic functions
variable [CompleteSpace V] [SecondCountableTopology V]

/-- docBlame -/
noncomputable def charfunc {e : AddChar ℝ circle} (P : MeasureTheory.FiniteMeasure V) {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    (w : W) : ℂ := ∫ v, e (-L v w) ∂P

theorem measure_eq_of_charfunc_eq (he : Continuous e) (he' : AddChar.IsNontrivial e)
    (hL' : ∀ v ≠ 0, L v ≠ 0) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (P P' : MeasureTheory.FiniteMeasure V)
    : (∀ w, ∫ v, probabilityChar' he hL w v ∂P = ∫ v, probabilityChar' he hL w v ∂P') → P = P' := by
  intro h
  apply Subalgebra.separatesMeasures_of_separatesPoints
      (probabilityChar'_StarSubalgebra_separatesPoints he he' hL hL')
      (probabilityChar'_starSubalgebra_bounded he hL)
  intro g hg
  obtain ⟨n, c, f, hf⟩ := mem_span_set'.1 hg
  rw [← hf]
  have : ∀ (P : MeasureTheory.FiniteMeasure V),
      ∫ v, (Finset.univ.sum fun i ↦ c i • ((f i) : C(V, ℂ))) v ∂↑P
      = (Finset.univ.sum fun i ↦ ∫ v, c i • ((f i) : C(V, ℂ)) v ∂↑P) := by
    intro P
    simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [MeasureTheory.integral_finset_sum Finset.univ]
    exact fun i _ => MeasureTheory.Integrable.const_mul
        (probabilityChar'_starSubalgebra_integrable he hL _
        (Submodule.subset_span (Subtype.coe_prop (f i)))) _
  rw [this P, this P']
  apply Finset.sum_congr rfl
  intro x _
  simp only [smul_eq_mul, MeasureTheory.integral_mul_left, mul_eq_mul_left_iff]
  left
  obtain ⟨w, hw⟩ := probabilityChar'_extract_w he hL (f x)
  rw [← hw]
  exact h w


-- example: V = W = ℝ ^ d, L = ⟨ , ⟩, e = fun x => Complex.exp (Complex.I * x)

variable {d : ℕ}

/-- docBlame -/
noncomputable
def probChar : AddChar ℝ circle where
  toFun z := expMapCircle (z)
  map_zero_one' := by simp only; rw [expMapCircle_zero]
  map_add_mul' x y := by simp only; rw [expMapCircle_add]

lemma probChar_apply (z : ℝ) : probChar z = expMapCircle z := rfl

lemma probChar_continuous : Continuous probChar := expMapCircle.continuous

/-- dot product of two vectors in ℝ^d as a bilinear map -/
noncomputable
def dotProduct' : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ := by
  apply LinearMap.mk₂ ℝ (fun v w : Fin d → ℝ => Matrix.dotProduct v w)
      (fun m1 m2 n => Matrix.add_dotProduct m1 m2 n)
      (fun c m n ↦ Matrix.smul_dotProduct c m n)
      (fun m n₁ n₂ ↦ Matrix.dotProduct_add m n₁ n₂)
      (fun c m n ↦ Matrix.dotProduct_smul c m n)

lemma dotProduct'_continuous : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) ↦ dotProduct' p.1 p.2 := by
  simp [dotProduct']
  apply continuous_finset_sum
  exact fun i _ => Continuous.mul (Continuous.comp (continuous_apply i) (Continuous.fst continuous_id))
      (Continuous.comp (continuous_apply i) (Continuous.snd continuous_id))

lemma probabilityChar'_eq (v w : Fin d → ℝ)
    : (probChar (dotProduct' v w)) = (probabilityChar' probChar_continuous dotProduct'_continuous w) v := by
  simp [probChar, probabilityChar']

lemma linearmapzero (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) : f ≠ 0 ↔ ∃ v, f v ≠ 0 := by
  exact DFunLike.ne_iff

theorem measure_eq_of_charfunc_eq' (P P' : MeasureTheory.FiniteMeasure ((i : Fin d) → ℝ))
    : (∀ w : Fin d → ℝ, ∫ v, ((probChar (dotProduct' v w)) : ℂ) ∂P
    = ∫ v, ((probChar (dotProduct' v w)) : ℂ) ∂P') → P = P' := by
  have h1 : probChar.IsNontrivial := by
    refine (AddChar.isNontrivial_iff_ne_trivial probChar).mpr ?_
    rw [DFunLike.ne_iff]
    use Real.pi
    rw [probChar_apply]
    intro h
    have heq := congrArg Subtype.val h
    rw [expMapCircle_apply Real.pi, Complex.exp_pi_mul_I] at heq
    norm_num at heq
  have h2 : ∀ (v : Fin d → ℝ), v ≠ 0 → dotProduct' v ≠ 0 := by
    intro v hv
    rw [linearmapzero]
    use v
    simp only [dotProduct', LinearMap.mk₂_apply, ne_eq, Matrix.dotProduct_self_eq_zero]
    exact hv
  intro h
  apply measure_eq_of_charfunc_eq probChar_continuous h1 h2 dotProduct'_continuous P P'
  simp [probabilityChar'_eq] at *
  exact h

#lint
