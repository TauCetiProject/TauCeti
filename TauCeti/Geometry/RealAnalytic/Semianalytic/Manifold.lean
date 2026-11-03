/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Analytic

/-!
# Semianalytic sets on real analytic manifolds

Semianalyticity on a boundaryless real analytic manifold is semianalyticity in an extended
chart. `MSemianalyticAt` uses the preferred chart, and
`mSemianalyticAt_iff_of_mem_maximalAtlas` shows that any chart of the maximal analytic atlas
may be used instead. In particular, this is a property of the set germ, not of the chosen chart.
The definition tests every ambient point, including points outside the set.

We prove finite Boolean closure and stability under analytic preimages, locally and globally.
The latter also gives invariance under analytic homeomorphisms. These results use the existing
convergent analytic chart calculus; no new manifold or submanifold structure is introduced.
No completeness or finite-dimensionality assumption on the model spaces is needed.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
di Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter IsManifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A set is semianalytic at a manifold point if its inverse image under the inverse extended
chart is semianalytic at the coordinate of that point. For a boundaryless model, only the germ
inside the chart matters. -/
def MSemianalyticAt (s : Set M) (x : M) : Prop :=
  SemianalyticAt ((extChartAt I x).symm ⁻¹' s) (extChartAt I x x)

/-- Semianalyticity at a manifold point is tested in the preferred extended chart. -/
theorem mSemianalyticAt_def {s : Set M} {x : M} :
    MSemianalyticAt I s x ↔
      SemianalyticAt ((extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
  Iff.rfl

variable {I}

/-- Semianalyticity at a manifold point depends only on the set germ there. -/
theorem MSemianalyticAt.congr {s t : Set M} {x : M} (hs : MSemianalyticAt I s x)
    (hst : s =ᶠ[𝓝 x] t) : MSemianalyticAt I t x := by
  apply (mSemianalyticAt_def I).2
  have hlim : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
    simpa only [extChartAt_to_inv] using (continuousAt_extChartAt_symm (I := I) x).tendsto
  exact ((mSemianalyticAt_def I).1 hs).congr (hst.comp_tendsto hlim)

/-- Germ-equivalent sets have the same semianalyticity at a manifold point. -/
theorem mSemianalyticAt_congr {s t : Set M} {x : M} (hst : s =ᶠ[𝓝 x] t) :
    MSemianalyticAt I s x ↔ MSemianalyticAt I t x :=
  ⟨fun hs => hs.congr hst, fun ht => ht.congr hst.symm⟩

/-- Sets semianalytic at a manifold point form an algebra of sets. -/
theorem isSetAlgebra_setOf_mSemianalyticAt (x : M) :
    MeasureTheory.IsSetAlgebra {s : Set M | MSemianalyticAt I s x} where
  empty_mem := by simp [mSemianalyticAt_def]
  compl_mem s hs := by
    apply (mSemianalyticAt_def I).2
    simpa only [preimage_compl] using
      ((mSemianalyticAt_def I).1 hs).compl
  union_mem s t hs ht := by
    apply (mSemianalyticAt_def I).2
    simpa only [preimage_union] using
      ((mSemianalyticAt_def I).1 hs).union ((mSemianalyticAt_def I).1 ht)

/-- The empty set is semianalytic at every manifold point. -/
@[simp]
theorem mSemianalyticAt_empty {x : M} : MSemianalyticAt I (∅ : Set M) x :=
  (isSetAlgebra_setOf_mSemianalyticAt x).empty_mem

/-- The whole manifold is semianalytic at every point. -/
@[simp]
theorem mSemianalyticAt_univ {x : M} : MSemianalyticAt I (univ : Set M) x :=
  (isSetAlgebra_setOf_mSemianalyticAt x).univ_mem

/-- Taking complements preserves and reflects semianalyticity at a manifold point. -/
@[simp]
theorem mSemianalyticAt_compl_iff {s : Set M} {x : M} :
    MSemianalyticAt I sᶜ x ↔ MSemianalyticAt I s x := by
  simp only [mSemianalyticAt_def, preimage_compl, semianalyticAt_compl_iff]

namespace MSemianalyticAt

variable {s t : Set M} {x : M}

/-- Complements preserve semianalyticity at a manifold point. -/
theorem compl (hs : MSemianalyticAt I s x) : MSemianalyticAt I sᶜ x :=
  mSemianalyticAt_compl_iff.2 hs

/-- Finite unions preserve semianalyticity at a manifold point. -/
theorem union (hs : MSemianalyticAt I s x) (ht : MSemianalyticAt I t x) :
    MSemianalyticAt I (s ∪ t) x :=
  (isSetAlgebra_setOf_mSemianalyticAt x).union_mem hs ht

/-- Finite intersections preserve semianalyticity at a manifold point. -/
theorem inter (hs : MSemianalyticAt I s x) (ht : MSemianalyticAt I t x) :
    MSemianalyticAt I (s ∩ t) x :=
  (isSetAlgebra_setOf_mSemianalyticAt x).inter_mem hs ht

/-- Differences preserve semianalyticity at a manifold point. -/
theorem sdiff (hs : MSemianalyticAt I s x) (ht : MSemianalyticAt I t x) :
    MSemianalyticAt I (s \ t) x :=
  (isSetAlgebra_setOf_mSemianalyticAt x).sdiff_mem hs ht

/-- A finite indexed union of sets semianalytic at a manifold point is semianalytic there. -/
protected theorem iUnion {ι : Type*} [Finite ι] {s : ι → Set M}
    (hs : ∀ i, MSemianalyticAt I (s i) x) : MSemianalyticAt I (⋃ i, s i) x := by
  simp only [mSemianalyticAt_def, preimage_iUnion] at hs ⊢
  exact .iUnion hs

/-- A finite indexed intersection of sets semianalytic at a manifold point is semianalytic
there, including the empty family. -/
protected theorem iInter {ι : Type*} [Finite ι] {s : ι → Set M}
    (hs : ∀ i, MSemianalyticAt I (s i) x) : MSemianalyticAt I (⋂ i, s i) x := by
  simp only [mSemianalyticAt_def, preimage_iInter] at hs ⊢
  exact .iInter hs

end MSemianalyticAt

/-- On the model space, manifold semianalyticity is the existing affine notion. -/
@[simp]
theorem mSemianalyticAt_model_iff {s : Set E} {x : E} :
    MSemianalyticAt 𝓘(ℝ, E) s x ↔ SemianalyticAt s x := by
  simp [mSemianalyticAt_def]

/-- A set on a manifold is semianalytic if it is semianalytic at every ambient point. -/
def IsMSemianalytic (I : ModelWithCorners ℝ E H) (s : Set M) : Prop :=
  ∀ x, MSemianalyticAt I s x

/-- Global manifold semianalyticity includes points outside the set. -/
theorem isMSemianalytic_iff {s : Set M} :
    IsMSemianalytic I s ↔ ∀ x, MSemianalyticAt I s x :=
  Iff.rfl

/-- A semianalytic set on a manifold is semianalytic at each point. -/
theorem IsMSemianalytic.mSemianalyticAt {s : Set M} (hs : IsMSemianalytic I s) (x : M) :
    MSemianalyticAt I s x :=
  hs x

/-- On a real normed model space the global manifold and affine notions agree. -/
@[simp]
theorem isMSemianalytic_model_iff {s : Set E} :
    IsMSemianalytic 𝓘(ℝ, E) s ↔ IsSemianalytic s := by
  simp only [isMSemianalytic_iff, isSemianalytic_iff, mSemianalyticAt_model_iff]

/-- Semianalytic sets on a manifold form an algebra of sets. -/
theorem isSetAlgebra_setOf_isMSemianalytic :
    MeasureTheory.IsSetAlgebra {s : Set M | IsMSemianalytic I s} where
  empty_mem _ := mSemianalyticAt_empty
  compl_mem _ hs x := (hs x).compl
  union_mem _ _ hs ht x := (hs x).union (ht x)

/-- The empty subset of a manifold is semianalytic. -/
@[simp]
theorem isMSemianalytic_empty : IsMSemianalytic I (∅ : Set M) :=
  (isSetAlgebra_setOf_isMSemianalytic).empty_mem

/-- The whole manifold is semianalytic. -/
@[simp]
theorem isMSemianalytic_univ : IsMSemianalytic I (univ : Set M) :=
  (isSetAlgebra_setOf_isMSemianalytic).univ_mem

/-- Complements preserve and reflect global semianalyticity on manifolds. -/
@[simp]
theorem isMSemianalytic_compl_iff {s : Set M} :
    IsMSemianalytic I sᶜ ↔ IsMSemianalytic I s :=
  forall_congr' fun _ => mSemianalyticAt_compl_iff

namespace IsMSemianalytic

variable {s t : Set M}

/-- The complement of a semianalytic subset of a manifold is semianalytic. -/
protected theorem compl (hs : IsMSemianalytic I s) : IsMSemianalytic I sᶜ :=
  fun x => (hs x).compl

/-- The union of semianalytic subsets of a manifold is semianalytic. -/
protected theorem union (hs : IsMSemianalytic I s) (ht : IsMSemianalytic I t) :
    IsMSemianalytic I (s ∪ t) :=
  fun x => (hs x).union (ht x)

/-- The intersection of semianalytic subsets of a manifold is semianalytic. -/
protected theorem inter (hs : IsMSemianalytic I s) (ht : IsMSemianalytic I t) :
    IsMSemianalytic I (s ∩ t) :=
  fun x => (hs x).inter (ht x)

/-- The difference of semianalytic subsets of a manifold is semianalytic. -/
protected theorem sdiff (hs : IsMSemianalytic I s) (ht : IsMSemianalytic I t) :
    IsMSemianalytic I (s \ t) :=
  fun x => (hs x).sdiff (ht x)

/-- Finite indexed unions of semianalytic subsets of a manifold are semianalytic. -/
protected theorem iUnion {ι : Type*} [Finite ι] {s : ι → Set M}
    (hs : ∀ i, IsMSemianalytic I (s i)) : IsMSemianalytic I (⋃ i, s i) :=
  fun x => .iUnion fun i => hs i x

/-- Finite indexed intersections of semianalytic subsets of a manifold are semianalytic. -/
protected theorem iInter {ι : Type*} [Finite ι] {s : ι → Set M}
    (hs : ∀ i, IsMSemianalytic I (s i)) : IsMSemianalytic I (⋂ i, s i) :=
  fun x => .iInter fun i => hs i x

end IsMSemianalytic

section AnalyticAtlas

variable [I.Boundaryless]

/-- Any two charts of the maximal analytic atlas give the same semianalytic set germs. -/
theorem _root_.OpenPartialHomeomorph.semianalyticAt_preimage_extend_symm_iff
    {s : Set M} {x : M} (e e' : OpenPartialHomeomorph M H)
    (he : e ∈ maximalAtlas I ω M) (he' : e' ∈ maximalAtlas I ω M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    SemianalyticAt ((e.extend I).symm ⁻¹' s) (e.extend I x) ↔
      SemianalyticAt ((e'.extend I).symm ⁻¹' s) (e'.extend I x) := by
  have transfer : ∀ (a b : OpenPartialHomeomorph M H),
      a ∈ maximalAtlas I ω M → b ∈ maximalAtlas I ω M →
      x ∈ a.source → x ∈ b.source →
      SemianalyticAt ((b.extend I).symm ⁻¹' s) (b.extend I x) →
      SemianalyticAt ((a.extend I).symm ⁻¹' s) (a.extend I x) := by
    intro a b ha hb hxa hxb hs
    let c := I.extendCoordChange a b
    have hmem : a.extend I x ∈ c.source := by
      rw [← a.extend_image_source_inter (I := I) b]
      exact mem_image_of_mem _ ⟨hxa, hxb⟩
    have hc : c (a.extend I x) = b.extend I x := by
      simp only [c, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
        (a.extend I).left_inv (by simpa only [OpenPartialHomeomorph.extend_source] using hxa)]
    have hp := (hc.symm ▸ hs).preimage_of_analyticOnNhd
      (I.isOpen_extendCoordChange_source.mem_nhds hmem)
      (I.analyticOnNhd_extendCoordChange ha hb)
    refine hp.congr ?_
    filter_upwards [I.isOpen_extendCoordChange_source.mem_nhds hmem] with y hy
    simp only [mem_preimage, c, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply]
    have hby : (a.extend I).symm y ∈ (b.extend I).source := hy.2
    rw [(b.extend I).left_inv hby]
  exact ⟨transfer e' e he' he hx' hx, transfer e e' he he' hx hx'⟩

variable [IsManifold I ω M]

/-- Manifold semianalyticity can be tested in any chart of the maximal analytic atlas. -/
theorem mSemianalyticAt_iff_of_mem_maximalAtlas {s : Set M} {x : M}
    {e : OpenPartialHomeomorph M H} (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source) :
    MSemianalyticAt I s x ↔ SemianalyticAt ((e.extend I).symm ⁻¹' s) (e.extend I x) :=
  (mSemianalyticAt_def I).trans <|
    (chartAt H x).semianalyticAt_preimage_extend_symm_iff e
      (chart_mem_maximalAtlas x) he (mem_chart_source H x) hx

end AnalyticAtlas

variable [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- Analytic preimages preserve semianalyticity at a manifold point. -/
theorem MSemianalyticAt.preimage {s : Set M'} {g : M → M'} {x : M}
    (hs : MSemianalyticAt I' s (g x)) (hg : ContMDiffAt I I' ω g x) :
    MSemianalyticAt I (g ⁻¹' s) x := by
  let c := writtenInExtChartAt I I' x g
  have hc : ContDiffAt ℝ ω c (extChartAt I x x) :=
    (contMDiffAt_iff.1 hg).2.contDiffAt (by simp [I.range_eq_univ])
  have hcx : c (extChartAt I x x) = extChartAt I' (g x) (g x) :=
    writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)
  -- Neighborhood stability of C^ω needs no completeness of the target model.
  have hp := (hcx.symm ▸ (mSemianalyticAt_def I').1 hs).preimage_of_analyticOnNhd
    (hc.eventually (by simp)) (fun _ hy => hy.analyticAt)
  apply (mSemianalyticAt_def I).2
  refine hp.congr ?_
  have hinv : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
    simpa only [extChartAt_to_inv] using (continuousAt_extChartAt_symm (I := I) x).tendsto
  have hlim := hg.continuousAt.tendsto.comp hinv
  have htarget := hlim (extChartAt_source_mem_nhds (I := I') (g x))
  filter_upwards [htarget] with y hy
  have hgy : g ((extChartAt I x).symm y) ∈ (extChartAt I' (g x)).source := hy
  simp only [mem_preimage, c, extChartAt_symm_writtenInExtChartAt hgy]

/-- Analytic preimages preserve global semianalyticity on manifolds. -/
theorem IsMSemianalytic.preimage {s : Set M'} {g : M → M'} (hs : IsMSemianalytic I' s)
    (hg : ContMDiff I I' ω g) : IsMSemianalytic I (g ⁻¹' s) :=
  fun x => (hs (g x)).preimage (hg x)

/-- A homeomorphism analytic in both directions preserves and reflects semianalytic set germs. -/
theorem _root_.Homeomorph.mSemianalyticAt_image_iff [I'.Boundaryless]
    {s : Set M} {x : M} (e : M ≃ₜ M') (he : ContMDiffAt I I' ω e x)
    (he' : ContMDiffAt I' I ω e.symm (e x)) :
    MSemianalyticAt I' (e '' s) (e x) ↔ MSemianalyticAt I s x := by
  rw [e.image_eq_preimage_symm]
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · simpa [preimage_preimage] using hs.preimage he
  · exact MSemianalyticAt.preimage (by simpa only [e.symm_apply_apply] using hs) he'

/-- Analytic homeomorphisms preserve and reflect semianalyticity. -/
theorem _root_.Homeomorph.isMSemianalytic_image_iff [I'.Boundaryless]
    {s : Set M} (e : M ≃ₜ M')
    (he : ContMDiff I I' ω e) (he' : ContMDiff I' I ω e.symm) :
    IsMSemianalytic I' (e '' s) ↔ IsMSemianalytic I s := by
  rw [e.image_eq_preimage_symm]
  refine ⟨fun hs => ?_, fun hs => hs.preimage he'⟩
  simpa [preimage_preimage] using hs.preimage he

/-- Zero loci of analytic scalar functions are semianalytic on the manifold. -/
theorem _root_.ContMDiffAt.mSemianalyticAt_setOf_eq_zero {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ω f x) : MSemianalyticAt I {y | f y = 0} x := by
  exact (mSemianalyticAt_model_iff.2 analyticAt_id.semianalyticAt_setOf_eq_zero).preimage hf

/-- Strict positivity loci of analytic scalar functions are semianalytic on the manifold. -/
theorem _root_.ContMDiffAt.mSemianalyticAt_setOf_pos {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ω f x) : MSemianalyticAt I {y | 0 < f y} x := by
  exact (mSemianalyticAt_model_iff.2 analyticAt_id.semianalyticAt_setOf_pos).preimage hf

end TauCeti
