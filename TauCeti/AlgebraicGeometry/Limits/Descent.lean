/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Affine.FinitePresentation
public import TauCeti.AlgebraicGeometry.Limits.Finite.Presentation
public import TauCeti.AlgebraicGeometry.Gluing.Pushout
public import TauCeti.AlgebraicGeometry.Gluing.Separated
public import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Descent of finitely presented schemes

Finitely presented schemes over a cofiltered affine-transition limit descend to a finite stage.
It suffices that one member of the diagram is quasi-compact and quasi-separated.

For a scheme of finite presentation over the limit, the theorem gives a finite-stage model
and a Cartesian square identifying its pullback with the original scheme. For example, a family
of finite presentation over the spectrum of a filtered colimit of rings can be defined over one
of the rings in the system.

## Main results

* `CategoryTheory.Limits.IsLimit.exists_isPullback_of_finitePresentation`: a finitely presented
  scheme over a cofiltered affine-transition limit with at least one quasi-compact quasi-separated
  member is the base change of a finitely presented scheme over some stage.

## References

* The Stacks Project, Lemma 32.10.1 ([Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)).
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}

section ModelData

/-- The property that `f : X ⟶ c.pt` is the base change along `c.π.app i : c.pt ⟶ D.obj i` of a
locally finitely presented, quasi-compact, quasi-separated scheme over some stage `D.obj i`. -/
private def HasFiniteStageModel (c : Cone D) {X : Scheme.{u}} (f : X ⟶ c.pt) : Prop :=
  ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (a : X ⟶ Y),
    LocallyOfFinitePresentation p ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
      IsPullback a f p (c.π.app i)

private lemma HasFiniteStageModel.comp_iso {c : Cone D} {X Y : Scheme.{u}} (e : Y ≅ X)
    {f : X ⟶ c.pt} (h : HasFiniteStageModel c f) :
    HasFiniteStageModel c (e.hom ≫ f) := by
  obtain ⟨i, Z, p, a, hp, hcpt, hqs, hsq⟩ := h
  refine ⟨i, Z, p, e.hom ≫ a, hp, hcpt, hqs, ?_⟩
  have hiso : IsPullback e.hom (e.hom ≫ f) f (𝟙 c.pt) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hsq

private lemma HasFiniteStageModel.preimage_open {c : Cone D} {X : Scheme.{u}} (f : X ⟶ c.pt)
    {U W : X.Opens} (hUW : U ≤ W) (hU : HasFiniteStageModel c (U.ι ≫ f)) :
    HasFiniteStageModel c ((W.ι ⁻¹ᵁ U).ι ≫ W.ι ≫ f) := by
  simpa only [Category.assoc, Scheme.Opens.isoOfLE_hom_ι_assoc] using
    hU.comp_iso (Scheme.Opens.isoOfLE hUW)

/-- Finite-stage model data together with a descended quasi-compact open. -/
private structure ModelWithOpenAt (c : Cone D) {U : Scheme.{u}} (u : U ⟶ c.pt)
    (W : U.Opens) (i : I) where
  scheme : Scheme.{u}
  map : scheme ⟶ D.obj i
  comparison : U ⟶ scheme
  openSubset : scheme.Opens
  finitePresentation : LocallyOfFinitePresentation map
  compactSpace : CompactSpace scheme
  quasiSeparated : QuasiSeparatedSpace scheme
  square : IsPullback comparison u map (c.π.app i)
  compactOpen : IsCompact (openSubset : Set scheme)
  preimage : comparison ⁻¹ᵁ openSubset = W

/-- A chart model uses the range of its overlap immersion as the chosen open. -/
private abbrev OpenChartModel (c : Cone D) {T U : Scheme.{u}} (u : U ⟶ c.pt) (r : T ⟶ U)
    [IsOpenImmersion r] (i : I) :=
  ModelWithOpenAt c u r.opensRange i

private noncomputable abbrev ModelWithOpenAt.baseChange {c : Cone D} {U : Scheme.{u}}
    {u : U ⟶ c.pt} {W : U.Opens} {i : I} (M : ModelWithOpenAt c u W i)
    {j : I} (t : j ⟶ i) [QuasiCompact (D.map t)] [QuasiSeparated (D.map t)] :
    ModelWithOpenAt c u W j where
  scheme := pullback M.map (D.map t)
  map := pullback.snd _ _
  comparison := (IsPullback.of_hasPullback M.map (D.map t)).lift M.comparison (u ≫ c.π.app j)
    (by rw [M.square.w, Category.assoc, c.w t])
  openSubset := pullback.fst M.map (D.map t) ⁻¹ᵁ M.openSubset
  finitePresentation := have := M.finitePresentation; inferInstance
  compactSpace := have := M.compactSpace; inferInstance
  quasiSeparated :=
    have := M.quasiSeparated
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  square := by
    have hsq : IsPullback M.comparison u M.map (c.π.app j ≫ D.map t) := by
      rw [c.w t]
      exact M.square
    exact hsq.of_right' (IsPullback.of_hasPullback M.map (D.map t))
  compactOpen := QuasiCompact.isCompact_preimage _ M.openSubset.isOpen M.compactOpen
  preimage := by
    rw [← Scheme.Hom.comp_preimage, IsPullback.lift_fst, M.preimage]

section OpenChart

variable {c : Cone D} {T U : Scheme.{u}} {u : U ⟶ c.pt} {r : T ⟶ U} [IsOpenImmersion r] {i : I}

private noncomputable def ModelWithOpenAt.overlapMap (M : OpenChartModel c u r i) :
    T ⟶ M.openSubset.toScheme :=
  IsOpenImmersion.lift M.openSubset.ι (r ≫ M.comparison) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    -- Express membership of the composite image as preimage membership at `r x`,
    -- so the model's preimage identity applies.
    change r x ∈ M.comparison ⁻¹ᵁ M.openSubset
    rw [M.preimage]
    exact ⟨x, rfl⟩)

private lemma ModelWithOpenAt.overlap_square (M : OpenChartModel c u r i) :
    IsPullback M.overlapMap r M.openSubset.ι M.comparison :=
  IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac ..).symm
    (by rw [Scheme.Opens.opensRange_ι, M.preimage])

private lemma ModelWithOpenAt.overlap_base_square (M : OpenChartModel c u r i) :
    IsPullback M.overlapMap (r ≫ u) (M.openSubset.ι ≫ M.map) (c.π.app i) :=
  M.overlap_square.paste_vert M.square

private lemma ModelWithOpenAt.baseChange_overlap_square (M : OpenChartModel c u r i)
    {j : I} (t : j ⟶ i) [QuasiCompact (D.map t)] [QuasiSeparated (D.map t)] :
    IsPullback (pullback.fst M.map (D.map t) ∣_ M.openSubset)
      ((M.baseChange t).openSubset.ι ≫ (M.baseChange t).map)
      (M.openSubset.ι ≫ M.map) (D.map t) :=
  (isPullback_morphismRestrict (pullback.fst M.map (D.map t)) M.openSubset).paste_vert
    (IsPullback.of_hasPullback M.map (D.map t))

private lemma ModelWithOpenAt.baseChange_overlapMap_comp (M : OpenChartModel c u r i)
    {j : I} (t : j ⟶ i) [QuasiCompact (D.map t)] [QuasiSeparated (D.map t)] :
    (M.baseChange t).overlapMap ≫
      (pullback.fst M.map (D.map t) ∣_ M.openSubset) = M.overlapMap := by
  rw [← cancel_mono M.openSubset.ι]
  simp only [Category.assoc, morphismRestrict_ι]
  rw [(M.baseChange t).overlap_square.w_assoc, IsPullback.lift_fst]
  exact M.overlap_square.w.symm

end OpenChart

/-- Gluing two finite-stage chart models along a compatible isomorphism of their descended
overlaps yields a finite-stage model of the union. -/
private lemma hasFiniteStageModel_of_compatible_charts {c : Cone D} {X : Scheme.{u}}
    (f : X ⟶ c.pt) (U V : X.Opens) (hUV : U ⊔ V = ⊤) {i : I}
    (M : OpenChartModel c (U.ι ≫ f) (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) i)
    (N : OpenChartModel c (V.ι ≫ f) (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) i)
    (e : M.openSubset.toScheme ≅ N.openSubset.toScheme)
    (he₁ : e.hom ≫ N.openSubset.ι ≫ N.map = M.openSubset.ι ≫ M.map)
    (he₂ : M.overlapMap ≫ e.hom = N.overlapMap) : HasFiniteStageModel c f := by
  let := M.finitePresentation; let := M.compactSpace; let := M.quasiSeparated
  let := N.finitePresentation; let := N.compactSpace; let := N.quasiSeparated
  let : CompactSpace M.openSubset.toScheme := isCompact_iff_compactSpace.mp M.compactOpen
  let p := pushout.desc (f := M.openSubset.ι) (g := e.hom ≫ N.openSubset.ι) M.map N.map
    (by simpa only [Category.assoc] using he₁.symm)
  have hf : M.overlapMap ≫ M.openSubset.ι = X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ M.comparison :=
    M.overlap_square.w
  have hg : M.overlapMap ≫ (e.hom ≫ N.openSubset.ι) =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ N.comparison := by
    rw [← Category.assoc, he₂]
    exact N.overlap_square.w
  have hv : IsPullback M.overlapMap (X.homOfLE (inf_le_right : U ⊓ V ≤ V))
      (e.hom ≫ N.openSubset.ι) N.comparison :=
    IsOpenImmersion.isPullback _ _ _ _ hg.symm (by
      rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι, N.preimage])
  let a := pushout.map (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
    (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) M.openSubset.ι
    (e.hom ≫ N.openSubset.ι) M.comparison N.comparison M.overlapMap hf.symm hg.symm
  have hsquare : IsPullback a (pushoutOpensDesc U V ≫ f) p (c.π.app i) := by
    apply Scheme.Hom.isPullback_pushout_map_desc_of_isPullback M.openSubset.ι
      (e.hom ≫ N.openSubset.ι) (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V))
      M.comparison N.comparison M.overlapMap M.map N.map _
      (pushoutOpensDesc U V ≫ f) (c.π.app i) M.overlap_square hv
    · rw [inl_pushoutOpensDesc_assoc]
      exact M.square
    · rw [inr_pushoutOpensDesc_assoc]
      exact N.square
  let : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have := isIso_pushoutOpensDesc U V hUV
  simpa using HasFiniteStageModel.comp_iso (asIso (pushoutOpensDesc U V)).symm
    ⟨i, pushout M.openSubset.ι (e.hom ≫ N.openSubset.ι), p, a,
      IsZariskiLocalAtSource.pushout_desc _ _ _ _ _ inferInstance inferInstance,
      inferInstance, quasiSeparatedSpace_pushout _ _, hsquare⟩

end ModelData

section Descent

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  {c : Cone D} (hc : IsLimit c)
include hc

/-- A quasi-compact open in a finite-stage model descends after passing to a later stage. -/
private lemma exists_modelWithOpenAt {X : Scheme.{u}} {f : X ⟶ c.pt}
    (h : HasFiniteStageModel c f) (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ j : I, Nonempty (ModelWithOpenAt c f W j) := by
  obtain ⟨i, Y, p, a, hp, hcpt, hqs, hsq⟩ := h
  have := hp; have := hcpt; have := hqs
  let c' := (c.pullbackOver p).extend hsq.flip.isoPullback.hom
  have hlim : IsLimit c' := (hc.pullbackOver p).ofIsoLimit
    (Cone.ext hsq.flip.isoPullback.symm (fun j ↦ by simp [c']))
  obtain ⟨j, V, hVc, hV⟩ := exists_preimage_eq (D.pullbackOver p) c' hlim W hW
  have hsq' : IsPullback (c'.π.app j) f (pullback.fst (D.map j.hom) p) (c.π.app j.left) := by
    refine IsPullback.of_right ?_ (by simp [c'])
      (IsPullback.of_hasPullback (D.map j.hom) p).flip
    simpa [c'] using hsq
  exact ⟨j.left, ⟨⟨pullback (D.map j.hom) p, pullback.fst _ _, c'.π.app j, V, inferInstance,
    inferInstance, quasiSeparatedSpace_of_quasiSeparated (pullback.snd _ _), hsq', hVc, hV⟩⟩⟩

/-- An affine scheme over an affine open of a stage has a finite-stage model. -/
private lemma HasFiniteStageModel.of_isAffine {i₀ : I} {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ c.pt) [LocallyOfFinitePresentation f]
    {V : (D.obj i₀).Opens} (hV : IsAffineOpen V) (q : X ⟶ V.toScheme)
    (hq : q ≫ V.ι = f ≫ c.π.app i₀) :
    HasFiniteStageModel c f := by
  have : IsAffine V.toScheme := hV
  have : ∀ j : Over i₀, IsAffine ((D.pullbackOver V.ι).obj j) := fun _ ↦ by
    dsimp; infer_instance
  let a := pullback.lift f q hq.symm
  have ha : a ≫ pullback.fst (c.π.app i₀) V.ι = f := pullback.lift_fst ..
  have : LocallyOfFinitePresentation (a ≫ pullback.fst (c.π.app i₀) V.ι) := by
    simpa only [ha] using (inferInstance : LocallyOfFinitePresentation f)
  have : LocallyOfFinitePresentation a :=
    locallyOfFinitePresentation_of_comp a (pullback.fst (c.π.app i₀) V.ι)
  obtain ⟨j, Y, hYaff, p, hp, b, hsq⟩ :=
    CategoryTheory.Functor.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine
      (D.pullbackOver V.ι) (c.pullbackOver V.ι) (hc.pullbackOver V.ι) a
  have := hYaff; have := hp
  have hbase : IsPullback ((c.pullbackOver V.ι).π.app j) (pullback.fst (c.π.app i₀) V.ι)
      (pullback.fst (D.map j.hom) V.ι) (c.π.app j.left) := by
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback (D.map j.hom) V.ι).flip
    simpa using (IsPullback.of_hasPullback (c.π.app i₀) V.ι).flip
  refine ⟨j.left, Y, p ≫ pullback.fst (D.map j.hom) V.ι, b,
    inferInstance, inferInstance, inferInstance, ?_⟩
  simpa only [ha] using hsq.paste_vert hbase

/-- An affine open of a scheme over the limit that lies over an affine open of one of the stages
descends to a finite stage. -/
private lemma HasFiniteStageModel.of_isAffineOpen {i₀ : I} {X : Scheme.{u}}
    (f : X ⟶ c.pt) [LocallyOfFinitePresentation f] {U : X.Opens} (hU : IsAffineOpen U)
    {V : (D.obj i₀).Opens} (hV : IsAffineOpen V) (hle : U ≤ (f ≫ c.π.app i₀) ⁻¹ᵁ V) :
    HasFiniteStageModel c (U.ι ≫ f) := by
  have : IsAffine U.toScheme := hU
  refine HasFiniteStageModel.of_isAffine hc _ hV ((f ≫ c.π.app i₀).resLE V U hle) ?_
  rw [Scheme.Hom.resLE_comp_ι, Category.assoc]

section AllStages

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- Descend the isomorphism between the two canonical pullback presentations of an overlap. -/
private lemma ModelWithOpenAt.exists_overlap_pullback_iso {T U V : Scheme.{u}}
    {u : U ⟶ c.pt} {v : V ⟶ c.pt} {r : T ⟶ U} {s : T ⟶ V}
    [IsOpenImmersion r] [IsOpenImmersion s] {i : I}
    (M : OpenChartModel c u r i) (N : OpenChartModel c v s i) (h : r ≫ u = s ≫ v) :
    ∃ (j : I) (t : j ⟶ i)
      (e : pullback (D.map t) (M.openSubset.ι ≫ M.map) ≅
        pullback (D.map t) (N.openSubset.ι ≫ N.map)),
      e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        M.overlap_base_square.flip.isoPullback.hom ≫
            pullback.map (c.π.app i) (M.openSubset.ι ≫ M.map) (D.map t)
              (M.openSubset.ι ≫ M.map) (c.π.app j) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ e.hom =
          N.overlap_base_square.flip.isoPullback.hom ≫
            pullback.map (c.π.app i) (N.openSubset.ι ≫ N.map) (D.map t)
              (N.openSubset.ι ≫ N.map) (c.π.app j) (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  let := M.finitePresentation; let := M.quasiSeparated
  let := N.finitePresentation; let := N.quasiSeparated
  let : CompactSpace M.openSubset.toScheme := isCompact_iff_compactSpace.mp M.compactOpen
  let : CompactSpace N.openSubset.toScheme := isCompact_iff_compactSpace.mp N.compactOpen
  let : QuasiSeparatedSpace M.openSubset.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding M.openSubset.ι.isOpenEmbedding
  let : QuasiSeparatedSpace N.openSubset.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding N.openSubset.ι.isOpenEmbedding
  let a := M.overlap_base_square.flip.isoPullback.symm ≪≫ N.overlap_base_square.flip.isoPullback
  have ha : a.hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← h, IsPullback.isoPullback_inv_fst]
  obtain ⟨j, t, e, he₁, he₂⟩ := hc.exists_iso_pullback_of_iso a ha
  refine ⟨j, t, e, he₁, ?_⟩
  rw [he₂]
  simp [a]

/-- Descend the isomorphism between the two descended overlap opens of two chart models. -/
private lemma ModelWithOpenAt.exists_iso_overlap {T U V : Scheme.{u}}
    {u : U ⟶ c.pt} {v : V ⟶ c.pt} {r : T ⟶ U} {s : T ⟶ V}
    [IsOpenImmersion r] [IsOpenImmersion s] {i : I}
    (M : OpenChartModel c u r i) (N : OpenChartModel c v s i) (h : r ≫ u = s ≫ v) :
    ∃ (j : I) (t : j ⟶ i)
      (e : (M.baseChange t).openSubset.toScheme ≅ (N.baseChange t).openSubset.toScheme),
      e.hom ≫ (N.baseChange t).openSubset.ι ≫ (N.baseChange t).map =
        (M.baseChange t).openSubset.ι ≫ (M.baseChange t).map ∧
      (M.baseChange t).overlapMap ≫ e.hom = (N.baseChange t).overlapMap := by
  obtain ⟨j, t, e, he₁, he₂⟩ := M.exists_overlap_pullback_iso hc N h
  let e₁ := (M.baseChange_overlap_square t).flip.isoPullback
  let e₂ := (N.baseChange_overlap_square t).flip.isoPullback
  have hcomp {T' U' : Scheme.{u}} {u' : U' ⟶ c.pt} {r' : T' ⟶ U'} [IsOpenImmersion r']
      (P : OpenChartModel c u' r' i) :
      (P.baseChange t).overlapMap ≫ (P.baseChange_overlap_square t).flip.isoPullback.hom =
        P.overlap_base_square.flip.isoPullback.hom ≫
          pullback.map (c.π.app i) (P.openSubset.ι ≫ P.map) (D.map t)
            (P.openSubset.ι ≫ P.map) (c.π.app j) (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simpa [Category.assoc, IsPullback.isoPullback_hom_fst] using
        (P.baseChange t).overlap_base_square.w
    · simpa [Category.assoc, IsPullback.isoPullback_hom_snd] using
        P.baseChange_overlapMap_comp t
  refine ⟨j, t, e₁ ≪≫ e ≪≫ e₂.symm, ?_, ?_⟩
  · dsimp only [Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Category.assoc, IsPullback.isoPullback_inv_fst, he₁,
      IsPullback.isoPullback_hom_fst]
  · rw [← cancel_mono e₂.hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, hcomp M, Category.assoc, he₂, ← hcomp N]

/-- Two finite-stage chart models glue after descending their common quasi-compact overlap. -/
private lemma HasFiniteStageModel.of_sup_eq_top {X : Scheme.{u}} (f : X ⟶ c.pt)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (hWc : IsCompact ((U ⊓ V : X.Opens) : Set X))
    (hU : HasFiniteStageModel c (U.ι ≫ f)) (hV : HasFiniteStageModel c (V.ι ≫ f)) :
    HasFiniteStageModel c f := by
  have hcomp {A B : X.Opens} (hAB : A ≤ B) (hAc : IsCompact (A : Set X)) :
      IsCompact ((X.homOfLE hAB).opensRange : Set B.toScheme) := by
    rw [Scheme.opensRange_homOfLE]
    exact B.ι.isOpenEmbedding.isInducing.isCompact_preimage' hAc
      (by rw [Scheme.Opens.range_ι]; exact hAB)
  obtain ⟨k, ⟨MU⟩⟩ := exists_modelWithOpenAt hc hU _ (hcomp inf_le_left hWc)
  obtain ⟨l, ⟨MV⟩⟩ := exists_modelWithOpenAt hc hV _ (hcomp inf_le_right hWc)
  let M : OpenChartModel c (U.ι ≫ f) (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      (IsCofiltered.min k l) := MU.baseChange (IsCofiltered.minToLeft k l)
  let N : OpenChartModel c (V.ι ≫ f) (X.homOfLE (inf_le_right : U ⊓ V ≤ V))
      (IsCofiltered.min k l) := MV.baseChange (IsCofiltered.minToRight k l)
  obtain ⟨_, t, e, he₁, he₂⟩ := M.exists_iso_overlap hc N (by
    simp only [← Category.assoc, Scheme.homOfLE_ι])
  exact hasFiniteStageModel_of_compatible_charts f U V hUV (M.baseChange t) (N.baseChange t)
    e he₁ he₂

/-- Finite-stage models of two opens glue when their intersection is quasi-compact. -/
private lemma HasFiniteStageModel.sup {X : Scheme.{u}} (f : X ⟶ c.pt) (U V : X.Opens)
    (hW : IsCompact ((U ⊓ V : X.Opens) : Set X))
    (hU : HasFiniteStageModel c (U.ι ≫ f)) (hV : HasFiniteStageModel c (V.ι ≫ f)) :
    HasFiniteStageModel c ((U ⊔ V).ι ≫ f) := by
  let W := U ⊔ V
  have hcomp : IsCompact (((W.ι ⁻¹ᵁ U) ⊓ (W.ι ⁻¹ᵁ V) : W.toScheme.Opens) : Set W.toScheme) := by
    rw [← Scheme.Hom.preimage_inf]
    exact W.ι.isOpenEmbedding.isInducing.isCompact_preimage' hW
      (by rw [Scheme.Opens.range_ι]; exact inf_le_left.trans le_sup_left)
  apply HasFiniteStageModel.of_sup_eq_top hc (W.ι ≫ f) (W.ι ⁻¹ᵁ U) (W.ι ⁻¹ᵁ V)
    (by rw [← Scheme.Hom.preimage_sup]; exact Scheme.Opens.ι_preimage_self W) hcomp
  · exact hU.preimage_open f le_sup_left
  · exact hV.preimage_open f le_sup_right

/-- A finite union of affine charts lying over affine opens of a stage has a finite-stage model. -/
private lemma hasFiniteStageModel_finsetSup {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {i : I} (f : X ⟶ c.pt) [LocallyOfFinitePresentation f] (s : Finset X.Opens)
    (hs : ∀ U ∈ s, IsAffineOpen U ∧ ∃ V : (D.obj i).Opens,
      IsAffineOpen V ∧ U ≤ (f ≫ c.π.app i) ⁻¹ᵁ V) :
    HasFiniteStageModel c ((s.sup id : X.Opens).ι ≫ f) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sup_empty]
    exact HasFiniteStageModel.of_isAffineOpen hc f (isAffineOpen_bot X)
      (isAffineOpen_bot (D.obj i)) bot_le
  | insert U s _ ih =>
    obtain ⟨hU, V, hV, hUV⟩ := hs U (Finset.mem_insert_self U s)
    have hs' := fun W hW ↦ hs W (Finset.mem_insert_of_mem hW)
    have hcomp : IsCompact ((s.sup id : X.Opens) : Set X) := by
      simpa only [TopologicalSpace.Opens.coe_finset_sup, Finset.sup_set_eq_biUnion,
        Function.comp_apply, id_eq] using s.isCompact_biUnion (fun W hW ↦ (hs' W hW).1.isCompact)
    rw [Finset.sup_insert, id]
    apply HasFiniteStageModel.sup hc f U (s.sup id)
    · exact QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen hU.isCompact (s.sup id).isOpen hcomp
    · exact HasFiniteStageModel.of_isAffineOpen hc f hU hV hUV
    · exact ih hs'

/-- A finitely presented scheme over a cofiltered limit of quasi-compact quasi-separated schemes
with affine transition maps is the base change of a finitely presented scheme over some stage. -/
private theorem exists_isPullback_of_finitePresentation_allStages {X : Scheme.{u}}
    (f : X ⟶ c.pt) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i)
      (_ : LocallyOfFinitePresentation p) (_ : QuasiCompact p)
      (_ : QuasiSeparated p) (a : X ⟶ Y),
      IsPullback a f p (c.π.app i) := by
  classical
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have := isAffineHom_π_app _ _ hc
  have : CompactSpace c.pt := QuasiCompact.compactSpace_of_compactSpace (c.π.app i₀)
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let A := {V : X.affineOpens // ∃ U : (D.obj i₀).affineOpens,
    V.val ≤ (f ≫ c.π.app i₀) ⁻¹ᵁ U.val}
  have htop : IsCompactElement (⊤ : X.Opens) :=
    (TopologicalSpace.Opens.isCompactElement_iff _).mpr (by simpa using isCompact_univ)
  obtain ⟨s, hs⟩ := htop.exists_finset_of_le_iSup (fun V : A ↦ V.val.val)
    (by rw [Scheme.Hom.iSup_affineOpens_le_preimage_eq_top])
  have hmodel := hasFiniteStageModel_finsetSup hc (i := i₀) f
    (s.image fun V : A ↦ V.val.val) (by
      intro U hU
      obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨W, hW⟩ := V.property
      exact ⟨V.val.property, W.val, W.property, hW⟩)
  have hsup : (s.image fun V : A ↦ V.val.val).sup id = ⊤ := by
    apply top_le_iff.mp
    rw [Finset.sup_image]
    simpa only [Function.comp_apply, id_eq, Finset.sup_eq_iSup] using hs
  rw [hsup] at hmodel
  replace hmodel := hmodel.comp_iso X.topIso.symm
  rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at hmodel
  obtain ⟨i, Y, p, a, hp, hcpt, hqs, hsq⟩ := hmodel
  have := hp; have := hcpt; have := hqs
  exact ⟨i, Y, p, hp, inferInstance, inferInstance, a, hsq⟩

end AllStages

end Descent

end AlgebraicGeometry

namespace CategoryTheory.Limits.IsLimit

open AlgebraicGeometry

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- A finitely presented scheme over a cofiltered affine-transition limit descends to a stage
as soon as one member of the diagram is quasi-compact and quasi-separated.
Stacks, Lemma 32.10.1 (01ZM). -/
theorem exists_isPullback_of_finitePresentation (i₀ : I)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i)
      (_ : LocallyOfFinitePresentation p) (_ : QuasiCompact p)
      (_ : QuasiSeparated p) (a : X ⟶ Y),
      IsPullback a f p (c.π.app i) := by
  let D' := Over.forget i₀ ⋙ D
  have {i j : Over i₀} (t : i ⟶ j) : IsAffineHom (D'.map t) :=
    inferInstanceAs (IsAffineHom (D.map t.left))
  have (i : Over i₀) : CompactSpace (D'.obj i) :=
    QuasiCompact.compactSpace_of_compactSpace (D.map i.hom)
  have (i : Over i₀) : QuasiSeparatedSpace (D'.obj i) :=
    quasiSeparatedSpace_of_quasiSeparated (D.map i.hom)
  have hc' : IsLimit (c.whisker (Over.forget i₀)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc
  obtain ⟨i, Y, p, hfp, hqc, hqs, a, hsq⟩ :=
    exists_isPullback_of_finitePresentation_allStages hc' f
  exact ⟨i.left, Y, p, hfp, hqc, hqs, a, hsq⟩

end CategoryTheory.Limits.IsLimit
