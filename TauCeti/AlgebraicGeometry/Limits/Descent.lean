/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Affine.FinitePresentation
public import TauCeti.AlgebraicGeometry.Limits.FinitePresentation
public import TauCeti.AlgebraicGeometry.Gluing.Pushout
public import TauCeti.AlgebraicGeometry.Gluing.Separated
public import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Descent of finitely presented schemes

Finitely presented schemes over a cofiltered affine-transition limit descend to a finite stage.
It suffices that one member of the diagram is quasi-compact and quasi-separated.

Reference: The Stacks Project, Lemma 32.10.1 (Tag 01ZM).
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {Index : Type u} [Category.{u} Index]
  {diagram : Index ⥤ Scheme.{u}} {cone : Cone diagram} (limit : IsLimit cone)

variable (diagram cone) in
/-- The property that `sourceMap : sourceScheme ⟶ lim Dⱼ` is the base change along
`lim Dⱼ ⟶ D_k` of a scheme of finite presentation over the stage `D_k`. -/
private def HasModelAt (stageIndex : Index) {sourceScheme : Scheme.{u}}
    (sourceMap : sourceScheme ⟶ cone.pt) : Prop :=
  ∃ (stageScheme : Scheme.{u}) (stageMap : stageScheme ⟶ diagram.obj stageIndex)
    (comparison : sourceScheme ⟶ stageScheme), LocallyOfFinitePresentation stageMap ∧
    CompactSpace stageScheme ∧ QuasiSeparatedSpace stageScheme ∧
      IsPullback comparison sourceMap stageMap (cone.π.app stageIndex)

variable (diagram cone) in
/-- The property that `sourceMap : sourceScheme ⟶ lim Dⱼ` is the base change of a scheme of
finite presentation over one of the stages. -/
private def HasFiniteStageModel {sourceScheme : Scheme.{u}}
    (sourceMap : sourceScheme ⟶ cone.pt) : Prop :=
  ∃ stageIndex, HasModelAt diagram cone stageIndex sourceMap

/-- Finite-stage model data together with a descended quasi-compact open. -/
private structure ModelWithOpenAt {U : Scheme.{u}} (u : U ⟶ cone.pt)
    (chosenOpen : U.Opens) (i : Index) where
  scheme : Scheme.{u}
  map : scheme ⟶ diagram.obj i
  comparison : U ⟶ scheme
  openSubset : scheme.Opens
  finitePresentation : LocallyOfFinitePresentation map
  compactSpace : CompactSpace scheme
  quasiSeparated : QuasiSeparatedSpace scheme
  square : IsPullback comparison u map (cone.π.app i)
  compactOpen : IsCompact (openSubset : Set scheme)
  preimage : comparison ⁻¹ᵁ openSubset = chosenOpen

variable (diagram cone) in
/-- A finite-stage model whose chosen open pulls back to the specified open. -/
private def HasModelWithOpenAt (stageIndex : Index) {sourceScheme : Scheme.{u}}
    (sourceMap : sourceScheme ⟶ cone.pt) (chosenOpen : sourceScheme.Opens) : Prop :=
  Nonempty (ModelWithOpenAt (diagram := diagram) sourceMap chosenOpen stageIndex)

/-- A chart model uses the range of its overlap immersion as the chosen open. -/
private abbrev OpenChartModel {T U : Scheme.{u}} (u : U ⟶ cone.pt) (r : T ⟶ U)
    [IsOpenImmersion r] (i : Index) :=
  ModelWithOpenAt (diagram := diagram) u r.opensRange i

variable {T U : Scheme.{u}} {u : U ⟶ cone.pt} {r : T ⟶ U} [IsOpenImmersion r]
  {i : Index}

private noncomputable def ModelWithOpenAt.overlapMap
    (M : OpenChartModel (diagram := diagram) u r i) : T ⟶ M.openSubset.toScheme :=
  IsOpenImmersion.lift M.openSubset.ι (r ≫ M.comparison) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    -- Membership in the chosen model open is membership in its comparison preimage.
    change r x ∈ M.comparison ⁻¹ᵁ M.openSubset
    rw [M.preimage]
    exact ⟨x, rfl⟩)

private lemma ModelWithOpenAt.overlap_square (M : OpenChartModel (diagram := diagram) u r i) :
    IsPullback M.overlapMap r M.openSubset.ι M.comparison :=
  IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac ..).symm
    (by rw [Scheme.Opens.opensRange_ι, M.preimage])

private lemma ModelWithOpenAt.overlap_base_square (M : OpenChartModel (diagram := diagram) u r i) :
    IsPullback M.overlapMap (r ≫ u) (M.openSubset.ι ≫ M.map) (cone.π.app i) :=
  M.overlap_square.paste_vert M.square

private noncomputable abbrev ModelWithOpenAt.baseChange {U : Scheme.{u}}
    {u : U ⟶ cone.pt} {chosenOpen : U.Opens} {i : Index}
    (M : ModelWithOpenAt (diagram := diagram) u chosenOpen i) {j : Index} (t : j ⟶ i)
    [QuasiCompact (diagram.map t)] [QuasiSeparated (diagram.map t)] :
    ModelWithOpenAt (diagram := diagram) u chosenOpen j := by
  let := M.finitePresentation
  let := M.compactSpace
  let := M.quasiSeparated
  have square : IsPullback M.comparison u M.map (cone.π.app j ≫ diagram.map t) := by
    rw [cone.w t]
    exact M.square
  let rightSquare := IsPullback.of_hasPullback M.map (diagram.map t)
  refine
    { scheme := pullback M.map (diagram.map t)
      map := pullback.snd _ _
      comparison := rightSquare.lift M.comparison (u ≫ cone.π.app j)
        (by rw [square.w, Category.assoc])
      openSubset := pullback.fst M.map (diagram.map t) ⁻¹ᵁ M.openSubset
      finitePresentation := inferInstance
      compactSpace := inferInstance
      quasiSeparated := quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
      square := square.of_right' rightSquare
      compactOpen := QuasiCompact.isCompact_preimage _ M.openSubset.isOpen M.compactOpen
      preimage := ?_ }
  rw [← Scheme.Hom.comp_preimage, IsPullback.lift_fst, M.preimage]

private lemma ModelWithOpenAt.baseChange_overlap_square
    (M : OpenChartModel (diagram := diagram) u r i) {j : Index} (t : j ⟶ i)
    [QuasiCompact (diagram.map t)] [QuasiSeparated (diagram.map t)] :
    IsPullback (pullback.fst M.map (diagram.map t) ∣_ M.openSubset)
      ((M.baseChange t).openSubset.ι ≫ (M.baseChange t).map)
      (M.openSubset.ι ≫ M.map) (diagram.map t) :=
  (isPullback_morphismRestrict (pullback.fst M.map (diagram.map t)) M.openSubset).paste_vert
    (IsPullback.of_hasPullback M.map (diagram.map t))

private lemma ModelWithOpenAt.baseChange_overlapMap_comp
    (M : OpenChartModel (diagram := diagram) u r i) {j : Index} (t : j ⟶ i)
    [QuasiCompact (diagram.map t)] [QuasiSeparated (diagram.map t)] :
    (M.baseChange t).overlapMap ≫
      (pullback.fst M.map (diagram.map t) ∣_ M.openSubset) = M.overlapMap := by
  rw [← cancel_mono M.openSubset.ι]
  simp only [Category.assoc, morphismRestrict_ι]
  rw [(M.baseChange t).overlap_square.w_assoc, IsPullback.lift_fst]
  exact M.overlap_square.w.symm

private lemma ModelWithOpenAt.overlapMap_comp_map
    (M : OpenChartModel (diagram := diagram) u r i) :
    M.overlapMap ≫ M.openSubset.ι ≫ M.map = r ≫ u ≫ cone.π.app i := by
  rw [M.overlap_square.w_assoc, M.square.w]

variable [IsCofiltered Index]
  [∀ {sourceIndex targetIndex : Index} (transition : sourceIndex ⟶ targetIndex),
    IsAffineHom (diagram.map transition)]

omit [IsCofiltered Index]
  [∀ {i j : Index} (f : i ⟶ j), IsAffineHom (diagram.map f)] in
private lemma HasModelWithOpenAt.mono {stageIndex laterIndex : Index}
    (transition : laterIndex ⟶ stageIndex)
    [QuasiCompact (diagram.map transition)] [QuasiSeparated (diagram.map transition)]
    {sourceScheme : Scheme.{u}}
    {sourceMap : sourceScheme ⟶ cone.pt} {chosenOpen : sourceScheme.Opens}
    (modelData : HasModelWithOpenAt diagram cone stageIndex sourceMap chosenOpen) :
    HasModelWithOpenAt diagram cone laterIndex sourceMap chosenOpen := by
  obtain ⟨M⟩ := modelData
  exact ⟨M.baseChange transition⟩

include limit in
/-- A quasi-compact open in a finite-stage model descends after passing to a later stage. -/
private lemma exists_modelWithOpenAt {stageIndex : Index} {sourceScheme : Scheme.{u}}
    {sourceMap : sourceScheme ⟶ cone.pt}
    (modelData : HasModelAt diagram cone stageIndex sourceMap) (chosenOpen : sourceScheme.Opens)
    (hW : IsCompact (chosenOpen : Set sourceScheme)) :
    ∃ laterIndex : Index, HasModelWithOpenAt diagram cone laterIndex sourceMap chosenOpen := by
  obtain ⟨stageScheme, stageMap, comparison, hp, hcpt, hqs, hsq⟩ := modelData
  have := hp; have := hcpt; have := hqs
  let c' := (cone.pullbackOver stageMap).extend hsq.flip.isoPullback.hom
  have hlim : IsLimit c' := (limit.pullbackOver stageMap).ofIsoLimit
    (Cone.ext hsq.flip.isoPullback.symm (fun overIndex ↦ by simp [c']))
  obtain ⟨overIndex, stageOpen, hOc, hO⟩ :=
    exists_preimage_eq (diagram.pullbackOver stageMap) c' hlim chosenOpen hW
  let a := c'.π.app overIndex
  have hsq' : IsPullback a sourceMap (pullback.fst (diagram.map overIndex.hom) stageMap)
      (cone.π.app overIndex.left) := by
    refine IsPullback.of_right ?_ (by simp [a, c'])
      (IsPullback.of_hasPullback (diagram.map overIndex.hom) stageMap).flip
    simpa [a, c'] using hsq
  exact ⟨overIndex.left, ⟨⟨pullback (diagram.map overIndex.hom) stageMap, pullback.fst _ _,
    a, stageOpen, inferInstance, inferInstance,
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd _ _), hsq', hOc, hO⟩⟩⟩

include limit in
/-- An affine scheme over an affine open of a stage has a finite-stage model. -/
private lemma HasFiniteStageModel.of_isAffine {baseStage : Index} {sourceScheme : Scheme.{u}}
    [IsAffine sourceScheme] (sourceMap : sourceScheme ⟶ cone.pt)
    [LocallyOfFinitePresentation sourceMap] {secondOpen : (diagram.obj baseStage).Opens}
    (hV : IsAffineOpen secondOpen) (openLift : sourceScheme ⟶ secondOpen.toScheme)
    (hq : openLift ≫ secondOpen.ι = sourceMap ≫ cone.π.app baseStage) :
    HasFiniteStageModel diagram cone sourceMap := by
  have : IsAffine secondOpen.toScheme := hV
  have : ∀ overIndex : Over baseStage,
      IsAffine ((diagram.pullbackOver secondOpen.ι).obj overIndex) := fun _ ↦ by
    dsimp; infer_instance
  let a := pullback.lift sourceMap openLift hq.symm
  have ha : a ≫ pullback.fst (cone.π.app baseStage) secondOpen.ι = sourceMap :=
    pullback.lift_fst ..
  have : LocallyOfFinitePresentation
      (a ≫ pullback.fst (cone.π.app baseStage) secondOpen.ι) := by
    simpa only [ha] using (inferInstance : LocallyOfFinitePresentation sourceMap)
  have : LocallyOfFinitePresentation a := locallyOfFinitePresentation_of_comp a
    (pullback.fst (cone.π.app baseStage) secondOpen.ι)
  obtain ⟨overIndex, stageScheme, hYaff, stageMap, hp, comparison, hsq⟩ :=
    CategoryTheory.Functor.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine
      (diagram.pullbackOver secondOpen.ι) (cone.pullbackOver secondOpen.ι)
      (limit.pullbackOver secondOpen.ι) a
  have := hYaff; have := hp
  have hbase : IsPullback
      ((cone.pullbackOver secondOpen.ι).π.app overIndex)
      (pullback.fst (cone.π.app baseStage) secondOpen.ι)
      (pullback.fst (diagram.map overIndex.hom) secondOpen.ι)
      (cone.π.app overIndex.left) := by
    refine IsPullback.of_right ?_ (by simp)
      (IsPullback.of_hasPullback (diagram.map overIndex.hom) secondOpen.ι).flip
    simpa using (IsPullback.of_hasPullback (cone.π.app baseStage) secondOpen.ι).flip
  refine ⟨overIndex.left, stageScheme,
    stageMap ≫ pullback.fst (diagram.map overIndex.hom) secondOpen.ι, comparison,
    inferInstance, inferInstance, inferInstance, ?_⟩
  simpa only [ha] using hsq.paste_vert hbase

include limit in
/-- An affine open of a scheme over the limit that lies over an affine open of
one of the stages descends to a finite stage. -/
private lemma HasFiniteStageModel.of_isAffineOpen {baseStage : Index}
    {sourceScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ cone.pt)
    [LocallyOfFinitePresentation sourceMap] {chosenOpen : sourceScheme.Opens}
    (hW : IsAffineOpen chosenOpen) {secondOpen : (diagram.obj baseStage).Opens}
    (hV : IsAffineOpen secondOpen)
    (hle : chosenOpen ≤ (sourceMap ≫ cone.π.app baseStage) ⁻¹ᵁ secondOpen) :
    HasFiniteStageModel diagram cone (chosenOpen.ι ≫ sourceMap) := by
  have : IsAffine chosenOpen.toScheme := hW
  refine HasFiniteStageModel.of_isAffine limit _ hV
    ((sourceMap ≫ cone.π.app baseStage).resLE secondOpen chosenOpen hle) ?_
  rw [Scheme.Hom.resLE_comp_ι, Category.assoc]

omit [IsCofiltered Index]
  [∀ {i j : Index} (f : i ⟶ j), IsAffineHom (diagram.map f)]
  in
private lemma HasFiniteStageModel.comp_iso {sourceScheme isomorphicSource : Scheme.{u}}
    (modelIso : isomorphicSource ≅ sourceScheme) {sourceMap : sourceScheme ⟶ cone.pt}
    (modelData : HasFiniteStageModel diagram cone sourceMap) :
    HasFiniteStageModel diagram cone (modelIso.hom ≫ sourceMap) := by
  obtain ⟨stageIndex, stageScheme, stageMap, comparison, hp, hcpt, hqs, hsq⟩ := modelData
  refine ⟨stageIndex, stageScheme, stageMap, modelIso.hom ≫ comparison, hp, hcpt, hqs, ?_⟩
  have hiso : IsPullback modelIso.hom (modelIso.hom ≫ sourceMap) sourceMap (𝟙 cone.pt) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hsq

variable [∀ i, CompactSpace (diagram.obj i)] [∀ i, QuasiSeparatedSpace (diagram.obj i)]

include limit in
/-- Descend the isomorphism between the two canonical pullback presentations of an overlap. -/
private lemma ModelWithOpenAt.exists_overlap_pullback_iso {T U V : Scheme.{u}}
    {u : U ⟶ cone.pt} {v : V ⟶ cone.pt} {r : T ⟶ U} {s : T ⟶ V}
    [IsOpenImmersion r] [IsOpenImmersion s] {i : Index}
    (M : OpenChartModel (diagram := diagram) u r i)
    (N : OpenChartModel (diagram := diagram) v s i) (h : r ≫ u = s ≫ v) :
    ∃ (j : Index) (t : j ⟶ i)
      (e : pullback (diagram.map t) (M.openSubset.ι ≫ M.map) ≅
        pullback (diagram.map t) (N.openSubset.ι ≫ N.map)),
      e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        M.overlap_base_square.flip.isoPullback.hom ≫
            pullback.map (cone.π.app i) (M.openSubset.ι ≫ M.map) (diagram.map t)
              (M.openSubset.ι ≫ M.map) (cone.π.app j) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ e.hom =
          N.overlap_base_square.flip.isoPullback.hom ≫
            pullback.map (cone.π.app i) (N.openSubset.ι ≫ N.map) (diagram.map t)
              (N.openSubset.ι ≫ N.map) (cone.π.app j) (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  let := M.finitePresentation; let := M.compactSpace; let := M.quasiSeparated
  let := N.finitePresentation; let := N.compactSpace; let := N.quasiSeparated
  let : CompactSpace M.openSubset.toScheme := isCompact_iff_compactSpace.mp M.compactOpen
  let : CompactSpace N.openSubset.toScheme := isCompact_iff_compactSpace.mp N.compactOpen
  let : QuasiSeparatedSpace M.openSubset.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding M.openSubset.ι.isOpenEmbedding
  let : QuasiSeparatedSpace N.openSubset.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding N.openSubset.ι.isOpenEmbedding
  let p := M.openSubset.ι ≫ M.map
  let q := N.openSubset.ι ≫ N.map
  let a := M.overlap_base_square.flip.isoPullback.symm ≪≫
    N.overlap_base_square.flip.isoPullback
  have ha : a.hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← h, IsPullback.isoPullback_inv_fst]
  obtain ⟨j, hji, b, hb₁, hb₂⟩ := limit.exists_pullbackMap_comp_eq a.hom ha
  have : IsIso (pullback.map (cone.π.app j) (pullback.fst (diagram.map hji) p) (cone.π.app j)
      (pullback.fst (diagram.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by exact hb₁.symm)) :=
    (MorphismProperty.pullbackMap_iff_of_pullbackMap_comp_eq
      (.isomorphisms Scheme) hji ha hb₁ hb₂).mpr (inferInstance : IsIso a.hom)
  obtain ⟨k, hkj, hk⟩ := limit.exists_isIso_pullbackMap b hb₁
  let ψ {Z : Scheme.{u}} (r : Z ⟶ diagram.obj i) :
      pullback (diagram.map hkj) (pullback.fst (diagram.map hji) r) ≅
        pullback (diagram.map (hkj ≫ hji)) r :=
    pullbackRightPullbackFstIso (diagram.map hji) r (diagram.map hkj) ≪≫
      pullback.congrHom (diagram.map_comp hkj hji).symm rfl
  let bK := pullback.map (diagram.map hkj) (pullback.fst (diagram.map hji) p) (diagram.map hkj)
    (pullback.fst (diagram.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by exact hb₁.symm)
  have : IsIso bK := hk
  let e := (ψ p).symm ≪≫ asIso bK ≪≫ ψ q
  refine ⟨k, hkj ≫ hji, e, ?_, ?_⟩
  · simp [e, ψ, bK, p, q]
  · apply pullback.hom_ext
    · simpa [e, ψ, bK, a, p, q, Category.assoc] using
        congrArg (M.overlap_base_square.flip.isoPullback.hom ≫ ·)
          (((reassoc_of% ha) (cone.π.app k)).symm)
    · have h := congrArg (· ≫ pullback.snd (diagram.map hji) q) hb₂
      simp only [Category.assoc] at h
      have key : pullback.map (cone.π.app i) p (diagram.map (hkj ≫ hji)) p
          (cone.π.app k) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ (ψ p).inv ≫
            pullback.snd (diagram.map hkj) (pullback.fst (diagram.map hji) p) =
          pullback.map (cone.π.app i) p (diagram.map hji) p
            (cone.π.app j) (𝟙 _) (𝟙 _) (by simp) (by simp) := by
        apply pullback.hom_ext <;> simp [ψ]
      have h' := congrArg (· ≫ b ≫ pullback.snd (diagram.map hji) q) key
      simpa [e, ψ, bK, a, p, q, Category.assoc] using
        congrArg (M.overlap_base_square.flip.isoPullback.hom ≫ ·) (h'.trans h)

include limit in
private lemma ModelWithOpenAt.exists_iso_overlap {T U V : Scheme.{u}}
    {u : U ⟶ cone.pt} {v : V ⟶ cone.pt} {r : T ⟶ U} {s : T ⟶ V}
    [IsOpenImmersion r] [IsOpenImmersion s] {i : Index}
    (M : OpenChartModel (diagram := diagram) u r i)
    (N : OpenChartModel (diagram := diagram) v s i) (h : r ≫ u = s ≫ v) :
    ∃ (j : Index) (t : j ⟶ i)
      (e : (M.baseChange t).openSubset.toScheme ≅ (N.baseChange t).openSubset.toScheme),
      e.hom ≫ (N.baseChange t).openSubset.ι ≫ (N.baseChange t).map =
        (M.baseChange t).openSubset.ι ≫ (M.baseChange t).map ∧
      (M.baseChange t).overlapMap ≫ e.hom = (N.baseChange t).overlapMap := by
  obtain ⟨j, t, e, he₁, he₂⟩ := M.exists_overlap_pullback_iso limit N h
  let e₁ := (M.baseChange_overlap_square t).flip.isoPullback
  let e₂ := (N.baseChange_overlap_square t).flip.isoPullback
  have hcomp {T' U' : Scheme.{u}} {u' : U' ⟶ cone.pt} {r' : T' ⟶ U'}
      [IsOpenImmersion r'] (P : OpenChartModel (diagram := diagram) u' r' i) :
      (P.baseChange t).overlapMap ≫ (P.baseChange_overlap_square t).flip.isoPullback.hom =
        P.overlap_base_square.flip.isoPullback.hom ≫
          pullback.map (cone.π.app i) (P.openSubset.ι ≫ P.map) (diagram.map t)
            (P.openSubset.ι ≫ P.map) (cone.π.app j) (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simpa [Category.assoc, IsPullback.isoPullback_hom_fst] using
        (P.baseChange t).overlapMap_comp_map
    · simpa [Category.assoc, IsPullback.isoPullback_hom_snd] using
        P.baseChange_overlapMap_comp t
  refine ⟨j, t, e₁ ≪≫ e ≪≫ e₂.symm, ?_, ?_⟩
  · dsimp only [Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Category.assoc, IsPullback.isoPullback_inv_fst, he₁,
      IsPullback.isoPullback_hom_fst]
  · rw [← cancel_mono e₂.hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, hcomp M, Category.assoc, he₂, ← hcomp N]

omit [IsCofiltered Index]
  [∀ {i j : Index} (f : i ⟶ j), IsAffineHom (diagram.map f)]
  [∀ i, CompactSpace (diagram.obj i)] [∀ i, QuasiSeparatedSpace (diagram.obj i)] in
private lemma hasFiniteStageModel_of_compatible_charts {X : Scheme.{u}} (f : X ⟶ cone.pt)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) {i : Index}
    (M : OpenChartModel (diagram := diagram) (U.ι ≫ f) (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) i)
    (N : OpenChartModel (diagram := diagram) (V.ι ≫ f) (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) i)
    (e : M.openSubset.toScheme ≅ N.openSubset.toScheme)
    (he₁ : e.hom ≫ N.openSubset.ι ≫ N.map = M.openSubset.ι ≫ M.map)
    (he₂ : M.overlapMap ≫ e.hom = N.overlapMap) : HasFiniteStageModel diagram cone f := by
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
  have hsquare : IsPullback a (pushoutOpensDesc U V ≫ f) p (cone.π.app i) := by
    apply Scheme.Hom.isPullback_pushout_map_desc_of_isPullback M.openSubset.ι
      (e.hom ≫ N.openSubset.ι) (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V))
      M.comparison N.comparison M.overlapMap M.map N.map _
      (pushoutOpensDesc U V ≫ f) (cone.π.app i) M.overlap_square hv
    · rw [inl_pushoutOpensDesc_assoc]
      exact M.square
    · rw [inr_pushoutOpensDesc_assoc]
      exact N.square
  let : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have := isIso_pushoutOpensDesc U V hUV
  refine ⟨i, pushout M.openSubset.ι (e.hom ≫ N.openSubset.ι), p,
    inv (pushoutOpensDesc U V) ≫ a,
    IsZariskiLocalAtSource.pushout_desc _ _ _ _ _ inferInstance inferInstance,
    inferInstance, quasiSeparatedSpace_pushout _ _, ?_⟩
  have hIso : IsPullback (inv (pushoutOpensDesc U V)) f (pushoutOpensDesc U V ≫ f)
      (𝟙 cone.pt) := IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hIso.paste_horiz hsquare

include limit in
/-- Two finite-stage chart models glue after descending their common quasi-compact overlap. -/
private lemma HasFiniteStageModel.of_sup_eq_top {X : Scheme.{u}} (f : X ⟶ cone.pt)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (hWc : IsCompact ((U ⊓ V : X.Opens) : Set X))
    (hU : HasFiniteStageModel diagram cone (U.ι ≫ f))
    (hV : HasFiniteStageModel diagram cone (V.ι ≫ f)) : HasFiniteStageModel diagram cone f := by
  have hc (A B : X.Opens) (hAB : IsCompact ((A ⊓ B : X.Opens) : Set X)) :
      IsCompact ((A.ι ⁻¹ᵁ B : A.toScheme.Opens) : Set A.toScheme) := by
    have he : (A.ι ⁻¹ᵁ B : A.toScheme.Opens) = A.ι ⁻¹ᵁ (A ⊓ B) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
    rw [he]
    exact A.ι.isOpenEmbedding.isInducing.isCompact_preimage' hAB
      (by rw [Scheme.Opens.range_ι]; exact inf_le_left)
  obtain ⟨i, hU⟩ := hU
  obtain ⟨j, hV⟩ := hV
  obtain ⟨k, hU⟩ := exists_modelWithOpenAt limit hU _ (hc U V hWc)
  obtain ⟨l, hV⟩ := exists_modelWithOpenAt limit hV _ (hc V U (by simpa [inf_comm] using hWc))
  obtain ⟨⟨Y, p, a, W, hp, hc, hq, hs, hW, ha⟩⟩ := hU.mono (IsCofiltered.minToLeft k l)
  obtain ⟨⟨Z, q, b, W', hq', hc', hq'', hs', hW', hb⟩⟩ := hV.mono (IsCofiltered.minToRight k l)
  let M : OpenChartModel (diagram := diagram) (U.ι ≫ f) (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      (IsCofiltered.min k l) :=
    ⟨Y, p, a, W, hp, hc, hq, hs, hW, by
      simpa [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf] using ha⟩
  let N : OpenChartModel (diagram := diagram) (V.ι ≫ f) (X.homOfLE (inf_le_right : U ⊓ V ≤ V))
      (IsCofiltered.min k l) :=
    ⟨Z, q, b, W', hq', hc', hq'', hs', hW', by
      simpa [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf] using hb⟩
  obtain ⟨_n, t, e, he₁, he₂⟩ := M.exists_iso_overlap limit N (by
    simp only [← Category.assoc, Scheme.homOfLE_ι])
  exact hasFiniteStageModel_of_compatible_charts f U V hUV (M.baseChange t) (N.baseChange t)
    e he₁ he₂

omit [IsCofiltered Index]
  [∀ {i j : Index} (g : i ⟶ j), IsAffineHom (diagram.map g)]
  [∀ i, CompactSpace (diagram.obj i)] [∀ i, QuasiSeparatedSpace (diagram.obj i)] in
private lemma HasFiniteStageModel.preimage_open {X : Scheme.{u}} (f : X ⟶ cone.pt)
    {U W : X.Opens} (hUW : U ≤ W) (hU : HasFiniteStageModel diagram cone (U.ι ≫ f)) :
    HasFiniteStageModel diagram cone ((W.ι ⁻¹ᵁ U).ι ≫ W.ι ≫ f) := by
  simpa only [Category.assoc, Scheme.Opens.isoOfLE_hom_ι_assoc] using
    HasFiniteStageModel.comp_iso (Scheme.Opens.isoOfLE hUW) hU

include limit in
/-- Finite-stage models of two opens glue when their intersection is quasi-compact. -/
private lemma HasFiniteStageModel.sup {X : Scheme.{u}} (f : X ⟶ cone.pt) (U V : X.Opens)
    (hW : IsCompact ((U ⊓ V : X.Opens) : Set X))
    (hU : HasFiniteStageModel diagram cone (U.ι ≫ f))
    (hV : HasFiniteStageModel diagram cone (V.ι ≫ f)) :
    HasFiniteStageModel diagram cone ((U ⊔ V).ι ≫ f) := by
  let W := U ⊔ V
  have hc : IsCompact (((W.ι ⁻¹ᵁ U) ⊓ (W.ι ⁻¹ᵁ V) : W.toScheme.Opens) : Set W.toScheme) := by
    rw [← Scheme.Hom.preimage_inf]
    exact W.ι.isOpenEmbedding.isInducing.isCompact_preimage' hW
      (by rw [Scheme.Opens.range_ι]; exact inf_le_left.trans le_sup_left)
  apply HasFiniteStageModel.of_sup_eq_top limit (W.ι ≫ f) (W.ι ⁻¹ᵁ U) (W.ι ⁻¹ᵁ V)
    (by rw [← Scheme.Hom.preimage_sup]; exact Scheme.Opens.ι_preimage_self W) hc
  · exact hU.preimage_open f le_sup_left
  · exact hV.preimage_open f le_sup_right

include limit in
/-- A finite union of affine charts lying over affine opens of a stage has a finite-stage model. -/
private lemma hasFiniteStageModel_finsetSup {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {i : Index} (f : X ⟶ cone.pt) [LocallyOfFinitePresentation f] (s : Finset X.Opens)
    (hs : ∀ U ∈ s, IsAffineOpen U ∧ ∃ V : (diagram.obj i).Opens,
      IsAffineOpen V ∧ U ≤ (f ≫ cone.π.app i) ⁻¹ᵁ V) :
    HasFiniteStageModel diagram cone ((s.sup id : X.Opens).ι ≫ f) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sup_empty]
    exact HasFiniteStageModel.of_isAffineOpen limit f (isAffineOpen_bot X)
      (isAffineOpen_bot (diagram.obj i)) bot_le
  | insert U s _ ih =>
    obtain ⟨hU, V, hV, hUV⟩ := hs U (Finset.mem_insert_self U s)
    have hs' := fun W hW ↦ hs W (Finset.mem_insert_of_mem hW)
    have hc : IsCompact ((s.sup id : X.Opens) : Set X) := by
      simpa only [TopologicalSpace.Opens.coe_finset_sup, Finset.sup_set_eq_biUnion,
        Function.comp_apply, id_eq] using s.isCompact_biUnion (fun W hW ↦ (hs' W hW).1.isCompact)
    rw [Finset.sup_insert, id]
    apply HasFiniteStageModel.sup limit f U (s.sup id)
    · exact QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen hU.isCompact (s.sup id).isOpen hc
    · exact HasFiniteStageModel.of_isAffineOpen limit f hU hV hUV
    · exact ih hs'

include limit in
/-- A finitely presented scheme over a cofiltered limit of quasi-compact,
quasi-separated schemes with affine transitions is the pullback of an actual
finitely presented scheme over some stage. -/
private theorem exists_isPullback_of_finitePresentation_allStages {sourceScheme : Scheme.{u}}
    (sourceMap : sourceScheme ⟶ cone.pt)
    [LocallyOfFinitePresentation sourceMap] [QuasiCompact sourceMap] [QuasiSeparated sourceMap] :
    ∃ (index : Index) (stageScheme : Scheme.{u}) (stageMap : stageScheme ⟶ diagram.obj index)
      (_ : LocallyOfFinitePresentation stageMap) (_ : QuasiCompact stageMap)
      (_ : QuasiSeparated stageMap) (comparison : sourceScheme ⟶ stageScheme),
      IsPullback comparison sourceMap stageMap (cone.π.app index) := by
  classical
  obtain ⟨baseStage⟩ : Nonempty Index := IsCofiltered.nonempty
  have := isAffineHom_π_app _ _ limit
  have : CompactSpace cone.pt := QuasiCompact.compactSpace_of_compactSpace (cone.π.app baseStage)
  have : QuasiSeparatedSpace cone.pt := quasiSeparatedSpace_of_quasiSeparated (cone.π.app baseStage)
  have : CompactSpace sourceScheme := QuasiCompact.compactSpace_of_compactSpace sourceMap
  have : QuasiSeparatedSpace sourceScheme := quasiSeparatedSpace_of_quasiSeparated sourceMap
  let A := {V : sourceScheme.affineOpens // ∃ U : (diagram.obj baseStage).affineOpens,
    V.val ≤ (sourceMap ≫ cone.π.app baseStage) ⁻¹ᵁ U.val}
  have htop : IsCompactElement (⊤ : sourceScheme.Opens) :=
    (TopologicalSpace.Opens.isCompactElement_iff _).mpr (by simpa using isCompact_univ)
  obtain ⟨s, hs⟩ := htop.exists_finset_of_le_iSup (fun V : A ↦ V.val.val)
    (by rw [Scheme.Hom.iSup_affineOpens_le_preimage_eq_top])
  have modelData := hasFiniteStageModel_finsetSup limit (i := baseStage) sourceMap
    (s.image fun V : A ↦ V.val.val) (by
      intro U hU
      obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨W, hW⟩ := V.property
      exact ⟨V.val.property, W.val, W.property, hW⟩)
  have hsup : (s.image fun V : A ↦ V.val.val).sup id = ⊤ := by
    apply top_le_iff.mp
    rw [Finset.sup_image]
    simpa only [Function.comp_apply, id_eq, Finset.sup_eq_iSup] using hs
  rw [hsup] at modelData
  replace modelData := HasFiniteStageModel.comp_iso sourceScheme.topIso.symm modelData
  rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at modelData
  obtain ⟨index, stageScheme, stageMap, comparison, hp, hcpt, hqs, hsq⟩ := modelData
  have := hp; have := hcpt; have := hqs
  exact ⟨index, stageScheme, stageMap, hp, inferInstance, inferInstance, comparison, hsq⟩

include limit in
omit [∀ i, CompactSpace (diagram.obj i)] [∀ i, QuasiSeparatedSpace (diagram.obj i)] in
/-- A finitely presented scheme over a cofiltered affine-transition limit descends to a stage
as soon as one member of the diagram is quasi-compact and quasi-separated. -/
theorem _root_.CategoryTheory.Limits.IsLimit.exists_isPullback_of_finitePresentation
    (baseStage : Index)
    [CompactSpace (diagram.obj baseStage)] [QuasiSeparatedSpace (diagram.obj baseStage)]
    {sourceScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ cone.pt)
    [LocallyOfFinitePresentation sourceMap] [QuasiCompact sourceMap] [QuasiSeparated sourceMap] :
    ∃ (index : Index) (stageScheme : Scheme.{u}) (stageMap : stageScheme ⟶ diagram.obj index)
      (_ : LocallyOfFinitePresentation stageMap) (_ : QuasiCompact stageMap)
      (_ : QuasiSeparated stageMap) (comparison : sourceScheme ⟶ stageScheme),
      IsPullback comparison sourceMap stageMap (cone.π.app index) := by
  let restrictedDiagram := Over.forget baseStage ⋙ diagram
  have {i j : Over baseStage} (t : i ⟶ j) : IsAffineHom (restrictedDiagram.map t) :=
    inferInstanceAs (IsAffineHom (diagram.map t.left))
  have (i : Over baseStage) : CompactSpace (restrictedDiagram.obj i) :=
    QuasiCompact.compactSpace_of_compactSpace (diagram.map i.hom)
  have (i : Over baseStage) : QuasiSeparatedSpace (restrictedDiagram.obj i) :=
    quasiSeparatedSpace_of_quasiSeparated (diagram.map i.hom)
  have restrictedLimit : IsLimit (cone.whisker (Over.forget baseStage)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget baseStage) cone).symm limit
  obtain ⟨i, X, f, hfp, hqc, hqs, a, square⟩ :=
    exists_isPullback_of_finitePresentation_allStages restrictedLimit sourceMap
  exact ⟨i.left, X, f, hfp, hqc, hqs, a, square⟩

end AlgebraicGeometry
