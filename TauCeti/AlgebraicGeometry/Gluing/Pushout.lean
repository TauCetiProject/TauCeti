/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import TauCeti.AlgebraicGeometry.Scheme.LocallyDirected

/-!
# Cartesian charts of pushouts along open immersions

Two schemes glued along a common open have the expected intersections of charts.
Cartesian morphisms of gluing data induce Cartesian chart squares. A quasi-compact
overlap preserves quasi-separatedness, and a two-open cover gives a pushout presentation.

Reference: The Stacks Project, Section 26.14, Gluing schemes (Tag 01JA).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {U X Y : Scheme.{u}} (f :
  U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion
  f] [IsOpenImmersion g]

instance [CompactSpace X] [CompactSpace Y] : CompactSpace ↑(pushout f
  g) := by
  constructor
  rw [← range_pushout_inl_union_range_pushout_inr f g]
  exact (isCompact_range (pushout.inl f g).continuous).union
    (isCompact_range (pushout.inr f g).continuous)

section PointsAndMap


lemma pushout_inl_eq_inr_iff (firstPoint : X) (secondPoint : Y) :
    pushout.inl f g firstPoint = pushout.inr f g secondPoint ↔ ∃
      intersectionPoint : U, f intersectionPoint = firstPoint ∧ g
      intersectionPoint = secondPoint := by
  -- Pushout inclusions are the corresponding colimit cocone maps.
  rw [show pushout.inl f g firstPoint = pushout.inr f g secondPoint ↔
      colimit.ι (span f g) WalkingSpan.left firstPoint = colimit.ι (span f
        g) WalkingSpan.right secondPoint from
    Iff.rfl, Scheme.IsLocallyDirected.ι_eq_ι_iff]
  constructor
  · rintro ⟨spanIndex, toFirst, toSecond, intersectionPoint, hx, hy⟩
    obtain (_ | ⟨_ | _⟩) := spanIndex
    · rw [Subsingleton.elim toFirst WalkingSpan.Hom.fst] at hx
      rw [Subsingleton.elim toSecond WalkingSpan.Hom.snd] at hy
      exact ⟨intersectionPoint, hx, hy⟩
    · exact nomatch toSecond
    · exact nomatch toFirst
  · rintro ⟨intersectionPoint, hx, hy⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, intersectionPoint, hx, hy⟩

lemma opensRange_pushout_inl_sup_opensRange_pushout_inr :
    (pushout.inl f g).opensRange ⊔ (pushout.inr f g).opensRange = ⊤ := by
  rw [eq_top_iff]
  rintro firstPoint -
  rw [TopologicalSpace.Opens.mem_sup]
  exact Set.eq_univ_iff_forall.mp (range_pushout_inl_union_range_pushout_inr f g)
    firstPoint

lemma preimage_opensRange_pushout_inl :
    pushout.inr f g ⁻¹ᵁ (pushout.inl f g).opensRange = g.opensRange := by
  ext targetPoint
  constructor
  · rintro ⟨secondPoint, hy⟩
    obtain ⟨intersectionPoint, -, rfl⟩ := (pushout_inl_eq_inr_iff f g secondPoint
      targetPoint).mp hy
    exact ⟨intersectionPoint, rfl⟩
  · rintro ⟨intersectionPoint, rfl⟩
    exact ⟨f intersectionPoint, (pushout_inl_eq_inr_iff f g _ _).mpr
      ⟨intersectionPoint, rfl, rfl⟩⟩

lemma preimage_opensRange_pushout_inr :
    pushout.inl f g ⁻¹ᵁ (pushout.inr f g).opensRange = f.opensRange := by
  ext secondPoint
  constructor
  · rintro ⟨targetPoint, hz⟩
    obtain ⟨intersectionPoint, rfl, -⟩ := (pushout_inl_eq_inr_iff f g secondPoint
      targetPoint).mp hz.symm
    exact ⟨intersectionPoint, rfl⟩
  · rintro ⟨intersectionPoint, rfl⟩
    exact ⟨g intersectionPoint, ((pushout_inl_eq_inr_iff f g _ _).mpr
      ⟨intersectionPoint, rfl, rfl⟩).symm⟩

variable {U' X' Y' : Scheme.{u}}
  (f' : U' ⟶ X') (g' : U' ⟶
  Y')
  [IsOpenImmersion f'] [IsOpenImmersion g']
  (a : X' ⟶ X) (b : Y' ⟶
    Y) (c : U' ⟶ U)
  (hf : c ≫ f = f' ≫ a) (hg :
    c ≫ g = g' ≫ b)

include hf hg in
lemma preimage_opensRange_pushout_inl_of_isPullback (square : IsPullback c
    g' g b) :
    pushout.map f' g' f g a b
      c hf.symm hg.symm ⁻¹ᵁ (pushout.inl f g).opensRange =
      (pushout.inl f' g').opensRange := by
  apply le_antisymm
  · rintro gluedPoint hp
    have : gluedPoint ∈ (pushout.inl f' g').opensRange ⊔ (pushout.inr
      f' g').opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (hmem | ⟨sourceSecondPoint, rfl⟩) := this
    · exact hmem
    · replace hp : (pushout.inr f' g' ≫ pushout.map f'
      g' f g a b c hf.symm
      hg.symm) sourceSecondPoint ∈
          (pushout.inl f g).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inr_desc] at hp
      obtain ⟨secondPoint, hy⟩ := hp
      obtain ⟨intersectionPoint, -, hu⟩ := (pushout_inl_eq_inr_iff f g secondPoint
        (b sourceSecondPoint)).mp
        (by rwa [Scheme.Hom.comp_apply] at hy)
      obtain ⟨sourceIntersectionPoint, -, rfl⟩ := Scheme.exists_preimage_of_isPullback square
        intersectionPoint sourceSecondPoint hu
      -- Express chart membership through the composite morphism.
      change pushout.inr f' g' (g' sourceIntersectionPoint) ∈
        (pushout.inl f' g').opensRange
      exact ⟨f' sourceIntersectionPoint, (pushout_inl_eq_inr_iff f'
        g' _ _).mpr ⟨sourceIntersectionPoint, rfl, rfl⟩⟩
  · rintro gluedPoint ⟨sourceFirstPoint, rfl⟩
    -- Express chart membership through the composite morphism.
    change (pushout.inl f' g' ≫ pushout.map f' g'
      f g a b c hf.symm hg.symm)
      sourceFirstPoint ∈
      (pushout.inl f g).opensRange
    rw [pushout.inl_desc, Scheme.Hom.comp_apply]
    exact ⟨a sourceFirstPoint, rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `Y`-component square is cartesian,
the `X`-component square of the induced morphism of pushouts is cartesian. -/
lemma isPullback_pushout_map_inl_of_isPullback (square : IsPullback c
    g' g b) :
    IsPullback a (pushout.inl f' g') (pushout.inl f
      g)
      (pushout.map f' g' f g a b
        c hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inl_desc _ _ _)
    (preimage_opensRange_pushout_inl_of_isPullback f g f' g'
      a b c hf hg square)

include hf hg in
lemma preimage_opensRange_pushout_inr_of_isPullback (square : IsPullback c
    f' f a) :
    pushout.map f' g' f g a b
      c hf.symm hg.symm ⁻¹ᵁ (pushout.inr f g).opensRange =
      (pushout.inr f' g').opensRange := by
  apply le_antisymm
  · rintro gluedPoint hp
    have : gluedPoint ∈ (pushout.inl f' g').opensRange ⊔ (pushout.inr
      f' g').opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (⟨sourceFirstPoint, rfl⟩ | hmem) := this
    · replace hp : (pushout.inl f' g' ≫ pushout.map f'
      g' f g a b c hf.symm
      hg.symm) sourceFirstPoint ∈
          (pushout.inr f g).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inl_desc] at hp
      obtain ⟨secondPoint, hz⟩ := hp
      obtain ⟨intersectionPoint, hu, -⟩ := (pushout_inl_eq_inr_iff f g (a
        sourceFirstPoint) secondPoint).mp
        (by rw [Scheme.Hom.comp_apply] at hz; exact hz.symm)
      obtain ⟨sourceIntersectionPoint, -, rfl⟩ := Scheme.exists_preimage_of_isPullback square
        intersectionPoint sourceFirstPoint hu
      -- Express chart membership through the composite morphism.
      change pushout.inl f' g' (f' sourceIntersectionPoint) ∈
        (pushout.inr f' g').opensRange
      exact ⟨g' sourceIntersectionPoint, ((pushout_inl_eq_inr_iff f'
        g' _ _).mpr ⟨sourceIntersectionPoint, rfl, rfl⟩).symm⟩
    · exact hmem
  · rintro gluedPoint ⟨sourceSecondPoint, rfl⟩
    -- Express chart membership through the composite morphism.
    change (pushout.inr f' g' ≫ pushout.map f' g'
      f g a b c hf.symm hg.symm)
      sourceSecondPoint ∈
      (pushout.inr f g).opensRange
    rw [pushout.inr_desc, Scheme.Hom.comp_apply]
    exact ⟨b sourceSecondPoint, rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `X`-component square is cartesian,
the `Y`-component square of the induced morphism of pushouts is cartesian. -/
lemma isPullback_pushout_map_inr_of_isPullback (square : IsPullback c f'
    f a) :
    IsPullback b (pushout.inr f' g') (pushout.inr f
      g)
      (pushout.map f' g' f g a b
        c hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inr_desc _ _ _)
    (preimage_opensRange_pushout_inr_of_isPullback f g f' g'
      a b c hf hg square)

end PointsAndMap

section QuasiSeparated

lemma image_inl_inter_image_inr (firstSubset : Set X) (secondSubset : Set Y) :
    (pushout.inl f g '' firstSubset) ∩ (pushout.inr f g '' secondSubset) =
      pushout.inl f g '' (firstSubset ∩ f '' (g ⁻¹' secondSubset)) := by
  apply subset_antisymm
  · rintro - ⟨⟨firstPoint, hx, rfl⟩, ⟨secondPoint, hy, hxy⟩⟩
    obtain ⟨intersectionPoint, hu, rfl⟩ := (pushout_inl_eq_inr_iff f g firstPoint
      secondPoint).mp hxy.symm
    exact ⟨firstPoint, ⟨hx, ⟨intersectionPoint, hy, hu⟩⟩, rfl⟩
  · rintro - ⟨firstPoint, ⟨hx, ⟨intersectionPoint, hu, rfl⟩⟩, rfl⟩
    exact ⟨⟨f intersectionPoint, hx, rfl⟩, ⟨g intersectionPoint, hu,
      ((pushout_inl_eq_inr_iff f g _ _).mpr ⟨intersectionPoint, rfl, rfl⟩).symm⟩⟩

/-- **The pushout of two quasi-separated schemes along a quasi-compact common open is
quasi-separated.** -/
lemma quasiSeparatedSpace_pushout [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    [CompactSpace U] : QuasiSeparatedSpace ↑(pushout f g) := by
  have hgc : IsCompact (Set.range g) := isCompact_range g.continuous
  -- Intersections of compact open charts remain compact through the overlap.
  have key : ∀ (firstSubset : Set X) (secondSubset : Set Y), IsOpen firstSubset →
    IsCompact firstSubset → IsOpen secondSubset → IsCompact secondSubset →
      IsCompact ((pushout.inl f g '' firstSubset) ∩ (pushout.inr f g ''
        secondSubset)) := by
    intro firstSubset secondSubset hAo hAc hBo hBc
    rw [image_inl_inter_image_inr]
    refine IsCompact.image ?_ (pushout.inl f g).continuous
    have preimage_compact : IsCompact (g ⁻¹' secondSubset) := by
      have he : g ⁻¹' secondSubset = g ⁻¹' (secondSubset ∩ Set.range g) := by
        rw [Set.preimage_inter, Set.preimage_range, Set.inter_univ]
      rw [he]
      exact g.isOpenEmbedding.isInducing.isCompact_preimage'
        (hBc.inter_of_isOpen hgc hBo g.isOpenEmbedding.isOpen_range) Set.inter_subset_right
    exact hAc.inter_of_isOpen (preimage_compact.image f.continuous) hAo
      (f.isOpenEmbedding.isOpenMap _ (hBo.preimage g.continuous))
  -- Compact open charts from either piece form a basis of the glued scheme.
  refine QuasiSeparatedSpace.of_isTopologicalBasis
    (b := fun chartIndex : {firstSubset : X.Opens // IsCompact (firstSubset : Set X)}
      ⊕
      {secondSubset : Y.Opens // IsCompact (secondSubset : Set Y)} ↦
      match chartIndex with
      | Sum.inl firstSubset => pushout.inl f g '' (firstSubset.1 : Set X)
      | Sum.inr secondSubset => pushout.inr f g '' (secondSubset.1 : Set Y))
    ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro - ⟨(⟨firstSubset, hA⟩ | ⟨secondSubset, hB⟩), rfl⟩
      · exact (pushout.inl f g).isOpenEmbedding.isOpenMap _ firstSubset.2
      · exact (pushout.inr f g).isOpenEmbedding.isOpenMap _ secondSubset.2
    · intro gluedPoint neighborhood hp hO
      have hcov : gluedPoint ∈ Set.range (pushout.inl f g) ∪ Set.range (pushout.inr
        f g) := by
        rw [range_pushout_inl_union_range_pushout_inr f g]; trivial
      obtain (⟨firstPoint, rfl⟩ | ⟨secondPoint, rfl⟩) := hcov
      · have hmem : firstPoint ∈ (⟨_, hO.preimage (pushout.inl f g).continuous⟩ :
        X.Opens) := hp
        obtain ⟨A₀, hA₀, hxA, hAO⟩ :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hmem
        exact ⟨_, ⟨Sum.inl ⟨A₀, hA₀.isCompact⟩, rfl⟩, ⟨firstPoint, hxA, rfl⟩,
          Set.image_subset_iff.mpr hAO⟩
      · have hmem : secondPoint ∈ (⟨_, hO.preimage (pushout.inr f g).continuous⟩ :
        Y.Opens) := hp
        obtain ⟨B₀, hB₀, hyB, hBO⟩ :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hmem
        exact ⟨_, ⟨Sum.inr ⟨B₀, hB₀.isCompact⟩, rfl⟩, ⟨secondPoint, hyB, rfl⟩,
          Set.image_subset_iff.mpr hBO⟩
  -- Check intersections for the four combinations of chart origins.
  · rintro (⟨firstSubset, hA⟩ | ⟨secondSubset, hB⟩) (⟨otherFirstOpen, hA'⟩ | ⟨otherSecondOpen, hB'⟩)
    · rw [← Set.image_inter (pushout.inl f g).isOpenEmbedding.injective]
      exact (hA.inter_of_isOpen hA' firstSubset.2 otherFirstOpen.2).image (pushout.inl f
        g).continuous
    · exact key _ _ firstSubset.2 hA otherSecondOpen.2 hB'
    · rw [Set.inter_comm]
      exact key _ _ otherFirstOpen.2 hA' secondSubset.2 hB
    · rw [← Set.image_inter (pushout.inr f g).isOpenEmbedding.injective]
      exact (hB.inter_of_isOpen hB' secondSubset.2 otherSecondOpen.2).image (pushout.inr f
        g).continuous

end QuasiSeparated

section TwoOpens

variable {S : Scheme.{u}} (V W : S.Opens)

/-- The morphism from the pushout of two opens of `S` along their intersection to
  `S`. -/
def pushoutOpensDesc :
    pushout ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
      ((S.homOfLE (inf_le_right : V ⊓ W ≤ W))) ⟶ S :=
  pushout.desc V.ι W.ι (by simp)

@[reassoc (attr := simp)]
lemma inl_pushoutOpensDesc :
    pushout.inl ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
      ((S.homOfLE (inf_le_right : V ⊓ W ≤ W))) ≫
      pushoutOpensDesc V W = V.ι :=
  pushout.inl_desc ..

@[reassoc (attr := simp)]
lemma inr_pushoutOpensDesc :
    pushout.inr ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
      ((S.homOfLE (inf_le_right : V ⊓ W ≤ W))) ≫
      pushoutOpensDesc V W = W.ι :=
  pushout.inr_desc ..

lemma preimage_opensRange_inl_pushoutOpensDesc :
    pushoutOpensDesc V W ⁻¹ᵁ V.ι.opensRange =
      (pushout.inl ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
        ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))).opensRange := by
  apply le_antisymm
  · intro gluedPoint hx
    have hcov : gluedPoint ∈ (pushout.inl ((S.homOfLE (inf_le_left : V ⊓ W ≤
      V)))
        ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))).opensRange ⊔
        (pushout.inr ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
          ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))).opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (hmem | ⟨secondPoint, rfl⟩) := hcov
    · exact hmem
    · replace hx : (pushout.inr ((S.homOfLE (inf_le_left : V ⊓ W ≤
      V))) ((S.homOfLE (inf_le_right : V ⊓ W ≤ W))) ≫
          pushoutOpensDesc V W) secondPoint ∈ V.ι.opensRange := hx
      rw [inr_pushoutOpensDesc] at hx
      obtain ⟨firstPoint, hu⟩ := hx
      -- Express chart membership through the composite morphism.
      change secondPoint ∈ pushout.inr ((S.homOfLE (inf_le_left : V ⊓ W ≤
        V))) ((S.homOfLE (inf_le_right : V ⊓ W ≤ W))) ⁻¹ᵁ
        (pushout.inl ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
          ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))).opensRange
      rw [preimage_opensRange_pushout_inl, Scheme.opensRange_homOfLE]
      exact ⟨show W.ι secondPoint ∈ V from hu ▸ firstPoint.2, secondPoint.2⟩
  · rintro gluedPoint ⟨firstPoint, rfl⟩
    -- Express chart membership through the composite morphism.
    change (pushout.inl ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
      ((S.homOfLE (inf_le_right : V ⊓ W ≤ W))) ≫
      pushoutOpensDesc V W) firstPoint ∈ V.ι.opensRange
    rw [inl_pushoutOpensDesc]
    exact ⟨firstPoint, rfl⟩

lemma preimage_opensRange_inr_pushoutOpensDesc :
    pushoutOpensDesc V W ⁻¹ᵁ W.ι.opensRange =
      (pushout.inr ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
        ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))).opensRange := by
  apply le_antisymm
  · intro gluedPoint hx
    have hcov : gluedPoint ∈ (pushout.inl ((S.homOfLE (inf_le_left : V ⊓ W ≤
      V)))
        ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))).opensRange ⊔
        (pushout.inr ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
          ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))).opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (⟨firstPoint, rfl⟩ | hmem) := hcov
    · replace hx : (pushout.inl ((S.homOfLE (inf_le_left : V ⊓ W ≤
      V))) ((S.homOfLE (inf_le_right : V ⊓ W ≤ W))) ≫
          pushoutOpensDesc V W) firstPoint ∈ W.ι.opensRange := hx
      rw [inl_pushoutOpensDesc] at hx
      obtain ⟨secondPoint, hv⟩ := hx
      -- Express chart membership through the composite morphism.
      change firstPoint ∈ pushout.inl ((S.homOfLE (inf_le_left : V ⊓ W ≤
        V))) ((S.homOfLE (inf_le_right : V ⊓ W ≤ W))) ⁻¹ᵁ
        (pushout.inr ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
          ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))).opensRange
      rw [preimage_opensRange_pushout_inr, Scheme.opensRange_homOfLE]
      exact ⟨firstPoint.2, show V.ι firstPoint ∈ W from hv ▸ secondPoint.2⟩
    · exact hmem
  · rintro gluedPoint ⟨secondPoint, rfl⟩
    -- Express chart membership through the composite morphism.
    change (pushout.inr ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
      ((S.homOfLE (inf_le_right : V ⊓ W ≤ W))) ≫
      pushoutOpensDesc V W) secondPoint ∈ W.ι.opensRange
    rw [inr_pushoutOpensDesc]
    exact ⟨secondPoint, rfl⟩

/-- The first chart of the pushout presentation of a two-open cover is cartesian. -/
lemma isPullback_inl_pushoutOpensDesc :
    IsPullback (𝟙 V.toScheme)
      (pushout.inl ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
        ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))) V.ι
      (pushoutOpensDesc V W) :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp) (preimage_opensRange_inl_pushoutOpensDesc V
    W)

/-- The second chart of the pushout presentation of a two-open cover is cartesian. -/
lemma isPullback_inr_pushoutOpensDesc :
    IsPullback (𝟙 W.toScheme)
      (pushout.inr ((S.homOfLE (inf_le_left : V ⊓ W ≤ V)))
        ((S.homOfLE (inf_le_right : V ⊓ W ≤ W)))) W.ι
      (pushoutOpensDesc V W) :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp) (preimage_opensRange_inr_pushoutOpensDesc V
    W)

/-- **A scheme covered by two open subschemes is the pushout of the two along their
intersection.** -/
lemma isIso_pushoutOpensDesc (hUV : V ⊔ W = ⊤) : IsIso (pushoutOpensDesc V
    W) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover
    (S.openCoverOfIsOpenCover (fun chartIndex : Bool ↦ cond chartIndex V W)
      ?_) fun chartIndex ↦ ?_
  · change iSup _ = ⊤
    rw [iSup_bool_eq]
    exact hUV
  · rw [MorphismProperty.isomorphisms.iff]
    match chartIndex with
    | true =>
      -- Express chart membership through the composite morphism.
      change IsIso (pullback.snd (pushoutOpensDesc V W) V.ι)
      have square := (isPullback_inl_pushoutOpensDesc V W).flip
      have projection_eq : pullback.snd (pushoutOpensDesc V W) V.ι =
        square.isoPullback.inv := by
        rw [← Category.id_comp (pullback.snd (pushoutOpensDesc V W) V.ι),
          ← square.isoPullback.inv_hom_id, Category.assoc, IsPullback.isoPullback_hom_snd,
          Category.comp_id]
      rw [projection_eq]; infer_instance
    | false =>
      -- Express chart membership through the composite morphism.
      change IsIso (pullback.snd (pushoutOpensDesc V W) W.ι)
      have square := (isPullback_inr_pushoutOpensDesc V W).flip
      have projection_eq : pullback.snd (pushoutOpensDesc V W) W.ι =
        square.isoPullback.inv := by
        rw [← Category.id_comp (pullback.snd (pushoutOpensDesc V W) W.ι),
          ← square.isoPullback.inv_hom_id, Category.assoc, IsPullback.isoPullback_hom_snd,
          Category.comp_id]
      rw [projection_eq]; infer_instance

end TwoOpens

end AlgebraicGeometry.Scheme
