/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Morphisms.OpenImmersion
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

variable {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y)
  [IsOpenImmersion f] [IsOpenImmersion g]

instance [CompactSpace X] [CompactSpace Y] : CompactSpace ↑(pushout f g) := by
  constructor
  rw [← range_pushout_inl_union_range_pushout_inr f g]
  exact (isCompact_range (pushout.inl f g).continuous).union
    (isCompact_range (pushout.inr f g).continuous)

section PointsAndMap


/-- Points from the two charts agree in the pushout iff they come from a common overlap point. -/
@[simp]
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

/-- The two pushout charts cover the pushout. -/
@[simp]
lemma opensRange_pushout_inl_sup_opensRange_pushout_inr :
    (pushout.inl f g).opensRange ⊔ (pushout.inr f g).opensRange = ⊤ := by
  rw [eq_top_iff]
  rintro firstPoint -
  rw [TopologicalSpace.Opens.mem_sup]
  exact Set.eq_univ_iff_forall.mp (range_pushout_inl_union_range_pushout_inr f g)
    firstPoint

/-- The second chart meets the first chart in the image of the overlap immersion `g`. -/
@[simp]
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

/-- The first chart meets the second chart in the image of the overlap immersion `f`. -/
@[simp]
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

/-- The overlap image in the second chart lies in the first chart's range. -/
lemma image_pushout_inr_opensRange_le :
    pushout.inr f g ''ᵁ g.opensRange ≤ (pushout.inl f g).opensRange := by
  rw [← preimage_opensRange_pushout_inl f g]
  exact (pushout.inr f g).image_preimage_le _

/-- The overlap image in the first chart lies in the second chart's range. -/
lemma image_pushout_inl_opensRange_le :
    pushout.inl f g ''ᵁ f.opensRange ≤ (pushout.inr f g).opensRange := by
  rw [← preimage_opensRange_pushout_inr f g]
  exact (pushout.inl f g).image_preimage_le _

/-- The preimage under a pushout descent map is the union of its preimages on the charts. -/
lemma preimage_pushout_desc {S : Scheme.{u}} (α : X ⟶ S) (β : Y ⟶ S)
    (h : f ≫ α = g ≫ β) (V : S.Opens) :
    pushout.desc α β h ⁻¹ᵁ V =
      pushout.inl f g ''ᵁ (α ⁻¹ᵁ V) ⊔ pushout.inr f g ''ᵁ (β ⁻¹ᵁ V) := by
  symm
  calc
    _ = pushout.inl f g ''ᵁ ((pushout.inl f g ≫ pushout.desc α β h) ⁻¹ᵁ V) ⊔
        pushout.inr f g ''ᵁ ((pushout.inr f g ≫ pushout.desc α β h) ⁻¹ᵁ V) := by
      rw [pushout.inl_desc, pushout.inr_desc]
    _ = (pushout.inl f g).opensRange ⊓ (pushout.desc α β h ⁻¹ᵁ V) ⊔
        (pushout.inr f g).opensRange ⊓ (pushout.desc α β h ⁻¹ᵁ V) := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
        Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Hom.image_preimage_eq_opensRange_inf]
    _ = _ := by rw [← inf_sup_right, opensRange_pushout_inl_sup_opensRange_pushout_inr, top_inf_eq]

variable {U' X' Y' : Scheme.{u}} (f' : U' ⟶ X') (g' : U' ⟶ Y')
  [IsOpenImmersion f'] [IsOpenImmersion g']
  (a : X' ⟶ X) (b : Y' ⟶ Y) (c : U' ⟶ U)
  (hf : c ≫ f = f' ≫ a) (hg : c ≫ g = g' ≫ b)

include hf hg in
/-- A cartesian overlap square makes the first chart pull back to the first chart. -/
@[simp]
lemma preimage_opensRange_pushout_inl_of_isPullback (square : IsPullback c g' g b) :
    pushout.map f' g' f g a b c hf.symm hg.symm ⁻¹ᵁ (pushout.inl f g).opensRange =
      (pushout.inl f' g').opensRange := by
  have overlap : b ⁻¹ᵁ g.opensRange = g'.opensRange := preimage_opensRange_of_isPullback square
  rw [pushout.map, preimage_pushout_desc]
  simp only [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange,
    Scheme.Hom.preimage_top, preimage_opensRange_pushout_inl, overlap,
    Scheme.Hom.image_top_eq_opensRange]
  exact sup_eq_left.mpr (image_pushout_inr_opensRange_le f' g')

include hf hg in
/-- A cartesian overlap square makes the first chart square of the pushout map cartesian. -/
lemma isPullback_pushout_map_inl_of_isPullback (square : IsPullback c g' g b) :
    IsPullback a (pushout.inl f' g') (pushout.inl f g)
      (pushout.map f' g' f g a b c hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inl_desc _ _ _)
    (preimage_opensRange_pushout_inl_of_isPullback f g f' g' a b c hf hg square)

include hf hg in
/-- A cartesian overlap square makes the second chart pull back to the second chart. -/
@[simp]
lemma preimage_opensRange_pushout_inr_of_isPullback (square : IsPullback c f' f a) :
    pushout.map f' g' f g a b c hf.symm hg.symm ⁻¹ᵁ (pushout.inr f g).opensRange =
      (pushout.inr f' g').opensRange := by
  have overlap : a ⁻¹ᵁ f.opensRange = f'.opensRange := preimage_opensRange_of_isPullback square
  rw [pushout.map, preimage_pushout_desc]
  simp only [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange,
    Scheme.Hom.preimage_top, preimage_opensRange_pushout_inr, overlap,
    Scheme.Hom.image_top_eq_opensRange]
  exact sup_eq_right.mpr (image_pushout_inl_opensRange_le f' g')

include hf hg in
/-- A cartesian overlap square makes the second chart square of the pushout map cartesian. -/
lemma isPullback_pushout_map_inr_of_isPullback (square : IsPullback c f' f a) :
    IsPullback b (pushout.inr f' g') (pushout.inr f g)
      (pushout.map f' g' f g a b c hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inr_desc _ _ _)
    (preimage_opensRange_pushout_inr_of_isPullback f g f' g' a b c hf hg square)

end PointsAndMap

section QuasiSeparated

/-- The intersection of chart images is the image of their intersection through the overlap. -/
lemma image_pushout_inl_inter_image_pushout_inr (firstSubset : Set X) (secondSubset : Set Y) :
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

/-- Images of compact opens in the two charts have compact intersection when the overlap
immersion into the second chart is quasi-compact. -/
lemma isCompact_image_pushout_inl_inter_image_pushout_inr [QuasiSeparatedSpace X]
    [QuasiCompact g] {A : Set X} {B : Set Y} (hAo : IsOpen A) (hAc : IsCompact A)
    (hBo : IsOpen B) (hBc : IsCompact B) :
    IsCompact ((pushout.inl f g '' A) ∩ (pushout.inr f g '' B)) := by
  rw [image_pushout_inl_inter_image_pushout_inr]
  refine IsCompact.image ?_ (pushout.inl f g).continuous
  exact hAc.inter_of_isOpen
    ((QuasiCompact.isCompact_preimage (f := g) B hBo hBc).image f.continuous) hAo
    (f.isOpenEmbedding.isOpenMap _ (hBo.preimage g.continuous))

/-- Gluing quasi-separated schemes along a quasi-compact open immersion preserves
quasi-separatedness. -/
instance quasiSeparatedSpace_pushout [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    [QuasiCompact g] : QuasiSeparatedSpace ↑(pushout f g) := by
  let chart : X.affineOpens ⊕ Y.affineOpens → (pushout f g).Opens
    | .inl A => pushout.inl f g ''ᵁ A.1
    | .inr B => pushout.inr f g ''ᵁ B.1
  refine Scheme.quasiSeparatedSpace_of_isOpenCover chart ?_ ?_ ?_
  · apply TopologicalSpace.IsOpenCover.mk
    rw [iSup_sum]
    simp only [← Scheme.Hom.image_iSup, iSup_affineOpens_eq_top,
      Scheme.Hom.image_top_eq_opensRange, opensRange_pushout_inl_sup_opensRange_pushout_inr]
  · rintro (A | B)
    · exact A.2.image_of_isOpenImmersion _
    · exact B.2.image_of_isOpenImmersion _
  · rintro (A | B) (A' | B') <;> simp only [chart, Scheme.Hom.coe_image]
    · rw [← Set.image_inter (pushout.inl f g).isOpenEmbedding.injective]
      exact (A.2.isCompact.inter_of_isOpen A'.2.isCompact A.1.2 A'.1.2).image
        (pushout.inl f g).continuous
    · exact isCompact_image_pushout_inl_inter_image_pushout_inr f g
        A.1.2 A.2.isCompact B'.1.2 B'.2.isCompact
    · rw [Set.inter_comm]
      exact isCompact_image_pushout_inl_inter_image_pushout_inr f g
        A'.1.2 A'.2.isCompact B.1.2 B.2.isCompact
    · rw [← Set.image_inter (pushout.inr f g).isOpenEmbedding.injective]
      exact (B.2.isCompact.inter_of_isOpen B'.2.isCompact B.1.2 B'.1.2).image
        (pushout.inr f g).continuous

end QuasiSeparated

section CartesianDesc

variable {S : Scheme.{u}} (α : X ⟶ S) (β : Y ⟶ S)
  [IsOpenImmersion α] [IsOpenImmersion β] (h : IsPullback f g α β)

omit [IsOpenImmersion β] in
/-- The first chart of a cartesian open span pulls back to the first pushout chart. -/
@[simp]
lemma preimage_opensRange_pushout_desc_inl :
    pushout.desc α β h.w ⁻¹ᵁ α.opensRange = (pushout.inl f g).opensRange := by
  have overlap : β ⁻¹ᵁ α.opensRange = g.opensRange := preimage_opensRange_of_isPullback h
  rw [preimage_pushout_desc, Scheme.Hom.preimage_opensRange, overlap,
    Scheme.Hom.image_top_eq_opensRange]
  exact sup_eq_left.mpr (image_pushout_inr_opensRange_le f g)

omit [IsOpenImmersion α] in
/-- The second chart of a cartesian open span pulls back to the second pushout chart. -/
@[simp]
lemma preimage_opensRange_pushout_desc_inr :
    pushout.desc α β h.w ⁻¹ᵁ β.opensRange = (pushout.inr f g).opensRange := by
  have overlap : α ⁻¹ᵁ β.opensRange = f.opensRange := preimage_opensRange_of_isPullback h.flip
  rw [preimage_pushout_desc, Scheme.Hom.preimage_opensRange, overlap,
    Scheme.Hom.image_top_eq_opensRange]
  exact sup_eq_right.mpr (image_pushout_inl_opensRange_le f g)

omit [IsOpenImmersion β] in
/-- The first chart square of descent from a cartesian open span is cartesian. -/
lemma isPullback_pushout_desc_inl :
    IsPullback (𝟙 X) (pushout.inl f g) α (pushout.desc α β h.w) :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp)
    (preimage_opensRange_pushout_desc_inl f g α β h)

omit [IsOpenImmersion α] in
/-- The second chart square of descent from a cartesian open span is cartesian. -/
lemma isPullback_pushout_desc_inr :
    IsPullback (𝟙 Y) (pushout.inr f g) β (pushout.desc α β h.w) :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp)
    (preimage_opensRange_pushout_desc_inr f g α β h)

/-- Descent from a cartesian span of open immersions is an open immersion. -/
lemma isOpenImmersion_pushout_desc :
    IsOpenImmersion (pushout.desc α β h.w : pushout f g ⟶ S) := by
  have cover (x : ↑(pushout f g)) :
      x ∈ Set.range (pushout.inl f g) ∨ x ∈ Set.range (pushout.inr f g) := by
    rw [← Set.mem_union, range_pushout_inl_union_range_pushout_inr]
    trivial
  apply IsOpenImmersion.of_forall_source_exists
  · intro x y hxy
    rcases cover x with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      rcases cover y with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · apply congrArg (pushout.inl f g)
      apply α.isOpenEmbedding.injective
      simpa only [← Scheme.Hom.comp_apply, pushout.inl_desc] using hxy
    · have heq : α x = β y := by
        simpa only [← Scheme.Hom.comp_apply, pushout.inl_desc, pushout.inr_desc] using hxy
      obtain ⟨z, hz, hz'⟩ := exists_preimage_of_isPullback h x y heq
      exact (pushout_inl_eq_inr_iff f g x y).mpr ⟨z, hz, hz'⟩
    · have heq : α y = β x := by
        simpa only [← Scheme.Hom.comp_apply, pushout.inl_desc, pushout.inr_desc] using hxy.symm
      obtain ⟨z, hz, hz'⟩ := exists_preimage_of_isPullback h y x heq
      exact ((pushout_inl_eq_inr_iff f g y x).mpr ⟨z, hz, hz'⟩).symm
    · apply congrArg (pushout.inr f g)
      apply β.isOpenEmbedding.injective
      simpa only [← Scheme.Hom.comp_apply, pushout.inr_desc] using hxy
  · intro x
    rcases cover x with hx | hx
    · refine ⟨X, pushout.inl f g, inferInstance, hx, ?_⟩
      simpa only [pushout.inl_desc] using (inferInstance : IsOpenImmersion α)
    · refine ⟨Y, pushout.inr f g, inferInstance, hx, ?_⟩
      simpa only [pushout.inr_desc] using (inferInstance : IsOpenImmersion β)

omit [IsOpenImmersion α] [IsOpenImmersion β] in
/-- Descent from an open span has the union of the chart ranges. -/
lemma range_pushout_desc (comm : f ≫ α = g ≫ β) :
    Set.range (pushout.desc α β comm) = Set.range α ∪ Set.range β := by
  calc
    _ = pushout.desc α β comm ''
        (Set.range (pushout.inl f g) ∪ Set.range (pushout.inr f g)) := by
      rw [range_pushout_inl_union_range_pushout_inr, Set.image_univ]
    _ = Set.range (pushout.inl f g ≫ pushout.desc α β comm) ∪
        Set.range (pushout.inr f g ≫ pushout.desc α β comm) := by
      rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
      simp only [Function.comp_def, ← Scheme.Hom.comp_apply]
    _ = _ := by rw [pushout.inl_desc, pushout.inr_desc]

/-- Descent from a covering cartesian open span is an isomorphism. -/
lemma isIso_pushout_desc (hcover : α.opensRange ⊔ β.opensRange = ⊤) :
    IsIso (pushout.desc α β h.w : pushout f g ⟶ S) := by
  have : IsOpenImmersion (pushout.desc α β h.w) := isOpenImmersion_pushout_desc f g α β h
  have hcover' : Set.range α ∪ Set.range β = Set.univ := by
    simpa only [TopologicalSpace.Opens.coe_sup, Scheme.Hom.coe_opensRange,
      TopologicalSpace.Opens.coe_top] using
      congrArg (fun U : S.Opens ↦ (U : Set S)) hcover
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top _
  apply TopologicalSpace.Opens.ext
  simpa only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top] using
    (range_pushout_desc f g α β h.w).trans hcover'

end CartesianDesc

section TwoOpens

variable {S : Scheme.{u}} (V W : S.Opens)

local notation "iV" => S.homOfLE (inf_le_left : V ⊓ W ≤ V)
local notation "iW" => S.homOfLE (inf_le_right : V ⊓ W ≤ W)

/-- The map from the pushout of two opens along their intersection to the ambient scheme. -/
def pushoutOpensDesc : pushout iV iW ⟶ S := pushout.desc V.ι W.ι (by simp)

@[reassoc (attr := simp)]
lemma inl_pushoutOpensDesc : pushout.inl iV iW ≫ pushoutOpensDesc V W = V.ι :=
  pushout.inl_desc ..

@[reassoc (attr := simp)]
lemma inr_pushoutOpensDesc : pushout.inr iV iW ≫ pushoutOpensDesc V W = W.ι :=
  pushout.inr_desc ..

/-- The preimage of the first open is the first pushout chart. -/
@[simp]
lemma preimage_pushoutOpensDesc_left :
    pushoutOpensDesc V W ⁻¹ᵁ V = (pushout.inl iV iW).opensRange := by
  simpa only [pushoutOpensDesc, Scheme.Opens.opensRange_ι] using
    preimage_opensRange_pushout_desc_inl iV iW V.ι W.ι (isPullback_opens_inf V W)

/-- The preimage of the second open is the second pushout chart. -/
@[simp]
lemma preimage_pushoutOpensDesc_right :
    pushoutOpensDesc V W ⁻¹ᵁ W = (pushout.inr iV iW).opensRange := by
  simpa only [pushoutOpensDesc, Scheme.Opens.opensRange_ι] using
    preimage_opensRange_pushout_desc_inr iV iW V.ι W.ι (isPullback_opens_inf V W)

/-- The first chart of the two-open pushout presentation is cartesian. -/
lemma isPullback_inl_pushoutOpensDesc :
    IsPullback (𝟙 V.toScheme) (pushout.inl iV iW) V.ι (pushoutOpensDesc V W) := by
  exact isPullback_pushout_desc_inl iV iW V.ι W.ι (isPullback_opens_inf V W)

/-- The second chart of the two-open pushout presentation is cartesian. -/
lemma isPullback_inr_pushoutOpensDesc :
    IsPullback (𝟙 W.toScheme) (pushout.inr iV iW) W.ι (pushoutOpensDesc V W) := by
  exact isPullback_pushout_desc_inr iV iW V.ι W.ι (isPullback_opens_inf V W)

/-- The pushout of two opens maps by an open immersion to the ambient scheme. -/
instance isOpenImmersion_pushoutOpensDesc : IsOpenImmersion (pushoutOpensDesc V W) := by
  unfold pushoutOpensDesc
  exact isOpenImmersion_pushout_desc iV iW V.ι W.ι (isPullback_opens_inf V W)

/-- The image of the pushout of two opens is their union. -/
@[simp]
lemma opensRange_pushoutOpensDesc : (pushoutOpensDesc V W).opensRange = V ⊔ W := by
  apply TopologicalSpace.Opens.ext
  simpa only [pushoutOpensDesc, Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_sup,
    Scheme.Opens.range_ι] using
    range_pushout_desc iV iW V.ι W.ι (isPullback_opens_inf V W).w

/-- A scheme covered by two opens is their pushout along the intersection. -/
lemma isIso_pushoutOpensDesc (hVW : V ⊔ W = ⊤) : IsIso (pushoutOpensDesc V W) :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _
    ((opensRange_pushoutOpensDesc V W).trans hVW)

end TwoOpens

end AlgebraicGeometry.Scheme
