/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.CoarseSpace
public import TauCeti.Topology.CategoryTheory.Nerve.FullSubcategory

/-!
# Saturated open restrictions of classifying spaces

For a groupoid `C` with continuous source, let `P` be an isomorphism-invariant property of
objects. In every degree, the nerve of the full restriction to `P` is precisely the part
of the nerve whose coarse image lies in the image of `P`. If `P` is open, realization of
this inclusion is an open embedding, and its range is exactly the preimage of that coarse
subset. `CategoryTheory.ObjectProperty.fatClassifyingSpaceRestrictionHomeomorph` identifies
this preimage, with its subspace topology, with the fat classifying space of the restriction.

No properness, étaleness, effectiveness or continuity of composition is needed here.
This is an open-restriction theorem; it makes no assertion about realization of a closed
union of faces.

The realization argument uses the augmented open-subspace theorem in
`TauCeti.AlgebraicTopology.FatRealization`, as in the action-groupoid specialization
`TauCeti.Topology.CategoryTheory.ActionGroupoid.Restrict`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Section 3.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology

namespace CategoryTheory.ObjectProperty

universe u

variable {C : Type u} [Category.{u} C] [IsGroupoid C]
  [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The restricted nerve is exactly the part over the image of the saturated object set
in the coarse space, in each degree. -/
theorem range_topologicalNerveMap_ι (m : SemiSimplexCategoryᵒᵖ) :
    range ((TauCeti.topologicalNerveMap P.ι P.continuous_mapTotal_ι).app
      (SemiSimplexCategory.toSimplexCategory.op.obj m)) =
      (TauCeti.fatClassifyingSpace.coarseAugmentation hs).app m ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) := by
  rw [TauCeti.coe_topologicalNerveMap_app]
  refine (P.range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms _).trans ?_
  ext F
  constructor
  · intro hF
    exact ⟨F.obj 0, hF,
      (TauCeti.fatClassifyingSpace.coarseAugmentation_app_apply hs m F).symm⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨e⟩ := Quotient.exact
      (h.trans (TauCeti.fatClassifyingSpace.coarseAugmentation_app_apply hs m F))
    exact P.prop_of_iso e hx

include hs in
/-- The inclusion of a saturated open full subgroupoid induces an open embedding on fat
classifying spaces. All isotropy arrows are retained. -/
theorem isOpenEmbedding_fatClassifyingSpaceMap_ι (hP : IsOpen {x | P x}) :
    IsOpenEmbedding (TauCeti.fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [TauCeti.fatClassifyingSpaceMap_eq]
  apply TauCeti.fatRealization.isOpenEmbedding_map_of_range_eq_preimage
    (TauCeti.fatClassifyingSpace.coarseAugmentation hs)
    (V := Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
  · intro m
    dsimp only [Functor.whiskerLeft_app]
    rw [TauCeti.coe_topologicalNerveMap_app]
    exact P.isOpenEmbedding_mapComposableArrows_ι hs hP _
  · exact P.range_topologicalNerveMap_ι hs

/-- The preimage of a saturated coarse subset is the image of the fat classifying space
of its full restriction. Openness is needed for the subspace comparison, not this equality. -/
theorem preimage_coarseMap_eq_range_fatClassifyingSpaceMap_ι :
    TauCeti.fatClassifyingSpace.coarseMap hs ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) =
      range (TauCeti.fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [TauCeti.fatClassifyingSpace.coarseMap_eq_augment,
    TauCeti.fatClassifyingSpaceMap_eq]
  exact TauCeti.fatRealization.preimage_augment_eq_range_map _
    (P.range_topologicalNerveMap_ι hs)

/-- The fat classifying space of a saturated open restriction is homeomorphic to the
actual coarse-map preimage, with its subspace topology. -/
def fatClassifyingSpaceRestrictionHomeomorph (hP : IsOpen {x | P x}) :
    TauCeti.fatClassifyingSpace P.FullSubcategory ≃ₜ
      (TauCeti.fatClassifyingSpace.coarseMap hs ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  (P.isOpenEmbedding_fatClassifyingSpaceMap_ι hs hP).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_coarseMap_eq_range_fatClassifyingSpaceMap_ι hs).symm)

/-- The restriction homeomorphism is induced by the original inclusion functor. -/
-- Rewrite before simplification normalizes the dependent TopCat carriers.
@[simp↓]
theorem fatClassifyingSpaceRestrictionHomeomorph_apply_val (hP : IsOpen {x | P x})
    (z : TauCeti.fatClassifyingSpace P.FullSubcategory) :
    (P.fatClassifyingSpaceRestrictionHomeomorph hs hP z).val =
      TauCeti.fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

/-- Mapping the inverse restriction homeomorphism back by inclusion recovers the given
point of the coarse-map preimage. -/
-- The classifying-space map also has dependent TopCat carriers.
@[simp↓]
theorem fatClassifyingSpaceMap_ι_fatClassifyingSpaceRestrictionHomeomorph_symm_apply
    (hP : IsOpen {x | P x})
    (z : TauCeti.fatClassifyingSpace.coarseMap hs ⁻¹'
      (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    TauCeti.fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.fatClassifyingSpaceRestrictionHomeomorph hs hP).symm z) = z.val :=
  congrArg Subtype.val ((P.fatClassifyingSpaceRestrictionHomeomorph hs hP).apply_symm_apply z)

end CategoryTheory.ObjectProperty
