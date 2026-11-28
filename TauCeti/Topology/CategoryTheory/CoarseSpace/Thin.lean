/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.CoarseSpace.Restrict
public import TauCeti.Topology.CategoryTheory.ThinClassifyingSpace
import TauCeti.Topology.Constructions.Basic

/-!
# Coarse-preimage comparisons of fat and thin classifying spaces

For a topological groupoid `C` with continuous source `Quiver.Total.left : Quiver.Total C → C`,
`TauCeti.thinClassifyingSpace.fatToThinClassifyingSpacePreimage` restricts
`TauCeti.fatToThinClassifyingSpace C` to the preimages of any subset `V` of the coarse quotient
`Quotient (isIsomorphicSetoid C)`. It is surjective for every subset `V` and a topological quotient
map whenever `V` is open or closed (`fatToThinClassifyingSpacePreimage_surjective`,
`isQuotientMap_fatToThinClassifyingSpacePreimage_of_isOpen`,
`isQuotientMap_fatToThinClassifyingSpacePreimage_of_isClosed`).

In `CategoryTheory.ObjectProperty`, the compatibility theorems
`thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace` and
`thinClassifyingSpaceRestrictionHomeomorph_symm_fatToThinClassifyingSpacePreimage`
identify `fatToThinClassifyingSpacePreimage` on saturated coarse preimages with
`TauCeti.fatToThinClassifyingSpace P.FullSubcategory` under the fat and thin embedding restriction
homeomorphisms (covering both open and closed saturated full subgroupoids).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* I. Moerdijk, *Classifying spaces and classifying topoi*, LNM **1616**, Springer, 1995.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Contemp. Math. **310** (2002), 205–222.
-/

public noncomputable section

open CategoryTheory Set Topology

universe u

namespace TauCeti

namespace thinClassifyingSpace

section CoarseSpace

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The preimage of `V` under `fatClassifyingSpace.coarseMap hs` equals its preimage under
`fatToThinClassifyingSpace C` followed by `thinClassifyingSpace.coarseMap hs`. -/
theorem preimage_fatClassifyingSpace_coarseMap_eq
    (V : Set (Quotient (isIsomorphicSetoid C))) :
    fatClassifyingSpace.coarseMap hs ⁻¹' V =
      fatToThinClassifyingSpace C ⁻¹' (coarseMap hs ⁻¹' V) := by
  rw [← Set.preimage_comp, ← TopCat.coe_comp, fatToThinClassifyingSpace_comp_coarseMap]

/-- The continuous map induced by `fatToThinClassifyingSpace C` on the preimages of a subset `V`
of the coarse quotient. -/
def fatToThinClassifyingSpacePreimage (V : Set (Quotient (isIsomorphicSetoid C))) :
    C(fatClassifyingSpace.coarseMap hs ⁻¹' V, coarseMap hs ⁻¹' V) :=
  ((fatToThinClassifyingSpace C).hom.restrictPreimage (coarseMap hs ⁻¹' V)).comp
    (Homeomorph.setCongr (preimage_fatClassifyingSpace_coarseMap_eq hs V) :
      C(fatClassifyingSpace.coarseMap hs ⁻¹' V,
        fatToThinClassifyingSpace C ⁻¹' (coarseMap hs ⁻¹' V)))

/-- Evaluating `fatToThinClassifyingSpacePreimage` on a subtype element applies
`fatToThinClassifyingSpace C` to its underlying point. -/
@[simp]
theorem fatToThinClassifyingSpacePreimage_apply_val
    (V : Set (Quotient (isIsomorphicSetoid C)))
    (z : fatClassifyingSpace.coarseMap hs ⁻¹' V) :
    (fatToThinClassifyingSpacePreimage hs V z).val = fatToThinClassifyingSpace C z.val := (rfl)

/-- For every subset `V` of the coarse quotient, `fatToThinClassifyingSpacePreimage hs V` is
surjective. -/
theorem fatToThinClassifyingSpacePreimage_surjective
    (V : Set (Quotient (isIsomorphicSetoid C))) :
    Function.Surjective (fatToThinClassifyingSpacePreimage hs V) :=
  ((fatToThinClassifyingSpace_surjective C).restrictPreimage _).comp
    (Homeomorph.setCongr _).surjective

/-- For an open subset `V` of the coarse quotient, `fatToThinClassifyingSpacePreimage hs V` is a
topological quotient map. -/
theorem isQuotientMap_fatToThinClassifyingSpacePreimage_of_isOpen
    {V : Set (Quotient (isIsomorphicSetoid C))} (hV : IsOpen V) :
    IsQuotientMap (fatToThinClassifyingSpacePreimage hs V) :=
  ((isQuotientMap_fatToThinClassifyingSpace C).restrictPreimage_isOpen
    (hV.preimage (coarseMap hs).hom.continuous)).comp
    (Homeomorph.setCongr _).isQuotientMap

/-- For a closed subset `V` of the coarse quotient, `fatToThinClassifyingSpacePreimage hs V` is a
topological quotient map. -/
theorem isQuotientMap_fatToThinClassifyingSpacePreimage_of_isClosed
    {V : Set (Quotient (isIsomorphicSetoid C))} (hV : IsClosed V) :
    IsQuotientMap (fatToThinClassifyingSpacePreimage hs V) :=
  Topology.IsQuotientMap.of_comp_eq_comp (isQuotientMap_fatToThinClassifyingSpace C)
    (fatToThinClassifyingSpacePreimage hs V).continuous
    (fatToThinClassifyingSpacePreimage_surjective hs V)
    ((hV.preimage (fatClassifyingSpace.coarseMap hs).hom.continuous)
      |>.isClosedEmbedding_subtypeVal.isClosedMap)
    continuous_subtypeVal Subtype.val_injective (funext fun _ ↦ rfl)
    fun z ⟨⟨y, hy⟩, hyz⟩ ↦
      ⟨⟨z, (preimage_fatClassifyingSpace_coarseMap_eq hs V).ge (by simpa [← hyz] using hy)⟩, rfl⟩

end CoarseSpace

end thinClassifyingSpace

end TauCeti

namespace CategoryTheory.ObjectProperty

open TauCeti

section SaturatedGroupoid

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The embedding restriction homeomorphisms identify the induced map on coarse preimages with the
fat-to-thin comparison for `P.FullSubcategory`. -/
theorem thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace
    (hfat : IsEmbedding (fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (hthin : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : fatClassifyingSpace P.FullSubcategory) :
    P.thinClassifyingSpaceRestrictionHomeomorph hs hthin
        (fatToThinClassifyingSpace P.FullSubcategory z) =
      thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
        (P.fatClassifyingSpaceRestrictionHomeomorph hs hfat z) := by
  ext
  rw [thinClassifyingSpaceRestrictionHomeomorph_apply_val,
    thinClassifyingSpace.fatToThinClassifyingSpacePreimage_apply_val,
    fatClassifyingSpaceRestrictionHomeomorph_apply_val]
  simpa only [TopCat.comp_app] using (ConcreteCategory.congr_hom
    (fatClassifyingSpaceMap_comp_fatToThinClassifyingSpace P.ι P.continuous_mapTotal_ι) z).symm

/-- Conjugating the induced map on coarse preimages by the embedding restriction homeomorphisms
recovers `fatToThinClassifyingSpace P.FullSubcategory`. -/
@[simp]
theorem thinClassifyingSpaceRestrictionHomeomorph_symm_fatToThinClassifyingSpacePreimage
    (hfat : IsEmbedding (fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (hthin : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : fatClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs hthin).symm
        (thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
          (P.fatClassifyingSpaceRestrictionHomeomorph hs hfat z)) =
      fatToThinClassifyingSpace P.FullSubcategory z :=
  ((P.thinClassifyingSpaceRestrictionHomeomorph hs hthin).symm_apply_eq).2
    (P.thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace
      hs hfat hthin z).symm

end SaturatedGroupoid

end CategoryTheory.ObjectProperty
