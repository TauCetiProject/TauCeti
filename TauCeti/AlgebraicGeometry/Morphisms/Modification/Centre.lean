/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The centre of a modification

For a morphism of schemes `f : X ⟶ Y`, being an isomorphism over an open of `Y` is local on `Y`,
so there is a largest open `isoLocus f` of `Y` over which `f` is an isomorphism: the union of all
opens `U` with `f ∣_ U` an isomorphism. Its closed complement `centre f` is the set of points of
`Y` over which `f` fails to be an isomorphism. For a modification the iso locus contains the dense
open of the definition, so it is dense and the centre is nowhere dense.

## Main definitions

* `TauCeti.AlgebraicGeometry.isoLocus f`: the largest open of `Y` over which `f` is an
  isomorphism.
* `TauCeti.AlgebraicGeometry.centre f`: its complement, a closed subset of `Y`.

## Main results

* `TauCeti.AlgebraicGeometry.isIso_morphismRestrict_iSup`: an isomorphism over each of a family of
  opens is an isomorphism over their union.
* `TauCeti.AlgebraicGeometry.le_isoLocus_iff`: an open lies in the iso locus exactly when `f` is
  an isomorphism over it.
* `TauCeti.AlgebraicGeometry.isIso_morphismRestrict_isoLocus`: `f` is an isomorphism over its
  iso locus, that is, over the complement of its centre.
* `TauCeti.AlgebraicGeometry.isClosed_centre`: the centre is closed.
* `TauCeti.AlgebraicGeometry.IsModification.dense_isoLocus` and
  `TauCeti.AlgebraicGeometry.IsModification.isNowhereDense_centre`: for a modification, the iso
  locus is dense and the centre is nowhere dense.
* `TauCeti.AlgebraicGeometry.centre_eq_empty_iff`: the centre is empty exactly when `f` is an
  isomorphism.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A morphism that is an isomorphism over each of a family of opens is an isomorphism over their
union. -/
theorem isIso_morphismRestrict_iSup (f : X ⟶ Y) {ι : Type*} (U : ι → Y.Opens)
    (H : ∀ i, IsIso (f ∣_ U i)) : IsIso (f ∣_ iSup U) := by
  let W := iSup U
  -- Cover `W` by the preimages of the `U i` under its inclusion.
  have hU : iSup (fun i ↦ W.ι ⁻¹ᵁ U i) = ⊤ := by
    refine W.ι.image_injective ?_
    simp only [Scheme.Hom.image_iSup, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Opens.opensRange_ι, Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact iSup_congr fun i ↦ inf_eq_right.mpr (le_iSup U i)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ hU
    fun i ↦ ?_
  have he : W.ι ''ᵁ (W.ι ⁻¹ᵁ U i) = U i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (le_iSup U i)
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f W _ ≪≫ morphismRestrictEq f he)).mpr (H i)

/-- A morphism that is an isomorphism over an open is an isomorphism over every smaller open. -/
theorem isIso_morphismRestrict_of_le (f : X ⟶ Y) {U V : Y.Opens} (hUV : U ≤ V)
    [IsIso (f ∣_ V)] : IsIso (f ∣_ U) := by
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hUV
  have : IsIso (f ∣_ V ∣_ (V.ι ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
      (inferInstanceAs (IsIso (f ∣_ V))) _
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V _ ≪≫ morphismRestrictEq f he)).mp this

/-- The *iso locus* of `f : X ⟶ Y`: the largest open of `Y` over which `f` is an isomorphism. -/
def isoLocus (f : X ⟶ Y) : Y.Opens :=
  ⨆ U : {U : Y.Opens // IsIso (f ∣_ U)}, U.1

/-- `f` is an isomorphism over its iso locus. -/
instance isIso_morphismRestrict_isoLocus (f : X ⟶ Y) : IsIso (f ∣_ isoLocus f) :=
  isIso_morphismRestrict_iSup f _ fun U ↦ U.2

/-- An open lies in the iso locus of `f` exactly when `f` is an isomorphism over it. -/
theorem le_isoLocus_iff (f : X ⟶ Y) {U : Y.Opens} : U ≤ isoLocus f ↔ IsIso (f ∣_ U) :=
  ⟨fun h ↦ isIso_morphismRestrict_of_le f h, fun h ↦ le_iSup_of_le ⟨U, h⟩ le_rfl⟩

/-- The iso locus of `f` is the whole target exactly when `f` is an isomorphism. -/
theorem isoLocus_eq_top_iff (f : X ⟶ Y) : isoLocus f = ⊤ ↔ IsIso f := by
  rw [eq_top_iff, le_isoLocus_iff]
  have h := IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (f := f) (fun _ : Unit ↦ ⊤) (by simp)
  exact ⟨fun hf ↦ h.mpr fun _ ↦ hf, fun hf ↦ h.mp hf ()⟩

/-- The *centre* of `f : X ⟶ Y`: the closed set of points of `Y` over which `f` is not an
isomorphism, the complement of `isoLocus f`. -/
def centre (f : X ⟶ Y) : Set Y :=
  (isoLocus f : Set Y)ᶜ

/-- The centre of a morphism is closed. -/
theorem isClosed_centre (f : X ⟶ Y) : IsClosed (centre f) :=
  (isoLocus f).isOpen.isClosed_compl

/-- `f` is an isomorphism over the complement of its centre. -/
theorem compl_centre (f : X ⟶ Y) : (centre f)ᶜ = isoLocus f :=
  compl_compl _

/-- An open avoids the centre of `f` exactly when `f` is an isomorphism over it. -/
theorem disjoint_centre_iff (f : X ⟶ Y) {U : Y.Opens} :
    Disjoint (U : Set Y) (centre f) ↔ IsIso (f ∣_ U) := by
  rw [centre, Set.disjoint_compl_right_iff_subset, ← le_isoLocus_iff]
  rfl

/-- The centre of `f` is empty exactly when `f` is an isomorphism. -/
theorem centre_eq_empty_iff (f : X ⟶ Y) : centre f = ∅ ↔ IsIso f := by
  rw [← isoLocus_eq_top_iff, centre, Set.compl_empty_iff, ← TopologicalSpace.Opens.coe_top,
    SetLike.coe_set_eq]

namespace IsModification

/-- The iso locus of a modification is dense. -/
theorem dense_isoLocus (f : X ⟶ Y) [IsModification f] : Dense (isoLocus f : Set Y) := by
  obtain ⟨U, hU, -, hf⟩ := exists_isIso_morphismRestrict (f := f)
  exact hU.mono ((le_isoLocus_iff f).mpr hf)

/-- The centre of a modification is nowhere dense: it is closed, and `f` is an isomorphism over
its dense complement. -/
theorem isNowhereDense_centre (f : X ⟶ Y) [IsModification f] : IsNowhereDense (centre f) := by
  rw [(isClosed_centre f).isNowhereDense_iff, interior_eq_empty_iff_dense_compl, compl_centre]
  exact dense_isoLocus f

end IsModification

end TauCeti.AlgebraicGeometry
