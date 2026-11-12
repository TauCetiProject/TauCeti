/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import TauCeti.AlgebraicGeometry.Restrict

/-!
# The iso locus and centre of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y`, being an isomorphism over an open of `Y` is local on `Y`,
so there is a largest open `f.isoLocus` of `Y` over which `f` is an isomorphism: the union of all
opens `U` with `f ∣_ U` an isomorphism. Its closed complement `f.centre` is the set of points of
`Y` over which `f` fails to be an isomorphism: a point lies in it exactly when `f` is an
isomorphism over none of its open neighbourhoods.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.isoLocus f`: the largest open of `Y` over which `f` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.Hom.centre f`: its complement, a closed subset of `Y`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_iSup`: an isomorphism over each of a
  family of opens is an isomorphism over their union.
* `AlgebraicGeometry.Scheme.Hom.le_isoLocus_iff`: an open lies in the iso locus exactly when `f`
  is an isomorphism over it.
* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_isoLocus`: `f` is an isomorphism over its
  iso locus, that is, over the complement of its centre.
* `AlgebraicGeometry.Scheme.Hom.mem_isoLocus_iff`, `AlgebraicGeometry.Scheme.Hom.mem_centre_iff`:
  the pointwise descriptions of the two loci.
* `AlgebraicGeometry.Scheme.Hom.isClosed_centre`: the centre is closed.
* `AlgebraicGeometry.Scheme.Hom.centre_eq_empty_iff`: the centre is empty exactly when `f` is an
  isomorphism.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

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

/-- The *iso locus* of `f : X ⟶ Y`: the largest open of `Y` over which `f` is an isomorphism. -/
def isoLocus (f : X ⟶ Y) : Y.Opens :=
  ⨆ U : {U : Y.Opens // IsIso (f ∣_ U)}, U.1

/-- The iso locus is the union of the opens over which `f` is an isomorphism. -/
theorem isoLocus_def (f : X ⟶ Y) :
    f.isoLocus = ⨆ U : {U : Y.Opens // IsIso (f ∣_ U)}, U.1 := by
  rw [isoLocus]

/-- `f` is an isomorphism over its iso locus. -/
instance isIso_morphismRestrict_isoLocus (f : X ⟶ Y) : IsIso (f ∣_ f.isoLocus) :=
  isIso_morphismRestrict_iSup f _ fun U ↦ U.2

/-- An open lies in the iso locus of `f` exactly when `f` is an isomorphism over it. -/
theorem le_isoLocus_iff (f : X ⟶ Y) {U : Y.Opens} : U ≤ f.isoLocus ↔ IsIso (f ∣_ U) :=
  ⟨fun h ↦ IsZariskiLocalAtTarget.restrict_of_le (MorphismProperty.isomorphisms Scheme)
      (inferInstanceAs (IsIso (f ∣_ f.isoLocus))) h,
    fun h ↦ le_iSup_of_le ⟨U, h⟩ le_rfl⟩

/-- A point lies in the iso locus of `f` exactly when `f` is an isomorphism over one of its open
neighbourhoods. -/
theorem mem_isoLocus_iff (f : X ⟶ Y) {y : Y} :
    y ∈ f.isoLocus ↔ ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) :=
  ⟨fun hy ↦ ⟨f.isoLocus, hy, inferInstance⟩,
    fun ⟨_, hy, hU⟩ ↦ (f.le_isoLocus_iff.mpr hU) hy⟩

/-- The iso locus of `f` is the whole target exactly when `f` is an isomorphism. -/
@[simp]
theorem isoLocus_eq_top_iff (f : X ⟶ Y) : f.isoLocus = ⊤ ↔ IsIso f := by
  rw [eq_top_iff, le_isoLocus_iff]
  have h := IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (f := f) (fun _ : Unit ↦ ⊤) (by simp)
  exact ⟨fun hf ↦ h.mpr fun _ ↦ hf, fun hf ↦ h.mp hf ()⟩

/-- The *centre* of `f : X ⟶ Y`: the closed set of points of `Y` over which `f` is not an
isomorphism, the complement of `f.isoLocus`. -/
def centre (f : X ⟶ Y) : Set Y :=
  (f.isoLocus : Set Y)ᶜ

/-- The centre of `f` is the complement of its iso locus. -/
theorem centre_def (f : X ⟶ Y) : f.centre = (f.isoLocus : Set Y)ᶜ := by
  rw [centre]

/-- A point lies in the centre of `f` exactly when `f` is an isomorphism over none of its open
neighbourhoods. -/
theorem mem_centre_iff (f : X ⟶ Y) {y : Y} :
    y ∈ f.centre ↔ ∀ U : Y.Opens, y ∈ U → ¬IsIso (f ∣_ U) := by
  rw [centre_def, Set.mem_compl_iff, SetLike.mem_coe, mem_isoLocus_iff]
  push Not
  rfl

/-- The centre of a morphism is closed. -/
theorem isClosed_centre (f : X ⟶ Y) : IsClosed f.centre :=
  f.isoLocus.isOpen.isClosed_compl

/-- `f` is an isomorphism over the complement of its centre. -/
@[simp]
theorem compl_centre (f : X ⟶ Y) : f.centreᶜ = f.isoLocus :=
  compl_compl _

/-- An open avoids the centre of `f` exactly when `f` is an isomorphism over it. -/
theorem disjoint_centre_iff (f : X ⟶ Y) {U : Y.Opens} :
    Disjoint (U : Set Y) f.centre ↔ IsIso (f ∣_ U) := by
  rw [centre_def, Set.disjoint_compl_right_iff_subset, ← le_isoLocus_iff]
  rfl

/-- The centre of `f` is empty exactly when `f` is an isomorphism. -/
@[simp]
theorem centre_eq_empty_iff (f : X ⟶ Y) : f.centre = ∅ ↔ IsIso f := by
  rw [← isoLocus_eq_top_iff, centre_def, Set.compl_empty_iff, ← TopologicalSpace.Opens.coe_top,
    SetLike.coe_set_eq]

end AlgebraicGeometry.Scheme.Hom
