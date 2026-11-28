/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Regular.Locus
public import TauCeti.RingTheory.RegularLocalRing.J2

/-!
# Openness of the regular locus over a J-2 base

A scheme locally of finite type has open regular locus if its image lies in a union of affine
opens of the base with J-2 coordinate rings. This applies in particular over the spectrum of one
J-2 ring.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isOpen_regularLocus_of_isJ2`: the source of a locally finite-type
  morphism has open regular locus if its image is covered by affine opens with J-2 coordinate rings.
* `AlgebraicGeometry.Scheme.Hom.isOpen_regularLocus_of_spec_isJ2`: a scheme locally of finite type
  over the spectrum of a J-2 ring has open regular locus.

The chart argument uses Mathlib's `Scheme.Hom.finiteType_appLE` and Tau Ceti's
`Scheme.Hom.preimage_regularLocus` and `TauCeti.Excellence.IsJ2.isOpen_regularLocus_of_finiteType`.

## References

* [Stacks Project, Lemma 29.19.2](https://stacks.math.columbia.edu/tag/07R4).
-/

public section

open TauCeti.Excellence

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A scheme locally of finite type has open regular locus if each point in its image has an
affine neighbourhood in the base with J-2 coordinate ring (Stacks, Lemma 29.19.2, Tag 07R4). -/
theorem isOpen_regularLocus_of_isJ2 (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h : ∀ x : X, ∃ U : Y.Opens, IsAffineOpen U ∧ f x ∈ U ∧ IsJ2 Γ(Y, U)) :
    IsOpen X.regularLocus := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, hJ2⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (f.mem_preimage.mpr hxU)
  let := (f.appLE U V hVU).hom.toAlgebra
  -- `RingHom.FiniteType` uses this same `toAlgebra` instance.
  have : Algebra.FiniteType Γ(Y, U) Γ(X, V) := f.finiteType_appLE hU hV hVU
  have hOpen : IsOpen (hV.fromSpec ⁻¹' X.regularLocus) := by
    rw [hV.fromSpec.preimage_regularLocus, Scheme.regularLocus_Spec]
    exact IsJ2.isOpen_regularLocus_of_finiteType (R := Γ(Y, U))
  refine ⟨hV.fromSpec '' (hV.fromSpec ⁻¹' X.regularLocus), Set.image_preimage_subset _ _,
    hV.fromSpec.isOpenEmbedding.isOpenMap _ hOpen, ?_⟩
  rw [Set.image_preimage_eq_inter_range, hV.range_fromSpec]
  exact Set.mem_inter hx hxV

/-- A scheme locally of finite type over the spectrum of a J-2 ring has open regular locus. -/
theorem isOpen_regularLocus_of_spec_isJ2 {R : CommRingCat.{u}} [IsJ2 R]
    (f : X ⟶ Spec R) [LocallyOfFiniteType f] : IsOpen X.regularLocus := by
  apply f.isOpen_regularLocus_of_isJ2
  intro x
  exact ⟨⊤, isAffineOpen_top _, TopologicalSpace.Opens.mem_top (f x),
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.isJ2⟩

end AlgebraicGeometry.Scheme.Hom
