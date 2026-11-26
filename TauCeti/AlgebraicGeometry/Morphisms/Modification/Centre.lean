/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# The centre of a modification

For a morphism of schemes `f : X ⟶ Y`, the iso locus `f.isoLocus` is the largest open of `Y` over
which `f` is an isomorphism, and its closed complement `f.centre` is the set of points over which
`f` fails to be an isomorphism (`TauCeti/AlgebraicGeometry/Morphisms/IsoLocus.lean`). For a
modification the iso locus contains the dense open of the definition, so it is dense and the
centre is nowhere dense.

A *modification witness* (`IsModification.Witness f U`) is an open `U ⊆ Y` that is dense, has
dense preimage `f⁻¹(U)` in `X`, and over which `f` is an isomorphism. A proper morphism is a
modification exactly when it has a witness, and the iso locus of a modification is the largest
witness.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsModification.Witness f U`: `U` is a dense open of `Y` with dense
  preimage over which `f` is an isomorphism.

## Main results

* `TauCeti.AlgebraicGeometry.IsModification.iff_exists_witness`: a proper morphism is a
  modification exactly when it has a witness.
* `TauCeti.AlgebraicGeometry.IsModification.witness_isoLocus`: the iso locus of a modification is
  a witness, and it contains every witness (`IsModification.Witness.le_isoLocus`).
* `TauCeti.AlgebraicGeometry.IsModification.dense_isoLocus` and
  `TauCeti.AlgebraicGeometry.IsModification.isNowhereDense_centre`: for a modification, the iso
  locus is dense and the centre is nowhere dense.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A *modification witness* for `f : X ⟶ Y` is an open `U ⊆ Y` that is dense, has dense preimage
`f⁻¹(U)` in `X`, and over which `f` is an isomorphism. A proper morphism with a witness is a
modification (`IsModification.of_witness`). -/
structure IsModification.Witness (f : X ⟶ Y) (U : Y.Opens) : Prop where
  /-- The open `U` is dense in `Y`. -/
  dense : Dense (U : Set Y)
  /-- The preimage `f⁻¹(U)` is dense in `X`. -/
  dense_preimage : Dense (f ⁻¹ᵁ U : Set X)
  /-- `f` restricts to an isomorphism `f⁻¹(U) ≅ U`. -/
  isIso : IsIso (f ∣_ U)

namespace IsModification

/-- Every modification has a witness. -/
theorem exists_witness (f : X ⟶ Y) [IsModification f] : ∃ U, Witness f U := by
  obtain ⟨U, hU, hfU, h⟩ := exists_isIso_morphismRestrict (f := f)
  exact ⟨U, hU, hfU, h⟩

/-- A proper morphism with a modification witness is a modification. -/
theorem of_witness (f : X ⟶ Y) [IsProper f] {U : Y.Opens} (h : Witness f U) :
    IsModification f where
  exists_isIso_morphismRestrict := ⟨U, h.dense, h.dense_preimage, h.isIso⟩

/-- A proper morphism is a modification exactly when it has a witness. -/
theorem iff_exists_witness (f : X ⟶ Y) [IsProper f] :
    IsModification f ↔ ∃ U, Witness f U :=
  ⟨fun _ ↦ exists_witness f, fun ⟨_, h⟩ ↦ of_witness f h⟩

/-- The whole target is a witness for an isomorphism. -/
theorem witness_top (f : X ⟶ Y) [IsIso f] : Witness f ⊤ :=
  ⟨by simp, by simp, inferInstance⟩

/-- A witness is contained in the iso locus. -/
theorem Witness.le_isoLocus {f : X ⟶ Y} {U : Y.Opens} (h : Witness f U) : U ≤ f.isoLocus :=
  f.le_isoLocus_iff.mpr h.isIso

/-- A larger open over which `f` is still an isomorphism is again a witness. -/
theorem Witness.mono {f : X ⟶ Y} {U U' : Y.Opens} (h : Witness f U) (hUU' : U ≤ U')
    (hU' : IsIso (f ∣_ U')) : Witness f U' :=
  ⟨h.dense.mono hUU', h.dense_preimage.mono (f.preimage_mono hUU'), hU'⟩

/-- The iso locus of a modification is a witness, the largest one (`Witness.le_isoLocus`). -/
theorem witness_isoLocus (f : X ⟶ Y) [IsModification f] : Witness f f.isoLocus := by
  obtain ⟨U, hU⟩ := exists_witness f
  exact hU.mono hU.le_isoLocus inferInstance

/-- The iso locus of a modification is dense. -/
theorem dense_isoLocus (f : X ⟶ Y) [IsModification f] : Dense (f.isoLocus : Set Y) := by
  obtain ⟨U, hU, -, hf⟩ := exists_isIso_morphismRestrict (f := f)
  exact hU.mono (f.le_isoLocus_iff.mpr hf)

/-- The centre of a modification is nowhere dense: it is closed, and `f` is an isomorphism over
its dense complement. -/
theorem isNowhereDense_centre (f : X ⟶ Y) [IsModification f] : IsNowhereDense f.centre := by
  rw [f.isClosed_centre.isNowhereDense_iff, interior_eq_empty_iff_dense_compl,
    Scheme.Hom.compl_centre]
  exact dense_isoLocus f

end IsModification

end TauCeti.AlgebraicGeometry
