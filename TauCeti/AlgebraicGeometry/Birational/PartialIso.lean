/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition

/-!
# The rational map of a partial isomorphism is invertible

A partial isomorphism `φ`, an isomorphism between dense opens of `X` and `Y` (Mathlib's
`AlgebraicGeometry.Scheme.PartialIso`), has a dominant partial map, and its rational map
`φ.toRationalMap` has inverse `φ.symm.toRationalMap` on both sides.

## Main results

* `AlgebraicGeometry.Scheme.PartialIso.toPartialMap_comp_symm_equiv`: the partial map of `φ`
  followed by that of `φ.symm` is equivalent to the identity.
* `AlgebraicGeometry.Scheme.PartialIso.toRationalMap_comp_symm` and
  `AlgebraicGeometry.Scheme.PartialIso.toRationalMap_symm_comp`: `φ⁻¹ ∘ φ = id` and
  `φ ∘ φ⁻¹ = id` as rational maps.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.PartialIso

variable {X Y : Scheme.{u}}

/-- The partial map of a partial isomorphism is dominant: its image is a dense open. -/
instance isDominant_toPartialMap_hom (φ : X.PartialIso Y) : IsDominant φ.toPartialMap.hom := by
  have := Opens.isDominant_ι φ.dense_target
  have : IsDominant (φ.iso.hom ≫ φ.target.ι) := inferInstance
  rwa [toPartialMap_hom]

/-- The partial map of a partial isomorphism followed by that of its inverse is equivalent to the
identity. -/
theorem toPartialMap_comp_symm_equiv [PreirreducibleSpace X] [Nonempty Y] (φ : X.PartialIso Y) :
    (φ.toPartialMap.comp φ.symm.toPartialMap).equiv (PartialMap.id X) := by
  obtain ⟨U, hU, V, hV, e⟩ := φ
  have := Opens.isDominant_ι hV
  -- By `toPartialMap_hom` and `symm_iso`, the two partial maps unfold definitionally to these
  -- anonymous constructors.
  change ((⟨U, hU, e.hom ≫ V.ι⟩ : X.PartialMap Y).comp ⟨V, hV, e.inv ≫ U.ι⟩).equiv
    (PartialMap.id X)
  have key : (e.hom ≫ V.ι) ∣_ V ≫ e.inv = ((e.hom ≫ V.ι) ⁻¹ᵁ V).ι := by
    rw [← cancel_mono (e.hom ≫ V.ι), Category.assoc, Iso.inv_hom_id_assoc, morphismRestrict_ι]
  refine ⟨_, (PartialMap.comp _ _).dense_domain, le_rfl,
    le_top.trans_eq (Hom.toPartialMap_domain _).symm, ?_⟩
  rw [PartialMap.restrict_hom, PartialMap.restrict_hom, homOfLE_rfl, Category.id_comp,
    PartialMap.comp_hom]
  -- reduce the projections of the anonymous constructors
  dsimp only
  rw [reassoc_of% key, Hom.isoImage_inv_ι, Hom.toPartialMap_hom, Category.comp_id, topIso_hom]
  exact (X.homOfLE_ι _).symm

/-- **A partial isomorphism is invertible as a rational map**: `φ⁻¹ ∘ φ = id`. -/
@[simp]
theorem toRationalMap_comp_symm [PreirreducibleSpace X] [Nonempty Y] (φ : X.PartialIso Y) :
    φ.toRationalMap.comp φ.symm.toRationalMap = RationalMap.id X := by
  rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff]
  exact φ.toPartialMap_comp_symm_equiv

/-- **A partial isomorphism is invertible as a rational map**: `φ ∘ φ⁻¹ = id`. -/
@[simp]
theorem toRationalMap_symm_comp [PreirreducibleSpace Y] [Nonempty X] (φ : X.PartialIso Y) :
    φ.symm.toRationalMap.comp φ.toRationalMap = RationalMap.id Y :=
  φ.symm.toRationalMap_comp_symm

end AlgebraicGeometry.Scheme.PartialIso
