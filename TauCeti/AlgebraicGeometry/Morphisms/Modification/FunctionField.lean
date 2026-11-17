/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

/-!
# Modifications induce isomorphisms of function fields

A modification `f : X ⟶ Y` is an isomorphism over a dense open `U ⊆ Y`, so its image is dense and,
being closed, all of `Y`. When `X` and `Y` are irreducible, the generic point of `X` lies in the
dense open `f ⁻¹ U`, where `f` is an isomorphism, so the stalk map of `f` at the generic point is an
isomorphism. Hence the pullback of rational functions `f^* : K(Y) ⟶ K(X)`
(`AlgebraicGeometry.Scheme.Hom.functionFieldMap`) is an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_functionFieldMap_of_isIso_stalkMap`: for a dominant morphism
  of irreducible schemes whose stalk map at the generic point is an isomorphism, the pullback of
  rational functions is an isomorphism.
* `TauCeti.AlgebraicGeometry.IsModification.isDominant` and
  `TauCeti.AlgebraicGeometry.IsModification.surjective`: modifications are dominant and surjective.
* `TauCeti.AlgebraicGeometry.IsModification.isIso_functionFieldMap`: a modification of irreducible
  schemes induces an isomorphism of function fields.
* `TauCeti.AlgebraicGeometry.IsModification.functionFieldEquiv`: the ring isomorphism
  `K(Y) ≃+* K(X)` induced by a modification `f : X ⟶ Y` of irreducible schemes.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- If the stalk map of a dominant morphism `f : X ⟶ Y` of irreducible schemes at the generic point
of `X` is an isomorphism, then so is the pullback of rational functions `f^* : K(Y) ⟶ K(X)`. -/
theorem isIso_functionFieldMap_of_isIso_stalkMap (f : X ⟶ Y) [IsDominant f]
    [IsIso (f.stalkMap (genericPoint X))] : IsIso f.functionFieldMap := by
  have : IsIso (Y.presheaf.stalkSpecializes
      (specializes_of_eq f.genericPoint_eq_of_isDominant)) :=
    (Y.presheaf.stalkCongr (.of_eq f.genericPoint_eq_of_isDominant.symm)).isIso_hom
  have h : Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant) ≫
      f.stalkMap (genericPoint X) = f.functionFieldMap := by
    rw [eq_functionFieldMap_iff, Spec.map_comp_assoc, SpecMap_stalkSpecializes_fromSpecStalk,
      SpecMap_stalkMap_fromSpecStalk]
  rw [← h]
  infer_instance

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.IsModification

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsModification f]

/-- A modification is dominant: its image contains the dense open over which it is an
isomorphism. -/
instance (priority := 100) isDominant : IsDominant f := by
  obtain ⟨U, hU, -, _⟩ := exists_isIso_morphismRestrict (f := f)
  refine ⟨hU.mono fun y hy ↦ ?_⟩
  obtain ⟨x, hx⟩ := (f ∣_ U).surjective ⟨y, hy⟩
  exact ⟨x.1, by simpa [morphismRestrict_base_coe] using congrArg Subtype.val hx⟩

/-- A modification is surjective: it is dominant and closed. -/
instance (priority := 100) surjective : Surjective f :=
  Surjective.of_universallyClosed_of_isDominant f

variable [IrreducibleSpace X] [IrreducibleSpace Y]

/-- A modification of irreducible schemes induces an isomorphism of function fields: the generic
point of the source lies over the dense open where the modification is an isomorphism. -/
instance isIso_functionFieldMap : IsIso f.functionFieldMap := by
  obtain ⟨U, -, hfU, _⟩ := exists_isIso_morphismRestrict (f := f)
  have hx : genericPoint X ∈ f ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr (by simpa using hfU.nonempty)
  have : IsIso (f.stalkMap (genericPoint X)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (morphismRestrictStalkMap f U ⟨_, hx⟩)).mp
      (((isIso_iff_isIso_stalkMap _).mp ‹_›).2 _)
  exact f.isIso_functionFieldMap_of_isIso_stalkMap

/-- The ring isomorphism `K(Y) ≃+* K(X)` of function fields induced by a modification
`f : X ⟶ Y` of irreducible schemes: the pullback of rational functions along `f`. This is
SchemeAndStackFoundations §4.11's *IsModification.functionField_equiv*. -/
@[expose]
noncomputable def functionFieldEquiv : Y.functionField ≃+* X.functionField :=
  RingEquiv.ofRingHom f.functionFieldMap.hom (inv f.functionFieldMap).hom
    (by ext; simp) (by ext; simp)

@[simp]
theorem functionFieldEquiv_apply (a : Y.functionField) :
    functionFieldEquiv f a = f.functionFieldMap.hom a :=
  rfl

@[simp]
theorem functionFieldEquiv_symm_apply (a : X.functionField) :
    (functionFieldEquiv f).symm a = (inv f.functionFieldMap).hom a :=
  rfl

end TauCeti.AlgebraicGeometry.IsModification
