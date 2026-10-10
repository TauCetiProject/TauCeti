/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Dominant morphisms of irreducible schemes and rational functions

A morphism `f : X ⟶ Y` of schemes is dominant (`AlgebraicGeometry.IsDominant`) when its image is
dense. Between irreducible schemes this says exactly that `f` sends the generic point of `X` to the
generic point of `Y`. The map of stalks at the generic point is then a homomorphism
`f^* : K(Y) ⟶ K(X)` of function fields, the pullback of rational functions along `f`. It is the
homomorphism through which `f` acts on the generic point: the canonical morphism
`Spec K(X) ⟶ X` followed by `f` is `Spec f^*` followed by the canonical morphism
`Spec K(Y) ⟶ Y`, and `f^*` is the only homomorphism with this property.

This is how a dominant morphism of integral curves is compared with a homomorphism of function
fields given by other means, for instance by explicit formulae: it suffices to compute the image of
the generic point.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.functionFieldMap`: the pullback `K(Y) ⟶ K(X)` of rational
  functions along a dominant morphism `f : X ⟶ Y` of irreducible schemes.

## Main results

* `AlgebraicGeometry.Scheme.Hom.genericPoint_eq_of_isDominant`: a dominant morphism of
  irreducible schemes sends the generic point to the generic point.
* `AlgebraicGeometry.isDominant_iff_genericPoint_eq`: conversely, a morphism of irreducible
  schemes sending the generic point to the generic point is dominant.
* `AlgebraicGeometry.isDominant_of_SpecMap_fromSpecStalk`: a morphism of irreducible schemes
  whose action on the generic point is given by a local homomorphism of function fields is
  dominant.
* `AlgebraicGeometry.Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk`: `Spec f^*` followed by
  `Spec K(Y) ⟶ Y` is `Spec K(X) ⟶ X` followed by `f`.
* `AlgebraicGeometry.Scheme.Hom.eq_functionFieldMap_iff`: `f^*` is the only homomorphism of
  function fields with this property.
* `AlgebraicGeometry.Scheme.Hom.germToFunctionField_functionFieldMap`: `f^*` sends the germ of a
  section `s` over an open `U` to the germ of its pullback `f^* s` over `f⁻¹ U`.
* `AlgebraicGeometry.Scheme.Hom.functionFieldMap_id` and
  `AlgebraicGeometry.Scheme.Hom.functionFieldMap_comp`: functoriality.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter I, Theorem 4.4 (dominant
  rational maps of varieties and homomorphisms of function fields).
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- A dominant morphism of irreducible schemes sends the generic point to the generic point. -/
theorem Scheme.Hom.genericPoint_eq_of_isDominant (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  -- `f` sends the generic point of `X` to a generic point of the closure of its image, which is
  -- all of `Y`
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h.eq (genericPoint_spec Y)

/-- A morphism of irreducible schemes is dominant exactly when it sends the generic point to the
generic point. -/
theorem isDominant_iff_genericPoint_eq {f : X ⟶ Y} :
    IsDominant f ↔ f (genericPoint X) = genericPoint Y := by
  refine ⟨fun _ ↦ f.genericPoint_eq_of_isDominant, fun h ↦ ⟨?_⟩⟩
  -- the image contains the generic point of `Y`, whose closure is `Y`
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, h⟩)

/-- A morphism `f : X ⟶ Y` of irreducible schemes is dominant when the canonical morphism
`Spec K(X) ⟶ X` followed by `f` factors as `Spec φ` followed by the canonical morphism
`Spec K(Y) ⟶ Y`, for a local homomorphism `φ : K(Y) ⟶ K(X)`. The homomorphism `φ` is then the
pullback of rational functions along `f` (`Scheme.Hom.eq_functionFieldMap_iff`). -/
theorem isDominant_of_SpecMap_fromSpecStalk (f : X ⟶ Y) (φ : Y.functionField ⟶ X.functionField)
    [IsLocalHom φ.hom]
    (h : Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ f) :
    IsDominant f := by
  -- evaluate both sides of `h` at the closed point of `Spec K(X)`, which `Spec φ` fixes
  refine isDominant_iff_genericPoint_eq.mpr <| calc
    f (genericPoint X)
      = f (X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint X.functionField)) :=
        congrArg _ Scheme.fromSpecStalk_closedPoint.symm
    _ = (X.fromSpecStalk (genericPoint X) ≫ f) (IsLocalRing.closedPoint X.functionField) :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) (IsLocalRing.closedPoint X.functionField) :=
        congrArg (fun g ↦ g (IsLocalRing.closedPoint X.functionField)) h.symm
    _ = genericPoint Y := (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg _ Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)

namespace Scheme.Hom

/-- The preimage of a nonempty open under a dominant morphism is nonempty. -/
instance nonempty_preimage_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  obtain ⟨_, hx, x, rfl⟩ := f.denseRange.inter_open_nonempty U U.2
    ⟨_, (Classical.arbitrary U).2⟩
  exact ⟨⟨x, hx⟩⟩

/-- The **pullback of rational functions** `f^* : K(Y) ⟶ K(X)` along a dominant morphism
`f : X ⟶ Y` of irreducible schemes: the map of stalks of `f` at the generic point of `X`, which `f`
sends to the generic point of `Y` (`genericPoint_eq_of_isDominant`). It is characterised by
`SpecMap_functionFieldMap_fromSpecStalk` and `eq_functionFieldMap_iff`, and it sends the germ of a
section `s` to the germ of `f^* s` (`germToFunctionField_functionFieldMap`). -/
noncomputable def functionFieldMap (f : X ⟶ Y) [IsDominant f] :
    Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant) ≫
    f.stalkMap (genericPoint X)

/-- **The pullback of rational functions describes the image of the generic point**: for a
dominant morphism `f : X ⟶ Y` of irreducible schemes, the canonical morphism `Spec K(X) ⟶ X`
followed by `f` is `Spec f^*` followed by the canonical morphism `Spec K(Y) ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem SpecMap_functionFieldMap_fromSpecStalk (f : X ⟶ Y) [IsDominant f] :
    Spec.map f.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [functionFieldMap, Spec.map_comp_assoc, SpecMap_stalkSpecializes_fromSpecStalk,
    SpecMap_stalkMap_fromSpecStalk]

/-- **The pullback of rational functions is unique**: a homomorphism `φ : K(Y) ⟶ K(X)` is the
pullback `f^*` along a dominant morphism `f : X ⟶ Y` of irreducible schemes exactly when
`Spec φ` followed by the canonical morphism `Spec K(Y) ⟶ Y` is the canonical morphism
`Spec K(X) ⟶ X` followed by `f`. -/
theorem eq_functionFieldMap_iff (f : X ⟶ Y) [IsDominant f]
    (φ : Y.functionField ⟶ X.functionField) :
    φ = f.functionFieldMap ↔
      Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [← f.SpecMap_functionFieldMap_fromSpecStalk, cancel_mono, Spec.map_inj]

/-- The pullback of rational functions `f^*` along a dominant morphism `f : X ⟶ Y` of irreducible
schemes sends the germ at the generic point of a section `s` of `𝒪_Y` over a nonempty open `U` to
the germ of its pullback `f^* s` over `f⁻¹ U`. -/
@[reassoc]
theorem germToFunctionField_functionFieldMap (f : X ⟶ Y) [IsDominant f] (U : Y.Opens)
    [Nonempty U] :
    Y.germToFunctionField U ≫ f.functionFieldMap = f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  rw [Scheme.germToFunctionField, Scheme.germToFunctionField, functionFieldMap,
    TopCat.Presheaf.germ_stalkSpecializes_assoc, germ_stalkMap]

/-- The pullback of rational functions along the identity is the identity. -/
@[simp]
theorem functionFieldMap_id : functionFieldMap (𝟙 X) = 𝟙 X.functionField := by
  rw [eq_comm, eq_functionFieldMap_iff, Spec.map_id, Category.id_comp, Category.comp_id]

/-- The pullback of rational functions along a composite of dominant morphisms of irreducible
schemes is the composite of the pullbacks, in the opposite order. -/
@[simp]
theorem functionFieldMap_comp [IrreducibleSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f]
    [IsDominant g] :
    (f ≫ g).functionFieldMap = g.functionFieldMap ≫ f.functionFieldMap := by
  rw [eq_comm, eq_functionFieldMap_iff, Spec.map_comp_assoc,
    SpecMap_functionFieldMap_fromSpecStalk, SpecMap_functionFieldMap_fromSpecStalk_assoc]

end Scheme.Hom

end AlgebraicGeometry
