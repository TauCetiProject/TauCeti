/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Binary coproducts of finite morphisms

Schemes with a finite morphism to a fixed scheme `X` are closed under binary coproducts: if
`f : U ⟶ X` and `g : V ⟶ X` are finite, then so is `coprod.desc f g : U ⨿ V ⟶ X`.
`AlgebraicGeometry.IsFinite.isClosedUnderColimitsOfShape_walkingPair` states this as closure of
`MorphismProperty.costructuredArrowObj L @IsFinite` under binary coproducts, in the shape of
Mathlib's `AlgebraicGeometry.IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete`. The
finiteness of `coprod.desc f g` is Mathlib's instance in
`Mathlib.AlgebraicGeometry.Morphisms.Finite`.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Objects of `CostructuredArrow L X` whose structure morphism is finite are closed under binary
coproducts. -/
instance IsFinite.isClosedUnderColimitsOfShape_walkingPair {C : Type*} [Category* C]
    [HasColimitsOfShape (Discrete WalkingPair) C] (L : C ⥤ Scheme.{u})
    [PreservesColimitsOfShape (Discrete WalkingPair) L] (X : Scheme.{u}) :
    (MorphismProperty.costructuredArrowObj L @IsFinite (X := X)).IsClosedUnderColimitsOfShape
      (Discrete WalkingPair) := by
  have : MorphismProperty.RespectsIso @IsFinite.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine CostructuredArrow.isClosedUnderColimitsOfShape (fun D _ ↦ colimit.cocone D)
    (fun D _ ↦ colimit.isColimit D) (fun D _ X s hs ↦ ?_) X
  have hdesc : (colimit.isColimit D).desc (Cocone.mk X s) =
      (HasColimit.isoOfNatIso (diagramIsoPair D)).hom ≫
        coprod.desc (s.app ⟨.left⟩) (s.app ⟨.right⟩) := by
    refine colimit.hom_ext fun ⟨j⟩ ↦ ?_
    cases j <;> simp
  have := hs ⟨.left⟩
  have := hs ⟨.right⟩
  rw [hdesc]
  infer_instance

end AlgebraicGeometry
