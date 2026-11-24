/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Basic

/-!
# Rational maps at the generic point

General facts about Mathlib's partial and rational maps from an irreducible scheme `X`, read at
the generic point of `X`: the domain of a partial map contains the generic point, the morphism
`Spec K(X) ⟶ Y` of a rational map commutes with postcomposition by a morphism, and for an
`S`-rational map it is a morphism over `S`.

## Main results

* `AlgebraicGeometry.Scheme.PartialMap.genericPoint_mem_domain`: the domain of a partial map from
  an irreducible scheme contains the generic point.
* `AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_compHom`: postcomposing a rational map
  with a morphism postcomposes its morphism `Spec K(X) ⟶ Y`.
* `AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_comp_over`: the morphism
  `Spec K(X) ⟶ Y` of an `S`-rational map is over `S`.
* `AlgebraicGeometry.Scheme.Hom.isOver_toRationalMap`: the rational map of an `S`-morphism is an
  `S`-rational map.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- The domain of a partial map from an irreducible scheme contains the generic point, since it
is a dense open. -/
theorem PartialMap.genericPoint_mem_domain [IrreducibleSpace X] (f : X.PartialMap Y) :
    genericPoint X ∈ f.domain :=
  haveI : Nonempty f.domain := f.dense_domain.nonempty.to_subtype
  TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem f.domain

/-- The morphism `Spec K(X) ⟶ Z` of a rational map followed by a morphism `g` is that of the
rational map followed by `g`. -/
theorem RationalMap.fromFunctionField_compHom [IrreducibleSpace X] (f : X ⤏ Y) (g : Y ⟶ Z) :
    (f.compHom g).fromFunctionField = f.fromFunctionField ≫ g := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  rw [← compHom_toRationalMap, fromFunctionField_toRationalMap, fromFunctionField_toRationalMap]
  exact PartialMap.fromSpecStalkOfMem_compHom f g _ _

/-- For an `S`-rational map `f : X ⤏ Y` from an irreducible scheme, the morphism
`Spec K(X) ⟶ Y` of `f` is a morphism over `S`. -/
theorem RationalMap.fromFunctionField_comp_over [IrreducibleSpace X] {S : Scheme.{u}}
    (f : X ⤏ Y) (sX : X ⟶ S) (sY : Y ⟶ S) [f.IsOver sX sY] :
    f.fromFunctionField ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX := by
  rw [← fromFunctionField_compHom, RationalMap.isOver_iff.mp ‹_›,
    fromFunctionField_toRationalMap, PartialMap.fromFunctionField,
    PartialMap.fromSpecStalkOfMem_toPartialMap]

/-- The rational map of an `S`-morphism is an `S`-rational map. -/
instance Hom.isOver_toRationalMap {S : Scheme.{u}} [X.Over S] [Y.Over S] (g : X ⟶ Y)
    [g.IsOver S] : g.toRationalMap.IsOver (X ↘ S) (Y ↘ S) :=
  haveI := Hom.isOver_toPartialMap (comp_over g S)
  inferInstance

end AlgebraicGeometry.Scheme
