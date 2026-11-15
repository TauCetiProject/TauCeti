/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Order.KrullDimension

/-!
# Codimension-one points of a scheme

A point of a scheme has codimension one when its coheight for the specialization order is one,
equivalently when it is the generic point of an irreducible closed subset of codimension one.
This file introduces the subtype of such points and records the one order-theoretic fact about
them that does not mention any further structure: a codimension-one point has no codimension-one
generization other than itself.

Codimension-one points index prime divisors, and they arise as centres of places of the function
field; this file holds only the common definition, independent of either theory.

## Main declarations

* `TauCeti.AlgebraicGeometry.CodimensionOnePoint`: the codimension-one points of a scheme.
* `TauCeti.AlgebraicGeometry.CodimensionOnePoint.eq_of_specializes`: a codimension-one
  generization of a codimension-one point is equal to it.
* `TauCeti.AlgebraicGeometry.CodimensionOnePoint.mapOfIsOpenImmersion`: pushforward of a
  codimension-one point along an open immersion, with its injectivity, range characterization,
  and functoriality lemmas.
-/

public section

open CategoryTheory Order AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A codimension-one point of a scheme: a point of coheight one for the specialization order,
that is, the generic point of an irreducible closed subset of codimension one. -/
abbrev CodimensionOnePoint (X : Scheme.{u}) : Type u :=
  {x : X // coheight x = 1}

namespace CodimensionOnePoint

/-- A codimension-one point admits no codimension-one generization other than itself. -/
lemma eq_of_specializes {X : Scheme.{u}} {x y : CodimensionOnePoint X}
    (h : (y : X) ⤳ (x : X)) : y = x := by
  refine Subtype.ext (h.antisymm ?_).eq
  by_contra hxy
  have := coheight_add_one_le <|
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h) (mt Scheme.le_iff_specializes.mp hxy)
  norm_num [x.property, y.property] at this

/-- Pushforward of a codimension-one point along an open immersion. -/
def mapOfIsOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (y : CodimensionOnePoint U) : CodimensionOnePoint X :=
  ⟨j y, (coheight_eq_of_isOpenImmersion j).trans y.2⟩

/-- Coercing `CodimensionOnePoint.mapOfIsOpenImmersion j y` to `X` gives `j y`. -/
@[simp]
theorem coe_mapOfIsOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (y : CodimensionOnePoint U) :
    (mapOfIsOpenImmersion j y : X) = j y :=
  (rfl)

/-- `CodimensionOnePoint.mapOfIsOpenImmersion j` is injective for an open immersion `j`. -/
theorem mapOfIsOpenImmersion_injective {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : Function.Injective (mapOfIsOpenImmersion j) :=
  fun _ _ h ↦ Subtype.ext (j.isOpenEmbedding.injective (congrArg Subtype.val h))

/-- `CodimensionOnePoint.mapOfIsOpenImmersion j` is injective in simp normal form. -/
@[simp]
theorem mapOfIsOpenImmersion_eq_iff {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {y₁ y₂ : CodimensionOnePoint U} :
    mapOfIsOpenImmersion j y₁ = mapOfIsOpenImmersion j y₂ ↔ y₁ = y₂ :=
  (mapOfIsOpenImmersion_injective j).eq_iff

/-- A codimension-one point of `X` lies in the range of `mapOfIsOpenImmersion j` if and only if
its underlying point lies in `Set.range j` (not `@[simp]` because `Set.mem_range` simplifies its
left-hand side; see `range_mapOfIsOpenImmersion`). -/
theorem mem_range_mapOfIsOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {η : CodimensionOnePoint X} :
    η ∈ Set.range (mapOfIsOpenImmersion j) ↔ (η : X) ∈ Set.range j :=
  ⟨fun ⟨y, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩, fun ⟨u, hu⟩ ↦
    ⟨⟨u, (coheight_eq_of_isOpenImmersion j).symm.trans (hu.symm ▸ η.2)⟩, Subtype.ext hu⟩⟩

/-- The range of `CodimensionOnePoint.mapOfIsOpenImmersion j` is the preimage of `Set.range j`
under coercion to `X`. -/
@[simp]
theorem range_mapOfIsOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Set.range (mapOfIsOpenImmersion j) = Subtype.val ⁻¹' Set.range j :=
  Set.ext fun _ ↦ mem_range_mapOfIsOpenImmersion j

/-- Pushforward of codimension-one points along the identity is the identity. -/
@[simp]
theorem mapOfIsOpenImmersion_id {X : Scheme.{u}} (y : CodimensionOnePoint X) :
    mapOfIsOpenImmersion (𝟙 X) y = y :=
  Subtype.ext (by simp)

/-- Pushforward of codimension-one points is functorial under composition of open immersions. -/
@[simp]
theorem mapOfIsOpenImmersion_comp {U V X : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] (y : CodimensionOnePoint U) :
    mapOfIsOpenImmersion (f ≫ g) y = mapOfIsOpenImmersion g (mapOfIsOpenImmersion f y) :=
  Subtype.ext (Scheme.Hom.comp_apply f g y.1)

end CodimensionOnePoint

end AlgebraicGeometry

end TauCeti
