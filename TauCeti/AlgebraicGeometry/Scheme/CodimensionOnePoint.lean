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
This file introduces the subtype of such points, proves that a codimension-one point has no
codimension-one generization other than itself, and defines the functorial injection on
codimension-one points induced by an open immersion.

Codimension-one points index prime divisors, and they arise as centres of places of the function
field; this file holds only the common definition, independent of either theory.

## Main declarations

* `TauCeti.AlgebraicGeometry.CodimensionOnePoint`: the codimension-one points of a scheme.
* `TauCeti.AlgebraicGeometry.CodimensionOnePoint.eq_of_specializes`: a codimension-one
  generization of a codimension-one point is equal to it.
* `TauCeti.AlgebraicGeometry.CodimensionOnePoint.mapOfIsOpenImmersion`: the injection on
  codimension-one points induced by an open immersion, with `@[simp]` characterization and
  functoriality lemmas.
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

variable {V U X : Scheme.{u}}

/-- A codimension-one point admits no codimension-one generization other than itself. -/
lemma eq_of_specializes {x y : CodimensionOnePoint X} (h : (y : X) ⤳ (x : X)) : y = x := by
  refine Subtype.ext (h.antisymm ?_).eq
  by_contra hxy
  have := coheight_add_one_le <|
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h) (mt Scheme.le_iff_specializes.mp hxy)
  norm_num [x.property, y.property] at this

/-- The injection on codimension-one points induced by an open immersion `j : U ⟶ X`. -/
def mapOfIsOpenImmersion (j : U ⟶ X) [IsOpenImmersion j] (u : CodimensionOnePoint U) :
    CodimensionOnePoint X :=
  ⟨j u, (coheight_eq_of_isOpenImmersion j).trans u.2⟩

/-- The underlying point of `CodimensionOnePoint.mapOfIsOpenImmersion j u` is `j u`. -/
@[simp]
lemma coe_mapOfIsOpenImmersion (j : U ⟶ X) [IsOpenImmersion j] (u : CodimensionOnePoint U) :
    (mapOfIsOpenImmersion j u : X) = j u :=
  (rfl)

/-- `CodimensionOnePoint.mapOfIsOpenImmersion j` is injective. -/
lemma mapOfIsOpenImmersion_injective (j : U ⟶ X) [IsOpenImmersion j] :
    Function.Injective (mapOfIsOpenImmersion j) :=
  fun _ _ h ↦ Subtype.ext (j.isOpenEmbedding.injective (by
    simpa only [coe_mapOfIsOpenImmersion] using congrArg Subtype.val h))

/-- `CodimensionOnePoint.mapOfIsOpenImmersion j` is injective as an `@[simp]` equality iff. -/
@[simp]
lemma mapOfIsOpenImmersion_inj (j : U ⟶ X) [IsOpenImmersion j] {u v : CodimensionOnePoint U} :
    mapOfIsOpenImmersion j u = mapOfIsOpenImmersion j v ↔ u = v :=
  (mapOfIsOpenImmersion_injective j).eq_iff

/-- A codimension-one point of `X` lies in the image of `CodimensionOnePoint.mapOfIsOpenImmersion j`
if and only if its underlying point lies in `Set.range j`. -/
lemma mem_range_mapOfIsOpenImmersion_iff (j : U ⟶ X) [IsOpenImmersion j]
    {η : CodimensionOnePoint X} :
    η ∈ Set.range (mapOfIsOpenImmersion j) ↔ (η : X) ∈ Set.range j := by
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨u.1, ?_⟩, fun ⟨u, hu⟩ ↦ ?_⟩
  · simpa only [coe_mapOfIsOpenImmersion] using congrArg Subtype.val hu
  · exact ⟨⟨u, (coheight_eq_of_isOpenImmersion j).symm.trans (hu.symm ▸ η.2)⟩, Subtype.ext hu⟩

/-- Along the identity morphism, `CodimensionOnePoint.mapOfIsOpenImmersion` is the identity. -/
@[simp]
lemma mapOfIsOpenImmersion_id (X : Scheme.{u}) :
    mapOfIsOpenImmersion (𝟙 X) = id := by
  ext u : 2
  simp

/-- `CodimensionOnePoint.mapOfIsOpenImmersion` respects composition of open immersions. -/
@[simp]
lemma mapOfIsOpenImmersion_comp (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i]
    [IsOpenImmersion j] :
    mapOfIsOpenImmersion (i ≫ j) = mapOfIsOpenImmersion j ∘ mapOfIsOpenImmersion i := by
  ext v : 2
  simp

end CodimensionOnePoint

end AlgebraicGeometry

end TauCeti
