/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Subobject.Basic
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Subobjects in a full subcategory closed under subobjects

Let `P` be a property of objects of a category `C` whose full subcategory has its inclusion
preserving monomorphisms. Then the subobjects of an object `X` of the full subcategory embed into
the subobjects of `X.obj` in `C` (`CategoryTheory.ObjectProperty.subobjectOrderEmbedding`). If `P`
is moreover closed under subobjects, for instance the finitely generated modules over a left
Noetherian ring, this embedding is an isomorphism
(`CategoryTheory.ObjectProperty.subobjectOrderIso`). Lattice-theoretic invariants of subobject
lattices, such as the length of an object, are therefore the same in the full subcategory and in
`C`.

## Main definitions

* `CategoryTheory.ObjectProperty.subobjectOrderEmbedding`: the order embedding
  `Subobject X ↪o Subobject X.obj` for `X : P.FullSubcategory`.
* `CategoryTheory.ObjectProperty.subobjectOrderIso`: the order isomorphism
  `Subobject X ≃o Subobject X.obj` for `X : P.FullSubcategory`, when `P` is closed under
  subobjects.

## Main results

* `CategoryTheory.ObjectProperty.subobjectOrderEmbedding_mk` and
  `CategoryTheory.ObjectProperty.subobjectOrderIso_mk`: the subobject represented by a
  monomorphism `f` goes to the subobject represented by `P.ι.map f`.
* `CategoryTheory.ObjectProperty.subobjectOrderIso_symm_mk`: the inverse sends the subobject
  represented by a monomorphism `g : Y ⟶ X.obj` to the subobject represented by `g` seen in the
  full subcategory.

## Implementation notes

The embedding sends a subobject `S` of `X` to the subobject of `X.obj` represented by the
inclusion of `S` into `C`; it reflects the order since the inclusion is full. When `P` is closed
under subobjects, a subobject `T` of `X.obj` has underlying object satisfying `P`, so its arrow
seen in the full subcategory, a monomorphism since the inclusion is faithful, represents a preimage
of `T`.

## References

* [Stacks, Tag 001D](https://stacks.math.columbia.edu/tag/001D), for full subcategories.
-/

public section

namespace CategoryTheory.ObjectProperty

open Subobject

universe v u

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

variable [P.ι.PreservesMonomorphisms]

/-- **Subobjects in a full subcategory are subobjects in the ambient category.** If the inclusion
of the full subcategory of `P` preserves monomorphisms, sending a subobject `S` of `X` to the
subobject of `X.obj` represented by the inclusion of `S` into `C` is an order embedding. -/
noncomputable def subobjectOrderEmbedding (X : P.FullSubcategory) :
    Subobject X ↪o Subobject X.obj :=
  OrderEmbedding.ofMapLEIff (fun S ↦ mk (P.ι.map S.arrow)) fun S T ↦
    ⟨fun h ↦ le_of_comm (homMk (ofMkLEMk _ _ h)) (by ext; simp [ofMkLEMk_comp]),
      fun h ↦ mk_le_mk_of_comm (P.ι.map (ofLE S T h)) (by rw [← Functor.map_comp, ofLE_arrow])⟩

/-- The embedding `subobjectOrderEmbedding` sends the subobject represented by a monomorphism `f`
to the subobject represented by `f` seen in `C`. -/
@[simp]
theorem subobjectOrderEmbedding_mk {X Y : P.FullSubcategory} (f : Y ⟶ X) [Mono f] :
    P.subobjectOrderEmbedding X (mk f) = mk (P.ι.map f) :=
  mk_eq_mk_of_comm _ _ (P.ι.mapIso (underlyingIso f))
    (by rw [Functor.mapIso_hom, ← Functor.map_comp, underlyingIso_hom_comp_eq_mk])

variable [P.IsClosedUnderSubobjects]

/-- **Subobjects in a full subcategory closed under subobjects.** If `P` is closed under
subobjects and its inclusion preserves monomorphisms, the subobjects of an object `X` of the full
subcategory are those of `X.obj` in the ambient category. -/
noncomputable def subobjectOrderIso (X : P.FullSubcategory) : Subobject X ≃o Subobject X.obj :=
  OrderIso.ofSurjective (P.subobjectOrderEmbedding X) fun T ↦
    ⟨mk (homMk T.arrow : (⟨T, P.prop_of_mono T.arrow X.property⟩ : P.FullSubcategory) ⟶ X),
      by simp⟩

/-- The isomorphism `subobjectOrderIso` sends the subobject represented by a monomorphism `f` to
the subobject represented by `f` seen in `C`. -/
@[simp]
theorem subobjectOrderIso_mk {X Y : P.FullSubcategory} (f : Y ⟶ X) [Mono f] :
    P.subobjectOrderIso X (mk f) = mk (P.ι.map f) :=
  P.subobjectOrderEmbedding_mk f

/-- The inverse of `subobjectOrderIso` sends the subobject represented by a monomorphism
`g : Y ⟶ X.obj` of `C` to the subobject represented by `g` seen in the full subcategory, whose
source `Y` satisfies `P` since `P` is closed under subobjects. -/
@[simp]
theorem subobjectOrderIso_symm_mk {X : P.FullSubcategory} {Y : C} (g : Y ⟶ X.obj) [Mono g] :
    (P.subobjectOrderIso X).symm (mk g) =
      mk (homMk g : (⟨Y, P.prop_of_mono g X.property⟩ : P.FullSubcategory) ⟶ X) :=
  (OrderIso.symm_apply_eq _).2 (by simp)

end CategoryTheory.ObjectProperty
