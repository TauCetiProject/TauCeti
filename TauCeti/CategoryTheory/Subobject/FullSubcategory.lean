/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Subobjects in a full subcategory closed under subobjects

Let `P` be a property of objects of a category `C` that is closed under subobjects and whose full
subcategory has its inclusion preserving monomorphisms, for instance the finitely generated modules
over a left Noetherian ring. Then the subobjects of an object `X` of the full subcategory are the
subobjects of `X` in `C` (`CategoryTheory.ObjectProperty.subobjectOrderIso`). Lattice-theoretic
invariants of subobject lattices, such as the length of an object, are therefore the same in the
full subcategory and in `C`.

## Main definitions

* `CategoryTheory.ObjectProperty.subobjectOrderIso`: the order isomorphism
  `Subobject X ≃o Subobject X.obj` for `X : P.FullSubcategory`.

## Implementation notes

The isomorphism sends a subobject `S` of `X` to the subobject of `X.obj` represented by the
inclusion of `S` into `C`. Its inverse sends a subobject `T` of `X.obj`, which satisfies `P` since
`P` is closed under subobjects, to the subobject of `X` represented by the arrow of `T` seen in the
full subcategory, a monomorphism since the inclusion is faithful.

## References

* [Stacks, Tag 001D](https://stacks.math.columbia.edu/tag/001D), for full subcategories.
-/

public section

namespace CategoryTheory.ObjectProperty

open Subobject

universe v u

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- A morphism of the full subcategory is a monomorphism as soon as it is one in `C`. -/
instance mono_homMk {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) [Mono f] : Mono (homMk f) :=
  P.ι.mono_of_mono_map ‹_›

variable [P.IsClosedUnderSubobjects] [P.ι.PreservesMonomorphisms]

/-- The subobject of `X` represented by the arrow of a subobject `T` of `X.obj`, whose source
satisfies `P` since `P` is closed under subobjects. -/
private noncomputable def liftSubobject {X : P.FullSubcategory} (T : Subobject X.obj) :
    Subobject X :=
  mk (homMk T.arrow : (⟨T, P.prop_of_mono T.arrow X.property⟩ : P.FullSubcategory) ⟶ X)

/-- **Subobjects in a full subcategory closed under subobjects.** If `P` is closed under
subobjects and its inclusion preserves monomorphisms, the subobjects of an object `X` of the full
subcategory are those of `X.obj` in the ambient category. -/
noncomputable def subobjectOrderIso (X : P.FullSubcategory) : Subobject X ≃o Subobject X.obj :=
  Equiv.toOrderIso
    { toFun S := mk (P.ι.map S.arrow)
      invFun := P.liftSubobject
      left_inv S := mk_eq_of_comm _ (P.isoMk (underlyingIso (P.ι.map S.arrow)))
        (by ext; exact underlyingIso_hom_comp_eq_mk _)
      right_inv T := mk_eq_of_comm _ (P.ι.mapIso (underlyingIso _))
        (P.ι.congr_map (underlyingIso_hom_comp_eq_mk (homMk T.arrow :
          (⟨T, P.prop_of_mono T.arrow X.property⟩ : P.FullSubcategory) ⟶ X))) }
    (fun S T h ↦ mk_le_mk_of_comm (P.ι.map (ofLE S T h)) (by rw [← Functor.map_comp, ofLE_arrow]))
    fun S T h ↦ mk_le_mk_of_comm (homMk (ofLE S T h)) (by ext; simp)

end CategoryTheory.ObjectProperty
