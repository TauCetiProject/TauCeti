/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift

/-!
# Universe lifts of nerves

The nerve of `AsSmall.{w} C` is canonically isomorphic to the universe lift
`SSet.uliftFunctor.obj (nerve C)` (`CategoryTheory.nerve.asSmallIso`).

## Main declarations

* `CategoryTheory.nerve.asSmallIso`: isomorphism
  `nerve (AsSmall.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C)`.
* `CategoryTheory.nerve.asSmallIso_hom_app`, `CategoryTheory.nerve.asSmallIso_inv_app`,
  `CategoryTheory.nerve.asSmallIso_inv_app_ulift_nerveEquiv_symm`: action on simplices and
  `0`-simplices.
-/

public section

open CategoryTheory Opposite Simplicial

universe w v u

namespace CategoryTheory.nerve

/-- The nerve of `AsSmall.{w} C` is isomorphic to the universe lift of `nerve C`. -/
def asSmallIso (C : Type u) [Category.{v} C] :
    nerve (AsSmall.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C) where
  hom := { app m := ↾fun s ↦ ULift.up ((AsSmall.down.mapComposableArrows m.unop.len).obj s) }
  inv := { app m := ↾fun s ↦ (AsSmall.up.mapComposableArrows m.unop.len).obj s.down }

@[simp] lemma asSmallIso_hom_app {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve (AsSmall.{w} C)) _⦋n⦌) :
    (asSmallIso.{w} C).hom.app (op ⦋n⦌) s =
      (nerve C).uliftFunctorObjEquiv (op ⦋n⦌)
        (objEquiv.symm ((AsSmall.down.mapComposableArrows n).obj (objEquiv s))) := by
  rw [objEquiv_eq, objEquiv_symm_eq]
  exact ULift.ext ((nerve C).uliftFunctorObjEquiv_down _ _).symm

@[simp] lemma asSmallIso_inv_app {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (SSet.uliftFunctor.{w, max u v}.obj (nerve C)) _⦋n⦌) :
    (asSmallIso.{w} C).inv.app (op ⦋n⦌) s =
      objEquiv.symm ((AsSmall.up.mapComposableArrows n).obj
        (objEquiv (((nerve C).uliftFunctorObjEquiv (op ⦋n⦌)).symm s))) := by
  rw [SSet.uliftFunctorObjEquiv_symm_eq_down, objEquiv_eq, objEquiv_symm_eq]
  -- Unfolds `asSmallIso.inv` (`TypeCat.ofHom_apply`) to
  -- `(AsSmall.up.mapComposableArrows n).obj s.down`.
  rfl

-- Not `@[simp]`: `asSmallIso_inv_app` already simplifies the LHS (`simpNF`).
lemma asSmallIso_inv_app_ulift_nerveEquiv_symm (C : Type u) [Category.{v} C] (X : C) :
    (asSmallIso.{w} C).inv.app (op ⦋0⦌)
        ((nerve C).uliftFunctorObjEquiv (op ⦋0⦌) (nerveEquiv.symm X)) =
      nerveEquiv.symm ((AsSmall.up : C ⥤ AsSmall.{w} C).obj X) := by
  rw [← objEquiv_symm_eq (nerveEquiv.symm X), asSmallIso_inv_app, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, Functor.mapComposableArrows_obj_nerveEquiv_symm, objEquiv_symm_eq]

end CategoryTheory.nerve
