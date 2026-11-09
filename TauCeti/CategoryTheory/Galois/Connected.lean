/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Basic

/-!
# Connected objects are invariant under equivalence

`CategoryTheory.PreGaloisCategory.IsConnected` is defined by conditions on initial objects,
monomorphisms and isomorphisms alone, and an equivalence of categories preserves and reflects all
three. This file records the resulting transport statements: connectedness is invariant under
isomorphism inside a category, and an equivalence `F : C ⥤ D` makes `F.obj A` connected exactly
when `A` is.

None of this needs the Galois axioms. Mathlib states connectedness for an object of an arbitrary
category and only later restricts to `PreGaloisCategory`, and that arbitrary generality is what is
used here; in particular the statements apply to a category that is merely *equivalent* to a
Galois category, which is how a connectedness criterion is transported to a concrete category
whose objects are not finite sets.

## Main declarations

* `CategoryTheory.PreGaloisCategory.IsConnected.of_iso`: an object isomorphic to a connected
  object is connected.
* `CategoryTheory.Functor.preservesIsConnected_of_isEquivalence`: an equivalence carries connected
  objects to connected objects, as an instance of Mathlib's `PreservesIsConnected`.
* `CategoryTheory.Functor.isConnected_obj_iff`: connectedness of `F.obj A` is equivalent to
  connectedness of `A`.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits PreGaloisCategory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- An object isomorphic to a connected object is connected. -/
theorem PreGaloisCategory.IsConnected.of_iso {A B : C} (e : A ≅ B) [IsConnected A] :
    IsConnected B where
  notInitial h := IsConnected.notInitial (h.ofIso e.symm)
  noTrivialComponent Y i _ hni := by
    have : IsIso (i ≫ e.inv) := IsConnected.noTrivialComponent Y (i ≫ e.inv) hni
    exact IsIso.of_isIso_comp_right i e.inv

namespace Functor

variable (F : C ⥤ D) [F.IsEquivalence]

/-- An equivalence of categories carries connected objects to connected objects. -/
instance preservesIsConnected_of_isEquivalence : PreservesIsConnected F where
  preserves {A} _ :=
    { notInitial h := IsConnected.notInitial (h.isInitialOfObj F A)
      noTrivialComponent Y i _ hni := by
        -- Write the subobject `Y` as the image of an object of `C`, and pull `i` back along `F`.
        let e := F.objObjPreimageIso Y
        have : Mono (F.map (F.preimage (e.hom ≫ i))) := by rw [map_preimage]; infer_instance
        have : Mono (F.preimage (e.hom ≫ i)) := F.mono_of_mono_map this
        have : IsIso (F.preimage (e.hom ≫ i)) := IsConnected.noTrivialComponent _ _
          fun h => hni (IsInitial.ofIso (h.isInitialObj F _) e)
        have : IsIso (e.hom ≫ i) := by rw [← map_preimage F (e.hom ≫ i)]; infer_instance
        exact IsIso.of_isIso_comp_left e.hom i }

/-- **Connectedness transports along an equivalence of categories**: for an equivalence
`F : C ⥤ D`, an object `A` of `C` is connected exactly when `F.obj A` is. -/
@[simp]
theorem isConnected_obj_iff (A : C) : IsConnected (F.obj A) ↔ IsConnected A := by
  refine ⟨fun _ => ?_, fun _ => PreservesIsConnected.preserves⟩
  exact
    { notInitial h := IsConnected.notInitial (h.isInitialObj F A)
      noTrivialComponent Y i _ hni := by
        have : IsIso (F.map i) := IsConnected.noTrivialComponent _ (F.map i)
          fun h => hni (h.isInitialOfObj F Y)
        exact isIso_of_reflects_iso i F }

end Functor

end CategoryTheory

end
