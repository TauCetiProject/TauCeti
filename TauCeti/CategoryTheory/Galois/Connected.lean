/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.CategoryTheory.Galois.Basic

/-!
# Connected objects: invariance under equivalence and a fibre-functor criterion

`CategoryTheory.PreGaloisCategory.IsConnected` is defined by conditions on initial objects,
monomorphisms and isomorphisms alone, and an equivalence of categories preserves and reflects all
three. This file records the resulting transport statements: connectedness is invariant under
isomorphism inside a category, and an equivalence `F : C ⥤ D` makes `F.obj A` connected exactly
when `A` is.

The equivalence statements need no Galois axioms. Mathlib states connectedness for an object of
an arbitrary category and only later restricts to `PreGaloisCategory`, and that arbitrary
generality is what is used there; in particular the statements apply to a category that is merely
*equivalent* to a Galois category, which is how a connectedness criterion is transported to a
concrete category whose objects are not finite sets.

The last statement does use the Galois axioms: for a fibre functor `F` on a pre-Galois category,
an object whose fibre is nonempty and acted on transitively by `Aut F` is connected. This is the
converse of Mathlib's `FiberFunctor.isPretransitive_of_isConnected`.

## Main declarations

* `CategoryTheory.PreGaloisCategory.IsConnected.of_iso`: an object isomorphic to a connected
  object is connected.
* `CategoryTheory.Functor.preservesIsConnected_of_isEquivalence`: an equivalence carries connected
  objects to connected objects, as an instance of Mathlib's `PreservesIsConnected`.
* `CategoryTheory.Functor.isConnected_obj_iff`: connectedness of `F.obj A` is equivalent to
  connectedness of `A`.
* `CategoryTheory.PreGaloisCategory.FiberFunctor.isConnected_of_isPretransitive`: an object whose
  fibre is nonempty, with `Aut F` acting transitively on it, is connected.
-/

public section

universe v₁ v₂ u₁ u₂ w

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

/-- An object whose fibre under a fibre functor `F` is nonempty, and on which `Aut F` acts
transitively, is connected. Mathlib's `FiberFunctor.isPretransitive_of_isConnected` is the
converse. -/
theorem PreGaloisCategory.FiberFunctor.isConnected_of_isPretransitive [PreGaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (X : C) [Nonempty (F.obj X)]
    [MulAction.IsPretransitive (Aut F) (F.obj X)] :
    IsConnected X where
  notInitial h := not_initial_of_inhabited F (Classical.arbitrary (F.obj X)) h
  noTrivialComponent Z i _ hZ := by
    obtain ⟨z⟩ := (not_initial_iff_fiber_nonempty F Z).mp hZ
    have hinj : Function.Injective (F.map i) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
    have hsurj : Function.Surjective (F.map i) := fun x ↦ by
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) (F.map i z) x
      exact ⟨σ • z, by rw [← mulAction_naturality, hσ]⟩
    have : IsIso (F.map i) :=
      (ConcreteCategory.isIso_iff_bijective (F.map i)).mpr ⟨hinj, hsurj⟩
    exact isIso_of_reflects_iso i F

end CategoryTheory

end
