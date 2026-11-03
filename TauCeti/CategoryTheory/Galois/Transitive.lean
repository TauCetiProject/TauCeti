/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!
# Connected objects are those with a transitive fibre

Let `C` be a Galois category with fibre functor `F`. Mathlib shows that the automorphism group
`Aut F` acts transitively on the fibre of every connected object
(`CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected`). This file proves
the converse: an object whose fibre is nonempty and a transitive `Aut F`-set is connected. Thus,
for an object with nonempty fibre, connectedness is equivalent to transitivity of the action of
the fundamental group on its fibre, which is how connected objects are recognised on the side of
finite sets with a group action.

The proof is direct. A subobject `Y ⟶ X` with nonempty fibre has a fibre which is a nonempty
`Aut F`-stable subset of the fibre of `X`, by naturality of the action. If the action on the fibre
of `X` is transitive, that subset is everything, so the subobject is bijective on fibres and hence
an isomorphism, since fibre functors reflect isomorphisms.

## Main results

* `CategoryTheory.PreGaloisCategory.FiberFunctor.isConnected_of_isPretransitive`: an object with
  nonempty fibre on which `Aut F` acts transitively is connected.
* `CategoryTheory.PreGaloisCategory.FiberFunctor.isConnected_iff_isPretransitive`: in a Galois
  category, for an object with nonempty fibre, connectedness is transitivity of `Aut F` on the
  fibre.

## References

* H. W. Lenstra, *Galois theory for schemes*, Section 3.
-/

public section

universe u₁ u₂ w

namespace CategoryTheory.PreGaloisCategory

open Limits

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

/-- An object whose fibre is nonempty and a transitive `Aut F`-set is connected. -/
theorem FiberFunctor.isConnected_of_isPretransitive [PreGaloisCategory C] [FiberFunctor F] (X : C)
    [Nonempty (F.obj X)]
    [MulAction.IsPretransitive (Aut F) (F.obj X)] : IsConnected X where
  notInitial := (not_initial_iff_fiber_nonempty F X).mpr inferInstance
  noTrivialComponent Y i _ hY := by
    obtain ⟨y⟩ := (not_initial_iff_fiber_nonempty F Y).mp hY
    have hinj : Function.Injective (F.map i) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
    -- The image of the fibre of `Y` contains a point and is stable under `Aut F`.
    have hsurj : Function.Surjective (F.map i) := fun x ↦ by
      obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F) (F.map i y) x
      exact ⟨σ • y, (mulAction_naturality F σ i y).symm⟩
    have : IsIso (F.map i) := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
    exact isIso_of_reflects_iso i F

/-- **Connected objects are those with a transitive fibre.** In a Galois category, an object with
nonempty fibre is connected if and only if `Aut F` acts transitively on its fibre. -/
theorem FiberFunctor.isConnected_iff_isPretransitive [GaloisCategory C] [FiberFunctor F] (X : C)
    [Nonempty (F.obj X)] :
    IsConnected X ↔ MulAction.IsPretransitive (Aut F) (F.obj X) :=
  ⟨fun _ ↦ isPretransitive_of_isConnected F X, fun _ ↦ isConnected_of_isPretransitive F X⟩

end CategoryTheory.PreGaloisCategory
