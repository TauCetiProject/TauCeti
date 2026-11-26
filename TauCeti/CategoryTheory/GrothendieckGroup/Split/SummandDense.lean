/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Functor.SummandDense
public import TauCeti.CategoryTheory.GrothendieckGroup.Split

/-!
# Split `K₀` and summand-dense functors

Two objects `X` and `Y` have the same class in the split Grothendieck group of `D` exactly when
`X ⊞ W ≅ Y ⊞ W` for some object `W` (`TauCeti.SplitK0.of_eq_of_iff`). If a functor `T : C ⥤ D`
is summand-dense, so that every object of `D` is a direct summand of an object `T P`, the common
summand `W` can be taken of the form `T P`: choose `W'` with `W ⊞ W' ≅ T P` and add `W'` to both
sides. This is the case of the essential image of `T` in
`TauCeti.SplitK0.of_eq_of_iff_of_forall_exists_biprod`.

This is how equalities in `K₀(D)` are lifted to isomorphisms in the image of `T`, as in the
exactness of `K₀(T) → K₀(C) → K₀(D)` for the relative group `K₀(T)` of a summand-dense functor.
For extension of scalars along a ring homomorphism `R → S` it says that two finitely generated
projective `S`-modules with the same class become isomorphic after adding a free module `Sⁿ`.

## Main results

* `TauCeti.SplitK0.of_eq_of_iff_of_isSummandDense`: for summand-dense `T`, `[X] = [Y]` in split
  `K₀` of `D` if and only if `X ⊞ T P ≅ Y ⊞ T P` for some object `P` of `C`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 2.17.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
  [HasZeroObject D] [HasBinaryBiproducts D] [EssentiallySmall.{w} D]

namespace SplitK0

/-- **Stable isomorphisms are realised in the image of a summand-dense functor**: if `T` is
summand-dense, two objects of `D` have the same class in split `K₀` exactly when they become
isomorphic after adding an object `T P`. -/
theorem of_eq_of_iff_of_isSummandDense (T : C ⥤ D) [T.IsSummandDense] {X Y : D} :
    (of X : SplitK0 D) = of Y ↔ ∃ P : C, Nonempty (X ⊞ T.obj P ≅ Y ⊞ T.obj P) := by
  rw [of_eq_of_iff_of_forall_exists_biprod T.essImage
    Functor.IsSummandDense.exists_biprod_mem_essImage]
  -- An object `B ≅ T P` of the essential image may be replaced by `T P` itself.
  exact ⟨fun ⟨_, ⟨P, ⟨e⟩⟩, ⟨f⟩⟩ => ⟨P, ⟨biprod.mapIso (Iso.refl X) e ≪≫ f ≪≫
    biprod.mapIso (Iso.refl Y) e.symm⟩⟩, fun ⟨P, h⟩ => ⟨T.obj P, T.obj_mem_essImage P, h⟩⟩

end SplitK0

end TauCeti
