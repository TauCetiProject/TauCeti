/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.GroupTheory.Coprod.FreelyIndecomposable.Basic

/-!
# The Grushko decomposition of `ℤ² ∗ F₂`

The free product `ℤ² ∗ F₂` of the free abelian group of rank two and the free group of rank two
has a Grushko decomposition with one freely indecomposable factor `G₁ = ℤ²` and a free factor of
rank `q = 2`: the group `ℤ²` is nontrivial and commutative, hence freely indecomposable, and it is
not infinite cyclic.
-/

public section

open Monoid
open scoped Monoid.Coprod

namespace TauCeti.Examples.FreelyIndecomposable

/-- The group `ℤ²` is not infinite cyclic. -/
theorem isEmpty_int_prod_int_mulEquiv_int : IsEmpty (Multiplicative (ℤ × ℤ) ≃* Multiplicative ℤ) :=
  ⟨fun e => not_isAddCyclic_prod_of_infinite_nontrivial ℤ ℤ <|
    isCyclic_multiplicative_iff.1 <| isCyclic_of_surjective e.symm e.symm.surjective⟩

/-- The Grushko decomposition of `ℤ² ∗ F₂` with the single factor `ℤ²` and a free factor of
rank `2`. -/
def intProdIntCoprodFreeGroup :
    GrushkoDecomposition (Multiplicative (ℤ × ℤ) ∗ FreeGroup (Fin 2)) :=
  .coprodFreeGroup (isFreelyIndecomposable_of_isMulCommutative _)
    isEmpty_int_prod_int_mulEquiv_int 2

/-- The decomposition of `ℤ² ∗ F₂` has a single freely indecomposable factor. -/
theorem intProdIntCoprodFreeGroup_p : intProdIntCoprodFreeGroup.p = 1 :=
  GrushkoDecomposition.coprodFreeGroup_p ..

/-- The free factor of the decomposition of `ℤ² ∗ F₂` has rank `2`. -/
theorem intProdIntCoprodFreeGroup_q : intProdIntCoprodFreeGroup.q = 2 :=
  GrushkoDecomposition.coprodFreeGroup_q ..

/-- The freely indecomposable factor of the decomposition of `ℤ² ∗ F₂` is the image of `ℤ²`. -/
theorem intProdIntCoprodFreeGroup_factor (i : Fin intProdIntCoprodFreeGroup.p) :
    intProdIntCoprodFreeGroup.factor i =
      (Coprod.inl : Multiplicative (ℤ × ℤ) →* _ ∗ FreeGroup (Fin 2)).range :=
  GrushkoDecomposition.coprodFreeGroup_factor _ _ _ i

end TauCeti.Examples.FreelyIndecomposable
