/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import TauCeti.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Topology.Category.TopCat.WeakEquivalence

/-!
# Weak equivalences of simplicial sets

A morphism `f : X ⟶ Y` of simplicial sets is a *weak equivalence* if its geometric realization
`|f| : |X| → |Y|` is a weak homotopy equivalence: it induces a bijection on path components and on
every homotopy group at every base point. These are the weak equivalences of the Kan–Quillen model
structure on `SSet`, whose cofibrations (the monomorphisms) and fibrations (the Kan fibrations,
with the right lifting property with respect to the horn inclusions) are Mathlib's scoped
instances in `SSet.modelCategoryQuillen`. This file adds the matching scoped
`CategoryWithWeakEquivalences` instance, so that `HomotopicalAlgebra.WeakEquivalence`,
`HomotopicalAlgebra.trivialCofibrations` and `HomotopicalAlgebra.trivialFibrations` refer to the
Kan–Quillen classes.

The weak equivalences are the inverse image under realization of the weak homotopy equivalences of
`TopCat`, so they inherit two out of three, retract stability and the isomorphisms from
`TauCeti.TopCat.weakEquivalences`. Every morphism between standard simplices `Δ[n] ⟶ Δ[m]` is a weak
equivalence, the realizations of standard simplices being contractible; in particular every `Δ[n]`
is weakly contractible.

## Main declarations

* `SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences`: the scoped instance, with
  `SSet.modelCategoryQuillen.weakEquivalences_eq` identifying the class.
* `SSet.modelCategoryQuillen.weakEquivalence_iff`: a morphism is a weak equivalence exactly when its
  realization is a weak homotopy equivalence.
* `SSet.modelCategoryQuillen.weakEquivalence_of_stdSimplex`: morphisms between standard simplices
  are weak equivalences.

## References

* D. Quillen, *Homotopical algebra*, Lecture Notes in Mathematics 43, Springer, 1967, Chapter II,
  Section 3.
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section I.11.
-/

public section

open CategoryTheory MorphismProperty HomotopicalAlgebra

open scoped Simplicial

universe u

namespace SSet.modelCategoryQuillen

/-- The weak equivalences for the Kan–Quillen model category structure on `SSet` are the
morphisms whose geometric realization is a weak homotopy equivalence. -/
scoped instance instCategoryWithWeakEquivalences : CategoryWithWeakEquivalences SSet.{u} where
  weakEquivalences := TauCeti.TopCat.weakEquivalences.inverseImage toTop

/-- The weak equivalences of simplicial sets are the inverse image under geometric realization of
the weak homotopy equivalences of `TopCat`. -/
lemma weakEquivalences_eq :
    weakEquivalences SSet.{u} = TauCeti.TopCat.weakEquivalences.inverseImage toTop :=
  rfl

/-- A morphism of simplicial sets is a weak equivalence exactly when its geometric realization is
a weak homotopy equivalence. -/
lemma weakEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ (toTop.map f).hom.IsWeakHomotopyEquivalence := by
  rw [HomotopicalAlgebra.weakEquivalence_iff, weakEquivalences_eq, inverseImage_iff,
    TauCeti.TopCat.mem_weakEquivalences_iff]

instance : (weakEquivalences SSet.{u}).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_eq]
  infer_instance

instance : (weakEquivalences SSet.{u}).IsMultiplicative := by
  rw [weakEquivalences_eq]
  infer_instance

instance : (weakEquivalences SSet.{u}).IsStableUnderRetracts := by
  rw [weakEquivalences_eq]
  infer_instance

/-- Every morphism between standard simplices is a weak equivalence: the geometric realizations of
`Δ[n]` and `Δ[m]` are contractible. In particular, `Δ[n] ⟶ Δ[0]` is a weak equivalence, so every
standard simplex is weakly contractible. -/
theorem weakEquivalence_of_stdSimplex {n m : SimplexCategory}
    (f : stdSimplex.{u}.obj n ⟶ stdSimplex.obj m) : WeakEquivalence f := by
  rw [weakEquivalence_iff]
  exact ContinuousMap.isWeakHomotopyEquivalence_of_contractibleSpace _

end SSet.modelCategoryQuillen
