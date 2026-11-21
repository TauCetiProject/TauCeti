/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.CoprodI

/-!
# Conjugacy of factor elements in an indexed free product

Two elements of the same factor `M i` of the indexed free product `Monoid.CoprodI M` of monoids
are conjugate in `CoprodI M` exactly when they are conjugate in `M i`: the canonical inclusion
`Monoid.CoprodI.of` preserves conjugacy, and projecting onto the `i`-th factor while killing all
other factors maps conjugate elements to conjugate elements and restricts to the identity on `M i`.
Elements of distinct factors `M i` and `M j` (`i ≠ j`) are conjugate in `CoprodI M` if and only if
both are trivial.

This is the indexed counterpart of `TauCeti.GroupTheory.Coprod.Conj` for binary free products
`M ∗ N`.

## Main results

* `Monoid.CoprodI.isConj_of_same_iff`: two elements of the same factor `M i` are conjugate in
  `CoprodI M` if and only if they are conjugate in `M i`.
* `Monoid.CoprodI.isConj_of_ne_iff`: elements of distinct factors `M i` and `M j` are conjugate in
  `CoprodI M` if and only if both are `1`.

## Implementation notes

`Monoid.CoprodI.isConj_of_same_iff` is a `simp` lemma of priority `high`, matching
`TauCeti.GroupTheory.Coprod.Conj`, so that in free products of groups it applies before
`isConj_iff` unfolds `IsConj`.
-/

public section

namespace Monoid.CoprodI

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

/-- Two elements of the same factor `M i` are conjugate in `CoprodI M` if and only if they are
conjugate in `M i`. -/
@[simp high]
theorem isConj_of_same_iff {i : ι} {x y : M i} :
    IsConj (of x : CoprodI M) (of y) ↔ IsConj x y := by
  classical
  refine ⟨fun h => ?_, of.map_isConj⟩
  simpa using (lift (Pi.mulSingle i (.id (M i)))).map_isConj h

/-- Elements of distinct factors `M i` and `M j` are conjugate in `CoprodI M` if and only if both
are `1`. -/
theorem isConj_of_ne_iff {i j : ι} (hij : i ≠ j) {x : M i} {y : M j} :
    IsConj (of x : CoprodI M) (of y) ↔ x = 1 ∧ y = 1 := by
  classical
  refine ⟨fun h => ⟨?_, ?_⟩, by rintro ⟨rfl, rfl⟩; simp⟩
  · have hx : IsConj x 1 := by
      simpa [Pi.mulSingle_eq_of_ne hij.symm] using
        (lift (Pi.mulSingle i (.id (M i)))).map_isConj h
    exact isConj_one_left.mp hx
  · have hy : IsConj 1 y := by
      simpa [Pi.mulSingle_eq_of_ne hij] using
        (lift (Pi.mulSingle j (.id (M j)))).map_isConj h
    exact isConj_one_right.mp hy

end Monoid.CoprodI
