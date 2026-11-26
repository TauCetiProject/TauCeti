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

Two elements of a factor `M i` of the indexed free product `Monoid.CoprodI M` of monoids are
conjugate in `CoprodI M` if and only if they are conjugate in `M i`: the canonical retraction onto
the `i`-th factor, which kills all other factors, maps conjugate elements to conjugate elements and
restricts to the identity on `M i`. Elements of distinct factors are conjugate only when both are
`1`.

## Main results

* `Monoid.CoprodI.isConj_of_iff`: two elements of `M i` are conjugate in `CoprodI M` if and only
  if they are conjugate in `M i`.
* `Monoid.CoprodI.isConj_of_of_ne`: elements of distinct factors are conjugate in `CoprodI M` if
  and only if both are `1`.
* `Monoid.CoprodI.eq_of_isConj_of`: if a nonidentity element of `M i` is conjugate in `CoprodI M`
  to an element of `M j`, then `i = j`.
-/

public section

namespace Monoid.CoprodI

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

/-- Two elements of the same factor `M i` are conjugate in `CoprodI M` if and only if they are
conjugate in `M i`.

Not `@[simp]`: when the factors are groups, `isConj_iff` simplifies the left-hand side. -/
theorem isConj_of_iff {i : ι} {x y : M i} :
    IsConj (of x : CoprodI M) (of y) ↔ IsConj x y := by
  refine ⟨fun h ↦ ?_, of.map_isConj⟩
  classical
  simpa using (lift (Pi.mulSingle i (.id (M i)))).map_isConj h

/-- Elements from distinct factors of `CoprodI M` are conjugate if and only if both are `1`. -/
theorem isConj_of_of_ne {i j : ι} (hij : i ≠ j) {x : M i} {y : M j} :
    IsConj (of x : CoprodI M) (of y) ↔ x = 1 ∧ y = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · classical
    have hx : IsConj x 1 := by
      simpa [Pi.mulSingle_eq_of_ne hij.symm] using
        (lift (Pi.mulSingle i (.id (M i)))).map_isConj h
    have hy : IsConj 1 y := by
      simpa [Pi.mulSingle_eq_of_ne hij] using
        (lift (Pi.mulSingle j (.id (M j)))).map_isConj h
    exact ⟨isConj_one_left.mp hx, isConj_one_right.mp hy⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- If a nonidentity element of `M i` is conjugate in `CoprodI M` to an element of `M j`, then
`i = j`. -/
theorem eq_of_isConj_of {i j : ι} {x : M i} {y : M j} (hx : x ≠ 1)
    (h : IsConj (of x : CoprodI M) (of y)) : i = j := by
  by_contra hij
  exact hx ((isConj_of_of_ne hij).mp h).1

end Monoid.CoprodI
