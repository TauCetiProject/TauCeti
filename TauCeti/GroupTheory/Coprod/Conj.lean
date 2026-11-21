/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Conjugacy of factor elements in a free product

Two elements of a factor of the free product `M ∗ N` of monoids are conjugate in `M ∗ N` exactly
when they are conjugate in that factor. The inclusion of the factor preserves conjugacy, and the
projection of `M ∗ N` onto the factor, which kills the other factor, maps conjugate elements to
conjugate elements and restricts to the identity on the factor. For instance, distinct elements
of an abelian factor are never conjugate in the free product. An element of one factor is
conjugate to an element of the other factor only when both are trivial.

## Main results

* `Monoid.Coprod.isConj_inl_iff`, `Monoid.Coprod.isConj_inr_iff`: two elements of a factor are
  conjugate in the free product if and only if they are conjugate in the factor.
* `Monoid.Coprod.isConj_inl_inr_iff`, `Monoid.Coprod.isConj_inr_inl_iff`: elements of different
  factors are conjugate in the free product if and only if both are trivial.

## Implementation notes

All four results are `simp` lemmas of priority `high`, so that in free products of groups they apply
before `isConj_iff` unfolds `IsConj`.
-/

public section

namespace Monoid.Coprod

variable {M N : Type*} [Monoid M] [Monoid N]

/-- Two elements of `M` are conjugate in the free product `M ∗ N` if and only if they are
conjugate in `M`. -/
@[simp high]
theorem isConj_inl_iff {a b : M} : IsConj (inl a : M ∗ N) (inl b) ↔ IsConj a b :=
  ⟨fun h => by simpa using fst.map_isConj h, (inl : M →* M ∗ N).map_isConj⟩

/-- Two elements of `N` are conjugate in the free product `M ∗ N` if and only if they are
conjugate in `N`. -/
@[simp high]
theorem isConj_inr_iff {a b : N} : IsConj (inr a : M ∗ N) (inr b) ↔ IsConj a b :=
  ⟨fun h => by simpa using snd.map_isConj h, (inr : N →* M ∗ N).map_isConj⟩

/-- An element of `M` and an element of `N` are conjugate in the free product `M ∗ N` if and
only if both are trivial. -/
@[simp high]
theorem isConj_inl_inr_iff {a : M} {b : N} : IsConj (inl a : M ∗ N) (inr b) ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨by simpa using fst.map_isConj h, by simpa using snd.map_isConj h⟩,
    fun ⟨ha, hb⟩ => by simp [ha, hb]⟩

/-- An element of `N` and an element of `M` are conjugate in the free product `M ∗ N` if and
only if both are trivial. -/
@[simp high]
theorem isConj_inr_inl_iff {a : N} {b : M} : IsConj (inr a : M ∗ N) (inl b) ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨by simpa using snd.map_isConj h, by simpa using fst.map_isConj h⟩,
    fun ⟨ha, hb⟩ => by simp [ha, hb]⟩

end Monoid.Coprod
