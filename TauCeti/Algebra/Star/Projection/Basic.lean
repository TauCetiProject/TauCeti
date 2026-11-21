/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
import TauCeti.Algebra.Ring.Idempotent.Basic

/-!
# Reflections of star projections

For a star projection `p` in a star ring, the reflection `1 - 2 * p` (the negative of the
symmetry `2 * p - 1` in Mathlib's `IsStarProjection.two_mul_sub_one_mem_unitary`) is self-adjoint
and squares to `1` (`IsIdempotentElem.one_sub_two_mul_mul_self`), so it lies in `unitary A`.

## Main declarations

* `IsStarProjection.isSelfAdjoint_one_sub_two_mul`: `1 - 2 * p` is self-adjoint.
* `IsStarProjection.one_sub_two_mul_mem_unitary`: `1 - 2 * p ∈ unitary A`.

## References

* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, Chapter 2,
  Lemma 2.1.4.
-/

public section

namespace IsStarProjection

section NonAssocStarRing

variable {A : Type*} [NonAssocRing A] [StarRing A] {p : A}

/-- For a star projection `p`, the reflection `1 - 2 * p` is self-adjoint. -/
theorem isSelfAdjoint_one_sub_two_mul (hp : IsStarProjection p) : IsSelfAdjoint (1 - 2 * p) := by
  rw [two_mul]
  exact .sub (.one A) (hp.isSelfAdjoint.add hp.isSelfAdjoint)

end NonAssocStarRing

section StarRing

variable {A : Type*} [Ring A] [StarRing A] {p : A}

/-- For a star projection `p`, the reflection `1 - 2 * p` is a unitary element. -/
theorem one_sub_two_mul_mem_unitary (hp : IsStarProjection p) : 1 - 2 * p ∈ unitary A := by
  rw [Unitary.mem_iff, hp.isSelfAdjoint_one_sub_two_mul.star_eq,
    hp.isIdempotentElem.one_sub_two_mul_mul_self]
  exact ⟨rfl, rfl⟩

end StarRing

end IsStarProjection
