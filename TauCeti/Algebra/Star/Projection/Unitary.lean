/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
import TauCeti.Algebra.Group.Idempotent

/-!
# Unitary conjugation of star projections

Unitary conjugation preserves and reflects star projections in any star monoid.

## Main results

* `IsStarProjection.star_right_conjugate`, `IsStarProjection.star_left_conjugate`,
  `isStarProjection_star_right_conjugate_iff`, `isStarProjection_star_left_conjugate_iff`:
  `u * p * star u` and `star u * p * u` are star projections iff `p` is a star projection.
-/

public section

namespace IsStarProjection

/-- Unitary conjugation `u * p * star u` preserves star projections. -/
theorem star_right_conjugate {R : Type*} [Monoid R] [StarMul R] {p : R}
    (hp : IsStarProjection p) (u : unitary R) :
    IsStarProjection ((u : R) * p * star (u : R)) :=
  ⟨hp.isIdempotentElem.mul_mul_of_mul_eq_one (Unitary.coe_star_mul_self u),
    hp.isSelfAdjoint.conjugate (u : R)⟩

/-- Unitary conjugation `star u * p * u` preserves star projections. -/
theorem star_left_conjugate {R : Type*} [Monoid R] [StarMul R] {p : R}
    (hp : IsStarProjection p) (u : unitary R) :
    IsStarProjection (star (u : R) * p * (u : R)) := by
  simpa using hp.star_right_conjugate (star u)

/-- An element `u * p * star u` conjugated by a unitary `u` is a star projection iff `p` is. -/
@[simp]
theorem _root_.isStarProjection_star_right_conjugate_iff {R : Type*} [Monoid R] [StarMul R]
    (u : unitary R) {p : R} :
    IsStarProjection ((u : R) * p * star (u : R)) ↔ IsStarProjection p :=
  ⟨fun h ↦ by
    have h' := h.star_left_conjugate u
    rwa [← mul_assoc, ← mul_assoc, Unitary.coe_star_mul_self, one_mul, mul_assoc,
      Unitary.coe_star_mul_self, mul_one] at h',
    fun h ↦ h.star_right_conjugate u⟩

/-- An element `star u * p * u` conjugated by a unitary `u` is a star projection iff `p` is. -/
@[simp]
theorem _root_.isStarProjection_star_left_conjugate_iff {R : Type*} [Monoid R] [StarMul R]
    (u : unitary R) {p : R} :
    IsStarProjection (star (u : R) * p * (u : R)) ↔ IsStarProjection p := by
  simpa using isStarProjection_star_right_conjugate_iff (star u) (p := p)

end IsStarProjection
