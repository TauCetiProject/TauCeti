/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.StrictPositivity

/-!
# Strict positivity of `a a⋆` and `a⋆ a` for a unit `a`

In a star-ordered ring, the products `a a⋆` and `a⋆ a` of a unit `a` with its adjoint are
nonnegative and invertible, hence strictly positive. In particular the square of an invertible
self-adjoint element is strictly positive.

## Main results

* `Units.isStrictlyPositive_mul_star`: `a a⋆` is strictly positive.
* `Units.isStrictlyPositive_star_mul`: `a⋆ a` is strictly positive.
* `IsSelfAdjoint.isStrictlyPositive_mul_self`: `a a` is strictly positive for an invertible
  self-adjoint `a`.
-/

public section

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]

namespace Units

variable (a : Aˣ)

/-- The product `a a⋆` of a unit with its adjoint is strictly positive. -/
theorem isStrictlyPositive_mul_star : IsStrictlyPositive ((a : A) * star (a : A)) :=
  (a.isUnit.mul a.isUnit.star).isStrictlyPositive (mul_star_self_nonneg _)

/-- The product `a⋆ a` of a unit with its adjoint is strictly positive. -/
theorem isStrictlyPositive_star_mul : IsStrictlyPositive (star (a : A) * a) :=
  (a.isUnit.star.mul a.isUnit).isStrictlyPositive (star_mul_self_nonneg _)

end Units

/-- The square of an invertible self-adjoint element is strictly positive. -/
theorem IsSelfAdjoint.isStrictlyPositive_mul_self {a : A} (ha : IsSelfAdjoint a) (hu : IsUnit a) :
    IsStrictlyPositive (a * a) :=
  (hu.mul hu).isStrictlyPositive ha.mul_self_nonneg
