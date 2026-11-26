/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Norm bounds for sums of positive squares in C⋆-algebras

In any (possibly nonunital) complex C⋆-algebra `A` equipped with the spectral order, `star x * x`
and `star y * y` are nonnegative, so `0 ≤ star x * x ≤ star x * x + star y * y`. Monotonicity of
the norm on nonnegative elements (`CStarAlgebra.norm_le_norm_of_le_of_nonneg`) combined with the
C⋆-identity `‖star x * x‖ = ‖x‖ ^ 2` gives `‖x‖ ^ 2 ≤ ‖star x * x + star y * y‖` and
`‖x‖ ≤ √‖star x * x + star y * y‖` without assuming unitality or commutativity.

## Main results

* `TauCeti.sq_norm_le_norm_star_mul_self_add` and `TauCeti.norm_le_sqrt_norm_star_mul_self_add`:
  `‖x‖ ^ 2 ≤ ‖star x * x + star y * y‖` and `‖x‖ ≤ √‖star x * x + star y * y‖` for all `x, y : A`.
* `IsSelfAdjoint.sq_norm_le_norm_mul_self_add` and `IsSelfAdjoint.norm_le_sqrt_norm_mul_self_add`:
  for self-adjoint `x, y : A`, `‖x‖ ^ 2 ≤ ‖x * x + y * y‖` and `‖x‖ ≤ √‖x * x + y * y‖`.
-/

public section

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- In any C⋆-algebra, adding a positive square `star y * y` cannot decrease the norm below
`‖star x * x‖ = ‖x‖ ^ 2`. -/
theorem sq_norm_le_norm_star_mul_self_add (x y : A) :
    ‖x‖ ^ 2 ≤ ‖star x * x + star y * y‖ := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  rw [sq, ← CStarRing.norm_star_mul_self]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (le_add_of_nonneg_right (star_mul_self_nonneg y)) (star_mul_self_nonneg x)

/-- Square-root form of `sq_norm_le_norm_star_mul_self_add`: `‖x‖ ≤ √‖star x * x + star y * y‖`. -/
theorem norm_le_sqrt_norm_star_mul_self_add (x y : A) :
    ‖x‖ ≤ √‖star x * x + star y * y‖ :=
  Real.le_sqrt_of_sq_le (sq_norm_le_norm_star_mul_self_add x y)

end TauCeti

section IsSelfAdjoint

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- For self-adjoint elements `x, y` of a C⋆-algebra, `‖x‖ ^ 2 ≤ ‖x * x + y * y‖`. -/
theorem IsSelfAdjoint.sq_norm_le_norm_mul_self_add {x y : A} (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) : ‖x‖ ^ 2 ≤ ‖x * x + y * y‖ := by
  simpa only [hx.star_eq, hy.star_eq] using TauCeti.sq_norm_le_norm_star_mul_self_add x y

/-- For self-adjoint elements `x, y` of a C⋆-algebra, `‖x‖ ≤ √‖x * x + y * y‖`. -/
theorem IsSelfAdjoint.norm_le_sqrt_norm_mul_self_add {x y : A} (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) : ‖x‖ ≤ √‖x * x + y * y‖ :=
  Real.le_sqrt_of_sq_le (hx.sq_norm_le_norm_mul_self_add hy)

end IsSelfAdjoint
