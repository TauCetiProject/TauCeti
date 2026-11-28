/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# The difference of orthogonal projections in a C⋆-ring

If `p` and `q` are star-orthogonal star projections of a C⋆-ring, then
`star (p - q) * (p - q) = p + q` is again a star projection, so the C⋆-identity gives
`‖p - q‖ ≤ 1` (`IsStarProjection.norm_sub_le_one`). On a Hilbert space, `p - q` is the
self-adjoint contraction acting as `1` on the range of `p`, as `-1` on the range of `q`, and as `0`
on the orthogonal complement of both.

## Main results

* `IsStarProjection.norm_sub_le_one`: `‖p - q‖ ≤ 1` for star-orthogonal star projections.
-/

public section

open scoped StarRing

/-- **The difference of orthogonal projections is a contraction**: `‖p - q‖ ≤ 1` for
star-orthogonal star projections `p` and `q` of a C⋆-ring, since
`star (p - q) * (p - q) = p + q` is a star projection. -/
theorem IsStarProjection.norm_sub_le_one {E : Type*} [NonUnitalNormedRing E] [StarRing E]
    [CStarRing E] {p q : E} (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p ⋆⟂ q) :
    ‖p - q‖ ≤ 1 := by
  have hsq : star (p - q) * (p - q) = p + q := by
    rw [star_sub, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, sub_mul, mul_sub, mul_sub,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, h.mul_eq_zero' hq.isSelfAdjoint,
      h.mul_eq_zero hq.isSelfAdjoint]
    abel
  have h1 := (h.isStarProjection_add hp hq).norm_le
  rw [← hsq, CStarRing.norm_star_mul_self] at h1
  nlinarith [norm_nonneg (p - q)]
