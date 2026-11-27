/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Orthogonal

/-!
# Conjugates of star projections

Conjugating a star projection `p` by an isometry `u`, that is `star u * u = 1`, gives the star
projection `u * p * star u` (`IsStarProjection.conjugate`); on a Hilbert space it is the
orthogonal projection onto the image under `u` of the range of `p`. If moreover `p * u * p = 0`,
that is `u` maps the range of `p` into its orthogonal complement, then `p` and `u * p * star u`
are star-orthogonal (`IsSelfAdjoint.isStarOrtho_conjugate`).

A self-adjoint involution `J` is such an isometry, with `star J = J`: when the range of `p` is
totally isotropic for the form `(v, w) ↦ ⟨v, J w⟩`, that is `p * J * p = 0`, the projections `p`
and `J * p * J` are orthogonal.

## Main results

* `IsStarProjection.conjugate`: `u * p * star u` is a star projection when `star u * u = 1`.
* `IsSelfAdjoint.isStarOrtho_conjugate`: `p ⋆⟂ u * p * star u` when `p` is self-adjoint and
  `p * u * p = 0`.
-/

public section

open scoped StarRing

variable {R : Type*}

/-- **The conjugate of a star projection by an isometry is a star projection**: if
`star u * u = 1`, then `u * p * star u` is a star projection. -/
theorem IsStarProjection.conjugate [Monoid R] [StarMul R] {p u : R} (hp : IsStarProjection p)
    (hu : star u * u = 1) : IsStarProjection (u * p * star u) where
  isIdempotentElem := by
    rw [IsIdempotentElem]
    calc u * p * star u * (u * p * star u) = u * (p * (star u * u) * p) * star u := by
          simp only [mul_assoc]
      _ = u * p * star u := by rw [hu, mul_one, hp.isIdempotentElem.eq]
  isSelfAdjoint := hp.isSelfAdjoint.conjugate u

/-- **A self-adjoint `p` with `p * u * p = 0` is star-orthogonal to its conjugate**
`u * p * star u`. -/
theorem IsSelfAdjoint.isStarOrtho_conjugate [NonUnitalSemiring R] [StarRing R] {p u : R}
    (hp : IsSelfAdjoint p) (h : p * u * p = 0) : p ⋆⟂ u * p * star u :=
  (hp.isStarOrtho_iff_mul_eq_zero (hp.conjugate u)).2 <| by
    rw [← mul_assoc, ← mul_assoc, h, zero_mul]
