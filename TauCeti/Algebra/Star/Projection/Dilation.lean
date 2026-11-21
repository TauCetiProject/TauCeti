/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Tactic.NoncommRing
public import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Projection dilations in a star ring

Let `q` be a star projection in a star ring and `u` an element with `star u * u = q` and
`q * u = 0`. For a bounded operator `u` on a Hilbert space, `u` maps the range of `q`
isometrically onto a subspace orthogonal to it. For self-adjoint `c` and `d` in the corner
`q R q` with `c * d = d * c` and `d * d = c - c * c`, the element

`projectionDilation q u c d = c + d * star u + u * d + u * (q - c) * star u`

is a star projection whose compression `q * _ * q` is `q * c * q`. Relative to the orthogonal
pieces `q` and `u * star u`, it is the block operator `[[c, d], [d, q - c]]`. In a C⋆-algebra,
taking `d` to be the square root of `c - c * c` shows that every positive contraction of the
corner is the compression of a star projection. On an infinite-dimensional Hilbert space this
is how positive contractions are shown to be weak operator limits of orthogonal projections.

## Main definitions

* `TauCeti.projectionDilation q u c d`: the element
  `c + d * star u + u * d + u * (q - c) * star u`.

## Main statements

* `TauCeti.isIdempotentElem_projectionDilation`: the projection dilation is idempotent under
  ring relations between `q`, `u`, `c` and `d` alone.
* `TauCeti.isStarProjection_projectionDilation`: under the hypotheses above, the projection
  dilation is a star projection.
* `TauCeti.mul_projectionDilation_mul`: if `q` is self-adjoint and `q * u = 0`, the compression
  of the projection dilation by `q` is `q * c * q`.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] [StarRing R]

/-- The **projection dilation** `c + d * star u + u * d + u * (q - c) * star u`. When `q` is a
star projection, `star u * u = q`, `q * u = 0`, and `c`, `d` are self-adjoint commuting elements
of the corner of `q` with `d * d = c - c * c`, this is the block operator `[[c, d], [d, q - c]]`
relative to `q` and `u * star u`. It is then a star projection
(`TauCeti.isStarProjection_projectionDilation`) with compression `q * c * q`
(`TauCeti.mul_projectionDilation_mul`). -/
def projectionDilation (q u c d : R) : R :=
  c + d * star u + u * d + u * (q - c) * star u

/-- Unfold the projection dilation. -/
theorem projectionDilation_def (q u c d : R) :
    projectionDilation q u c d = c + d * star u + u * d + u * (q - c) * star u :=
  (rfl)

/-- The compression of a projection dilation by `q` is `q * c * q`. -/
theorem mul_projectionDilation_mul {q u : R} (hq : IsSelfAdjoint q) (hqu : q * u = 0)
    (c d : R) : q * projectionDilation q u c d * q = q * c * q := by
  have huq : star u * q = 0 := hq.star_mul_eq_zero_of_mul_eq_zero hqu
  calc q * projectionDilation q u c d * q
      = q * c * q + q * d * (star u * q) + (q * u) * d * q
          + (q * u) * (q - c) * (star u * q) := by
        rw [projectionDilation_def]; noncomm_ring
    _ = q * c * q := by simp [huq, hqu]

/-- A projection dilation is idempotent under ring relations alone: `q` is idempotent,
`star u * u = q`, `q * u = 0` and `star u * q = 0`, `c` and `d` are commuting elements of the
corner of `q` (`c * q = c = q * c` and `d * q = d = q * d`), and `d * d = c - c * c`. -/
theorem isIdempotentElem_projectionDilation {q u c d : R} (hq : IsIdempotentElem q)
    (hu : star u * u = q) (hqu : q * u = 0) (huq : star u * q = 0) (hcq : c * q = c)
    (hqc : q * c = c) (hdq : d * q = d) (hqd : q * d = d) (hcd : Commute c d)
    (hdd : d * d = c - c * c) : IsIdempotentElem (projectionDilation q u c d) := by
  have hqq : q * q = q := hq.eq
  have hcu : c * u = 0 := by rw [← hcq, mul_assoc, hqu, mul_zero]
  have hdu : d * u = 0 := by rw [← hdq, mul_assoc, hqu, mul_zero]
  have huc : star u * c = 0 := by rw [← hqc, ← mul_assoc, huq, zero_mul]
  have hud : star u * d = 0 := by rw [← hqd, ← mul_assoc, huq, zero_mul]
  -- Write the dilation as `x + u * y`; the products `x * u`, `y * u`, `x * x` and `y * x`
  -- simplify by the orthogonality relations.
  set v := star u
  have hx : (c + d * v) * u = d := by rw [add_mul, mul_assoc, hcu, hu, hdq, zero_add]
  have hy : (d + (q - c) * v) * u = q - c := by
    rw [add_mul, mul_assoc, hdu, hu, sub_mul, hqq, hcq, zero_add]
  have hxx : (c + d * v) * (c + d * v) = c * c + c * d * v := by
    calc (c + d * v) * (c + d * v)
        = c * c + c * d * v + d * (v * c) + d * (v * d) * v := by noncomm_ring
      _ = c * c + c * d * v := by rw [huc, hud]; simp
  have hyx : (d + (q - c) * v) * (c + d * v) = d * c + d * d * v := by
    calc (d + (q - c) * v) * (c + d * v)
        = d * c + d * d * v + (q - c) * (v * c) + (q - c) * (v * d) * v := by noncomm_ring
      _ = d * c + d * d * v := by rw [huc, hud]; simp
  have hP : projectionDilation q u c d = (c + d * v) + u * (d + (q - c) * v) := by
    rw [projectionDilation_def]; noncomm_ring
  -- The remaining identity is a combination of the corner relations.
  have hdd' : d * d - (c - c * c) = 0 := sub_eq_zero.mpr hdd
  have hcd' : c * d - d * c = 0 := sub_eq_zero.mpr hcd.eq
  have hdq' : d * q - d = 0 := sub_eq_zero.mpr hdq
  have hqd' : q * d - d = 0 := sub_eq_zero.mpr hqd
  have hqq' : q * q - q = 0 := sub_eq_zero.mpr hqq
  have hqc' : q * c - c = 0 := sub_eq_zero.mpr hqc
  have hcq' : c * q - c = 0 := sub_eq_zero.mpr hcq
  rw [IsIdempotentElem, hP, ← sub_eq_zero]
  calc ((c + d * v) + u * (d + (q - c) * v)) * ((c + d * v) + u * (d + (q - c) * v))
        - ((c + d * v) + u * (d + (q - c) * v))
      = (c + d * v) * (c + d * v) + (c + d * v) * u * (d + (q - c) * v)
        + u * ((d + (q - c) * v) * (c + d * v))
        + u * ((d + (q - c) * v) * u) * (d + (q - c) * v)
        - ((c + d * v) + u * (d + (q - c) * v)) := by noncomm_ring
    _ = c * c + c * d * v + d * (d + (q - c) * v) + u * (d * c + d * d * v)
        + u * (q - c) * (d + (q - c) * v)
        - ((c + d * v) + u * (d + (q - c) * v)) := by rw [hxx, hx, hyx, hy]
    _ = (d * d - (c - c * c)) + (c * d - d * c) * v + (d * q - d) * v
        - u * (c * d - d * c) + u * (q * d - d)
        + u * ((d * d - (c - c * c)) + (q * q - q) - (q * c - c) - (c * q - c)) * v := by
      noncomm_ring
    _ = 0 := by rw [hdd', hcd', hdq', hqd', hqq', hqc', hcq']; simp

/-- A **projection dilation** is a star projection. Here `star u * u = q` and `q * u = 0` say
that `u` maps the range of the star projection `q` isometrically onto a piece orthogonal to it,
`c` and `d` are self-adjoint commuting elements of the corner of `q`, and
`d * d = c - c * c`. -/
theorem isStarProjection_projectionDilation {q u c d : R} (hq : IsStarProjection q)
    (hu : star u * u = q) (hqu : q * u = 0) (hc : IsSelfAdjoint c) (hcq : c * q = c)
    (hd : IsSelfAdjoint d) (hdq : d * q = d) (hcd : Commute c d) (hdd : d * d = c - c * c) :
    IsStarProjection (projectionDilation q u c d) := by
  refine ⟨isIdempotentElem_projectionDilation hq.isIdempotentElem hu hqu
    (hq.isSelfAdjoint.star_mul_eq_zero_of_mul_eq_zero hqu) hcq
    (hc.mul_eq_right_of_mul_eq_left hq.isSelfAdjoint hcq) hdq
    (hd.mul_eq_right_of_mul_eq_left hq.isSelfAdjoint hdq) hcd hdd, ?_⟩
  rw [IsSelfAdjoint, projectionDilation_def]
  simp only [star_add, star_mul, star_sub, star_star, hc.star_eq, hd.star_eq,
    hq.isSelfAdjoint.star_eq]
  noncomm_ring

end TauCeti
