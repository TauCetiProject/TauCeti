/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Order and compression by projections

Compression by a star projection preserves positivity, but need not decrease a positive element.
It decreases a positive element exactly when the projection commutes with that element.
The key zero-corner criterion says that `star b * a * b = 0` for positive `a` exactly when
`a * b = 0`; thus a vanishing positive corner forces the off-diagonal terms to vanish too.
-/

public section

open CFC

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A corner of a positive element vanishes exactly when the element annihilates the
compressing factor on the right. -/
@[simp]
theorem star_mul_mul_eq_zero_iff_of_nonneg {a : A} (ha : 0 ≤ a) (b : A) :
    star b * a * b = 0 ↔ a * b = 0 := by
  constructor
  · intro h
    have hs : sqrt a * b = 0 := by
      rw [← norm_eq_zero, ← sq_eq_zero_iff, ← norm_star_mul_mul_self_of_nonneg b ha,
        h, norm_zero]
    calc
      a * b = sqrt a * (sqrt a * b) := by rw [← mul_assoc, sqrt_mul_sqrt_self a ha]
      _ = 0 := by rw [hs, mul_zero]
  · intro h
    simp [mul_assoc, h]

end TauCeti

namespace IsStarProjection

variable {A : Type*}

/-- If compression by a projection lies below an element, the projection commutes with it.
Neither positivity of the element nor a unit is required. -/
theorem commute_of_conjugate_le [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p a : A} (hp : IsStarProjection p) (h : p * a * p ≤ a) : Commute p a := by
  -- The positive difference has a zero p-corner, so it annihilates p on both sides.
  have hd : 0 ≤ a - p * a * p := sub_nonneg.mpr h
  have hcorner : star p * (a - p * a * p) * p = 0 := by
    rw [hp.isSelfAdjoint.star_eq]
    calc
      p * (a - p * a * p) * p = p * a * p - (p * p) * a * (p * p) := by
        noncomm_ring
      _ = 0 := by rw [hp.isIdempotentElem.eq, sub_self]
  have hz := (TauCeti.star_mul_mul_eq_zero_iff_of_nonneg hd p).mp hcorner
  have hright : a * p = p * a * p := by
    simpa [sub_mul, mul_assoc, hp.isIdempotentElem.eq, sub_eq_zero] using hz
  have hleft : p * a = p * a * p := by
    have : p * (a - p * a * p) = 0 := by
      simpa only [star_mul, hp.isSelfAdjoint.star_eq, hd.isSelfAdjoint.star_eq, star_zero]
        using congrArg star hz
    simpa [mul_sub, ← mul_assoc, hp.isIdempotentElem.eq, sub_eq_zero] using this
  exact hleft.trans hright.symm

/-- Compression of a positive element by a projection lies below that element exactly when
the projection commutes with it. Positivity is needed only for the reverse implication. -/
theorem conjugate_le_iff_commute [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p a : A} (hp : IsStarProjection p) (ha : 0 ≤ a) : p * a * p ≤ a ↔ Commute p a := by
  constructor
  · exact hp.commute_of_conjugate_le
  · intro h
    have hcorner : star (sqrt a - sqrt a * p) * (sqrt a - sqrt a * p) =
        a - p * a * p := by
      calc
        _ = sqrt a * sqrt a - (sqrt a * sqrt a) * p - p * (sqrt a * sqrt a) +
            p * (sqrt a * sqrt a) * p := by
          rw [star_sub, star_mul, (sqrt_nonneg a).star_eq, hp.isSelfAdjoint.star_eq]
          noncomm_ring
        _ = a - p * a * p := by
          rw [sqrt_mul_sqrt_self a ha]
          noncomm_ring [hp.isIdempotentElem.eq, h.eq]
    exact sub_nonneg.mp (hcorner ▸ star_mul_self_nonneg _)

end IsStarProjection
