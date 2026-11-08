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

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Compression of a positive element by a projection lies below that element exactly when
the projection commutes with it. Positivity of the element is essential. -/
theorem compression_le_iff_commute {p a : A} (hp : IsStarProjection p) (ha : 0 ≤ a) :
    p * a * p ≤ a ↔ Commute p a := by
  constructor
  · intro h
    -- The positive difference has a zero p-corner, so it annihilates p.
    have hd : 0 ≤ a - p * a * p := sub_nonneg.mpr h
    have hcorner : star p * (a - p * a * p) * p = 0 := by
      rw [hp.isSelfAdjoint.star_eq]
      calc
        p * (a - p * a * p) * p = p * a * p - (p * p) * a * (p * p) := by
          noncomm_ring
        _ = 0 := by rw [hp.isIdempotentElem.eq, sub_self]
    have hright : a * p = p * a * p := by
      have := (TauCeti.star_mul_mul_eq_zero_iff_of_nonneg hd p).mp hcorner
      simpa [sub_mul, mul_assoc, hp.isIdempotentElem.eq, sub_eq_zero] using this
    have hleft : p * a = p * a * p := by
      simpa [star_mul, hp.isSelfAdjoint.star_eq, ha.isSelfAdjoint.star_eq, mul_assoc]
        using congrArg star hright
    exact hleft.trans hright.symm
  · intro h
    have hcorner : (1 - p) * a * (1 - p) = a - p * a * p := by
      noncomm_ring [hp.isIdempotentElem.eq, h.eq]
    exact sub_nonneg.mp (hcorner ▸ hp.one_sub.isSelfAdjoint.conjugate_nonneg ha)

end IsStarProjection
