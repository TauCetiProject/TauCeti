/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# Positive contractions in star-ordered rings

In a star-ordered ring, an element `c` with `0 ≤ c ≤ 1` satisfies `c * c ≤ c`. The proof writes
`c - c * c` as the sum of the conjugates `(1 - c) * c * (1 - c)` and `c * (1 - c) * c` of the
nonnegative elements `c` and `1 - c`. In a C⋆-algebra the defect `c - c * c` therefore has a
square root, which is what is needed to dilate a positive contraction to a projection.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

/-- A positive contraction `c`, that is `0 ≤ c ≤ 1`, satisfies `c * c ≤ c`. -/
theorem mul_self_le_self_of_mem_Icc {c : R} (hc : c ∈ Set.Icc 0 1) : c * c ≤ c := by
  have hsa : IsSelfAdjoint c := .of_nonneg hc.1
  have h : c - c * c = star (1 - c) * c * (1 - c) + star c * (1 - c) * c := by
    rw [star_sub, star_one, hsa.star_eq]; noncomm_ring
  rw [← sub_nonneg, h]
  exact add_nonneg (star_left_conjugate_nonneg hc.1 _)
    (star_left_conjugate_nonneg (sub_nonneg.mpr hc.2) _)

end TauCeti
