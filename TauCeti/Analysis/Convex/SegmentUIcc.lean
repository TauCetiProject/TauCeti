/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment

/-!
# Affine parametrizations of unordered intervals

In a linearly ordered field, Mathlib identifies the segment between `a` and `b` with the unordered
interval `[[a, b]]` (`segment_eq_uIcc`) and places the affine line map at times in `[0, 1]` on that
segment (`lineMap_mem_segment`). This file records the resulting membership statement in the
explicit affine form `t ↦ (b - a) * t + a`, which is how the oriented time reparametrization of
the cylinder homotopy operator over `[[a, b]]` is written.

## Main results

* `Set.sub_mul_add_mem_uIcc`: `(b - a) * t + a ∈ [[a, b]]` for `t ∈ [0, 1]`.
-/

public section

namespace Set

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The affine map `t ↦ (b - a) * t + a` sends `[0, 1]` into the unordered interval `[[a, b]]`,
whichever of `a` and `b` is larger. -/
theorem sub_mul_add_mem_uIcc {a b t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : (b - a) * t + a ∈ uIcc a b := by
  simpa [← segment_eq_uIcc, AffineMap.lineMap_apply_ring', mul_comm] using
    lineMap_mem_segment 𝕜 a b ht

end Set
