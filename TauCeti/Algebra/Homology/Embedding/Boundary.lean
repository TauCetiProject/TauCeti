/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Boundary

/-!
# The boundary of the embedding `n ↦ -n`

Mathlib computes the upper boundary of the embedding `ComplexShape.embeddingUpIntLE p : n ↦ p - n`
of `ComplexShape.down ℕ` into `ComplexShape.up ℤ`. This file records the same computation for
`ComplexShape.embeddingDownNat : n ↦ -n`, which agrees with `embeddingUpIntLE 0` only up to
`0 - n = -n`.

## Main results

* `ComplexShape.boundaryLE_embeddingDownNat_iff`: the boundary of `embeddingDownNat` is `0`.
-/

public section

namespace ComplexShape

/-- The only boundary degree of the embedding `n ↦ -n` of `ComplexShape.down ℕ` into
`ComplexShape.up ℤ` is `0`. -/
@[simp]
lemma boundaryLE_embeddingDownNat_iff (n : ℕ) :
    embeddingDownNat.BoundaryLE n ↔ n = 0 := by
  -- `embeddingDownNat` is `embeddingUpIntLE 0` up to `0 - n = -n`.
  simpa only [Embedding.BoundaryLE, embeddingUpIntLE_f, embeddingDownNat_f, zero_sub] using
    boundaryLE_embeddingUpIntLE_iff 0 n

end ComplexShape
