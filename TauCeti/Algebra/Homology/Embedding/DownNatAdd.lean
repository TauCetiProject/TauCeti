/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic

/-!
# The embedding `n ↦ n + k` of `ComplexShape.down ℕ`

Extending a chain complex indexed by `ℕ` along the embedding `n ↦ n + k` of `ComplexShape.down ℕ`
into itself places it `k` degrees higher, with zero objects in the degrees below `k`. This is
Mathlib's `ComplexShape.embeddingDown'Add 1 k`, restated for the shape `ComplexShape.down ℕ`
(definitionally `ComplexShape.down' 1`) so that it applies to `ChainComplex C ℕ` and its instances
are found there.

## Main definitions

* `ComplexShape.embeddingDownNatAdd`: the embedding `n ↦ n + k` of `ComplexShape.down ℕ`.
-/

public section

namespace ComplexShape

/-- The embedding `n ↦ n + k` of `ComplexShape.down ℕ` into itself: Mathlib's
`ComplexShape.embeddingDown'Add 1 k`, since `ComplexShape.down ℕ` unfolds to `down' 1`. -/
def embeddingDownNatAdd (k : ℕ) :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
  embeddingDown'Add (1 : ℕ) k

@[simp] lemma embeddingDownNatAdd_f (k n : ℕ) : (embeddingDownNatAdd k).f n = n + k := (rfl)

instance (k : ℕ) : (embeddingDownNatAdd k).IsRelIff :=
  inferInstanceAs (embeddingDown'Add (1 : ℕ) k).IsRelIff

instance (k : ℕ) : (embeddingDownNatAdd k).IsTruncLE :=
  inferInstanceAs (embeddingDown'Add (1 : ℕ) k).IsTruncLE

end ComplexShape
