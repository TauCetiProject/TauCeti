/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic

/-!
# The embedding `n ↦ n + 1` of `ComplexShape.down ℕ`

Extending a chain complex indexed by `ℕ` along the embedding `n ↦ n + 1` of `ComplexShape.down ℕ`
into itself places it one degree higher, with a zero object in degree `0`. This is Mathlib's
`ComplexShape.embeddingDown'Add 1 1`, restated for the shape `ComplexShape.down ℕ` (definitionally
`ComplexShape.down' 1`) so that its instances are found there.

## Main definitions

* `ComplexShape.embeddingDownNatSucc`: the embedding `n ↦ n + 1` of `ComplexShape.down ℕ`.
-/

public section

namespace ComplexShape

/-- The embedding `n ↦ n + 1` of `ComplexShape.down ℕ` into itself: Mathlib's
`ComplexShape.embeddingDown'Add 1 1`, since `ComplexShape.down ℕ` unfolds to `down' 1`. -/
@[expose] def embeddingDownNatSucc : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
  embeddingDown'Add (1 : ℕ) 1

@[simp] lemma embeddingDownNatSucc_f (n : ℕ) : embeddingDownNatSucc.f n = n + 1 := rfl

instance : embeddingDownNatSucc.IsRelIff :=
  inferInstanceAs (embeddingDown'Add (1 : ℕ) 1).IsRelIff

instance : embeddingDownNatSucc.IsTruncLE :=
  inferInstanceAs (embeddingDown'Add (1 : ℕ) 1).IsTruncLE

end ComplexShape
