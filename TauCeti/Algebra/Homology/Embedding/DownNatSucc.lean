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
into itself places it one degree higher, with a zero object in degree `0`. Mathlib's
`ComplexShape.embeddingDown'Add 1 1` is this embedding for the shape `ComplexShape.down' 1`, but
its instances are not found for `ComplexShape.down ℕ`.

## Main definitions

* `ComplexShape.embeddingDownNatSucc`: the embedding `n ↦ n + 1` of `ComplexShape.down ℕ`.
-/

public section

namespace ComplexShape

/-- The embedding `n ↦ n + 1` of `ComplexShape.down ℕ` into itself. -/
@[expose] def embeddingDownNatSucc : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
  Embedding.mk' _ _ (· + 1) (fun _ _ h ↦ by simpa using h) (by simp)

@[simp] lemma embeddingDownNatSucc_f (n : ℕ) : embeddingDownNatSucc.f n = n + 1 := rfl

-- The relation `(down ℕ).Rel (b + 1 + 1) (a + 1)` unfolds to `b + 1 + 1 = a + 1`.
instance : embeddingDownNatSucc.IsRelIff where
  rel' a b (h : b + 1 + 1 = a + 1) := show b + 1 = a by omega

-- The relation `(down ℕ).Rel i (j + 1)` unfolds to `j + 1 + 1 = i`.
instance : embeddingDownNatSucc.IsTruncLE where
  mem_prev {i j} (h : j + 1 + 1 = i) := ⟨j + 1, h⟩

end ComplexShape
