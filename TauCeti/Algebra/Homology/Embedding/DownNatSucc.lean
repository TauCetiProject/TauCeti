/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# The embedding `n ↦ n + 1` of `ComplexShape.down ℕ`

Extending a chain complex indexed by `ℕ` along the embedding `n ↦ n + 1` of `ComplexShape.down ℕ`
into itself places it one degree higher, with a zero object in degree `0`. Mathlib's
`ComplexShape.embeddingDown'Add 1 1` is this embedding for the shape `ComplexShape.down' 1`, but
its instances are not found for `ComplexShape.down ℕ`.

## Main definitions and results

* `ComplexShape.embeddingDownNatSucc`: the embedding `n ↦ n + 1` of `ComplexShape.down ℕ`.
* `HomologicalComplex.isZero_extend_embeddingDownNatSucc_homology_zero`: the extended complex
  has zero homology in degree `0`.
* `HomologicalComplex.isIso_homologyMap_extendMap_embeddingDownNatSucc_zero`: an extended chain
  map is an isomorphism in homology in degree `0`.
-/

public section

open CategoryTheory Limits

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

namespace HomologicalComplex

open ComplexShape

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The extension of a complex along `n ↦ n + 1` is zero in degree `0`. -/
lemma isZero_extend_embeddingDownNatSucc_X_zero (K : HomologicalComplex C (ComplexShape.down ℕ)) :
    IsZero ((K.extend embeddingDownNatSucc).X 0) :=
  K.isZero_extend_X _ _ fun i h ↦ by simp at h

/-- The extension of a complex along `n ↦ n + 1` has zero homology in degree `0`. -/
lemma isZero_extend_embeddingDownNatSucc_homology_zero
    (K : HomologicalComplex C (ComplexShape.down ℕ))
    [(K.extend embeddingDownNatSucc).HasHomology 0] :
    IsZero ((K.extend embeddingDownNatSucc).homology 0) :=
  (K.extend_exactAt _ 0 fun i h ↦ by simp at h).isZero_homology

/-- The extension along `n ↦ n + 1` of a chain map is an isomorphism in homology in degree `0`. -/
lemma isIso_homologyMap_extendMap_embeddingDownNatSucc_zero
    {K L : HomologicalComplex C (ComplexShape.down ℕ)} (f : K ⟶ L)
    [(K.extend embeddingDownNatSucc).HasHomology 0]
    [(L.extend embeddingDownNatSucc).HasHomology 0] :
    IsIso (homologyMap (extendMap f embeddingDownNatSucc) 0) :=
  ⟨0, (isZero_extend_embeddingDownNatSucc_homology_zero K).eq_of_src _ _,
    (isZero_extend_embeddingDownNatSucc_homology_zero L).eq_of_src _ _⟩

end HomologicalComplex
