/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite

/-!
# Complex-shape helpers for the negation embedding

Mathlib's `ComplexShape.embeddingDownIntUpInt` embeds `ComplexShape.down ℤ` into
`ComplexShape.up ℤ` via `n ↦ -n` (`Mathlib.Algebra.Homology.CochainComplexOpposite`). Because
`ComplexShape.embeddingDownIntUpInt` is semireducible rather than `@[reducible]`,
`Function.Surjective Neg.neg` is not definitionally equal to
`Function.Surjective ComplexShape.embeddingDownIntUpInt.f` at `implicit` transparency. This file
exposes the surjectivity lemma with its explicit projection type, together with the index sum
identity `embeddingDownIntUpInt.f i + i = 0`, for use with
`HomologicalComplex.restrictionCyclesIsoOfSurjective` and
`HomologicalComplex.restrictionHomologyIsoOfSurjective`.

## Main results

* `ComplexShape.surjective_embeddingDownIntUpInt_f`: surjectivity of
  `ComplexShape.embeddingDownIntUpInt.f`, typed directly with that projection.
* `ComplexShape.embeddingDownIntUpInt_f_add_self`: the sum `embeddingDownIntUpInt.f i + i = 0`.
-/

public section

namespace ComplexShape

/-- Surjectivity of `ComplexShape.embeddingDownIntUpInt.f` stated with that projection so
`HomologicalComplex.restrictionCyclesIsoOfSurjective` and
`HomologicalComplex.restrictionHomologyIsoOfSurjective` match without unfolding the embedding. -/
lemma surjective_embeddingDownIntUpInt_f : Function.Surjective embeddingDownIntUpInt.f :=
  neg_surjective

/-- The index of `K⁻ᵢ = K⁻ⁱ` and the degree `i` add up to zero. -/
lemma embeddingDownIntUpInt_f_add_self (i : ℤ) : embeddingDownIntUpInt.f i + i = 0 := by
  simp

end ComplexShape
