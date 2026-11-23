/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-!
# Lifting morphisms to extensions along truncation embeddings

Let `e : c.Embedding c'` be an embedding of complex shapes. Mathlib extends a morphism
`φ : K.restriction e ⟶ L` to a morphism `K ⟶ L.extend e` (`ComplexShape.Embedding.liftExtend`)
under the condition `e.HasLift φ`, which asks `φ` to kill the boundaries coming into the lower
boundary of `e` (`ComplexShape.Embedding.BoundaryGE`). When every index of `c'` with a
differential into the image of `e` already lies in that image (`e.IsTruncLE`), for instance for
the embedding `n ↦ n + k` of `ComplexShape.down ℕ` into itself, the lower boundary is empty and
every morphism lifts.

## Main results

* `ComplexShape.Embedding.not_boundaryGE`: for `e.IsTruncLE`, no index is in the lower boundary.
* `ComplexShape.Embedding.hasLift`: for `e.IsTruncLE`, every morphism `K.restriction e ⟶ L`
  extends to `K ⟶ L.extend e`.
-/

public section

open CategoryTheory Limits

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

/-- If every index with a differential into the image of `e` lies in the image of `e`, the lower
boundary of `e` is empty. -/
theorem not_boundaryGE [e.IsTruncLE] (j : ι) : ¬e.BoundaryGE j := fun hj ↦ by
  obtain ⟨i, hi⟩ := e.mem_prev hj.1
  exact hj.2 i (hi ▸ hj.1)

/-- Along an embedding `e` with `e.IsTruncLE`, every morphism `K.restriction e ⟶ L` satisfies the
lifting condition, so it extends to a morphism `K ⟶ L.extend e`
(`ComplexShape.Embedding.liftExtend`). -/
theorem hasLift [e.IsTruncLE] {C : Type*} [Category* C] [HasZeroMorphisms C]
    {K : HomologicalComplex C c'} {L : HomologicalComplex C c} (φ : K.restriction e ⟶ L) :
    e.HasLift φ :=
  fun j hj ↦ absurd hj (e.not_boundaryGE j)

end ComplexShape.Embedding
