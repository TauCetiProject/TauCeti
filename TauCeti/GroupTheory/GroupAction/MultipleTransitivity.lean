/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Multiple transitivity through the permutation representation

The full permutation group of a type is `n`-pretransitive for every `n`
(`Equiv.Perm.isMultiplyPretransitive`). Hence so is every action whose permutation representation
`MulAction.toPermHom G α : G →* Equiv.Perm α` is surjective, that is, every action inducing all
permutations of `α`. For a Galois group acting on the embeddings of a field, this is the condition
that the Galois group is the full symmetric group on the embeddings.

## Main results

* `MulAction.isMultiplyPretransitive_of_surjective_toPermHom`: an action inducing every
  permutation is `n`-pretransitive for every `n`.
-/

public section

namespace MulAction

variable {G α : Type*} [Group G] [MulAction G α]

/-- An action inducing every permutation of `α` is `n`-pretransitive for every `n`. -/
theorem isMultiplyPretransitive_of_surjective_toPermHom
    (h : Function.Surjective (toPermHom G α)) (n : ℕ) : IsMultiplyPretransitive G α n := by
  rw [isMultiplyPretransitive_iff]
  intro x y
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_smul_eq_embedding x y
  obtain ⟨g, rfl⟩ := h π
  exact ⟨g, Function.Embedding.ext fun i ↦ by
    simpa [Function.Embedding.smul_apply] using DFunLike.congr_fun hπ i⟩

end MulAction
