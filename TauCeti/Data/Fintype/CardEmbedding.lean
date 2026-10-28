/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.CardEmbedding

/-!
# The number of injective maps between finite types

The injective maps `α → β` between finite types correspond to the embeddings `α ↪ β`, so there
are `(card β).descFactorial (card α)` of them. This restates `Fintype.card_embedding_eq` for the
subtype of injective functions, the form in which counts over injective tuples `Fin n → V` are
taken.
-/

public section

namespace Fintype

/-- There are `(card β).descFactorial (card α)` injective maps `α → β`; for instance
`|V| (|V| - 1) (|V| - 2)` injective triples `Fin 3 → V`. This is `Fintype.card_embedding_eq` for
the subtype of injective functions. -/
theorem card_subtype_injective {α β : Type*} [Fintype α] [Fintype β]
    [Fintype {f : α → β // Function.Injective f}] :
    card {f : α → β // Function.Injective f} = (card β).descFactorial (card α) := by
  rw [card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _), card_embedding_eq]

end Fintype
