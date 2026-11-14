/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Embedding.Basic

/-!
# Coercion of `Equiv.subtypeInjectiveEquivEmbedding`

`Equiv.subtypeInjectiveEquivEmbedding` identifies the subtype of injective functions `α → β` with
the type of embeddings `α ↪ β` without changing the underlying function
(`Equiv.coe_subtypeInjectiveEquivEmbedding_apply`).
-/

public section

namespace Equiv

/-- `Equiv.subtypeInjectiveEquivEmbedding` preserves the underlying function. -/
@[simp, grind =]
theorem coe_subtypeInjectiveEquivEmbedding_apply {α β : Sort*}
    (f : {f : α → β // Function.Injective f}) :
    (subtypeInjectiveEquivEmbedding α β f : α → β) = f.1 :=
  (rfl)

end Equiv
