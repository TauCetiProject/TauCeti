/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Option

/-!
# Options and equivalences

An equivalence `e : α ≃ β` maps `Option α` to `Option β` by `Option.map e`. This file records the
value of that map at a point: `Option.map e o = some y` exactly when `o = some (e.symm y)`.

This is the form in which `Equiv.optionCongr` describes the conjugation of a partial function by an
equivalence, for instance of a root operator of a crystal under transport along a bijection.
-/

public section

namespace Option

/-- An option is mapped to `some y` by an equivalence exactly when it is `some` of the preimage of
`y`. -/
-- Not `@[simp]`: the simp lemma `Option.map_eq_some_iff` rewrites the left-hand side to an
-- existential, which `simpNF` rejects.
theorem map_equiv_eq_some_iff {α β : Type*} {e : α ≃ β} {o : Option α} {y : β} :
    o.map e = some y ↔ o = some (e.symm y) := by
  cases o <;> simp [Equiv.eq_symm_apply]

end Option

end
