/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Option.Basic

/-!
# Options and subtypes

`Option.pmap Subtype.mk` corestricts an `Option α` to a subtype `{a // p a}`, sending `some a` to
`some ⟨a, _⟩` when `a` satisfies `p` and to `none` otherwise. This is the map that restricts a
partial function, such as a root operator of a crystal, to a subset closed under it.

The lemma below records when the corestriction is `some b`. It cannot be `@[simp]`: the simp lemma
`Option.pmap_eq_some_iff` rewrites the same left-hand side to an existential over the witness.
-/

public section

namespace Option

/-- An option corestricted to a subtype is `some b` exactly when the original option is `some` of
the underlying element of `b`. -/
theorem pmap_subtype_mk_eq_some_iff {α : Type*} {p : α → Prop} {o : Option α}
    {h : ∀ a ∈ o, p a} {b : {a // p a}} :
    o.pmap Subtype.mk h = some b ↔ o = some b.1 := by
  cases o with
  | none => simp
  | some a => simp [Subtype.ext_iff]

end Option

end
