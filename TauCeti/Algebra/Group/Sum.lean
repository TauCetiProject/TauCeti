/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Group structures on families indexed by a sum type

A family `Sum.elim G₁ G₂` indexed by `α ⊕ β` takes the value `G₁ a` at `Sum.inl a` and `G₂ b` at
`Sum.inr b`. When `G₁` and `G₂` are families of groups, each value of `Sum.elim G₁ G₂` is a group
(`Sum.instGroupElim`). This is the family of isotropy groups of a product of implicit atlases, in
the sense of Pardon.
-/

public section

namespace Sum

universe u

variable {α β : Type*} {G₁ : α → Type u} {G₂ : β → Type u}

/-- The family `Sum.elim G₁ G₂` indexed by `α ⊕ β` is a family of groups when `G₁` and `G₂` are. -/
instance instGroupElim [∀ a, Group (G₁ a)] [∀ b, Group (G₂ b)] :
    ∀ i : α ⊕ β, Group (Sum.elim G₁ G₂ i)
  | .inl a => inferInstanceAs (Group (G₁ a))
  | .inr b => inferInstanceAs (Group (G₂ b))

end Sum
