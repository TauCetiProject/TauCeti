/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Set.Finite.Range

/-!
# Extending a finite injective family in an infinite type

In an infinite type `γ`, a finite injective family `f : α → γ` extends to an injective map
`Sum.elim f g : α ⊕ β → γ` for any countable `β`: the complement of the finite range of `f` is
infinite, so it contains a copy of `ℕ`, and hence of `β`.

## Main results

* `Function.Injective.exists_sumElim_injective`: a finite injective family in an infinite type
  extends injectively over `α ⊕ β` for every countable `β`.
-/

public section

namespace Function.Injective

variable {α β γ : Type*} {f : α → γ}

/-- In an infinite type, a finite injective family `f` extends to an injective map
`Sum.elim f g` out of `α ⊕ β`, for every countable `β`. -/
theorem exists_sumElim_injective [Finite α] [Infinite γ] [Countable β] (hf : Injective f) :
    ∃ g : β → γ, Injective (Sum.elim f g) := by
  obtain ⟨c, hc⟩ := Countable.exists_injective_nat β
  let e := Set.Infinite.natEmbedding _ (Set.finite_range f).infinite_compl
  exact ⟨fun b ↦ e (c b), hf.sumElim (Subtype.val_injective.comp (e.injective.comp hc))
    fun a b h ↦ (e (c b)).property ⟨a, h⟩⟩

end Function.Injective
