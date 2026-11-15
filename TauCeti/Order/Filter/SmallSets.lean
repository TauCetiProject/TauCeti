/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.SmallSets
public import TauCeti.Order.Filter.Basic

/-!
# Indexing a net by the members of a filter

A family indexed by the members of a filter `l` — a net of the shape `k : {s : Set α // s ∈ l} → β`
— is naturally taken along `Filter.atBot`, where `{s : Set α // s ∈ l}` carries the inclusion
order, so that `∀ᶠ s in atBot, p s` says that `p` holds for every small enough member of `l`.

The members of a filter are directed downward (`Filter.isCodirectedOrder_mem`), so
`Filter.atBot_neBot` makes this index filter nontrivial. This file records that it agrees with
`comap Subtype.val l.smallSets`.
-/

public section

namespace Filter

variable {α : Type*} (l : Filter α)

/-- On the members of a filter `l`, ordered by inclusion, `atBot` is the pullback of
`l.smallSets`: both say that a property holds for every small enough member of `l`. -/
theorem comap_val_smallSets_eq_atBot :
    comap (Subtype.val : {s : Set α // s ∈ l} → Set α) l.smallSets = atBot :=
  ((l.hasBasis_smallSets.comap _).to_hasBasis (fun s hs ↦ ⟨⟨s, hs⟩, trivial, fun _ ↦ id⟩)
    fun s _ ↦ ⟨s.1, s.2, fun _ ↦ id⟩).eq_of_same_basis atBot_basis

end Filter
