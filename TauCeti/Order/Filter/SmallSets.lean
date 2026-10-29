/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.SmallSets

/-!
# Indexing a net by the members of a filter

A family indexed by the members of a filter `l` — a net of the shape `k : {s : Set α // s ∈ l} → β`
— is naturally taken along `Filter.comap Subtype.val l.smallSets`, for which `∀ᶠ s in _, p s` says
that `p` holds for every small enough member of `l`. This file records, as an instance, that this
index filter is never the bottom filter, so that convergence along it has content.
-/

public section

namespace Filter

/-- The index filter of a net indexed by the members of a filter `l`, namely
`comap Subtype.val l.smallSets` on `{s : Set α // s ∈ l}`, is not the bottom filter. -/
instance comap_val_smallSets_neBot {α : Type*} (l : Filter α) :
    NeBot (comap (Subtype.val : {s : Set α // s ∈ l} → Set α) l.smallSets) :=
  comap_neBot_iff_frequently.2 <| (frequently_smallSets_mem l).mono fun s hs ↦ ⟨⟨s, hs⟩, rfl⟩

end Filter
