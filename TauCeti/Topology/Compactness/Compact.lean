/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact

/-!
# Directed families of closed sets in a compact space

A directed family of nonempty closed subsets of a compact space has nonempty intersection. This
is Mathlib's `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed` with the
compactness of each member read off from the ambient space, which is the form in which
inverse-limit arguments over profinite spaces and groups consume it.

## Main statements

* `TauCeti.nonempty_iInter_of_directed_nonempty_isClosed`: a directed family of nonempty closed
  subsets of a compact space has nonempty intersection.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Proposition 1.1.4, whose proof rests on this
  lemma.
-/

public section

namespace TauCeti

/-- A directed family of nonempty closed subsets of a compact space has nonempty
intersection. -/
theorem nonempty_iInter_of_directed_nonempty_isClosed {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {ι : Type*} [Nonempty ι] (s : ι → Set X) (hdir : Directed (· ⊇ ·) s)
    (hne : ∀ i, (s i).Nonempty) (hclosed : ∀ i, IsClosed (s i)) :
    (⋂ i, s i).Nonempty :=
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed s hdir hne
    (fun i ↦ (hclosed i).isCompact) hclosed

end TauCeti
