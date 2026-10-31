/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.KnotTheory.PDCode.Components

/-!
# Components of the closure of a braid word

The closure of a braid word on at least one strand is never the empty diagram: it has at least
one component (`TauCeti.BraidWord.componentCount_closure_pos`). If the word is empty, every strand
closes up to a crossing-free circle; otherwise the closure has a crossing, and so a component
through it.

## Main results

* `TauCeti.BraidWord.componentCount_closure_pos`: the closure of a braid word on at least one
  strand has a component.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2.
-/

public section

namespace TauCeti.BraidWord

variable {n : ℕ} (w : BraidWord (n + 1))

/-- The closure of a braid word on at least one strand has a component: a crossing-free circle if
the word is empty, and a component through a crossing otherwise. -/
theorem componentCount_closure_pos : 0 < w.closure.toPDCode.componentCount := by
  rcases Nat.eq_zero_or_pos w.length with h | h
  · obtain rfl := List.length_eq_zero_iff.mp h
    rw [PDCode.componentCount_eq, crossinglessComponentCount_closure]
    exact Nat.lt_add_left _ (Finset.card_pos.mpr ⟨0, by simpa using crossingsAt_nil (n := n + 1) 0⟩)
  · exact PDCode.componentCount_pos _ h.ne'

end TauCeti.BraidWord
