/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Perfect

/-!
# Countable sets are meagre in perfect spaces

In a `T₁` space a point that is not isolated is a closed set with empty interior, so it is nowhere
dense. Hence in a perfect `T₁` space every countable set is meagre, being a countable union of
nowhere dense singletons. In a nonempty perfect Baire space a comeagre set is not meagre, so it is
uncountable.

These facts are how Baire category arguments on Cantor space `ℕ → Bool` and on other perfect
Polish spaces produce uncountably many points: a property holding on a comeagre set holds at
uncountably many points, and a countable exceptional set is negligible. For example, an
equivalence relation whose classes are countable has meagre classes.

## Main results

* `TauCeti.isNowhereDense_singleton`: in a `T₁` space, a non-isolated point is nowhere dense.
* `Set.Countable.isMeagre`: in a perfect `T₁` space, every countable set is meagre.
* `TauCeti.not_countable_of_mem_residual`: in a nonempty perfect `T₁` Baire space, every comeagre
  set is uncountable.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Section 8 (meagre sets and the Baire category theorem).
-/

public section

open Set Topology

variable {X : Type*} [TopologicalSpace X] [T1Space X]

namespace TauCeti

/-- In a `T₁` space, a point that is not isolated is a nowhere dense set. -/
theorem isNowhereDense_singleton (x : X) [(𝓝[≠] x).NeBot] : IsNowhereDense ({x} : Set X) :=
  isClosed_singleton.isNowhereDense_iff.2 (interior_singleton x)

end TauCeti

/-- **Countable sets are meagre in a perfect `T₁` space.** -/
theorem Set.Countable.isMeagre [PerfectSpace X] {s : Set X} (hs : s.Countable) : IsMeagre s := by
  simpa using isMeagre_biUnion hs fun x _ => (TauCeti.isNowhereDense_singleton x).isMeagre

namespace TauCeti

/-- **Comeagre sets are uncountable** in a nonempty perfect `T₁` Baire space. -/
theorem not_countable_of_mem_residual [PerfectSpace X] [BaireSpace X] [Nonempty X] {s : Set X}
    (hs : s ∈ residual X) : ¬s.Countable :=
  fun h => not_isMeagre_of_mem_residual hs h.isMeagre

end TauCeti
