/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact

/-!
# Compact sublevels under modifications on a compact set

If two functions agree off a compact set, a closed sublevel of the second is compact as soon as
the corresponding sublevel of the first is: it lies in the union of that sublevel and the compact
set.

## Main declarations

* `IsCompact.setOf_le_of_eqOn_compl`: compactness of sublevels transfers between functions that
  agree off a compact set.
-/

public section

open Set

/-- **Compact sublevels survive modification on a compact set.** If `g` agrees with `f` off a
compact set `K`, the sublevel of `f` at `c` is compact and the sublevel of `g` at `c` is closed,
then the sublevel of `g` at `c` is compact. -/
theorem IsCompact.setOf_le_of_eqOn_compl {X α : Type*} [TopologicalSpace X] [LE α] {f g : X → α}
    {K : Set X} {c : α} (hf : IsCompact {x | f x ≤ c}) (hK : IsCompact K) (hfg : EqOn f g Kᶜ)
    (hg : IsClosed {x | g x ≤ c}) : IsCompact {x | g x ≤ c} := by
  refine (hf.union hK).of_isClosed_subset hg fun x hx ↦ ?_
  by_cases hxK : x ∈ K
  · exact Or.inr hxK
  · refine Or.inl ?_
    rw [mem_ofPred_eq, hfg hxK]
    exact hx
