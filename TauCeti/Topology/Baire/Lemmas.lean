/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Closure

/-!
# Meagre sets and closed covers of open sets

A set `s` in a topological space `X` is meagre (`IsMeagre s`) when its complement belongs to the
`residual` filter. Consequently, meagreness is invariant under eventual equality
`s =ᶠ[residual X] t` (written `s =ᵇ t` when `Mathlib.Topology.Baire.BaireMeasurable` is open).

In a Baire space, a nonempty open set covered by countably many closed sets meets the interior of
one of them. This is the form of the Baire category theorem used in arguments that localize a
property holding at every point of an open set to an open subset where it holds uniformly.

## Main results

* `IsMeagre.congr`: if `s` is meagre and `s =ᶠ[residual X] t`, then `t` is meagre.
* `TauCeti.isMeagre_congr`: if `s =ᶠ[residual X] t`, then `IsMeagre s ↔ IsMeagre t`.
* `IsOpen.exists_inter_interior_nonempty_of_subset_iUnion`: a countable closed cover of a nonempty
  open set `W` in a Baire space has a member whose interior meets `W`.
-/

public section

open Filter Set

/-- Meagreness transfers across eventual equality with respect to `residual X`. -/
theorem IsMeagre.congr {X : Type*} [TopologicalSpace X] {s t : Set X} (hs : IsMeagre s)
    (h : s =ᶠ[residual X] t) : IsMeagre t := by
  rw [IsMeagre, ← eventually_mem_set] at hs ⊢
  exact hs.mp (h.compl.mem_iff.mono fun _ hiff hx => hiff.1 hx)

/-- **The Baire category theorem for a cover of an open set.** In a Baire space, if a nonempty
open set `W` is covered by countably many closed sets, then the interior of one of them meets `W`.
For `W = univ` this is `nonempty_interior_of_iUnion_of_closed`. -/
theorem IsOpen.exists_inter_interior_nonempty_of_subset_iUnion {X ι : Type*} [TopologicalSpace X]
    [BaireSpace X] [Countable ι] {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) {f : ι → Set X}
    (hf : ∀ i, IsClosed (f i)) (hcov : W ⊆ ⋃ i, f i) : ∃ i, (W ∩ interior (f i)).Nonempty := by
  -- Adding the closed complement of `W` gives a countable closed cover of the whole space.
  have hU : ⋃ o : Option ι, o.elim Wᶜ f = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    by_cases hx : x ∈ W
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hx)
      exact mem_iUnion.2 ⟨some i, hi⟩
    · exact mem_iUnion.2 ⟨none, hx⟩
  have hc : ∀ o : Option ι, IsClosed (o.elim Wᶜ f) := by
    rintro (_ | i)
    exacts [hW.isClosed_compl, hf i]
  obtain ⟨x, hxW, hx⟩ := dense_iff_inter_open.1 (dense_iUnion_interior_of_closed hc hU) W hW hne
  obtain ⟨o, ho⟩ := mem_iUnion.1 hx
  cases o with
  | none => exact absurd hxW (interior_subset ho)
  | some i => exact ⟨i, x, hxW, ho⟩

namespace TauCeti

/-- Meagreness is invariant under eventual equality with respect to `residual X`. -/
theorem isMeagre_congr {X : Type*} [TopologicalSpace X] {s t : Set X}
    (h : s =ᶠ[residual X] t) : IsMeagre s ↔ IsMeagre t :=
  ⟨fun hs => hs.congr h, fun ht => ht.congr h.symm⟩

end TauCeti
