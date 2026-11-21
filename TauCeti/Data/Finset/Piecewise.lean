/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Piecewise functions on pairwise disjoint finite sets

Given a background function `g : α → κ`, a finite family of pairwise disjoint finite sets
`supp : β → Finset α` indexed by `G : Finset β`, and local functions `f : β → α → κ`,
`Finset.exists_piecewise_of_pairwiseDisjoint` glues the local functions onto a single function
`h : α → κ` agreeing with `g` outside `G.biUnion supp` while counting the exact number of modified
points across the union.
-/

public section

namespace Finset

/-- **Piecewise gluing on pairwise disjoint finite sets.** Given a background function `g : α → κ`,
a finite family of pairwise disjoint finite sets `supp : β → Finset α` indexed by `G : Finset β`,
and local functions `f : β → α → κ`, there exists a single function `h : α → κ` agreeing with `f i`
on each `supp i` (`i ∈ G`), agreeing with `g` outside `G.biUnion supp`, and modifying exactly
`∑ i ∈ G, #{a ∈ supp i | f i a ≠ g a}` points. -/
theorem exists_piecewise_of_pairwiseDisjoint {α β κ : Type*} [DecidableEq α] [DecidableEq κ]
    (G : Finset β) (supp : β → Finset α) (hdisj : (G : Set β).PairwiseDisjoint supp)
    (g : α → κ) (f : β → α → κ) :
    ∃ h : α → κ,
      (∀ i ∈ G, ∀ a ∈ supp i, h a = f i a) ∧
      (∀ a ∉ G.biUnion supp, h a = g a) ∧
      #{a ∈ G.biUnion supp | h a ≠ g a} = ∑ i ∈ G, #{a ∈ supp i | f i a ≠ g a} := by
  classical
  let h : α → κ := fun a ↦
    if hex : ∃ i ∈ G, a ∈ supp i then f hex.choose a else g a
  have h_eq {i : β} (hi : i ∈ G) {a : α} (ha : a ∈ supp i) : h a = f i a := by
    have hex : ∃ j ∈ G, a ∈ supp j := ⟨i, hi, ha⟩
    have hch : hex.choose = i := by
      by_contra hne
      exact disjoint_left.1 (hdisj hex.choose_spec.1 hi hne) hex.choose_spec.2 ha
    simp only [h, dite_eq_left hex, hch]
  have h_out {a : α} (ha : a ∉ G.biUnion supp) : h a = g a := by
    simp only [mem_biUnion, not_exists, not_and] at ha
    exact dite_eq_right fun ⟨i, hi, hm⟩ ↦ ha i hi hm
  refine ⟨h, fun i hi a ha ↦ h_eq hi ha, fun a ha ↦ h_out ha, ?_⟩
  have hfilt : {a ∈ G.biUnion supp | h a ≠ g a} = G.biUnion fun i ↦ {a ∈ supp i | h a ≠ g a} := by
    ext a
    simp only [mem_filter, mem_biUnion]
    tauto
  rw [hfilt, card_biUnion fun i hi j hj hij ↦
    (hdisj hi hj hij).mono (filter_subset _ _) (filter_subset _ _)]
  exact sum_congr rfl fun i hi ↦ congrArg card (filter_congr fun a ha ↦ by rw [h_eq hi ha])

end Finset
