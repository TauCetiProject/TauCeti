/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.HexGraph
public import TauCeti.Combinatorics.Tiling.Lozenge.Hole
public import TauCeti.Examples.Combinatorics.Tiling.Lozenge.Cochain

/-!
# Checks: holes obstruct simple connectivity

* The ring `R_ring` round `W(0)` (defined in the `Cochain` examples) with the hole `Q = {W(0)}`
  satisfies the hypothesis of `TauCeti.not_isSimplyConnectedRegion_of_hole`, which shows again that
  it is not simply connected.
* The five faces at the origin other than `W(0)` with `Q = {W(0)}` do not: `B(e₁)` shares the edge
  `(e₁, 2)` with `W(0)` and lies in neither set. That region is simply connected, by shelling, and
  the faces outside it are connected through shared edges.
* For `R = ∅` the conclusion holds trivially, since simple connectivity includes nonemptiness.
-/

public section

namespace TauCeti.Examples.HoleChecks

open TauCeti

/-- `R_ring` with the hole `Q = {W(0)}` satisfies the hypothesis of
`not_isSimplyConnectedRegion_of_hole`, so it is not simply connected. -/
example : ¬ IsSimplyConnectedRegion Examples.Cochain.ringRegion :=
  not_isSimplyConnectedRegion_of_hole (Q := {⟨(0, 0), true⟩}) (Finset.singleton_nonempty _)
    (fun q hq => by rw [Finset.mem_singleton.1 hq]; simp [Examples.Cochain.ringRegion])
    (fun q hq g e he hg => by
      rw [Finset.mem_singleton.1 hq] at he
      by_cases hne : g = ⟨(0, 0), true⟩
      · exact Or.inl (Finset.mem_singleton.2 hne)
      have hadj := hexGraph_adj_of_mem_edges (Ne.symm hne) he hg
      rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_true] at hadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hadj
      rcases hadj with rfl | rfl | rfl <;> simp [Examples.Cochain.ringRegion])

/-- The five faces at the origin other than `W(0)`: `B(0)`, `W(−e₁)`, `B(−e₃)`, `W(−e₃)`,
`B(−e₂)`. -/
abbrev fiveFaces : Set TriFace :=
  insert ⟨(0, -1), false⟩ (insert ⟨(-1, -1), true⟩ (insert ⟨(-1, -1), false⟩
    (insert ⟨(-1, 0), true⟩ {⟨(0, 0), false⟩})))

/-- With `Q = {W(0)}` the hypothesis fails for the five faces: `B(e₁)` shares the edge `(e₁, 2)`
with `W(0)` and lies neither in `Q` nor in the region. -/
example : ∃ g : TriFace, ∃ e ∈ (⟨(0, 0), true⟩ : TriFace).edges, e ∈ g.edges ∧
    g ∉ ({⟨(0, 0), true⟩} : Finset TriFace) ∧ g ∉ fiveFaces :=
  ⟨⟨(1, 0), false⟩, ⟨(1, 0), 1⟩, by simp, by simp, by simp, by simp⟩

/-- The five faces at the origin other than `W(0)` are simply connected, by shelling in the order
`B(0)`, `W(−e₁)`, `B(−e₃)`, `W(−e₃)`, `B(−e₂)`, each glued along one edge, adding one new
vertex. -/
theorem isSimplyConnectedRegion_fiveFaces : IsSimplyConnectedRegion fiveFaces := by
  have h1 := isSimplyConnectedRegion_singleton (⟨(0, 0), false⟩ : TriFace)
  have h2 := h1.insert_of_notMem_regionVertices (f := ⟨(-1, 0), true⟩) (i := 1) (p := (-1, 0))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  have h3 := h2.insert_of_notMem_regionVertices (f := ⟨(-1, -1), false⟩) (i := 0) (p := (-1, -1))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  have h4 := h3.insert_of_notMem_regionVertices (f := ⟨(-1, -1), true⟩) (i := 2) (p := (0, -1))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  exact h4.insert_of_notMem_regionVertices (f := ⟨(0, -1), false⟩) (i := 1) (p := (1, 0))
    (by simp) (by simp) (by simp [Prod.ext_iff])

/-- The faces outside the five faces are connected through shared edges, as for every finite simply
connected region; in particular `W(0)` is joined to the rest through `B(e₁)`. -/
example : (hexGraph.induce fiveFacesᶜ).Connected :=
  isSimplyConnectedRegion_fiveFaces.connected_induce_compl (Set.toFinite _)

/-- The empty region is not simply connected. -/
example : ¬ IsSimplyConnectedRegion ∅ := fun h => Set.not_nonempty_empty h.nonempty

end TauCeti.Examples.HoleChecks
