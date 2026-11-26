/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Hole

/-!
# Checks: holes obstruct simple connectivity

* For the ring `R_ring` round `W(0)` with `Q = {W(0)}`, see
  `TauCeti/Examples/Combinatorics/Tiling/Lozenge/Cochain.lean`, where `R_ring` is defined.
* The five faces at the origin other than `W(0)` with `Q = {W(0)}` do not: `B(e₁)` shares the edge
  `(e₁, 2)` with `W(0)` and lies in neither set. That region is simply connected, by shelling.
* For `R = ∅` the conclusion holds trivially, since simple connectivity includes nonemptiness.
-/

public section

namespace TauCeti.Examples.HoleChecks

open TauCeti

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
`B(0)`, `W(−e₁)`, `B(−e₃)`, `W(−e₃)`, `B(−e₂)`, one new edge and vertex each time. -/
example : IsSimplyConnectedRegion fiveFaces := by
  have h1 := isSimplyConnectedRegion_singleton (⟨(0, 0), false⟩ : TriFace)
  have h2 := h1.insert_of_notMem_regionVertices (f := ⟨(-1, 0), true⟩) (i := 1) (p := (-1, 0))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  have h3 := h2.insert_of_notMem_regionVertices (f := ⟨(-1, -1), false⟩) (i := 0) (p := (-1, -1))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  have h4 := h3.insert_of_notMem_regionVertices (f := ⟨(-1, -1), true⟩) (i := 2) (p := (0, -1))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  exact h4.insert_of_notMem_regionVertices (f := ⟨(0, -1), false⟩) (i := 1) (p := (1, 0))
    (by simp) (by simp) (by simp [Prod.ext_iff])

/-- The empty region is not simply connected. -/
example : ¬ IsSimplyConnectedRegion ∅ := fun h => Set.not_nonempty_empty h.nonempty

end TauCeti.Examples.HoleChecks
