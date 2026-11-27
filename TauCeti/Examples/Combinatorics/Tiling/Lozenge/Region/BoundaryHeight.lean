/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.BoundaryHeight

/-!
# Checks: boundary heights

* Unit hexagon: integrating `c₀` round the outer hexagon from `h(1,0) = 0` gives `h = 0` at
  `(1,0)`, `(1,1)`, `(0,1)` and `h = −1` at `(−1,0)`, `(−1,−1)`, `(0,−1)` (the two diagonal
  boundary edges carry the increments), consistently round the loop.
* A single white face `W(0)` has no boundary height: round the triangle `c₀` sums to
  `0 + 0 − 1 ≠ 0`. The same holds for `W(0)` and `B(1,1)` meeting at the vertex `(1,1)`, a region
  with one face of each colour that is therefore untileable.
-/

public section

namespace TauCeti.Examples.LozengeBoundaryHeightChecks

open TauCeti

/-! ### The unit hexagon -/

/-- The unit hexagon: the six faces round `0`. -/
abbrev hexagon : Set TriFace := vertexFaces (0, 0)

theorem mem_boundaryEdges_hexagon (e : TriEdge)
    (he : (e.whiteFace ∈ hexagon ↔ e.blackFace ∉ hexagon) := by
      simp [hexagon, vertexFaces_def, Prod.ext_iff]) :
    e ∈ boundaryEdges hexagon :=
  mem_boundaryEdges_iff.2 he

/-- The boundary height of the unit hexagon normalised by `h(1,0) = 0`. -/
example {h : ℤ × ℤ → ℤ} (hh : IsBoundaryHeight hexagon h) (h₀ : h (1, 0) = 0) :
    h (1, 1) = 0 ∧ h (0, 1) = 0 ∧ h (-1, 0) = -1 ∧ h (-1, -1) = -1 ∧ h (0, -1) = -1 := by
  have h₁ := isBoundaryHeight_def.1 hh ⟨(1, 0), 1⟩ (mem_boundaryEdges_hexagon _)
  have h₂ := isBoundaryHeight_def.1 hh ⟨(0, 1), 0⟩ (mem_boundaryEdges_hexagon _)
  have h₃ := isBoundaryHeight_def.1 hh ⟨(-1, 0), 2⟩ (mem_boundaryEdges_hexagon _)
  have h₄ := isBoundaryHeight_def.1 hh ⟨(-1, -1), 1⟩ (mem_boundaryEdges_hexagon _)
  have h₅ := isBoundaryHeight_def.1 hh ⟨(-1, -1), 0⟩ (mem_boundaryEdges_hexagon _)
  simp only [TriEdge.target_mk, latticeDir_zero, latticeDir_one, latticeDir_two,
    neutralIncrement_def, Prod.mk_add_mk] at h₁ h₂ h₃ h₄ h₅
  norm_num at h₁ h₂ h₃ h₄ h₅
  omega

/-- The sixth boundary edge `(0,−1) → (1,0)` is consistent with the other five: `c₀` sums to `0`
round the outer hexagon. -/
example {h : ℤ × ℤ → ℤ} (hh : IsBoundaryHeight hexagon h) : h (1, 0) - h (0, -1) = 1 := by
  have := isBoundaryHeight_def.1 hh ⟨(0, -1), 2⟩ (mem_boundaryEdges_hexagon _)
  simp only [TriEdge.target_mk, latticeDir_two, neutralIncrement_def, Prod.mk_add_mk] at this
  norm_num at this
  exact this

/-! ### Regions without boundary heights -/

/-- If the three edges of `W(0)` are boundary edges of `R`, then `R` has no boundary height. -/
theorem not_isBoundaryHeight_of_edges {R : Set TriFace}
    (hR : ∀ k : Fin 3, (⟨(0, 0), true⟩ : TriFace).edge k ∈ boundaryEdges R) (h : ℤ × ℤ → ℤ) :
    ¬ IsBoundaryHeight R h := fun hh => by
  have h₁ := isBoundaryHeight_def.1 hh _ (hR 0)
  have h₂ := isBoundaryHeight_def.1 hh _ (hR 1)
  have h₃ := isBoundaryHeight_def.1 hh _ (hR 2)
  simp only [TriFace.edge_mk_true, TriEdge.target_mk, latticeDir_zero, latticeDir_one,
    latticeDir_two, neutralIncrement_def, Prod.mk_add_mk] at h₁ h₂ h₃
  norm_num at h₁ h₂ h₃
  omega

/-- A single white face has no boundary height. -/
example (h : ℤ × ℤ → ℤ) : ¬ IsBoundaryHeight {⟨(0, 0), true⟩} h :=
  not_isBoundaryHeight_of_edges
    (fun k => mem_boundaryEdges_iff.2 (by fin_cases k <;> simp [Prod.ext_iff])) h

/-- `W(0)` and `B(1,1)`, meeting at the vertex `(1,1)`, have no boundary height, so they have no
tiling although they have one face of each colour. -/
example (h : ℤ × ℤ → ℤ) : ¬ IsBoundaryHeight {⟨(0, 0), true⟩, ⟨(1, 1), false⟩} h :=
  not_isBoundaryHeight_of_edges
    (fun k => mem_boundaryEdges_iff.2 (by fin_cases k <;> simp [Prod.ext_iff])) h

/-- Hence `W(0)` and `B(1,1)` have no tiling with a height function. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn {⟨(0, 0), true⟩, ⟨(1, 1), false⟩} H) :
    ¬ IsTiling {⟨(0, 0), true⟩, ⟨(1, 1), false⟩} (tilingOfHeightOn {⟨(0, 0), true⟩,
      ⟨(1, 1), false⟩} H) := fun hM =>
  not_isBoundaryHeight_of_edges
    (fun k => mem_boundaryEdges_iff.2 (by fin_cases k <;> simp [Prod.ext_iff])) H
    (hH.isBoundaryHeight_iff.2 hM)

end TauCeti.Examples.LozengeBoundaryHeightChecks
