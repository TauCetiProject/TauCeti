/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Basic

/-!
# Diagonal reflection of grid stabilizations

Transposition exchanges the new row and column of a stabilization and sends the split
marking to its transposed position. In particular it preserves all eight elementary
stabilization types, including those crossing the chosen cut of the torus. This lets
transposition act on grid diagrams modulo moves.

The stabilization conventions follow Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- Transposition exchanges the inserted row and column of an `O`-stabilization. -/
@[simp]
theorem transpose_stabilizeO (c r : Fin (n + 1)) (s : Fin n) :
    (G.stabilizeO c r s).transpose = G.transpose.stabilizeO r c (G.O s) := by
  ext1 <;> simp [GridState.transpose_splitPoint, GridState.transpose_insertPoint]

/-- Transposition exchanges the inserted row and column of an `X`-stabilization. -/
@[simp]
theorem transpose_stabilizeX (c r : Fin (n + 1)) (s : Fin n) :
    (G.stabilizeX c r s).transpose = G.transpose.stabilizeX r c (G.X s) := by
  ext1 <;> simp [GridState.transpose_splitPoint, GridState.transpose_insertPoint]

/-- Diagonal reflection preserves elementary `O`-stabilizations. -/
@[simp]
theorem isOStabilization_transpose (G' : GridDiagram (n + 1)) :
    IsOStabilization G.transpose G'.transpose ↔ IsOStabilization G G' := by
  have forward {H : GridDiagram n} {H' : GridDiagram (n + 1)}
      (h : IsOStabilization H H') : IsOStabilization H.transpose H'.transpose := by
    obtain ⟨c, r, s, hc, hr, rfl⟩ := (isOStabilization_iff _ _).mp h
    apply (isOStabilization_iff _ _).mpr
    refine ⟨r, c, H.O s, hr, ?_, by simp⟩
    simpa only [transpose_O, GridState.transpose_apply_apply] using hc
  exact ⟨fun h ↦ by simpa only [transpose_transpose] using forward h, forward⟩

/-- Diagonal reflection preserves elementary `X`-stabilizations. -/
@[simp]
theorem isXStabilization_transpose (G' : GridDiagram (n + 1)) :
    IsXStabilization G.transpose G'.transpose ↔ IsXStabilization G G' := by
  simpa only [swapMarkings_transpose, isOStabilization_swapMarkings] using
    isOStabilization_transpose G.swapMarkings G'.swapMarkings

/-- Diagonal reflection preserves elementary stabilizations of either marking type. -/
@[simp]
theorem isStabilization_transpose (G' : GridDiagram (n + 1)) :
    IsStabilization G.transpose G'.transpose ↔ IsStabilization G G' := by
  simp only [isStabilization_iff, isOStabilization_transpose, isXStabilization_transpose]

/-- Diagonal reflection preserves elementary destabilizations. -/
@[simp]
theorem isDestabilization_transpose (G' : GridDiagram (n + 1)) :
    IsDestabilization G'.transpose G.transpose ↔ IsDestabilization G' G := by
  simp only [isDestabilization_iff_isStabilization, isStabilization_transpose]

end TauCeti.GridDiagram
