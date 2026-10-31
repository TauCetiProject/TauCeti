/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.UnknottingNumber
public import TauCeti.KnotTheory.Grid.Move.Transpose

/-!
# Transposition preserves unknotting number

Diagonal reflection carries cross-commutations to cross-commutations and fixes the
unknot. It is therefore an automorphism of the crossing-change graph and preserves
its extended distances, including infinite unknotting numbers.

The crossing-change conventions follow Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 6.
-/

public section

namespace TauCeti.GridLink

/-- Transposition transports a crossing change between grid links. -/
theorem IsCrossingChange.transpose {L L' : GridLink} (h : IsCrossingChange L L') :
    IsCrossingChange L.transpose L'.transpose := by
  obtain ⟨n, G, G', hcross, rfl, rfl⟩ := (isCrossingChange_iff _ _).mp h
  simpa only [transpose_toGridLink] using
    ((GridDiagram.isCrossCommutation_transpose _ _).mpr hcross).isCrossingChange

/-- Transposition preserves and reflects the crossing-change relation. -/
@[simp]
theorem isCrossingChange_transpose_iff {L L' : GridLink} :
    IsCrossingChange L.transpose L'.transpose ↔ IsCrossingChange L L' :=
  ⟨fun h ↦ by simpa only [transpose_transpose] using h.transpose,
    IsCrossingChange.transpose⟩

/-- Transposition is an automorphism of the crossing-change graph. -/
def crossingChangeGraphTransposeIso : crossingChangeGraph ≃g crossingChangeGraph where
  toEquiv := transposeEquiv
  map_rel_iff' := by simp

/-- The graph automorphism acts by transposition of grid links. -/
@[simp]
theorem crossingChangeGraphTransposeIso_apply (L : GridLink) :
    crossingChangeGraphTransposeIso L = L.transpose :=
  transposeEquiv_apply L

/-- The inverse graph automorphism also acts by transposition. -/
@[simp]
theorem crossingChangeGraphTransposeIso_symm_apply (L : GridLink) :
    crossingChangeGraphTransposeIso.symm L = L.transpose :=
  transposeEquiv_symm_apply L

/-- Transposition preserves the extended crossing-change distance between any two grid links. -/
@[simp]
theorem crossingChangeGraph_edist_transpose (L L' : GridLink) :
    crossingChangeGraph.edist L.transpose L'.transpose = crossingChangeGraph.edist L L' := by
  simpa only [crossingChangeGraphTransposeIso_apply] using
    crossingChangeGraphTransposeIso.edist_eq L L'

/-- Diagonal reflection fixes the unknot, whose two-by-two diagram is symmetric. -/
@[simp]
theorem transpose_unknot : unknot.transpose = unknot := by
  have h : (GridDiagram.unknot 0).transpose = GridDiagram.unknot 0 := by
    ext c <;> simp only [GridDiagram.transpose_O, GridDiagram.transpose_X,
      GridState.transpose_apply, GridDiagram.unknot_O_toPerm, GridDiagram.unknot_X_toPerm] <;>
      fin_cases c <;> decide
  rw [← GridDiagram.toGridLink_unknot 0, transpose_toGridLink, h]

/-- Transposition preserves unknotting number, also when it is infinite. -/
@[simp]
theorem unknottingNumber_transpose (L : GridLink) :
    L.transpose.unknottingNumber = L.unknottingNumber := by
  simpa only [unknottingNumber_def, transpose_unknot] using
    crossingChangeGraph_edist_transpose L unknot

end TauCeti.GridLink
