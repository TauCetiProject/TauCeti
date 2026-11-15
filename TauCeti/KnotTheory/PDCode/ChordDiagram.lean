/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.Contraction
public import TauCeti.KnotTheory.PDCode.Planar

/-!
# Planarity of PD-codes through chord diagrams

The underlying graph of a PD-code is the ribbon graph whose rotation is the counterclockwise
rotation `TauCeti.PDCode.crossingRotation` of the slots at each crossing and whose edge involution
is the arc matching. Contracting a spanning tree of a connected code leaves a one-vertex chord
diagram with the same faces, whose `n + 1` bands are the arcs outside the tree.

This file translates planarity, defined by the Euler characteristic, through such contractions:
a connected code is planar exactly when the bands of its contracted chord diagram do not
interleave (`TauCeti.PDCode.isPlanar_iff_isNoncrossingMatching`). A pair of interleaved bands is
thus a finite certificate of nonplanarity, and a noncrossing contraction is a finite
combinatorial model of the planar graph, from which the graph is recovered by expanding the
contracted tree.

## Main results

* `TauCeti.PDCode.nonempty_spanningTreeContraction`: the underlying graph of a connected code
  has a spanning-tree contraction.
* `TauCeti.PDCode.isPlanar_iff_isNoncrossingMatching`: a connected code is planar exactly when the
  bands of any of its spanning-tree contractions do not interleave.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n : ℕ} {D : PDCode n}

/-- The underlying graph of a PD-code with connected underlying graph has a spanning-tree
contraction to a one-vertex chord diagram. -/
theorem nonempty_spanningTreeContraction (hD : D.toPermutationTriple.IsConnected) :
    Nonempty (SpanningTreeContraction D.crossingRotation D.edgePair.val) := by
  have : Nonempty (Fin (4 * n)) := ⟨⟨0, by have := hD.ne_zero; omega⟩⟩
  have hconn := hD.isPretransitive
  rw [← PermutationTriple.closure_pair_eq_monodromyGroup, toPermutationTriple_σ0,
    toPermutationTriple_σ1] at hconn
  exact TauCeti.nonempty_spanningTreeContraction D.edgePair.prop.involutive hconn

/-- **Planarity is noninterleaving of the contracted chord diagram.** A PD-code with connected
underlying graph is planar exactly when the bands of a spanning-tree contraction of the graph do
not interleave, in any numbering of the half-edges making its single vertex cyclic rotation. -/
theorem isPlanar_iff_isNoncrossingMatching (hD : D.toPermutationTriple.IsConnected)
    (c : SpanningTreeContraction D.crossingRotation D.edgePair.val) {m : ℕ}
    (e : Fin (4 * n) ≃ Fin m) (he : e.permCongr c.rotation = finRotate m) :
    D.IsPlanar ↔ (e.permCongr c.matching).IsNoncrossingMatching := by
  have hm : m = 4 * n := by simpa using (Fintype.card_congr e).symm
  rw [c.isNoncrossingMatching_permCongr_matching_iff e he,
    isPlanar_iff_faceCount_eq_of_isConnected hD, faceCount_def, facePerm_def,
    orbitCount_crossingRotation, orbitCount_edgePair]
  omega

end TauCeti.PDCode
