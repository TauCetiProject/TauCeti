/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Components
public import TauCeti.Combinatorics.RibbonGraph.OfPermutationTriple

/-!
# Planar rotation systems for PD-codes

The cyclic crossing slots and the arc matching of a `PDCode` form an orientable rotation
system. Its vertices are the crossings, its edges are the matched pairs, and its faces are
the cycles of `PDCode.facePerm`, including fixed points. Capping those boundary cycles by
disks gives a closed orientable surface for each connected component of the projection graph.
The Euler condition `F = n + 2c` says that every such surface has genus zero: there are `n`
vertices, `2n` edges, and `c` connected components. `PDCode.IsPlanar` imposes this condition.

The associated `PermutationTriple` and its ribbon graph provide the connectivity and Euler
characteristic API. Crossing-free circles are retained in the original code; they can be placed
in disjoint disks. This representation does not choose an outer face or nesting of disconnected
projection components. Consequently a common-face move below concerns a single boundary cycle,
not two arbitrarily chosen components of the complement of a disconnected drawing.

This is the rotation-system encoding of planar diagrams (Lickorish, *An Introduction to Knot
Theory*, Chapter 1), using the permutation convention of the existing PD-code modules.
It supplies the planar/locality layer for diagram Reidemeister moves and the Jones polynomial
from the bracket. No geometric realization theorem is asserted.
-/

public section

namespace TauCeti.PDCode

variable {n : ℕ}

/-- Counterclockwise rotation by one slot at each crossing. -/
def crossingRotation (D : PDCode n) : Equiv.Perm (Fin (4 * n)) :=
  D.halfEdge.permCongr ((crossingSlotEquiv n).permCongr
    (Equiv.prodCongr (Equiv.refl (Fin n)) (finCycle 1)))

/-- Rotation takes a crossing slot to the next counterclockwise slot. -/
@[simp] theorem crossingRotation_halfEdge (D : PDCode n) (i : Fin n) (s : Fin 4) :
    D.crossingRotation (D.halfEdge (crossingSlotEquiv n (i, s))) =
      D.halfEdge (crossingSlotEquiv n (i, s + 1)) := by
  simp [crossingRotation, finCycle_apply]

/-- Follow an arc, then turn counterclockwise to follow the boundary of a face. -/
def facePerm (D : PDCode n) : Equiv.Perm (Fin (4 * n)) :=
  D.crossingRotation * D.edgePair.val

/-- Face traversal crosses the arc before rotating at its endpoint. -/
@[simp] theorem facePerm_apply (D : PDCode n) (x : Fin (4 * n)) :
    D.facePerm x = D.crossingRotation (D.edgePair.val x) := by
  simp only [facePerm, Equiv.Perm.mul_def, Equiv.trans_apply]

/-- The permutation triple carried by the PD-code rotation system.

The first component is the inverse crossing rotation, the second is the arc matching, and the
third component is the face permutation. This is the bridge to the existing ribbon-graph API.
-/
def projectionTriple (D : PDCode n) : PermutationTriple (4 * n) :=
  PermutationTriple.ofTwo D.crossingRotation⁻¹ D.edgePair.val

@[simp] theorem projectionTriple_σ0 (D : PDCode n) :
    D.projectionTriple.σ0 = D.crossingRotation⁻¹ := by
  simp only [projectionTriple, PermutationTriple.ofTwo_σ0]

@[simp] theorem projectionTriple_σ1 (D : PDCode n) :
    D.projectionTriple.σ1 = D.edgePair.val := by
  simp only [projectionTriple, PermutationTriple.ofTwo_σ1]

@[simp] theorem projectionTriple_σinf (D : PDCode n) :
    D.projectionTriple.σinf = D.facePerm := by
  have hpair : D.edgePair.val⁻¹ = D.edgePair.val := by
    apply Equiv.ext
    intro x
    apply D.edgePair.val.injective
    simp [D.edgePair.apply_apply]
  rw [projectionTriple, PermutationTriple.ofTwo_σinf, facePerm]
  simp [hpair]

/-- A PD rotation system is planar when capping its face cycles gives genus zero in every
connected component. The formula is `V - E + F = 2c`, with `V = n` and `E = 2n`. -/
def IsPlanar (D : PDCode n) : Prop :=
  orbitCount D.projectionTriple.σinf =
    n + 2 * Nat.card D.projectionTriple.ribbonGraph.ConnectedComponent

/-- The face-count characterization of planarity of a PD rotation system. -/
theorem isPlanar_iff (D : PDCode n) : D.IsPlanar ↔
    orbitCount D.projectionTriple.σinf =
      n + 2 * Nat.card D.projectionTriple.ribbonGraph.ConnectedComponent := Iff.rfl

/-- For a connected projection, planarity is the Euler condition `F = n + 2`. -/
theorem isPlanar_iff_of_connected (D : PDCode n)
    (h : D.projectionTriple.IsConnected) :
    D.IsPlanar ↔ orbitCount D.facePerm = n + 2 := by
  have hr : D.projectionTriple.ribbonGraph.IsConnected :=
    (PermutationTriple.isConnected_ribbonGraph D.projectionTriple).mpr h
  have hc : Fintype.card D.projectionTriple.ribbonGraph.ConnectedComponent = 1 :=
    (BipartiteRibbonGraph.isConnected_iff_card_connectedComponent_eq_one _).mp hr
  rw [isPlanar_iff, projectionTriple_σinf, Nat.card_eq_fintype_card, hc]

end TauCeti.PDCode

namespace TauCeti

/-- An oriented planar rotation-system diagram. The subtype retains the existing oriented
PD-code and adds the genus-zero condition, without choosing a geometric drawing or outer face. -/
abbrev OrientedPlanarDiagram (n : ℕ) := {D : OrientedPDCode n // D.toPDCode.IsPlanar}

end TauCeti
