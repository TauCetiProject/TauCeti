/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Basic
public import TauCeti.GroupTheory.Perm.SumCongr

/-! # Components of PD-codes

The arcs of a PD-code and the local strands at its crossings determine a permutation of the
half-edge labels. Its outgoing restriction has one orbit per component meeting a crossing.
Crossing-free components remain an explicit field of `PDCode`.

The orbits of `componentPermOutgoing` correspond to the crossing-bearing components; the
unrestricted `componentPerm` preserves orientation and therefore has separate incoming and
outgoing orbits for each such component.

The traversal follows M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3.
-/

public section
namespace TauCeti
open Equiv Equiv.Perm
namespace PDCode
variable {n : ℕ}

/-- The permutation induced by moving to the opposite slot at each crossing. -/
def crossingTurn (D : PDCode n) : Equiv.Perm (Fin (4 * n)) :=
  D.halfEdge.permCongr
    ((PDCode.crossingSlotEquiv n).permCongr
      (Equiv.prodCongr (Equiv.refl (Fin n)) PDCode.oppositeCrossingSlot))

/-- Computes `crossingTurn` by converting a half-edge to its crossing slot,
    taking the opposite slot, and converting back. -/
theorem crossingTurn_apply (D : PDCode n) (h : Fin (4 * n)) :
    D.crossingTurn h = D.halfEdge
      ((PDCode.crossingSlotEquiv n).permCongr
        (Equiv.prodCongr (Equiv.refl (Fin n)) PDCode.oppositeCrossingSlot)
        (D.halfEdge⁻¹ h)) := by
  simp [crossingTurn, Equiv.Perm.mul_def]

/-- The component traversal moves across an arc and then through a crossing. -/
def componentPerm (D : PDCode n) : Equiv.Perm (Fin (4 * n)) :=
  D.crossingTurn * D.edgePair.val

/-- Traversal pairs the arc first, then takes the opposite crossing slot. -/
@[simp] theorem componentPerm_apply (D : PDCode n) (h : Fin (4 * n)) :
    D.componentPerm h = D.crossingTurn (D.edgePair.val h) := by
  simp [componentPerm, Equiv.Perm.mul_def]

/-- Crossing turns take a crossing slot to its opposite slot. -/
@[simp] theorem crossingTurn_crossing (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.crossingTurn (D.crossing i slot) = D.crossing i (oppositeCrossingSlot slot) := by
  simp [crossingTurn]

/-- Mirroring preserves the opposite-slot permutation. -/
@[simp] theorem crossingTurn_mirror (D : PDCode n) : D.mirror.crossingTurn = D.crossingTurn := by
  simp [crossingTurn]

/-- Mirroring preserves component traversal. -/
@[simp] theorem componentPerm_mirror (D : PDCode n) :
    D.mirror.componentPerm = D.componentPerm := by
  simp [componentPerm]

/-- The number of crossing-bearing components, each represented by two directed traversal orbits.
For an oriented code, `OrientedPDCode.orbitCount_componentPermOutgoing` identifies this with
its outgoing orbit count. -/
noncomputable def crossingComponentCount (D : PDCode n) : ℕ :=
  orbitCount D.componentPerm / 2

/-- The crossing-bearing component count is half the unrestricted traversal orbit count. -/
theorem crossingComponentCount_def (D : PDCode n) :
    D.crossingComponentCount = orbitCount D.componentPerm / 2 := by simp [crossingComponentCount]

/-- A code with no crossing visits has no crossing-bearing components. -/
@[simp] theorem crossingComponentCount_zero (D : PDCode 0) :
    D.crossingComponentCount = 0 := by
  have h := Equiv.Perm.orbitCount_le_card D.componentPerm
  simp at h
  simp [crossingComponentCount, h]

/-- Mirroring preserves the number of crossing-bearing components. -/
@[simp] theorem crossingComponentCount_mirror (D : PDCode n) :
    D.mirror.crossingComponentCount = D.crossingComponentCount := by
  simp [crossingComponentCount]

end PDCode

namespace OrientedPDCode

/-- The crossing turn reverses the orientation of a half-edge. -/
@[simp] theorem orientation_crossingTurn (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.crossingTurn h) = !D.orientation h := by
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨i, slot, rfl⟩ := (PDCode.crossingSlotEquiv n).surjective x
  simp [PDCode.crossingTurn_apply, Prod.map, D.orientation_oppositeCrossingSlot]

/-- The component traversal preserves the orientation of a half-edge. -/
@[simp] theorem orientation_componentPerm (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.toPDCode.componentPerm h) = D.orientation h := by
  rw [PDCode.componentPerm_apply]
  rw [orientation_crossingTurn, D.orientation_edgePair, Bool.not_not]

/-- The component traversal permutation restricted to half-edges pointing away from crossings. -/
noncomputable def componentPermOutgoing (D : OrientedPDCode n) :
    Equiv.Perm {h : Fin (4 * n) // D.orientation h = true} :=
  D.toPDCode.componentPerm.subtypePerm (fun h => by
    simp only [orientation_componentPerm])

/-- Outgoing traversal has the same half-edge value as unrestricted traversal. -/
@[simp] theorem componentPermOutgoing_apply (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.componentPermOutgoing h = ⟨D.toPDCode.componentPerm h, by
      exact (orientation_componentPerm D h).trans h.property⟩ := by
  simp only [componentPermOutgoing, Equiv.Perm.subtypePerm_apply]

end OrientedPDCode
end TauCeti
