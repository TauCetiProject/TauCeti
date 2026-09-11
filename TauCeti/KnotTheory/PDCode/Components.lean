/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Basic
public import TauCeti.GroupTheory.Perm.OrbitCount

/-! # Components of PD-codes

The arcs of a PD-code and the local strands at its crossings determine a permutation of the
half-edge labels. Its orbits are the components meeting a crossing. Crossing-free components
remain the explicit field of `OrientedPDCode`.

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
@[simp] theorem crossingTurn_apply (D : PDCode n) (h : Fin (4 * n)) :
    D.crossingTurn h = D.halfEdge
      ((PDCode.crossingSlotEquiv n).permCongr
        (Equiv.prodCongr (Equiv.refl (Fin n)) PDCode.oppositeCrossingSlot)
        (D.halfEdge⁻¹ h)) := by
  simp [crossingTurn, Equiv.Perm.mul_def]

/-- The component traversal moves across an arc and then through a crossing. -/
def componentPerm (D : PDCode n) : Equiv.Perm (Fin (4 * n)) :=
  D.crossingTurn * D.edgePair.val

@[simp] theorem componentPerm_apply (D : PDCode n) (h : Fin (4 * n)) :
    D.componentPerm h = D.crossingTurn (D.edgePair.val h) := by
  simp [componentPerm, Equiv.Perm.mul_def]

end PDCode

namespace OrientedPDCode

/-- The crossing turn reverses the orientation of a half-edge. -/
@[simp] theorem crossingTurn_reverses_orientation (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.crossingTurn h) = !D.orientation h := by
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨i, slot, rfl⟩ := (PDCode.crossingSlotEquiv n).surjective x
  simp [PDCode.crossingTurn_apply, Prod.map, D.orientation_oppositeCrossingSlot]

/-- The component traversal preserves the orientation of a half-edge. -/
@[simp] theorem componentPerm_preserves_orientation (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.toPDCode.componentPerm h) = D.orientation h := by
  rw [PDCode.componentPerm_apply]
  rw [crossingTurn_reverses_orientation, D.orientation_edgePair, Bool.not_not]

/-- The component traversal permutation restricted to half-edges pointing away from crossings. -/
noncomputable def componentPermOutgoing (D : OrientedPDCode n) :
    Equiv.Perm {h : Fin (4 * n) // D.orientation h = true} :=
  D.toPDCode.componentPerm.subtypePerm (fun h => by
    simp only [componentPerm_preserves_orientation])

@[simp] theorem componentPermOutgoing_apply (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.componentPermOutgoing h = ⟨D.toPDCode.componentPerm h, by
      exact (componentPerm_preserves_orientation D h).trans h.property⟩ := by
  apply Subtype.ext
  rfl

/-- Component count of the crossing-bearing part of a PD-code. -/
noncomputable def crossingComponentCount (D : OrientedPDCode n) : ℕ :=
  orbitCount (componentPermOutgoing D)

theorem crossingComponentCount_def (D : OrientedPDCode n) :
    D.crossingComponentCount = orbitCount (componentPermOutgoing D) := by
  simp [crossingComponentCount]

/-- A code with no crossing visits has no crossing-bearing components. -/
@[simp] theorem crossingComponentCount_zero (D : OrientedPDCode 0) :
    D.crossingComponentCount = 0 := by
  have hperm : componentPermOutgoing D =
      (1 : Equiv.Perm {h : Fin 0 // D.orientation h = true}) := by
    apply Equiv.ext
    exact fun h => Subtype.ext (Fin.elim0 h.1)
  rw [crossingComponentCount, hperm, orbitCount_one]
  simp

end OrientedPDCode
end TauCeti
