/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode
public import TauCeti.GroupTheory.Perm.OrbitCount

/-! # Components of PD-codes

The arcs of a PD-code and the local strands at its crossings determine a permutation of the
half-edge labels. Its orbits are the components meeting a crossing. Crossing-free components
remain the explicit field of `OrientedPDCode`.
-/

public section
namespace TauCeti
open Equiv Equiv.Perm
namespace OrientedPDCode
variable {n : ℕ}

/-- The permutation induced by moving to the opposite slot at each crossing. -/
def crossingTurn (D : OrientedPDCode n) : Equiv.Perm (Fin (4 * n)) :=
  D.halfEdge *
    (PDCode.crossingSlotEquiv n).permCongr
      (Equiv.prodCongr (Equiv.refl (Fin n)) PDCode.oppositeCrossingSlot) * D.halfEdge⁻¹

@[simp] theorem crossingTurn_apply (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.crossingTurn h = D.halfEdge
      ((PDCode.crossingSlotEquiv n).permCongr
        (Equiv.prodCongr (Equiv.refl (Fin n)) PDCode.oppositeCrossingSlot)
        (D.halfEdge⁻¹ h)) := by
  simp [crossingTurn, Equiv.Perm.mul_def]

/-- The component traversal moves across an arc and then through its crossing. -/
def componentPerm (D : OrientedPDCode n) : Equiv.Perm (Fin (4 * n)) :=
  D.edgePair.val * D.crossingTurn

@[simp] theorem componentPerm_def (D : OrientedPDCode n) :
    D.componentPerm = D.edgePair.val * D.crossingTurn := by simp [componentPerm]

/-- Component count of the crossing-bearing part of a PD-code. -/
noncomputable def componentCount (D : OrientedPDCode n) : ℕ := orbitCount D.componentPerm

@[simp] theorem componentCount_eq_orbitCount (D : OrientedPDCode n) :
    D.componentCount = orbitCount D.componentPerm := by simp [componentCount]

/-- A code with no crossing visits has no crossing-bearing components. -/
theorem componentCount_zero (D : OrientedPDCode 0) : D.componentCount = 0 := by
  have hperm : D.componentPerm = (1 : Equiv.Perm (Fin 0)) := by
    apply Equiv.ext
    exact fun h => Fin.elim0 h
  rw [componentCount, hperm, orbitCount_one]
  simp

end OrientedPDCode
end TauCeti
