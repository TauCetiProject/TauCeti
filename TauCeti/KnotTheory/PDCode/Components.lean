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
  D.crossingTurn * D.edgePair.val

@[simp] theorem componentPerm_def (D : OrientedPDCode n) :
    D.componentPerm = D.crossingTurn * D.edgePair.val := by simp [componentPerm]

private theorem crossingTurn_reverses_orientation (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.crossingTurn h) = !D.orientation h := by
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨i, slot, rfl⟩ := (PDCode.crossingSlotEquiv n).surjective x
  simp [Prod.map, D.orientation_oppositeCrossingSlot]

private theorem componentPerm_preserves_orientation (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.componentPerm h) = D.orientation h := by
  change D.orientation (D.crossingTurn (D.edgePair.val h)) = D.orientation h
  rw [crossingTurn_reverses_orientation, D.orientation_edgePair, Bool.not_not]

/-- The component traversal permutation restricted to half-edges pointing away from crossings. -/
noncomputable def componentPermOutgoing (D : OrientedPDCode n) :
    Equiv.Perm {h : Fin (4 * n) // D.orientation h = true} :=
  Equiv.ofBijective (fun h => ⟨D.componentPerm h, by
    rw [componentPerm_preserves_orientation D h, h.property]⟩) (by
    constructor
    · intro a b hab
      exact Subtype.ext (D.componentPerm.injective (Subtype.ext_iff.mp hab))
    · intro b
      obtain ⟨h, hh⟩ := D.componentPerm.surjective b.1
      refine ⟨⟨h, ?_⟩, ?_⟩
      · rw [← componentPerm_preserves_orientation D h, hh, b.property]
      · exact Subtype.ext hh
  )

/-- Component count of the crossing-bearing part of a PD-code. -/
noncomputable def componentCount (D : OrientedPDCode n) : ℕ :=
  orbitCount (componentPermOutgoing D)

@[simp] theorem componentCount_eq_orbitCount (D : OrientedPDCode n) :
    D.componentCount = orbitCount (componentPermOutgoing D) := by simp [componentCount]

/-- A code with no crossing visits has no crossing-bearing components. -/
theorem componentCount_zero (D : OrientedPDCode 0) : D.componentCount = 0 := by
  have hperm : componentPermOutgoing D =
      (1 : Equiv.Perm {h : Fin 0 // D.orientation h = true}) := by
    apply Equiv.ext
    exact fun h => Subtype.ext (Fin.elim0 h.1)
  rw [componentCount, hperm, orbitCount_one]
  simp

end OrientedPDCode
end TauCeti
