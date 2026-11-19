/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Components

/-!
# Coordinates for visits to an oriented crossing

At an oriented crossing, its four half-edges are distinguished by two Boolean choices:
over versus under, and outgoing versus incoming. These coordinates identify outgoing
half-edges with pairs consisting of a crossing and an over/under choice. They are useful
for reading a diagram by following its component traversal, independently of the arbitrary
starting slot of each crossing.

## References

* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3.
-/

public noncomputable section

namespace TauCeti.OrientedPDCode

variable {n : ℕ}

/-- The four slots at an oriented crossing are determined by whether the strand is over
and whether the half-edge points out of the crossing. -/
def crossingSlotDataEquiv (D : OrientedPDCode n) (c : Fin n) : Fin 4 ≃ Bool × Bool :=
  Equiv.ofBijective (fun s => (D.isOver c s, D.orientation (D.crossing c s))) <| by
    apply (Fintype.bijective_iff_injective_and_card _).2
    refine ⟨?_, by decide⟩
    intro s t h
    have ho := congrArg Prod.fst h
    have hd := congrArg Prod.snd h
    dsimp only at ho hd
    rw [D.orientation_crossing_eq c s, D.orientation_crossing_eq c t] at hd
    cases h0 : D.orientation (D.crossing c 0) <;>
      cases h1 : D.orientation (D.crossing c 1) <;> cases hp : D.overPair c <;>
      fin_cases s <;> fin_cases t <;> simp_all [PDCode.isOver_def]

/-- Slot coordinates record over/under and outgoing/incoming status. -/
@[simp]
theorem crossingSlotDataEquiv_apply (D : OrientedPDCode n) (c : Fin n) (s : Fin 4) :
    D.crossingSlotDataEquiv c s = (D.isOver c s, D.orientation (D.crossing c s)) :=
  (rfl)

/-- Half-edges are equivalently crossing labels with over/under and outgoing/incoming data. -/
def halfEdgeDataEquiv (D : OrientedPDCode n) :
    Fin (4 * n) ≃ Fin n × Bool × Bool :=
  (D.halfEdge.symm.trans (PDCode.crossingSlotEquiv n).symm).trans
    (Equiv.prodCongrRight D.crossingSlotDataEquiv)

/-- The coordinates of a specified crossing slot retain its crossing label and decorations. -/
@[simp]
theorem halfEdgeDataEquiv_crossing (D : OrientedPDCode n) (c : Fin n) (s : Fin 4) :
    D.halfEdgeDataEquiv (D.halfEdge (PDCode.crossingSlotEquiv n (c, s))) =
      (c, D.isOver c s, D.orientation (D.halfEdge (PDCode.crossingSlotEquiv n (c, s)))) := by
  simp [halfEdgeDataEquiv]

/-- The final Boolean of half-edge data records its orientation. -/
@[simp]
theorem halfEdgeDataEquiv_orientation (D : OrientedPDCode n) (h : Fin (4 * n)) :
    (D.halfEdgeDataEquiv h).2.2 = D.orientation h := by
  obtain ⟨⟨c, s⟩, rfl⟩ := ((PDCode.crossingSlotEquiv n).trans D.halfEdge).surjective h
  simp

/-- Outgoing half-edges are equivalently crossings together with an over/under choice. -/
def outgoingHalfEdgeDataEquiv (D : OrientedPDCode n) :
    {h : Fin (4 * n) // D.orientation h = true} ≃ Fin n × Bool where
  toFun h := ((D.halfEdgeDataEquiv h).1, (D.halfEdgeDataEquiv h).2.1)
  invFun p := ⟨D.halfEdgeDataEquiv.symm (p.1, p.2, true), by
    rw [← D.halfEdgeDataEquiv_orientation, Equiv.apply_symm_apply]⟩
  left_inv h := by
    apply Subtype.ext
    apply D.halfEdgeDataEquiv.injective
    simp only [Equiv.apply_symm_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · rfl
    · simp [h.property]
  right_inv p := by simp

/-- Outgoing coordinates forget the final, necessarily true, direction coordinate. -/
@[simp]
theorem outgoingHalfEdgeDataEquiv_apply (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.outgoingHalfEdgeDataEquiv h =
      ((D.halfEdgeDataEquiv h).1, (D.halfEdgeDataEquiv h).2.1) := (rfl)

/-- Passing through a crossing retains its label and over/under choice and reverses direction. -/
@[simp]
theorem halfEdgeDataEquiv_crossingTurn (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.halfEdgeDataEquiv (D.crossingTurn h) =
      ((D.halfEdgeDataEquiv h).1, (D.halfEdgeDataEquiv h).2.1,
        !(D.halfEdgeDataEquiv h).2.2) := by
  obtain ⟨⟨c, s⟩, rfl⟩ := ((PDCode.crossingSlotEquiv n).trans D.halfEdge).surjective h
  simp only [Equiv.trans_apply, PDCode.crossingTurn_crossing]
  simp only [PDCode.crossing_apply, halfEdgeDataEquiv_crossing]
  rw [PDCode.isOver_oppositeCrossingSlot]
  congr 2
  exact D.orientation_oppositeCrossingSlot c s

end TauCeti.OrientedPDCode
