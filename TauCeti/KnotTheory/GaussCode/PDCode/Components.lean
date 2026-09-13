/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.PDCode.Basic
public import TauCeti.KnotTheory.PDCode.Components
import TauCeti.GroupTheory.Perm.OrbitCountFinRotate

/-!
# Component traversal of the PD-code of a Gauss code

The outgoing half-edges of a converted Gauss code are canonically its visits. Under this
identification, PD component traversal is cyclic rotation of the visits. Consequently the
conversion produces a single crossing-bearing component when there are crossings; in the
crossing-free case its explicit circle is the unique component instead.

The traversal comparison is the component bookkeeping needed to recover a Gauss word by
traversing a one-component oriented PD-code from a chosen start. It compares combinatorial
codes, without imposing planar realizability.

The conventions follow M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3.
-/

public section

namespace TauCeti.BasedOrientedGaussCode

variable {n : ℕ}

/-- Turning through a crossing preserves the visit and exchanges its two half-edges. -/
@[simp]
theorem toOrientedPDCode_crossingTurn_visitHalfEdge (D : BasedOrientedGaussCode n)
    (i : Fin (2 * n)) (outgoing : Bool) :
    D.toOrientedPDCode.crossingTurn (visitHalfEdgeEquiv n (i, outgoing)) =
      visitHalfEdgeEquiv n (i, !outgoing) := by
  obtain ⟨⟨c, slot⟩, hs⟩ :=
    ((PDCode.crossingSlotEquiv n).trans D.toOrientedPDCode.halfEdge).surjective
      (visitHalfEdgeEquiv n (i, outgoing))
  have hslot : D.toOrientedPDCode.halfEdge (PDCode.crossingSlotEquiv n (c, slot)) =
      visitHalfEdgeEquiv n (i, outgoing) := hs
  have hdata := (visitHalfEdgeEquiv n).injective
    ((D.toOrientedPDCode_crossing c slot).symm.trans hslot)
  rw [← hslot, PDCode.crossingTurn_crossing, PDCode.crossing_apply,
    toOrientedPDCode_crossing]
  simp only [crossingVisit_oppositeCrossingSlot, crossingOutgoing_oppositeCrossingSlot]
  rw [Prod.mk.injEq] at hdata
  simp [hdata.1, hdata.2]

/-- Visits correspond to outgoing half-edges of the converted PD-code. -/
noncomputable def outgoingHalfEdgeEquiv (D : BasedOrientedGaussCode n) :
    Fin (2 * n) ≃ {h : Fin (4 * n) // D.toOrientedPDCode.orientation h = true} where
  toFun i := ⟨visitHalfEdgeEquiv n (i, true), by simp⟩
  invFun h := ((visitHalfEdgeEquiv n).symm h).1
  left_inv i := by simp
  right_inv h := by
    apply Subtype.ext
    obtain ⟨⟨i, outgoing⟩, hi⟩ := (visitHalfEdgeEquiv n).surjective h.val
    have ho : outgoing = true := by
      simpa only [← hi, toOrientedPDCode_orientation_halfEdge] using h.property
    simp [← hi, ho]

/-- The outgoing half-edge corresponding to a visit uses its outgoing endpoint label. -/
@[simp]
theorem outgoingHalfEdgeEquiv_apply (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    (D.outgoingHalfEdgeEquiv i).val = visitHalfEdgeEquiv n (i, true) := (rfl)

/-- Recovering the visit forgets the outgoing decoration after decoding its half-edge label. -/
@[simp]
theorem outgoingHalfEdgeEquiv_symm_apply (D : BasedOrientedGaussCode n)
    (h : {h : Fin (4 * n) // D.toOrientedPDCode.orientation h = true}) :
    D.outgoingHalfEdgeEquiv.symm h = ((visitHalfEdgeEquiv n).symm h.val).1 := (rfl)

/-- Outgoing component traversal of a converted Gauss code is cyclic rotation of its visits. -/
theorem toOrientedPDCode_componentPermOutgoing (D : BasedOrientedGaussCode n) :
    D.toOrientedPDCode.componentPermOutgoing = D.outgoingHalfEdgeEquiv.permCongr (finRotate _) := by
  ext h
  obtain ⟨i, rfl⟩ := D.outgoingHalfEdgeEquiv.surjective h
  simp [Equiv.permCongr_apply, OrientedPDCode.componentPermOutgoing_apply]

/-- A Gauss code with crossings produces exactly one crossing-bearing PD component. -/
@[simp]
theorem toOrientedPDCode_crossingComponentCount (D : BasedOrientedGaussCode n) :
    D.toOrientedPDCode.toPDCode.crossingComponentCount = if n = 0 then 0 else 1 := by
  rw [← OrientedPDCode.orbitCount_componentPermOutgoing,
    toOrientedPDCode_componentPermOutgoing, Equiv.orbitCount_permCongr, orbitCount_finRotate]
  simp

/-- Including the explicit crossing-free circles, the converted code has exactly one component. -/
theorem toOrientedPDCode_componentCount (D : BasedOrientedGaussCode n) :
    D.toOrientedPDCode.toPDCode.crossingComponentCount +
      D.toOrientedPDCode.crossinglessComponentCount = 1 := by
  simp only [toOrientedPDCode_crossingComponentCount, toOrientedPDCode_crossinglessComponentCount]
  split <;> simp

end TauCeti.BasedOrientedGaussCode
