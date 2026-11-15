/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Three.Basic

/-!
# Labelled components under the third Reidemeister move

The local half-edge rewire restricts to an equivalence of outgoing half-edges and conjugates
outgoing traversal. It therefore induces `OrientedPDCode.reidemeisterThreeComponentEquiv`,
a bijection of actual link components, not just an equality of component counts. Every
crossing-free label is fixed individually. The representative formulas in both directions
specify the transport, including its identity action outside the three selected crossings.

The transport is defined for the native rewire at any three distinct crossings. When they
satisfy `PDCode.HasReidemeisterThreeTriangle`, it is the component correspondence of a third
Reidemeister move. Neither planarity nor the triangle's height order is needed for the
traversal conjugacy itself.

The diagram and move conventions follow M. Mastin, *Links and Planar Diagram Codes*,
Definitions 2–3, and W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

open Equiv

variable {n : ℕ} (D : OrientedPDCode n) (c : Fin 3 ↪ Fin n)

/-- The third-move rewire carries outgoing half-edges to outgoing half-edges, preserving the
orientation of each strand. -/
def reidemeisterThreeOutgoingEquiv :
    {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * n) // (D.reidemeisterThree c).orientation h = true} :=
  (D.reidemeisterThreePerm c).subtypeEquiv fun _ ↦ by simp

/-- On half-edge labels, outgoing transport is the native local rewire. -/
@[simp] theorem reidemeisterThreeOutgoingEquiv_apply
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    (D.reidemeisterThreeOutgoingEquiv c h).val = D.reidemeisterThreePerm c h := by
  simp [reidemeisterThreeOutgoingEquiv, Equiv.subtypeEquiv]

/-- Inverse outgoing transport uses the inverse native local rewire. -/
@[simp] theorem reidemeisterThreeOutgoingEquiv_symm_apply
    (h : {h : Fin (4 * n) // (D.reidemeisterThree c).orientation h = true}) :
    ((D.reidemeisterThreeOutgoingEquiv c).symm h).val =
      (D.reidemeisterThreePerm c).symm h := by
  simp [reidemeisterThreeOutgoingEquiv, Equiv.subtypeEquiv]

/-- Outgoing traversal before and after a third-move rewire is conjugate by its outgoing
half-edge equivalence. -/
theorem componentPermOutgoing_reidemeisterThree :
    (D.reidemeisterThree c).componentPermOutgoing =
      (D.reidemeisterThreeOutgoingEquiv c).permCongr D.componentPermOutgoing := by
  ext h
  simp [reidemeisterThreeOutgoingEquiv, Equiv.subtypeEquiv,
    PDCode.componentPerm_reidemeisterThree]

/-- The labelled component bijection for the native third-move rewire. It transports outgoing
traversal classes and keeps each crossing-free circle label. -/
def reidemeisterThreeComponentEquiv : D.Component ≃ (D.reidemeisterThree c).Component :=
  D.componentEquiv _ (D.reidemeisterThreeOutgoingEquiv c)
    (D.componentPermOutgoing_reidemeisterThree c) (finCongr (by simp))

/-- A component represented by an outgoing half-edge is sent to the component represented by
its local rewire image. -/
@[simp] theorem reidemeisterThreeComponentEquiv_componentOfOutgoing
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.reidemeisterThreeComponentEquiv c (D.componentOfOutgoing h) =
      (D.reidemeisterThree c).componentOfOutgoing (D.reidemeisterThreeOutgoingEquiv c h) := by
  exact D.componentEquiv_componentOfOutgoing _ _ _ _ h

/-- The third move keeps every individual crossing-free component label. -/
@[simp] theorem reidemeisterThreeComponentEquiv_inr (i : Fin D.crossinglessComponentCount) :
    D.reidemeisterThreeComponentEquiv c (Sum.inr i) =
      Sum.inr (Fin.cast (by simp) i) := by
  rw [reidemeisterThreeComponentEquiv, componentEquiv_inr]
  rfl

/-- Inverse component transport is represented by inverse outgoing transport. -/
@[simp] theorem reidemeisterThreeComponentEquiv_symm_componentOfOutgoing
    (h : {h : Fin (4 * n) // (D.reidemeisterThree c).orientation h = true}) :
    (D.reidemeisterThreeComponentEquiv c).symm
        ((D.reidemeisterThree c).componentOfOutgoing h) =
      D.componentOfOutgoing ((D.reidemeisterThreeOutgoingEquiv c).symm h) := by
  apply (D.reidemeisterThreeComponentEquiv c).injective
  simp

/-- Inverse component transport also fixes every crossing-free label. -/
@[simp] theorem reidemeisterThreeComponentEquiv_symm_inr
    (i : Fin (D.reidemeisterThree c).crossinglessComponentCount) :
    (D.reidemeisterThreeComponentEquiv c).symm (Sum.inr i) =
      Sum.inr (Fin.cast (by simp) i) := by
  apply (D.reidemeisterThreeComponentEquiv c).injective
  simp

/-- Outside the three selected crossings, a component can be transported using the very same
outgoing half-edge label. This records the unchanged exterior of the local rewire. -/
theorem reidemeisterThreeComponentEquiv_componentOfOutgoing_of_notMem
    {i : Fin n} (hi : i ∉ Set.range c) (k : Fin 4)
    (hk : D.orientation (D.crossing i k) = true) :
    D.reidemeisterThreeComponentEquiv c (D.componentOfOutgoing ⟨D.crossing i k, hk⟩) =
      (D.reidemeisterThree c).componentOfOutgoing ⟨D.crossing i k, by
        rw [orientation_reidemeisterThree_crossing_of_notMem D c hi]
        exact hk⟩ := by
  rw [reidemeisterThreeComponentEquiv_componentOfOutgoing]
  congr 1
  apply Subtype.ext
  rw [reidemeisterThreeOutgoingEquiv_apply]
  exact PDCode.reidemeisterThreePerm_crossing_of_notMem D.toPDCode c hi k

end TauCeti.OrientedPDCode
