/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.TopBranchedCover.Invariants
public import TauCeti.Combinatorics.RibbonGraph.ConnectedClassInvariants

/-!
# Dessin classification of topological branched covers of the sphere

Classifies `TopBranchedCover.IsoClass.{0} n` by `Quotient (connectedIsoSetoid.{u} n)`, matching
cycle data, deck-group order, and regularity.
-/

public noncomputable section

namespace TauCeti.TopBranchedCover.IsoClass

open BipartiteRibbonGraph

universe u

/-- **Topological branched covers are classified by connected bipartite ribbon graphs.** -/
def equivConnectedRibbonGraph (n : ℕ) : IsoClass.{0} n ≃ Quotient (connectedIsoSetoid.{u} n) :=
  (equivConnectedIsoClass n).trans (connectedIsoClassEquiv.{u} n).symm

variable {n : ℕ} (c : IsoClass.{0} n)

/-- `connectedIsoClassEquiv` after `equivConnectedRibbonGraph` is `equivConnectedIsoClass`. -/
@[simp] theorem connectedIsoClassEquiv_equivConnectedRibbonGraph :
    connectedIsoClassEquiv.{u} n (equivConnectedRibbonGraph.{u} n c) =
      equivConnectedIsoClass n c := by simp [equivConnectedRibbonGraph]

/-- `equivConnectedRibbonGraph` matches `ramificationPartitions` with `connectedCycleData`. -/
@[simp] theorem connectedCycleData_equivConnectedRibbonGraph :
    connectedCycleData n (equivConnectedRibbonGraph.{u} n c) =
      c.ramificationPartitions := by simp [← cycleData_connectedIsoClassEquiv]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the order of the deck/automorphism group. -/
@[simp] theorem connectedNatCardAut_equivConnectedRibbonGraph :
    connectedNatCardAut n (equivConnectedRibbonGraph.{u} n c) =
      c.natCardDeck := by simp [← natCardAutomorphismGroup_connectedIsoClassEquiv]

/-- `IsoClass.equivConnectedRibbonGraph` preserves regularity. -/
@[simp] theorem connectedIsRegular_equivConnectedRibbonGraph :
    ConnectedIsRegular n (equivConnectedRibbonGraph.{u} n c) ↔
      c.IsRegular := by simp [← isRegular_connectedIsoClassEquiv]

end TauCeti.TopBranchedCover.IsoClass
