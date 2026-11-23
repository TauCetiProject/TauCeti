/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Genus
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.TopBranchedCover.Dessin.Basic

/-!
# Euler characteristic and genus comparisons for topological dessins

Matches `TopBranchedCover.IsoClass` invariants with `connectedEulerChar` and `connectedGenus`.
-/

public noncomputable section

namespace TauCeti.TopBranchedCover.IsoClass

open BipartiteRibbonGraph

universe u

variable {n : ℕ} (c : IsoClass.{0} n)

/-- `IsoClass.equivConnectedRibbonGraph` preserves the Euler characteristic. -/
@[simp] theorem connectedEulerChar_equivConnectedRibbonGraph :
    connectedEulerChar n (equivConnectedRibbonGraph.{u} n c) = c.eulerChar := by
  simp [← eulerChar_connectedIsoClassEquiv]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the genus. -/
@[simp] theorem connectedGenus_equivConnectedRibbonGraph :
    connectedGenus n (equivConnectedRibbonGraph.{u} n c) = c.genus := by
  simp [← genus_connectedIsoClassEquiv]

end TauCeti.TopBranchedCover.IsoClass
