/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Dessin.Basic
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Genus

/-!
# Euler characteristic and genus comparisons for dessins

Matches the topological Euler characteristic and genus of `TopBranchedCover.IsoClass.{0} n` and
`AnalyticBelyiPair` isomorphism classes with `connectedEulerChar` and `connectedGenus` of dessins.
-/

public noncomputable section

namespace TauCeti

open BipartiteRibbonGraph

universe u

namespace TopBranchedCover.IsoClass

variable {n : ℕ} (c : IsoClass.{0} n)

/-- `IsoClass.equivConnectedRibbonGraph` preserves the Euler characteristic. -/
@[simp] theorem connectedEulerChar_equivConnectedRibbonGraph :
    connectedEulerChar n (equivConnectedRibbonGraph.{u} n c) = c.eulerChar := by
  simp [← eulerChar_connectedIsoClassEquiv]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the genus. -/
@[simp] theorem connectedGenus_equivConnectedRibbonGraph :
    connectedGenus n (equivConnectedRibbonGraph.{u} n c) = c.genus := by
  simp [← genus_connectedIsoClassEquiv]

end TopBranchedCover.IsoClass

namespace AnalyticBelyiPair

variable {n : ℕ} (P : Quotient (isoSetoid.{0} n))

/-- `isoClassEquivConnectedRibbonGraph` matches the topological and dessin Euler characteristics. -/
@[simp] theorem connectedEulerChar_isoClassEquivConnectedRibbonGraph :
    connectedEulerChar n (isoClassEquivConnectedRibbonGraph.{u} n P) = isoClassEulerChar n P := by
  simp [← eulerChar_connectedIsoClassEquiv]

/-- `isoClassEquivConnectedRibbonGraph` matches the topological genus with the dessin genus. -/
@[simp] theorem connectedGenus_isoClassEquivConnectedRibbonGraph :
    connectedGenus n (isoClassEquivConnectedRibbonGraph.{u} n P) = isoClassGenus n P := by
  simp [← genus_connectedIsoClassEquiv]

end AnalyticBelyiPair

end TauCeti
