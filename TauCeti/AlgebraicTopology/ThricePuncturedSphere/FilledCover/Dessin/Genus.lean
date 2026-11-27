/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Dessin.Basic
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Genus

/-!
# Euler characteristic and genus comparisons for analytic dessins

Matches `isoClassEulerChar` and `isoClassGenus` with `connectedEulerChar` and `connectedGenus`.
-/

public noncomputable section

namespace TauCeti.AnalyticBelyiPair

open BipartiteRibbonGraph

universe u

variable {n : ℕ} (P : Quotient (isoSetoid.{0} n))

/-- `isoClassEquivConnectedRibbonGraph` matches the topological and dessin Euler characteristics. -/
@[simp] theorem connectedEulerChar_isoClassEquivConnectedRibbonGraph :
    connectedEulerChar n (isoClassEquivConnectedRibbonGraph.{u} n P) = isoClassEulerChar n P := by
  simp [← eulerChar_connectedIsoClassEquiv]

/-- `isoClassEquivConnectedRibbonGraph` matches the topological genus with the dessin genus. -/
@[simp] theorem connectedGenus_isoClassEquivConnectedRibbonGraph :
    connectedGenus n (isoClassEquivConnectedRibbonGraph.{u} n P) = isoClassGenus n P := by
  simp [← genus_connectedIsoClassEquiv]

end TauCeti.AnalyticBelyiPair
