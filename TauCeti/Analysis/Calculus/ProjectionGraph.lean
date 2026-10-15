/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ProjectionGraph
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Differentiability of graph-straightening charts

The ambient chart `ContinuousLinearMap.projectionGraphChart` and its inverse inherit
the differentiability of the graph map `g` at the projected point. Both have
explicit linear-shear differentials. In particular, a graph map with zero derivative gives
an ambient chart with identity derivative, as needed to identify the tangent space of a
local invariant disk.
-/

public section

open Set Topology
open scoped ContDiff

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (P : E →L[𝕜] E) (g : E → E)
  {U : Set E} (hU : IsOpen U) (hg : ContinuousOn g (P.range ∩ U))
  (hPg : ∀ v ∈ (P.range : Set E) ∩ U, P (g v) = 0)

/-- The graph chart is `C^n` wherever `g` is `C^n` at the projected point. -/
theorem contDiffAt_projectionGraphChart {n : ℕ∞ω} {z : E}
    (hgs : ContDiffAt 𝕜 n g (P z)) :
    ContDiffAt 𝕜 n (P.projectionGraphChart g hU hg hPg) z := by
  convert contDiffAt_id.sub (hgs.comp z P.contDiff.contDiffAt) using 1
  ext w
  simp

/-- The inverse chart is `C^n` wherever `g` is `C^n` at the projected point. -/
theorem contDiffAt_projectionGraphChart_symm {n : ℕ∞ω} {z : E}
    (hgs : ContDiffAt 𝕜 n g (P z)) :
    ContDiffAt 𝕜 n (P.projectionGraphChart g hU hg hPg).symm z := by
  convert contDiffAt_id.add (hgs.comp z P.contDiff.contDiffAt) using 1
  ext w
  simp

/-- The differential of the straightening chart is the corresponding linear shear. -/
theorem hasFDerivAt_projectionGraphChart {z : E} {D : E →L[𝕜] E}
    (hgs : HasFDerivAt g D (P z)) :
    HasFDerivAt (P.projectionGraphChart g hU hg hPg)
      (ContinuousLinearMap.id 𝕜 E - D.comp P) z := by
  convert (hasFDerivAt_id z).sub (hgs.comp z P.hasFDerivAt) using 1
  ext w
  simp

/-- The differential of the inverse graph chart is the inverse linear shear. -/
theorem hasFDerivAt_projectionGraphChart_symm {z : E} {D : E →L[𝕜] E}
    (hgs : HasFDerivAt g D (P z)) :
    HasFDerivAt (P.projectionGraphChart g hU hg hPg).symm
      (ContinuousLinearMap.id 𝕜 E + D.comp P) z := by
  convert (hasFDerivAt_id z).add (hgs.comp z P.hasFDerivAt) using 1
  ext w
  simp

end ContinuousLinearMap
