/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ProjectionGraph
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.Determinant
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Differentiability of graph-straightening charts

The ambient chart `ContinuousLinearMap.projectionGraphChart` and its inverse inherit
the differentiability of the graph map `g` at the projected point. Both have
explicit linear-shear differentials. In particular, a graph map with zero derivative gives
an ambient chart with identity derivative, as needed to identify the tangent space of a
local invariant disk. When the derivative of `g` takes values in the kernel of `P`, the inverse
chart preserves volume: its Jacobian determinant is `1`.
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

/-- **The inverse graph chart preserves volume.** When the differential `D` of `g` takes values
in the kernel of `P`, the differential `1 + D ∘ P` of the inverse chart has determinant
`det (1 + P ∘ D) = 1`, by the Weinstein–Aronszajn identity `LinearMap.det_one_add_comp_comm`. -/
theorem det_fderiv_projectionGraphChart_symm [FiniteDimensional 𝕜 E] {z : E} {D : E →L[𝕜] E}
    (hgs : HasFDerivAt g D (P z)) (hPD : P ∘L D = 0) :
    (fderiv 𝕜 (P.projectionGraphChart g hU hg hPg).symm z).det = 1 := by
  have h := LinearMap.det_one_add_comp_comm (D : E →ₗ[𝕜] E) (P : E →ₗ[𝕜] E)
  rw [← toLinearMap_comp P, hPD] at h
  rw [(P.hasFDerivAt_projectionGraphChart_symm g hU hg hPg hgs).fderiv]
  simpa [det, ← Module.End.one_eq_id] using h

end ContinuousLinearMap
