/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Topology
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Continuous linear bundling of `ContinuousAlternatingMap.smulRight`

Over a nontrivially normed field `𝕜`, tensoring a scalar-valued continuous alternating map
`η : E [⋀^ι]→L[𝕜] 𝕜` on the right with a vector `y : F` via `η.smulRight y` is continuous linear
in `y` (`ContinuousAlternatingMap.smulRightCLM`).
-/

public section

namespace ContinuousAlternatingMap

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

/-- `ContinuousAlternatingMap.smulRight` bundled as a continuous linear map in the vector argument,
sending `y : F` to `η.smulRight y : E [⋀^ι]→L[𝕜] F`. -/
def smulRightCLM (η : E [⋀^ι]→L[𝕜] 𝕜) : F →L[𝕜] E [⋀^ι]→L[𝕜] F :=
  ((ContinuousLinearMap.applyₗ (E [⋀^ι]→L[𝕜] F) (RingHom.id 𝕜) η).comp
    (ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E 𝕜 F ι)).comp
      (ContinuousLinearMap.smulRightL 𝕜 𝕜 𝕜 𝕜 F (ContinuousLinearMap.id 𝕜 𝕜))

@[simp]
theorem smulRightCLM_apply (η : E [⋀^ι]→L[𝕜] 𝕜) (y : F) :
    η.smulRightCLM y = η.smulRight y := by
  ext v; simp [smulRightCLM]

end ContinuousAlternatingMap
