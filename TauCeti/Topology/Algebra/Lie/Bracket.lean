/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# The bracket of a finite-dimensional Lie module as a continuous bilinear map

Let `L` be a Lie algebra over a complete nontrivially normed field `𝕜` acting on a Lie module `M`,
both finite-dimensional Hausdorff topological vector spaces. Every bilinear map between such spaces
is continuous, so the action `(x, m) ↦ ⁅x, m⁆` is a continuous bilinear map
`TauCeti.lieL 𝕜 L M : L →L[𝕜] M →L[𝕜] M` (`TauCeti.lieL_apply`). Taking `M = L` gives the bracket
of `L`. Through `ContinuousLinearMap.isBoundedBilinearMap`, this makes the bracket of a
finite-dimensional normed Lie algebra smooth.
-/

public section

noncomputable section

namespace TauCeti

variable (𝕜 L M : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [LieRing L] [LieAlgebra 𝕜 L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul 𝕜 L] [FiniteDimensional 𝕜 L] [T2Space L]
  [AddCommGroup M] [Module 𝕜 M] [LieRingModule L M] [LieModule 𝕜 L M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul 𝕜 M]
  [FiniteDimensional 𝕜 M] [T2Space M]

/-- The action `(x, m) ↦ ⁅x, m⁆` of a finite-dimensional Lie algebra on a finite-dimensional Lie
module, as a continuous bilinear map. For `M = L` this is the bracket of `L`. -/
def lieL : L →L[𝕜] M →L[𝕜] M :=
  (LieModule.toEnd 𝕜 L M : L →ₗ[𝕜] Module.End 𝕜 M).toContinuousBilinearMap

variable {𝕜 L M}

@[simp]
theorem lieL_apply (x : L) (m : M) : lieL 𝕜 L M x m = ⁅x, m⁆ :=
  (rfl)

end TauCeti
