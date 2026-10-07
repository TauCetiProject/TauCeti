/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GlobalChart
public import TauCeti.Geometry.Manifold.LinearSlice

import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Manifold structures on Morse stable and unstable sets

For a globally `C²` function on a finite-dimensional real inner product space with globally
Lipschitz gradient, the stable and unstable sets of a nondegenerate critical point carry
`C¹` manifold structures. Their topology is the subspace topology, and their inclusions into
the ambient space are `C¹`. The model spaces are the positive and negative Hessian spectral
subspaces, of dimensions `finrank E - morseIndex f x` and `morseIndex f x`, respectively.

The global straightening charts from `IsNondegenerateCriticalPoint.exists_stableSet_chart`
and `exists_unstableSet_chart` supply the local normal forms. The linear-slice atlas
construction assembles them without choosing a basis or changing the topology. These
manifold structures allow stable and unstable sets to be used as domains of manifold maps,
as required when studying their transverse intersections and connecting trajectories.

The results concern complete negative-gradient flows on a vector space; they do not assert
the stable-manifold theorem for an arbitrary vector field or on an arbitrary manifold.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

namespace TauCeti
namespace IsNondegenerateCriticalPoint

open scoped Gradient Manifold ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E} {K : ℝ≥0}

/-- The global stable set of a Morse critical point has a `C¹` manifold structure modelled on
the stable Hessian subspace, with its subspace topology and a `C¹` inclusion into the ambient
space. The dimension of the model plus the Morse index equals the ambient dimension. -/
theorem exists_stableSet_isManifold (h : IsNondegenerateCriticalPoint f x)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f)) :
    ∃ C : ChartedSpace h.contDiffAt.stableLinearSubspace
        (Flow.stableSet (negativeGradientFlow f hf) x), letI := C
      IsManifold 𝓘(ℝ, h.contDiffAt.stableLinearSubspace) 1
        (Flow.stableSet (negativeGradientFlow f hf) x) ∧
      ContMDiff 𝓘(ℝ, h.contDiffAt.stableLinearSubspace) 𝓘(ℝ, E) 1
        (Subtype.val : Flow.stableSet (negativeGradientFlow f hf) x → E) := by
  exact exists_isManifold_of_linearSubspaceCharts
    (Submodule.IsCompl.isTopCompl_of_isClosed
      h.isCompl_unstableLinearSubspace_stableLinearSubspace.symm
      h.contDiffAt.stableLinearSubspace.closed_of_finiteDimensional
      h.contDiffAt.unstableLinearSubspace.closed_of_finiteDimensional)
    (fun y ↦ h.exists_stableSet_chart hfs hf y.property)

/-- The global unstable set of a Morse critical point has a `C¹` manifold structure modelled
on the unstable Hessian subspace, with its subspace topology and a `C¹` inclusion into the
ambient space. The model dimension is the Morse index. -/
theorem exists_unstableSet_isManifold (h : IsNondegenerateCriticalPoint f x)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f)) :
    ∃ C : ChartedSpace h.contDiffAt.unstableLinearSubspace
        (Flow.unstableSet (negativeGradientFlow f hf) x), letI := C
      IsManifold 𝓘(ℝ, h.contDiffAt.unstableLinearSubspace) 1
        (Flow.unstableSet (negativeGradientFlow f hf) x) ∧
      ContMDiff 𝓘(ℝ, h.contDiffAt.unstableLinearSubspace) 𝓘(ℝ, E) 1
        (Subtype.val : Flow.unstableSet (negativeGradientFlow f hf) x → E) := by
  exact exists_isManifold_of_linearSubspaceCharts
    (Submodule.IsCompl.isTopCompl_of_isClosed
      h.isCompl_unstableLinearSubspace_stableLinearSubspace
      h.contDiffAt.unstableLinearSubspace.closed_of_finiteDimensional
      h.contDiffAt.stableLinearSubspace.closed_of_finiteDimensional)
    (fun y ↦ h.exists_unstableSet_chart hfs hf y.property)

end IsNondegenerateCriticalPoint
end TauCeti
