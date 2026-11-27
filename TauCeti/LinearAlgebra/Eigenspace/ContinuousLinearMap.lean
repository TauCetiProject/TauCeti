/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Eigenspaces of continuous linear endomorphisms of complete spaces

An eigenspace of a continuous linear endomorphism `f` of a Hausdorff topological module is closed
(`ContinuousLinearMap.isClosed_eigenspace`). So in a complete space it is complete
(`ContinuousLinearMap.completeSpace_eigenspace`), and operators between eigenspaces of continuous
linear endomorphisms of Banach spaces, such as the restrictions
`ContinuousLinearMap.restrictEigenspace` of an operator intertwining two endomorphisms, are again
operators between Banach spaces.
-/

public section

namespace ContinuousLinearMap

open Module End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [UniformSpace M] [CompleteSpace M]
  [T0Space M] [ContinuousConstSMul R M] [IsTopologicalAddGroup M]

/-- An eigenspace of a continuous linear endomorphism of a complete space is complete. -/
instance completeSpace_eigenspace (f : M →L[R] M) (μ : R) :
    CompleteSpace (eigenspace (f : End R M) μ) :=
  (isClosed_eigenspace f μ).completeSpace_coe

end ContinuousLinearMap
