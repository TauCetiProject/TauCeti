/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Bounded operators on a finite-dimensional space

A bounded operator on a finite-dimensional normed space is just a linear map, so its spectrum is
the finite set of eigenvalues. This holds over every field of scalars acting compatibly, for
instance over `ℝ` for an operator on a complex space.

## Main results

* `ContinuousLinearMap.finite_spectrum`: a bounded operator on a finite-dimensional normed space
  has finite spectrum, also over subfields of the scalars such as `ℝ ⊆ ℂ`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- A bounded operator on a finite-dimensional normed space has finite spectrum over any field
`S` of scalars acting compatibly, for instance over `ℝ` for an operator on a complex space. -/
theorem finite_spectrum (S : Type*) [Field S] [Algebra S 𝕜] [Algebra S (V →L[𝕜] V)]
    [IsScalarTower S 𝕜 (V →L[𝕜] V)] (T : V →L[𝕜] V) : (spectrum S T).Finite := by
  have := FiniteDimensional.complete 𝕜 V
  rw [← spectrum.preimage_algebraMap 𝕜, spectrum_eq]
  exact (Module.End.finite_spectrum _).preimage (algebraMap S 𝕜).injective.injOn

end ContinuousLinearMap
