/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous linear maps out of coordinate spaces

A continuous linear map out of a finite coordinate space `ι → R` is determined by its values on
the standard basis vectors `Pi.single i 1`.

## Main results

* `ContinuousLinearMap.pi_ext_single`: a continuous linear map out of a coordinate space is
  determined by its values on the standard basis.
-/

public section

namespace ContinuousLinearMap

variable {R M ι : Type*} [Semiring R] [TopologicalSpace R] [AddCommMonoid M] [TopologicalSpace M]
  [Module R M] [Finite ι] [DecidableEq ι]

/-- A continuous linear map out of a coordinate space `ι → R` is determined by its values on the
standard basis vectors `Pi.single i 1`. -/
theorem pi_ext_single {f g : (ι → R) →L[R] M}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g :=
  coe_injective <| (Pi.basisFun R ι).ext fun i ↦ by simpa using h i

end ContinuousLinearMap
