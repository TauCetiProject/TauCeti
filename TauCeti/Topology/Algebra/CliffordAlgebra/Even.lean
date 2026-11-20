/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Linear maps out of the even Clifford subalgebra

The even subalgebra `CliffordAlgebra.even Q` carries the subspace topology of the module topology
on the Clifford algebra. It is the degree-zero summand of the `ZMod 2`-grading
`CliffordAlgebra.evenOdd Q`, so the projection onto it along the odd part is a linear map of the
whole Clifford algebra. Composing with this projection extends every linear map out of the even
subalgebra to a linear map out of the Clifford algebra, which is continuous for the module topology.
Hence every linear map out of the even subalgebra is continuous, over any topological commutative
ring and with no finiteness assumption. This is how even-algebra constructions, such as the
comparison `CliffordAlgebra.evenEquivEvenNeg` of the even algebras of `Q` and `-Q`, become
continuous.

## Main results

* `CliffordAlgebra.continuous_even_linearMap`: a linear map out of the even subalgebra, into a
  topological module, is continuous.
-/

public section

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- Every linear map out of the even Clifford subalgebra, with its subspace topology, into a
topological module is continuous. -/
@[fun_prop]
theorem continuous_even_linearMap {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [ContinuousAdd N] [ContinuousSMul R N] (φ : even Q →ₗ[R] N) : Continuous φ := by
  -- The projection onto the degree-zero summand of `evenOdd Q`, whose carrier is `even Q`.
  let π : CliffordAlgebra Q →ₗ[R] even Q :=
    DirectSum.component R (ZMod 2) (fun i ↦ evenOdd Q i) 0 ∘ₗ
      (DirectSum.decomposeLinearEquiv (evenOdd Q)).toLinearMap
  have hπ (x : even Q) : π x = x :=
    Subtype.ext (DirectSum.decompose_of_mem_same (evenOdd Q) x.2)
  refine ((IsModuleTopology.continuous_of_linearMap (φ ∘ₗ π)).comp
    continuous_subtype_val).congr fun x ↦ ?_
  simp [hπ]

end CliffordAlgebra
