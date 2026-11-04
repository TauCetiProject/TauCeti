/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.LinearAlgebra.Determinant.Line

/-!
# The determinant line of a Fredholm operator

A Fredholm operator `T : E →L[𝕜] F` has finite-dimensional kernel and cokernel, so its
determinant line `det (ker T) ⊗ (det (F ⧸ range T))^*` (`LinearMap.detLine`) is a line over `𝕜`.
Orientations of moduli spaces in Morse and Floer theory are orientations of these lines for
the linearized operators.

## Main results

* `ContinuousLinearMap.IsFredholm.finrank_detLine`: the determinant line of a Fredholm operator is
  one-dimensional.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

open Module

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The determinant line `det (ker T) ⊗ (det (F ⧸ range T))^*` of a Fredholm operator is
one-dimensional. -/
theorem IsFredholm.finrank_detLine {T : E →L[𝕜] F} (hT : IsFredholm T) :
    finrank 𝕜 (T : E →ₗ[𝕜] F).detLine = 1 :=
  have := hT.finite_ker
  have := hT.finite_coker
  LinearMap.finrank_detLine _

end ContinuousLinearMap
