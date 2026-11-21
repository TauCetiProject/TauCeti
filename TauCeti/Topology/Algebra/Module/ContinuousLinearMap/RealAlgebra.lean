/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Real scalars for continuous linear endomorphisms over real algebras

For a topological module `E` over a commutative real algebra `𝕜` (for example an `RCLike`
field), restricting the scalar action along `ℝ → 𝕜` gives a real algebra structure on the
continuous linear endomorphisms `E →L[𝕜] E`, compatible with the `𝕜`-action.

## Main definitions and results

* `ContinuousLinearMap.realAlgebra`: the `Algebra ℝ (E →L[𝕜] E)` structure obtained by
  restricting scalars along `ℝ → 𝕜`.
* `ContinuousLinearMap.realIsScalarTower`: with this structure, `IsScalarTower ℝ 𝕜 (E →L[𝕜] E)`.

Neither declaration is registered as a global typeclass instance when this module is imported.
At `𝕜 = ℝ` and `𝕜 = ℂ`, and whenever `E` carries its own real structure, Mathlib's
`ContinuousLinearMap.algebra` already provides a real algebra structure. Enable the real algebra
locally with `attribute [local instance] ContinuousLinearMap.realAlgebra`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [CommSemiring 𝕜] [Algebra ℝ 𝕜] [TopologicalSpace E] [AddCommGroup E]
  [Module 𝕜 E] [ContinuousConstSMul 𝕜 E] [IsTopologicalAddGroup E]

/-- The real algebra structure on continuous linear endomorphisms of a topological module over a
commutative real algebra `𝕜`, obtained by restricting scalars along `ℝ → 𝕜`, so that
`r • T = algebraMap ℝ 𝕜 r • T`. -/
@[reducible]
def realAlgebra : Algebra ℝ (E →L[𝕜] E) :=
  Algebra.restrictScalars ℝ 𝕜 (E →L[𝕜] E)

attribute [local instance] realAlgebra

/-- With `ContinuousLinearMap.realAlgebra`, the real and `𝕜`-scalar actions on continuous linear
endomorphisms form a scalar tower. -/
theorem realIsScalarTower : IsScalarTower ℝ 𝕜 (E →L[𝕜] E) :=
  IsScalarTower.restrictScalars ℝ 𝕜 (E →L[𝕜] E)

end ContinuousLinearMap

end
