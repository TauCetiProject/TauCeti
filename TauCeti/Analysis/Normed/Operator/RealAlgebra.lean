/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Real scalars for bounded operators over `RCLike` fields

For a normed space `E` over `RCLike 𝕜`, restricting the scalar action along `ℝ → 𝕜` gives a
real algebra structure on the bounded endomorphisms `E →L[𝕜] E`, compatible with the `𝕜`-action.

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

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The real algebra structure on bounded endomorphisms of a normed space over an `RCLike`
field, obtained by restricting scalars along `ℝ → 𝕜`, so that `r • T = (r : 𝕜) • T`. -/
@[reducible]
def realAlgebra : Algebra ℝ (E →L[𝕜] E) :=
  Algebra.restrictScalars ℝ 𝕜 (E →L[𝕜] E)

attribute [local instance] realAlgebra

/-- With `ContinuousLinearMap.realAlgebra`, the real and `𝕜`-scalar actions on bounded
endomorphisms form a scalar tower. -/
theorem realIsScalarTower : IsScalarTower ℝ 𝕜 (E →L[𝕜] E) :=
  IsScalarTower.restrictScalars ℝ 𝕜 (E →L[𝕜] E)

end ContinuousLinearMap

end
