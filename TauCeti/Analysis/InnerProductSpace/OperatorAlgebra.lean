/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Real scalars for bounded operators on `RCLike` Hilbert spaces

Restricting the scalar action on bounded operators along `ℝ → 𝕜` gives the real algebra
structure needed to apply the real continuous functional calculus to self-adjoint operators.
The structures here are the scalar foundation for the operator modulus on complete Hilbert
spaces.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The real module structure on bounded endomorphisms, obtained by restricting scalars. -/
instance instModuleRealRCLike : Module ℝ (E →L[𝕜] E) :=
  Module.restrictScalars ℝ 𝕜 (E →L[𝕜] E)

/-- The real scalar tower on bounded endomorphisms of an `RCLike` inner product space, obtained
by restricting the existing `𝕜`-scalar action. -/
instance instIsScalarTowerRealRCLike : IsScalarTower ℝ 𝕜 (E →L[𝕜] E) :=
  IsScalarTower.restrictScalars ℝ 𝕜 (E →L[𝕜] E)

/-- The real algebra structure on bounded endomorphisms of an `RCLike` inner product space,
obtained by restricting scalars along `ℝ → 𝕜`. -/
instance instAlgebraRealRCLike : Algebra ℝ (E →L[𝕜] E) :=
  Algebra.restrictScalars ℝ 𝕜 (E →L[𝕜] E)

end ContinuousLinearMap

end
