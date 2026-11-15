/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Star.LinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuity of intrinsic conjugation of operators

Mathlib's intrinsic star on `WithConv (E →L[𝕜] F)` sends `f` to
`x ↦ star (f (star x))`, unlike the Hilbert-space adjoint. Over a complete
nontrivially normed field, for finite-dimensional source spaces this operation is
continuous in the operator topology. In particular,
entrywise conjugation preserves continuous families of finite matrices.

The operator and its algebraic laws are those of
`Mathlib.Topology.Algebra.Star.LinearMap` (Monica Omar).
-/

public section

open WithConv

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [InvolutiveStar 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [StarAddMonoid E] [StarModule 𝕜 E]
  [ContinuousStar E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [StarAddMonoid F] [StarModule 𝕜 F]
  [ContinuousStar F]

/-- Intrinsic conjugation is continuous on operators with finite-dimensional source. -/
theorem continuous_intrinsicStar :
    Continuous (fun f : E →L[𝕜] F => (star (toConv f)).ofConv) := by
  refine continuous_clm_apply.2 fun x => ?_
  -- Intrinsic star evaluates as `star (f (star x))`; `ofConv` only removes the wrapper.
  exact (ContinuousLinearMap.apply 𝕜 F (star x)).continuous.star

end ContinuousLinearMap
