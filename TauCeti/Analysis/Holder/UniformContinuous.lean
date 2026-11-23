/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Topology.ContinuousMap.Bounded.UniformContinuous

/-!
# Bounded `C^{k+1,α}` maps are bounded and uniformly continuous

A bounded `C^{k+1,α}` map is Lipschitz (`TauCeti.CkHolderSpace.lipschitzWith`), so forgetting its
derivatives lands in the closed subspace `BUC(E, F)` of bounded uniformly continuous functions.
This file records that inclusion as the continuous linear map `TauCeti.CkHolderSpace.toBUC`.
Its density on finite-dimensional real inner product spaces,
`TauCeti.CkHolderSpace.denseRange_toBUC`, is proved by heat regularization in
`TauCeti.Analysis.PDE.HeatKernel.UniformContinuous`.
-/

public section
noncomputable section

namespace TauCeti.CkHolderSpace

open BoundedContinuousFunction
open scoped NNReal ContDiff

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The inclusion of `C_b^{k+1,α}(E, F)` in the bounded uniformly continuous functions
`BUC(E, F)`, forgetting the derivatives. -/
def toBUC : CkHolderSpace (k + 1) α E F →L[ℝ] uniformContinuousSubmodule ℝ E F :=
  toBoundedContinuousFunctionCLM.codRestrict (uniformContinuousSubmodule ℝ E F).toSubmodule
    fun f ↦ (mem_uniformContinuousSubmodule _).2 <| by
      simpa using f.lipschitzWith.uniformContinuous

/-- The inclusion `toBUC` does not change values. -/
@[simp]
theorem toBUC_apply (f : CkHolderSpace (k + 1) α E F) (x : E) :
    ((toBUC f : uniformContinuousSubmodule ℝ E F) : E →ᵇ F) x = f x := by
  rw [toBUC, ContinuousLinearMap.coe_codRestrict_apply, toBoundedContinuousFunctionCLM_apply,
    coe_toBoundedContinuousFunction]

end TauCeti.CkHolderSpace
