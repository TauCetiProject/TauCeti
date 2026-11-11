/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Bounded uniformly continuous functions

`BoundedContinuousFunction.uniformContinuousSubmodule` is the closed vector subspace of bounded
continuous functions consisting of uniformly continuous functions. Its norm is the inherited
supremum norm, and its carrier is a Banach space whenever the target is complete. This is the
natural space for initial data whose diffusion evolution attains its trace in supremum norm;
bounded continuity alone does not imply uniform attainment on a noncompact domain.
-/

public section

namespace BoundedContinuousFunction

variable {X F : Type*} [UniformSpace X]

/-- Uniformly continuous bounded functions form a closed subset for the supremum metric. -/
theorem isClosed_setOf_uniformContinuous [PseudoMetricSpace F] :
    IsClosed {f : X →ᵇ F | UniformContinuous f} := by
  apply isSeqClosed_iff_isClosed.mp
  intro f g hf hg
  exact (tendsto_iff_tendstoUniformly.mp hg).uniformContinuous
    (Filter.Eventually.of_forall hf).frequently

/-- The closed vector subspace of bounded uniformly continuous functions, with the inherited
supremum norm. Its carrier is complete when `F` is complete. -/
def uniformContinuousSubmodule (𝕜 X F : Type*) [NormedField 𝕜] [UniformSpace X]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] : ClosedSubmodule 𝕜 (X →ᵇ F) where
  carrier := {f | UniformContinuous f}
  zero_mem' := uniformContinuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c
  isClosed' := isClosed_setOf_uniformContinuous

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Membership in the bounded uniformly continuous subspace. -/
@[simp]
theorem mem_uniformContinuousSubmodule (f : X →ᵇ F) :
    f ∈ uniformContinuousSubmodule 𝕜 X F ↔ UniformContinuous f :=
  (Iff.rfl)

end BoundedContinuousFunction
