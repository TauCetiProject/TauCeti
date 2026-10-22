/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Closed derivative graphs for bounded continuous functions

The Fréchet derivative identity is closed under uniform convergence of bounded continuous value
and derivative fields. The derivative field may be read through a uniformly continuous map.
These results supply the closed graph used to construct complete spaces of differentiable maps.

The proofs use Mathlib's `hasFDerivAt_of_tendstoUniformly`.
-/

public section

namespace TauCeti

open Filter Topology
open scoped BoundedContinuousFunction

universe u v

/-- The set of bounded continuous fields satisfying a Fréchet derivative identity, with the
derivative read off the second field through a uniformly continuous map, is closed. -/
theorem isClosed_setOf_hasFDerivAt_comp {𝕜 : Type*} {E : Type u} {Y Z : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [PseudoMetricSpace Z]
    (L : Z → E →L[𝕜] Y) (hL : UniformContinuous L) :
    IsClosed {J : (E →ᵇ Y) × (E →ᵇ Z) | ∀ x, HasFDerivAt (J.1 : E → Y) (L (J.2 x)) x} := by
  rw [← isSeqClosed_iff_isClosed]
  intro J j hJ hjlim x
  apply hasFDerivAt_of_tendstoUniformly
      (f := fun n ↦ (J n).1) (f' := fun n y ↦ L ((J n).2 y))
      (g := j.1) (g' := fun y ↦ L (j.2 y)) (l := atTop)
  · exact hL.comp_tendstoUniformly
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
        ((continuous_snd.tendsto j).comp hjlim))
  · intro n y
    exact hJ n y
  · intro y
    exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      ((continuous_fst.tendsto j).comp hjlim)).tendsto_at y

/-- The set of bounded continuous fields satisfying the Fréchet derivative identity is closed. -/
theorem isClosed_setOf_hasFDerivAt {𝕜 : Type*} {E : Type u} {Y : Type v}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] :
    IsClosed {J : (E →ᵇ Y) × (E →ᵇ (E →L[𝕜] Y)) |
      ∀ x, HasFDerivAt (J.1 : E → Y) (J.2 x) x} :=
  isClosed_setOf_hasFDerivAt_comp id uniformContinuous_id

end TauCeti
