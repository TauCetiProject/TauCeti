/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Convergence in the weak topology

A family converges in `WeakSpace 𝕜 E` exactly when its values under every continuous linear
functional converge (`TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto`). This lets
weak convergence be used without unfolding the definition of `WeakSpace` as a `WeakBilin` space.
No injectivity of the duality pairing is needed, since the weak topology is induced by the
evaluations.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- A family converges weakly exactly when its values under every continuous linear functional
converge. -/
theorem tendsto_toWeakSpace_iff_forall_eval_tendsto {α : Type*} {l : Filter α} {u : α → E}
    {x : E} :
    Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) l (𝓝 (toWeakSpace 𝕜 E x)) ↔
      ∀ f : StrongDual 𝕜 E, Tendsto (fun n ↦ f (u n)) l (𝓝 (f x)) :=
  (IsInducing.induced _).tendsto_nhds_iff.trans tendsto_pi_nhds

end TauCeti
