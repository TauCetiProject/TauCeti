/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Functions with a prescribed limit form a closed subspace

For any filter on the domain, the functions tending to a fixed value form a closed subset of
the space of functions with the uniform convergence topology. In particular, families tending
to zero along the cofinite filter form a complete space when the coefficient space is complete.

The limit interchange is Mathlib's `TendstoUniformly.tendsto_of_eventually_tendsto`.
-/

public section

open Filter Topology

namespace UniformFun

variable {α β : Type*} [UniformSpace β] {l : Filter α} {b : β}

/-- Functions with a prescribed limit along a filter form a closed subset for uniform
convergence. No separation or completeness assumption on the codomain is needed. -/
theorem isClosed_setOfPred_tendsto :
    IsClosed {f : UniformFun α β | Tendsto (toFun f) l (𝓝 b)} := by
  refine isClosed_iff_forall_filter.mpr fun f u _ hu huf ↦ ?_
  rw [← tendsto_id', UniformFun.tendsto_iff_tendstoUniformly] at huf
  exact huf.tendsto_of_eventually_tendsto (Filter.le_principal_iff.mp hu)
    (tendsto_const_nhds (x := b))

end UniformFun
