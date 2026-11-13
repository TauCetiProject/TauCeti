/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Vanishing parameter derivatives outside a fixed support

A family vanishing outside a fixed set for nearby parameters has zero parameter derivative
outside that set. This permits iteration of differentiation while retaining a common support.
-/

public section

open Filter Set
open scoped Topology

/-- A parameter derivative vanishes outside any set supporting the family uniformly on a
neighbourhood of the parameter. No topology on the spatial domain is needed. -/
theorem HasFDerivAt.eq_zero_of_forall_notMem {𝕜 H E X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {D : H → X → E} {D' : H →L[𝕜] E}
    {U : Set H} {K : Set X} {t : H} {x : X} (hderiv : HasFDerivAt (D · x) D' t)
    (hU : U ∈ 𝓝 t) (hsupp : ∀ s ∈ U, ∀ y ∉ K, D s y = 0) (hx : x ∉ K) : D' = 0 := by
  refine hderiv.unique ((hasFDerivAt_const (0 : E) t).congr_of_eventuallyEq ?_)
  filter_upwards [hU] with s hs using hsupp s hs x hx
