/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Derivatives of locally constant functions

A derivative of a function constant near a point is zero. In particular, a family vanishing
outside a fixed set for nearby parameters has zero parameter derivative outside that set.
-/

public section

open Filter
open scoped Topology

/-- A derivative of a function constant on a neighbourhood of the point is zero. -/
theorem HasFDerivAt.eq_zero_of_eventually_const {𝕜 H E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup H] [Module 𝕜 H] [TopologicalSpace H]
    [ContinuousAdd H] [ContinuousSMul 𝕜 H] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E]
    {f : H → E} {f' : H →L[𝕜] E} {t : H} {c : E} (hf : HasFDerivAt f f' t)
    (h : f =ᶠ[𝓝 t] fun _ ↦ c) : f' = 0 :=
  hf.unique (hasFDerivAt_zero_of_eventually_const c h)
