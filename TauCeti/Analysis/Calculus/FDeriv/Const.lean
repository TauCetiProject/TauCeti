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
The derivative within any set vanishes outside the topological support, without a uniqueness
assumption on derivatives within that set. A function constant on an open set has vanishing
first and second derivatives on that set.
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

/-- The derivative within any set vanishes outside the topological support. No uniqueness
hypothesis on differentiation within the set is required. -/
theorem TauCeti.fderivWithin_of_notMem_tsupport (𝕜 : Type*) {E F : Type*}
    [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    {f : E → F} {s : Set E} {x : E} (h : x ∉ tsupport f) :
    fderivWithin 𝕜 f s x = 0 := by
  rw [(notMem_tsupport_iff_eventuallyEq.1 h).fderivWithin_eq_of_nhds]
  exact fderivWithin_const_apply _

/-- A function constant on an open set has zero derivative at every point of that set. -/
theorem TauCeti.fderiv_eq_zero_of_eqOn_const (𝕜 : Type*) {E F : Type*}
    [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    {f : E → F} {U : Set E} (hU : IsOpen U) {c : F} (h : Set.EqOn f (fun _ ↦ c) U) {x : E}
    (hx : x ∈ U) : fderiv 𝕜 f x = 0 := by
  rw [(eventuallyEq_of_mem (hU.mem_nhds hx) h).fderiv_eq, fderiv_const_apply]

/-- A function constant on an open set has zero second derivatives at every point of that set: the
derivative of each directional derivative vanishes there. -/
theorem TauCeti.fderiv_fderiv_apply_eq_zero_of_eqOn_const (𝕜 : Type*) {E F : Type*}
    [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    {f : E → F} {U : Set E} (hU : IsOpen U) {c : F} (h : Set.EqOn f (fun _ ↦ c) U) {x : E}
    (hx : x ∈ U) (u : E) : fderiv 𝕜 (fun y ↦ fderiv 𝕜 f y u) x = 0 :=
  TauCeti.fderiv_eq_zero_of_eqOn_const 𝕜 hU (c := 0)
    (fun _ hy ↦ by simp [TauCeti.fderiv_eq_zero_of_eqOn_const 𝕜 hU h hy]) hx
