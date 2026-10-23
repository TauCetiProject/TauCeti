/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Derivatives of maps into a closed subspace

For maps between topological vector spaces over a nontrivially normed field, if the increments
`f y - f x` lie in a closed subspace `S` for `y` near `x`, that is, if `f` takes its values in the
affine subspace `f x + S` near `x`, then its derivative at `x` takes values in `S`. This is what
shows that the Lie bracket of two vector fields tangent to a fixed subspace is again tangent to it.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousSMul 𝕜 F]
  {f : E → F} {f' : E →L[𝕜] F} {x : E} {S : Submodule 𝕜 F}

/-- If `f` has derivative `f'` at `x` and its increments `f y - f x` lie in the closed subspace `S`
for `y` near `x`, then `f'` takes values in `S`. -/
theorem _root_.HasFDerivAt.apply_mem_of_eventually_sub_mem (hf : HasFDerivAt f f' x)
    (hS : IsClosed (S : Set F)) (hfS : ∀ᶠ y in 𝓝 x, f y - f x ∈ S) (v : E) : f' v ∈ S := by
  refine hS.mem_of_tendsto (hf.lim v tendsto_norm_cobounded_atTop) ?_
  have hsmall : Tendsto (fun c : 𝕜 ↦ x + c⁻¹ • v) (Bornology.cobounded 𝕜) (𝓝 x) := by
    simpa using tendsto_const_nhds.add ((tendsto_inv₀_cobounded (α := 𝕜)).smul_const v)
  filter_upwards [hsmall.eventually hfS] with c hc
  exact S.smul_mem c hc

/-- If the increments `f y - f x` lie in the closed subspace `S` for `y` near `x`, then the
derivative of `f` at `x` takes values in `S`. -/
theorem fderiv_apply_mem_of_eventually_sub_mem (hS : IsClosed (S : Set F))
    (hfS : ∀ᶠ y in 𝓝 x, f y - f x ∈ S) (v : E) : fderiv 𝕜 f x v ∈ S := by
  by_cases hf : DifferentiableAt 𝕜 f x
  · exact hf.hasFDerivAt.apply_mem_of_eventually_sub_mem hS hfS v
  · simp [fderiv_zero_of_not_differentiableAt hf, S.zero_mem]

end TauCeti
