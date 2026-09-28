/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Derivatives of maps into a closed subspace

If the increments `f y - f x` of a map lie in a closed subspace `S` for `y` near `x`, that is, if
`f` takes its values in the affine subspace `f x + S` near `x`, then its derivative at `x` takes
values in `S`: the difference quotients lie in `S`, and so does their limit. This is what shows
that the Lie bracket of two vector fields tangent to a fixed subspace is again tangent to it.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {f' : E →L[𝕜] F} {x : E} {S : Submodule 𝕜 F}

/-- If `f` has derivative `f'` at `x` and its increments `f y - f x` lie in the closed subspace `S`
for `y` near `x`, then `f'` takes values in `S`. -/
theorem _root_.HasFDerivAt.apply_mem_of_eventually_sub_mem (hf : HasFDerivAt f f' x)
    (hS : IsClosed (S : Set F)) (hfS : ∀ᶠ y in 𝓝 x, f y - f x ∈ S) (v : E) : f' v ∈ S := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hlim : Tendsto (fun k : ℕ ↦ ‖c ^ k‖) atTop atTop := by
    simpa only [norm_pow] using tendsto_pow_atTop_atTop_of_one_lt hc
  refine hS.mem_of_tendsto (hf.lim v hlim) ?_
  have hsmall : Tendsto (fun k : ℕ ↦ x + (c ^ k)⁻¹ • v) atTop (𝓝 x) := by
    have h0 : Tendsto (fun k : ℕ ↦ (c ^ k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hlim)
    simpa using tendsto_const_nhds.add (h0.smul_const v)
  filter_upwards [hsmall.eventually hfS] with k hk
  exact S.smul_mem _ hk

/-- If the increments `f y - f x` lie in the closed subspace `S` for `y` near `x`, then the
derivative of `f` at `x` takes values in `S`. -/
theorem fderiv_apply_mem_of_eventually_sub_mem (hS : IsClosed (S : Set F))
    (hfS : ∀ᶠ y in 𝓝 x, f y - f x ∈ S) (v : E) : fderiv 𝕜 f x v ∈ S := by
  by_cases hf : DifferentiableAt 𝕜 f x
  · exact hf.hasFDerivAt.apply_mem_of_eventually_sub_mem hS hfS v
  · simp [fderiv_zero_of_not_differentiableAt hf, S.zero_mem]

end TauCeti
