/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Derivatives of maps into a closed subspace

For maps between topological vector spaces over a nontrivially normed field, if the increments
`f y - f x` lie in a closed subspace `S` for `y` near `x`, that is, if `f` takes its values in the
affine subspace `f x + S` near `x`, then its derivative at `x` takes values in `S`. This is what
shows that the Lie bracket of two vector fields tangent to a fixed subspace is again tangent to it.

The general form `HasFDerivWithinAt.apply_mem_of_eventually_sub_mem` only asks for the increments
to lie in `S` for `y` near `x` within a set `s`, and concludes that the derivative within `s` maps
the tangent cone of `s` at `x` into `S`. A variant asks only for the increments along a direction
`v` in which the set contains a segment through `x`.

Dually, a map vanishing on a subspace near one of its points has derivative vanishing on that
subspace.
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

/-- If `f` has derivative `f'` within `s` at `x` and its increments `f y - f x` lie in the closed
subspace `S` for `y` near `x` within `s`, then `f'` maps the tangent cone of `s` at `x` into `S`. -/
theorem _root_.HasFDerivWithinAt.apply_mem_of_eventually_sub_mem {s : Set E} {v : E}
    (hf : HasFDerivWithinAt f f' s x) (hS : IsClosed (S : Set F))
    (hfS : ∀ᶠ y in 𝓝[s] x, f y - f x ∈ S) (hv : v ∈ tangentConeAt 𝕜 s x) : f' v ∈ S := by
  obtain ⟨_, l, _, c, d, hd₀, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
  have hd : Tendsto (fun n ↦ x + d n) l (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd₀, hds⟩
  refine hS.mem_of_tendsto (hf.lim hd₀ hds hcd) ?_
  filter_upwards [hd.eventually hfS] with n hn
  exact S.smul_mem (c n) hn

/-- If `f` has derivative `f'` at `x` and its increments `f y - f x` lie in the closed subspace `S`
for `y` near `x`, then `f'` takes values in `S`. -/
theorem _root_.HasFDerivAt.apply_mem_of_eventually_sub_mem (hf : HasFDerivAt f f' x)
    (hS : IsClosed (S : Set F)) (hfS : ∀ᶠ y in 𝓝 x, f y - f x ∈ S) (v : E) : f' v ∈ S :=
  (hf.hasFDerivWithinAt (s := Set.univ)).apply_mem_of_eventually_sub_mem hS
    (nhdsWithin_le_nhds hfS) (by simp)

/-- If the increments `f y - f x` lie in the closed subspace `S` for `y` near `x`, then the
derivative of `f` at `x` takes values in `S`. -/
theorem fderiv_apply_mem_of_eventually_sub_mem (hS : IsClosed (S : Set F))
    (hfS : ∀ᶠ y in 𝓝 x, f y - f x ∈ S) (v : E) : fderiv 𝕜 f x v ∈ S := by
  by_cases hf : DifferentiableAt 𝕜 f x
  · exact hf.hasFDerivAt.apply_mem_of_eventually_sub_mem hS hfS v
  · simp [fderiv_zero_of_not_differentiableAt hf, S.zero_mem]

/-- If `f` has derivative `f'` at `x` within `s`, the segment `x + t • v` lies in `s` for small
`t`, and the increments `f (x + t • v) - f x` lie in the closed subspace `S` for small `t`, then
`f' v ∈ S`. -/
theorem _root_.HasFDerivWithinAt.apply_mem_of_eventually_add_smul_sub_mem {s : Set E} {v : E}
    (hf : HasFDerivWithinAt f f' s x) (hS : IsClosed (S : Set F))
    (hs : ∀ᶠ t : 𝕜 in 𝓝 0, x + t • v ∈ s) (hfS : ∀ᶠ t : 𝕜 in 𝓝 0, f (x + t • v) - f x ∈ S) :
    f' v ∈ S := by
  have hd : Tendsto (fun t : 𝕜 ↦ t • v) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (tendsto_id.smul_const v).mono_left (nhdsWithin_le_nhds (a := (0 : 𝕜)))
  have hcd : Tendsto (fun t : 𝕜 ↦ t⁻¹ • t • v) (𝓝[≠] 0) (𝓝 v) :=
    tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun t ht ↦ by
      simp [smul_smul, inv_mul_cancel₀ (show t ≠ 0 from ht)])
  refine hS.mem_of_tendsto (hf.lim hd (hs.filter_mono nhdsWithin_le_nhds) hcd) ?_
  exact (hfS.filter_mono nhdsWithin_le_nhds).mono fun t ht ↦ S.smul_mem _ ht

/-- If `f` vanishes on the subspace `S` near a point `x ∈ S` and has derivative `f'` at `x`, then
`f'` vanishes on `S`. -/
theorem _root_.HasFDerivAt.apply_eq_zero_of_eventually_eq_zero [T2Space F] {S : Submodule 𝕜 E}
    (hf : HasFDerivAt f f' x) (hx : x ∈ S) (hfS : ∀ᶠ y in 𝓝[(S : Set E)] x, f y = 0) {v : E}
    (hv : v ∈ S) : f' v = 0 := by
  have h0 : HasFDerivWithinAt f (0 : E →L[𝕜] F) S x :=
    (hasFDerivWithinAt_const (0 : F) x _).congr_of_eventuallyEq hfS (hfS.self_of_nhdsWithin hx)
  have hv' : v ∈ tangentConeAt 𝕜 (S : Set E) x :=
    mem_tangentConeAt_of_add_smul_mem (l := 𝓝[≠] (0 : 𝕜)) (c := id) tendsto_id
      (Eventually.of_forall fun c ↦ S.add_mem hx (S.smul_mem c hv))
  simpa using hf.hasFDerivWithinAt.unique_on h0 hv'

end TauCeti
