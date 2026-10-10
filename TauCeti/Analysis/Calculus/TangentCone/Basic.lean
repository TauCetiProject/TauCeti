/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Tangent cones of linear subspaces and of curves

Two basic facts about Mathlib's tangent cone `tangentConeAt` in topological modules.
The subspace calculation lets flattening charts identify their model subspaces with intrinsic
tangent spaces, while the curve lemma places velocities of invariant flows in the tangent cones
of their invariant sets.

## Main results

* `Submodule.tangentConeAt_eq`: the tangent cone of a closed subspace at one of its points is the
  subspace itself.
* `HasDerivAt.mem_tangentConeAt`: the velocity of a curve lying in a set is tangent to the set.
-/

public section

open Filter Set Topology

variable {𝕜 E : Type*}

namespace Submodule

variable [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace 𝕜] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
  [(𝓝[≠] (0 : 𝕜)).NeBot]

/-- Over a division ring where `0` is not isolated, the tangent cone of a closed submodule
at one of its points is the submodule itself. -/
@[simp]
theorem tangentConeAt_eq (L : Submodule 𝕜 E) (hL : IsClosed (L : Set E)) {x : E} (hx : x ∈ L) :
    tangentConeAt 𝕜 (L : Set E) x = L := by
  refine Subset.antisymm (fun v hv ↦ ?_) fun v hv ↦ ?_
  · obtain ⟨ι, l, hl, c, d, -, hdL, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
    exact hL.mem_of_tendsto hcd (hdL.mono fun n hn ↦
      L.smul_mem _ ((L.add_mem_iff_right hx).1 hn))
  · exact mem_tangentConeAt_of_add_smul_mem (l := 𝓝[≠] (0 : 𝕜)) (c := id) tendsto_id
      (Eventually.of_forall fun c ↦ L.add_mem hx (L.smul_mem c hv))

end Submodule

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]

/-- The velocity of a curve which stays in a set `S` near time `t` lies in the tangent cone of `S`
at the point reached at time `t`. -/
theorem HasDerivAt.mem_tangentConeAt {γ : 𝕜 → E} {v : E} {t : 𝕜} {S : Set E}
    (hγ : HasDerivAt γ v t) (hS : ∀ᶠ s in 𝓝 t, γ s ∈ S) : v ∈ tangentConeAt 𝕜 S (γ t) := by
  refine mem_tangentConeAt_of_seq (𝓝[≠] t) (fun s ↦ (s - t)⁻¹) (fun s ↦ γ s - γ t) ?_ ?_ ?_
  · simpa only [sub_eq_add_neg, add_neg_cancel] using
      (hγ.hasFDerivAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add_const (-(γ t))
  · simpa using hS.filter_mono nhdsWithin_le_nhds
  · have hd : Tendsto (fun s : 𝕜 ↦ s - t) (𝓝[≠] t) (𝓝 0) := by
      simpa using (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto id (𝓝[≠] t) (𝓝 t)).sub_const t
    have hcd : Tendsto (fun s : 𝕜 ↦ (s - t)⁻¹ • (s - t)) (𝓝[≠] t) (𝓝 (1 : 𝕜)) :=
      tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun s hs ↦ by
        simp [smul_eq_mul, sub_ne_zero.mpr hs])
    simpa only [add_sub_cancel, ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      hγ.hasFDerivAt.hasFDerivWithinAt.lim hd
        (Eventually.of_forall fun _ ↦ mem_univ _) hcd
