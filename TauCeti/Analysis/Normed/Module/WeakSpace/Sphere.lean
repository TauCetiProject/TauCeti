/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.Algebra.Module.WeakSpace
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Spheres of linear maps of infinite rank in the weak topology

In a topological vector space, every weak neighbourhood of a point contains an affine line in a
direction not annihilated by a linear map `j` whenever `LinearMap.range (j : V →ₗ[𝕜] F)` is
infinite-dimensional (`LinearMap.exists_apply_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds`).
When `j` maps into a normed space over `ℝ` or `ℂ`, this line meets the sphere `{u | ‖j u‖ = r}`
for every `r ≥ 0`, so `0` lies in the weak closure of that sphere, the sphere is not weakly closed
when `r > 0`, and over any nontrivially normed field `j` is not continuous from the weak topology
to the norm topology. This is why weak-to-norm continuity of compact operators only holds on bounded
sets.

## Main results

* `TauCeti.zero_mem_closure_toWeakSpace_setOf_norm_eq`: `0` lies in the weak closure of every
  sphere of a linear map with infinite-dimensional range.
* `TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq`: spheres of positive radius are not weakly
  closed.
* `TauCeti.not_isBounded_image_comp_toWeakSpace_symm_of_mem_nhds`: a linear map with
  infinite-dimensional range cannot map any weak neighbourhood to a norm-bounded set.
* `TauCeti.not_continuousAt_comp_toWeakSpace_symm` and
  `TauCeti.not_continuous_comp_toWeakSpace_symm`: a linear map with infinite-dimensional range is
  not weak-to-norm continuous at any point.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Springer, 2011, §3.2, Example 1 (weak closure of the unit sphere).
-/

public section

open Bornology Set Topology

namespace TauCeti

section Sphere

variable {𝕜 V F G : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FunLike G V F] [LinearMapClass G 𝕜 V F] {j : G}

/-- `0` lies in the weak closure of every sphere `{u | ‖j u‖ = r}` (`0 ≤ r`) of a linear map `j`
into a normed space over `ℝ` or `ℂ` whenever `LinearMap.range (j : V →ₗ[𝕜] F)` is
infinite-dimensional. -/
theorem zero_mem_closure_toWeakSpace_setOf_norm_eq
    (hj : ¬ FiniteDimensional 𝕜 (LinearMap.range (j : V →ₗ[𝕜] F))) {r : ℝ} (hr : 0 ≤ r) :
    (0 : WeakSpace 𝕜 V) ∈ closure (toWeakSpace 𝕜 V '' {u | ‖j u‖ = r}) := by
  refine mem_closure_iff_nhds.2 fun U hU ↦ ?_
  obtain ⟨v, hv, hline⟩ :=
    (j : V →ₗ[𝕜] F).exists_apply_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds
      (x := (0 : V)) hj (by simpa only [map_zero] using hU)
  have hjv : ‖j v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  -- Rescale `v` so that its image has norm `r`.
  refine ⟨_, hline ((r / ‖j v‖ : ℝ) : 𝕜), mem_image_of_mem _ ?_⟩
  simp [map_smul, norm_smul, abs_of_nonneg hr, hjv]

/-- A sphere `{u | ‖j u‖ = r}` of positive radius of a linear map `j` into a normed space over `ℝ`
or `ℂ` is not weakly closed whenever `LinearMap.range (j : V →ₗ[𝕜] F)` is infinite-dimensional. -/
theorem not_isClosed_toWeakSpace_setOf_norm_eq
    (hj : ¬ FiniteDimensional 𝕜 (LinearMap.range (j : V →ₗ[𝕜] F))) {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 V '' {u | ‖j u‖ = r}) := fun hclosed ↦ by
  obtain ⟨u, hu, hu0⟩ :=
    hclosed.closure_subset (zero_mem_closure_toWeakSpace_setOf_norm_eq hj hr.le)
  rw [map_eq_zero_iff _ (toWeakSpace 𝕜 V).injective] at hu0
  subst hu0
  simp only [mem_ofPred_eq, map_zero, norm_zero] at hu
  exact hr.ne hu

end Sphere

section Discontinuity

/-- A linear map `j` with infinite-dimensional range into a normed space cannot map any weak
neighbourhood to a norm-bounded set. -/
theorem not_isBounded_image_comp_toWeakSpace_symm_of_mem_nhds
    {𝕜 V F G : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FunLike G V F] [LinearMapClass G 𝕜 V F] {j : G}
    (hj : ¬ FiniteDimensional 𝕜 (LinearMap.range (j : V →ₗ[𝕜] F))) {x : V}
    {U : Set (WeakSpace 𝕜 V)} (hU : U ∈ 𝓝 (toWeakSpace 𝕜 V x)) :
    ¬ IsBounded ((fun w : WeakSpace 𝕜 V ↦ j ((toWeakSpace 𝕜 V).symm w)) '' U) := by
  intro hbdd
  obtain ⟨v, hv, hline⟩ :=
    (j : V →ₗ[𝕜] F).exists_apply_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds hj hU
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (j x)).1 hbdd
  have hzero : LinearMap.toSpanSingleton 𝕜 F (j v) = 0 :=
    LinearMap.eq_zero_of_forall_norm_apply_le (C := R) fun c ↦ by
      have hmem : j (x + c • v) ∈ (fun w : WeakSpace 𝕜 V ↦ j ((toWeakSpace 𝕜 V).symm w)) '' U :=
        ⟨toWeakSpace 𝕜 V (x + c • v), hline c, by simp⟩
      have h := Metric.mem_closedBall.1 (hR hmem)
      rwa [dist_eq_norm, map_add, map_smul, add_sub_cancel_left] at h
  exact hv (by simpa using congrArg (· (1 : 𝕜)) hzero)

/-- A linear map `j` with infinite-dimensional range into a normed space is discontinuous at every
point when the domain carries its weak topology and the codomain carries its norm topology. -/
theorem not_continuousAt_comp_toWeakSpace_symm {𝕜 V F G : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FunLike G V F] [LinearMapClass G 𝕜 V F] {j : G}
    (hj : ¬ FiniteDimensional 𝕜 (LinearMap.range (j : V →ₗ[𝕜] F))) (x : V) :
    ¬ ContinuousAt (fun w : WeakSpace 𝕜 V ↦ j ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V x) := fun hc ↦
  not_isBounded_image_comp_toWeakSpace_symm_of_mem_nhds hj
    (hc.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos))
    (Metric.isBounded_ball.subset (image_preimage_subset _ _))

/-- A linear map `j` with infinite-dimensional range into a normed space is not continuous from
the weak topology to the norm topology. -/
theorem not_continuous_comp_toWeakSpace_symm {𝕜 V F G : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FunLike G V F] [LinearMapClass G 𝕜 V F] {j : G}
    (hj : ¬ FiniteDimensional 𝕜 (LinearMap.range (j : V →ₗ[𝕜] F))) :
    ¬ Continuous fun w : WeakSpace 𝕜 V ↦ j ((toWeakSpace 𝕜 V).symm w) :=
  fun hcont ↦ not_continuousAt_comp_toWeakSpace_symm hj 0 hcont.continuousAt

end Discontinuity

end TauCeti
