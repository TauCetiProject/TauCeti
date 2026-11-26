/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Analysis.Normed.Operator.LinearPMap.GraphSpace
public import TauCeti.Topology.Algebra.Module.LinearPMap.Basic

/-!
# Closed range and the Poincaré inequality

The range of a closed partial linear map `T : E →ₗ.[𝕜] F` from a Hilbert space to a Banach space
is closed exactly when `T` satisfies a **Poincaré inequality** `‖u‖ ≤ c ‖T u‖`, for some `c > 0`
and every `u` in the domain of `T` orthogonal to its kernel. For the exterior derivative of a
Hilbert complex, this is the closed range condition of Arnold, Falk and Winther.

## Main results

* `LinearPMap.isClosed_range_of_norm_le_mul_norm`: a Poincaré inequality closes the range; the
  target need not be complete.
* `LinearPMap.exists_norm_le_mul_norm_of_isClosed_range`: a closed range gives a Poincaré
  inequality when `F` is complete, by the open mapping theorem on the graph space.
* `LinearPMap.isClosed_range_iff_exists_norm_le_mul_norm`: the two together.

## References

* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to
  numerical stability*, Bull. Amer. Math. Soc. 47 (2010), §3.1.
* J. Brüning, M. Lesch, *Hilbert complexes*, J. Funct. Anal. 108 (1992).
-/

public section

noncomputable section

open Filter Topology

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace E] {T : E →ₗ.[𝕜] F}

/-- **A Poincaré inequality closes the range.** If a closed partial linear map `T` from a Hilbert
space satisfies `‖u‖ ≤ c ‖T u‖` for every `u` in its domain orthogonal to its kernel, then its
range is closed. -/
theorem isClosed_range_of_norm_le_mul_norm (hT : T.IsClosed) {c : ℝ}
    (hc : ∀ u : T.domain, (u : E) ∈ T.kerᗮ → ‖(u : E)‖ ≤ c * ‖T u‖) :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) := by
  have : T.ker.HasOrthogonalProjection :=
    have := hT.isClosed_ker.completeSpace_coe
    inferInstance
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  obtain ⟨y', hy', hlim⟩ := mem_closure_iff_seq_limit.1 hy
  -- Each `y' n` has a preimage `v n` orthogonal to the kernel.
  have hpre : ∀ n, ∃ v : T.domain, (v : E) ∈ T.kerᗮ ∧ T v = y' n := fun n ↦ by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (hy' n)
    obtain ⟨v, hv, hTv⟩ := exists_coe_eq_sub_starProjection u
    exact ⟨v, hv ▸ T.ker.sub_starProjection_mem_orthogonal _, hTv.trans hu⟩
  choose v hv hTv using hpre
  -- The Poincaré inequality makes `v` Cauchy, since `y'` is.
  have hK : 0 < max c 0 + 1 := by positivity
  have hcauchy : CauchySeq fun n ↦ (v n : E) := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq (ε / (max c 0 + 1)) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h := hc (v m - v n) (Submodule.sub_mem _ (hv m) (hv n))
    rw [map_sub, hTv, hTv, Submodule.coe_sub] at h
    have ht := hN m hm n hn
    rw [dist_eq_norm] at ht ⊢
    calc ‖(v m : E) - v n‖ ≤ c * ‖y' m - y' n‖ := h
      _ ≤ (max c 0 + 1) * ‖y' m - y' n‖ :=
        mul_le_mul_of_nonneg_right (by linarith [le_max_left c 0]) (norm_nonneg _)
      _ < (max c 0 + 1) * (ε / (max c 0 + 1)) := mul_lt_mul_of_pos_left ht hK
      _ = ε := mul_div_cancel₀ _ hK.ne'
  -- The limit of `v` is a preimage of `y`, as the graph of `T` is closed.
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine mem_range_iff.2 ⟨x, hT.mem_of_tendsto (hx.prodMk_nhds hlim)
    (Eventually.of_forall fun n ↦ ?_)⟩
  simpa only [hTv, SetLike.mem_coe] using T.mem_graph (v n)

/-- **A closed range gives a Poincaré inequality.** If a closed partial linear map `T` from a
Hilbert space to a Banach space has closed range, then for some `c > 0`, `‖u‖ ≤ c ‖T u‖` for
every `u` in its domain orthogonal to its kernel. This is the open mapping theorem for `T` on its
graph space. -/
theorem exists_norm_le_mul_norm_of_isClosed_range [CompleteSpace F] (hT : T.IsClosed)
    (hR : _root_.IsClosed (LinearMap.range T.toFun : Set F)) :
    ∃ c > 0, ∀ u : T.domain, (u : E) ∈ T.kerᗮ → ‖(u : E)‖ ≤ c * ‖T u‖ := by
  have := hT.completeSpace_graphSpace
  have := hR.completeSpace_coe
  have hmem : ∀ z, T.graphSnd z ∈ LinearMap.range T.toFun := fun z ↦
    T.range_graphSnd ▸ LinearMap.mem_range_self _ z
  -- The bounded operator `T.graphSnd`, onto the range of `T`, is surjective.
  let S : T.graphSpace →L[𝕜] LinearMap.range T.toFun := T.graphSnd.codRestrict _ hmem
  have hS : Function.Surjective S := by
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 (T.range_graphSnd ▸ hy)
    exact ⟨z, Subtype.ext (T.graphSnd.coe_codRestrict_apply _ hmem z)⟩
  obtain ⟨C, hC0, hC⟩ := S.exists_preimage_norm_le hS
  refine ⟨C, hC0, fun u hu ↦ ?_⟩
  obtain ⟨z, hz, hzle⟩ := hC ⟨T u, LinearMap.mem_range_self _ u⟩
  -- The vector `w` of the domain with graph `z` has `T w = T u`, so `w - u` lies in the kernel.
  set w := T.toGraphSpace.symm z
  have hTw : T w = T u := by
    rw [apply_toGraphSpace_symm, ← graphSnd_apply, ← T.graphSnd.coe_codRestrict_apply _ hmem z,
      hz]
  have hk : (w : E) - u ∈ T.ker := by
    rw [← Submodule.coe_sub, coe_mem_ker_iff, map_sub, hTw, sub_self]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (u : E) ((w : E) - u)
    (Submodule.inner_left_of_mem_orthogonal hk hu)
  rw [add_sub_cancel] at hpyth
  have hw : ‖(w : E)‖ ≤ C * ‖T u‖ := by
    rw [coe_toGraphSpace_symm, ← graphFst_apply]
    exact (T.norm_graphFst_apply_le z).trans hzle
  nlinarith [norm_nonneg (u : E), norm_nonneg (w : E), sq_nonneg ‖(w : E) - u‖]

/-- **Closed range is a Poincaré inequality.** A closed partial linear map `T` from a Hilbert
space to a Banach space has closed range if and only if, for some `c > 0`, `‖u‖ ≤ c ‖T u‖` for
every `u` in its domain orthogonal to its kernel. -/
theorem isClosed_range_iff_exists_norm_le_mul_norm [CompleteSpace F] (hT : T.IsClosed) :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) ↔
      ∃ c > 0, ∀ u : T.domain, (u : E) ∈ T.kerᗮ → ‖(u : E)‖ ≤ c * ‖T u‖ :=
  ⟨exists_norm_le_mul_norm_of_isClosed_range hT, fun ⟨_, _, hc⟩ ↦
    isClosed_range_of_norm_le_mul_norm hT hc⟩

end LinearPMap
