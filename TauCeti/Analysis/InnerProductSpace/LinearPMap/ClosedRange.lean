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

A Poincaré inequality follows from compactness: if the vectors of the domain orthogonal to the
kernel with `‖u‖ ≤ 1` and `‖T u‖ ≤ 1` form a relatively compact set, a sequence violating the
inequality would converge, after normalization, to a unit vector both in the kernel and orthogonal
to it. Between Hilbert spaces, the **closed range theorem** says that a closed densely defined `T`
has closed range exactly when its adjoint does: a Poincaré inequality for `T†` gives one for `T` by
duality, as `(ker T)ᗮ` is then the range of `T†`.

## Main results

* `LinearPMap.isClosed_range_of_norm_le_mul_norm`: a Poincaré inequality closes the range; the
  target need not be complete.
* `LinearPMap.exists_norm_le_mul_norm_of_isClosed_range`: a closed range gives a Poincaré
  inequality when `F` is complete, by the open mapping theorem on the graph space.
* `LinearPMap.isClosed_range_iff_exists_norm_le_mul_norm`: the two together.
* `LinearPMap.exists_norm_le_mul_norm_of_isCompact_closure`: compactness gives a Poincaré
  inequality.
* `LinearPMap.isClosed_range_adjoint_iff`: the closed range theorem.

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
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]

section Normed

variable [NormedSpace 𝕜 F] {T : E →ₗ.[𝕜] F}

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

omit [CompleteSpace E] in
/-- **Compactness gives a Poincaré inequality.** Let `T` be a closed partial linear map from a
Hilbert space. If every `u` in the domain of `T`, orthogonal to its kernel, with `‖u‖ ≤ 1` and
`‖T u‖ ≤ 1`, lies in a set `s` with compact closure, then for some `c > 0`, `‖u‖ ≤ c ‖T u‖` for
every `u` in the domain of `T` orthogonal to its kernel. -/
theorem exists_norm_le_mul_norm_of_isCompact_closure (hT : T.IsClosed) {s : Set E}
    (hs : IsCompact (_root_.closure s))
    (hsub : ∀ u : T.domain, (u : E) ∈ T.kerᗮ → ‖(u : E)‖ ≤ 1 → ‖T u‖ ≤ 1 → (u : E) ∈ s) :
    ∃ c > 0, ∀ u : T.domain, (u : E) ∈ T.kerᗮ → ‖(u : E)‖ ≤ c * ‖T u‖ := by
  by_contra! h
  -- A sequence of unit vectors orthogonal to the kernel with `‖T w n‖ < 1 / (n + 1)`.
  have hseq : ∀ n : ℕ, ∃ w : T.domain, (w : E) ∈ T.kerᗮ ∧ ‖(w : E)‖ = 1 ∧
      ‖T w‖ < 1 / (n + 1) := fun n ↦ by
    obtain ⟨u, hu, hlt⟩ := h (n + 1) (by positivity)
    have hu0 : (u : E) ≠ 0 := fun h0 ↦ by
      rw [h0, norm_zero] at hlt
      exact hlt.not_ge (by positivity)
    have hpos : 0 < ‖(u : E)‖ := norm_pos_iff.2 hu0
    refine ⟨(‖(u : E)‖⁻¹ : 𝕜) • u, Submodule.smul_mem _ _ hu, norm_smul_inv_norm hu0, ?_⟩
    simp only [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
    rw [inv_mul_lt_iff₀ hpos]
    field_simp
    linarith [hlt]
  choose w hw hw1 hwT using hseq
  have hTw : Tendsto (fun n ↦ T (w n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n ↦ (hwT n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨a, -, φ, hφ, hlim⟩ := hs.tendsto_subseq fun n ↦
    subset_closure (hsub (w n) (hw n) (hw1 n).le ((hwT n).le.trans
      (div_le_one_of_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by positivity))))
  -- The limit is a unit vector in the kernel of `T`, by the closed graph, and orthogonal to it.
  have hker : a ∈ T.ker := (T.mem_ker_iff_mem_graph).2 <| hT.mem_of_tendsto
    (hlim.prodMk_nhds (hTw.comp hφ.tendsto_atTop)) (Eventually.of_forall fun n ↦ T.mem_graph _)
  have hperp : a ∈ T.kerᗮ := (Submodule.isClosed_orthogonal _).mem_of_tendsto hlim
    (Eventually.of_forall fun n ↦ hw (φ n))
  have hnorm : ‖a‖ = 1 := tendsto_nhds_unique hlim.norm (by simp [hw1])
  rw [Submodule.disjoint_def.1 T.ker.orthogonal_disjoint a hker hperp, norm_zero] at hnorm
  exact zero_ne_one hnorm

end Normed

/-! ### The closed range theorem -/

section Adjoint

variable [InnerProductSpace 𝕜 F] [CompleteSpace F] {T : E →ₗ.[𝕜] F}

/-- **A closed range for the adjoint gives a Poincaré inequality.** If the adjoint of a
closed densely defined partial linear map `T` between Hilbert spaces has closed range, then for
some `c > 0`, `‖u‖ ≤ c ‖T u‖` for every `u` in the domain of `T` orthogonal to its kernel. -/
theorem exists_norm_le_mul_norm_of_isClosed_range_adjoint (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (hR : _root_.IsClosed (LinearMap.range T†.toFun : Set E)) :
    ∃ c > 0, ∀ u : T.domain, (u : E) ∈ T.kerᗮ → ‖(u : E)‖ ≤ c * ‖T u‖ := by
  obtain ⟨c, hc, hP⟩ := exists_norm_le_mul_norm_of_isClosed_range (adjoint_isClosed hd) hR
  have : T†.ker.HasOrthogonalProjection :=
    have := (adjoint_isClosed hd).isClosed_ker.completeSpace_coe
    inferInstance
  refine ⟨c, hc, fun u hu ↦ ?_⟩
  -- The vectors orthogonal to `ker T` form the range of `T†`, so `u = T† v` with `v ⊥ ker T†`.
  rw [← topologicalClosure_range_adjoint_eq_orthogonal_ker hT hd,
    hR.submodule_topologicalClosure_eq] at hu
  obtain ⟨v₀, hv₀⟩ := LinearMap.mem_range.1 hu
  obtain ⟨v, hv, hTv⟩ := exists_coe_eq_sub_starProjection v₀
  have hvperp : (v : F) ∈ T†.kerᗮ := hv ▸ T†.ker.sub_starProjection_mem_orthogonal _
  have hTv' : T† v = u := hTv.trans hv₀
  -- Then `‖u‖² = re ⟪T† v, u⟫ = re ⟪v, T u⟫ ≤ ‖v‖ ‖T u‖ ≤ c ‖u‖ ‖T u‖`.
  have hsq : ‖(u : E)‖ ^ 2 ≤ c * ‖(u : E)‖ * ‖T u‖ := by
    calc ‖(u : E)‖ ^ 2 = RCLike.re (inner 𝕜 (T† v) (u : E)) := by
          rw [hTv', inner_self_eq_norm_sq]
      _ = RCLike.re (inner 𝕜 (v : F) (T u)) := by rw [adjoint_isFormalAdjoint hd v u]
      _ ≤ ‖(v : F)‖ * ‖T u‖ := (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ c * ‖T† v‖ * ‖T u‖ := by gcongr; exact hP v hvperp
      _ = c * ‖(u : E)‖ * ‖T u‖ := by rw [hTv']
  rcases (norm_nonneg (u : E)).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith

/-- If the adjoint of a closed densely defined partial linear map between Hilbert spaces has
closed range, so does the map. -/
theorem isClosed_range_of_isClosed_range_adjoint (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (hR : _root_.IsClosed (LinearMap.range T†.toFun : Set E)) :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) :=
  have ⟨_, _, hc⟩ := exists_norm_le_mul_norm_of_isClosed_range_adjoint hT hd hR
  isClosed_range_of_norm_le_mul_norm hT hc

/-- **The closed range theorem.** A closed densely defined partial linear map between Hilbert
spaces has closed range if and only if its adjoint does. -/
theorem isClosed_range_adjoint_iff (hT : T.IsClosed) (hd : Dense (T.domain : Set E)) :
    _root_.IsClosed (LinearMap.range T†.toFun : Set E) ↔
      _root_.IsClosed (LinearMap.range T.toFun : Set F) := by
  refine ⟨isClosed_range_of_isClosed_range_adjoint hT hd, fun hR ↦ ?_⟩
  rw [← adjoint_adjoint hT hd] at hR
  exact isClosed_range_of_isClosed_range_adjoint (adjoint_isClosed hd)
    (dense_adjoint_domain hT.isClosable) hR

end Adjoint

end LinearPMap
