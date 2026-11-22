/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SubmoduleAdjoint
public import TauCeti.Analysis.Normed.Operator.LinearPMap.GraphSpace
public import TauCeti.Topology.Algebra.Module.LinearPMap.Basic

/-!
# The Hodge decomposition of a Hilbert complex

Let `d₀ : E →ₗ.[𝕜] F` and `d₁ : F →ₗ.[𝕜] G` be densely defined partial linear maps between
Hilbert spaces, with `d₁` closed and `range d₀ ≤ ker d₁`. This is one segment of a Hilbert complex,
in the sense of Brüning and Lesch; the model is the `L²` de Rham complex, where `d₀` and `d₁` are
the weak exterior derivative in two consecutive degrees. The **harmonic space**
`LinearPMap.harmonicSpace d₀ d₁ = ker d₁ ⊓ ker d₀†` consists of the vectors that are closed for the
complex and coclosed for its adjoint. This file proves the **Hodge decomposition**

`F = closure (range d₀) ⊕ harmonicSpace d₀ d₁ ⊕ closure (range d₁†)`,

an orthogonal decomposition, and the characterization of closed ranges by a **Poincaré
inequality**: the range of a closed operator `T` is closed exactly when `‖u‖ ≤ c ‖T u‖` for some
`c` and every `u` in the domain of `T` orthogonal to its kernel.

For bounded operators with closed range, the decomposition of the kernel is
`ContinuousLinearMap.range_sup_ker_inf_ker_adjoint`. Here the operators are unbounded, as the
exterior derivative is on `L²` forms, so the decomposition uses the closures of the ranges, and
needs no closed range assumption.

## Main results

* `LinearPMap.topologicalClosure_range_eq_orthogonal_ker_adjoint`: for a densely defined `T`,
  `closure (range T) = (ker T†)ᗮ`; and
  `LinearPMap.topologicalClosure_range_adjoint_eq_orthogonal_ker`: for a closed densely defined
  `T`, `closure (range T†) = (ker T)ᗮ`.
* `LinearPMap.harmonicSpace_eq_orthogonal_sup`: the harmonic space is the orthogonal complement of
  `closure (range d₀) ⊔ closure (range d₁†)`.
* `LinearPMap.topologicalClosure_range_sup_harmonicSpace`: for a complex, the kernel of `d₁` is
  `closure (range d₀) ⊔ harmonicSpace d₀ d₁`, the weak Hodge decomposition of the closed vectors.
* `LinearPMap.topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range_adjoint`:
  the three summands of the Hodge decomposition span `F`; the three orthogonality relations are
  `LinearPMap.isOrtho_topologicalClosure_range_harmonicSpace`,
  `LinearPMap.isOrtho_harmonicSpace_topologicalClosure_range_adjoint` and
  `LinearPMap.isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint`.
* `LinearPMap.isClosed_range_iff_exists_norm_le_mul_norm`: a closed operator between Hilbert spaces
  has closed range if and only if it satisfies a Poincaré inequality on the orthogonal complement
  of its kernel.

## References

* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to
  numerical stability*, Bull. Amer. Math. Soc. 47 (2010), §3.1.
* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques,
  and applications*, Acta Numerica 15 (2006), §3.
* J. Brüning, M. Lesch, *Hilbert complexes*, J. Funct. Anal. 108 (1992).
-/

public section

noncomputable section

open Filter Topology

namespace LinearPMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-! ### Closures of ranges as orthogonal complements of kernels -/

section Range

variable [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] F}

/-- The closure of the range of a densely defined partial linear map `T` is the orthogonal
complement of the kernel of its adjoint. -/
theorem topologicalClosure_range_eq_orthogonal_ker_adjoint (hd : Dense (T.domain : Set E)) :
    (LinearMap.range T.toFun).topologicalClosure = T†.kerᗮ := by
  rw [← orthogonal_range_eq_ker_adjoint hd, Submodule.orthogonal_orthogonal_eq_closure]

/-- The orthogonal complement of the range of the adjoint of a closed densely defined partial
linear map `T` is the kernel of `T`. -/
theorem orthogonal_range_adjoint_eq_ker (hT : T.IsClosed) (hd : Dense (T.domain : Set E)) :
    (LinearMap.range T†.toFun)ᗮ = T.ker := by
  rw [orthogonal_range_eq_ker_adjoint (dense_adjoint_domain hT.isClosable), adjoint_adjoint hT hd]

/-- The closure of the range of the adjoint of a closed densely defined partial linear map `T` is
the orthogonal complement of the kernel of `T`. -/
theorem topologicalClosure_range_adjoint_eq_orthogonal_ker (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (LinearMap.range T†.toFun).topologicalClosure = T.kerᗮ := by
  rw [← orthogonal_range_adjoint_eq_ker hT hd, Submodule.orthogonal_orthogonal_eq_closure]

end Range

/-! ### The harmonic space and the Hodge decomposition -/

section Hodge

variable [CompleteSpace E] {d₀ : E →ₗ.[𝕜] F} {d₁ : F →ₗ.[𝕜] G}

variable (d₀ d₁) in
/-- The **harmonic space** `ker d₁ ⊓ ker d₀†` of a pair of composable partial linear maps
`d₀ : E →ₗ.[𝕜] F` and `d₁ : F →ₗ.[𝕜] G`: the vectors of `F` that are closed for `d₁` and coclosed
for the adjoint of `d₀`. -/
def harmonicSpace : Submodule 𝕜 F :=
  d₁.ker ⊓ d₀†.ker

@[simp]
theorem mem_harmonicSpace_iff {x : F} : x ∈ harmonicSpace d₀ d₁ ↔ x ∈ d₁.ker ∧ x ∈ d₀†.ker :=
  Submodule.mem_inf

/-- Harmonic vectors are closed: they lie in the kernel of `d₁`. -/
theorem harmonicSpace_le_ker : harmonicSpace d₀ d₁ ≤ d₁.ker :=
  inf_le_left

/-- Harmonic vectors are coclosed: they lie in the kernel of `d₀†`. -/
theorem harmonicSpace_le_ker_adjoint : harmonicSpace d₀ d₁ ≤ d₀†.ker :=
  inf_le_right

/-- The harmonic space is closed when `d₁` is closed and `d₀` is densely defined. -/
theorem isClosed_harmonicSpace (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed) :
    _root_.IsClosed (harmonicSpace d₀ d₁ : Set F) :=
  hc₁.isClosed_ker.inter (adjoint_isClosed hd₀).isClosed_ker

/-- The harmonic space consists of the vectors of `ker d₁` orthogonal to the range of `d₀`. -/
theorem harmonicSpace_eq_ker_inf_orthogonal_range (hd₀ : Dense (d₀.domain : Set E)) :
    harmonicSpace d₀ d₁ = d₁.ker ⊓ (LinearMap.range d₀.toFun)ᗮ := by
  rw [harmonicSpace, orthogonal_range_eq_ker_adjoint hd₀]

/-- **Harmonic vectors are orthogonal to exact and coexact ones.** For `d₀` densely defined and
`d₁` closed and densely defined, the harmonic space is the orthogonal complement of
`closure (range d₀) ⊔ closure (range d₁†)`. -/
theorem harmonicSpace_eq_orthogonal_sup [CompleteSpace F] [CompleteSpace G]
    (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F)) :
    harmonicSpace d₀ d₁ = ((LinearMap.range d₀.toFun).topologicalClosure ⊔
      (LinearMap.range d₁†.toFun).topologicalClosure)ᗮ := by
  rw [← Submodule.inf_orthogonal, topologicalClosure_range_eq_orthogonal_ker_adjoint hd₀,
    topologicalClosure_range_adjoint_eq_orthogonal_ker hc₁ hd₁,
    Submodule.orthogonal_orthogonal_eq_closure, Submodule.orthogonal_orthogonal_eq_closure,
    (adjoint_isClosed hd₀).isClosed_ker.submodule_topologicalClosure_eq,
    hc₁.isClosed_ker.submodule_topologicalClosure_eq, harmonicSpace, inf_comm]

omit [CompleteSpace E] in
/-- In a complex `range d₀ ≤ ker d₁` with `d₁` closed, the closure of the range of `d₀` is still
contained in the kernel of `d₁`. -/
theorem topologicalClosure_range_le_ker (hc₁ : d₁.IsClosed)
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ≤ d₁.ker :=
  Submodule.topologicalClosure_minimal _ hcomplex hc₁.isClosed_ker

/-- The closure of the range of `d₀` is orthogonal to the harmonic space. -/
theorem isOrtho_topologicalClosure_range_harmonicSpace (hd₀ : Dense (d₀.domain : Set E)) :
    (LinearMap.range d₀.toFun).topologicalClosure ⟂ harmonicSpace d₀ d₁ := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le, Submodule.orthogonal_closure,
    orthogonal_range_eq_ker_adjoint hd₀]
  exact harmonicSpace_le_ker_adjoint

/-- The harmonic space is orthogonal to the closure of the range of `d₁†`. -/
theorem isOrtho_harmonicSpace_topologicalClosure_range_adjoint [CompleteSpace F] [CompleteSpace G]
    (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F)) :
    harmonicSpace d₀ d₁ ⟂ (LinearMap.range d₁†.toFun).topologicalClosure := by
  rw [Submodule.isOrtho_iff_le, topologicalClosure_range_adjoint_eq_orthogonal_ker hc₁ hd₁]
  exact harmonicSpace_le_ker.trans (Submodule.le_orthogonal_orthogonal _)

omit [CompleteSpace E] in
/-- In a complex, the closures of the ranges of `d₀` and of `d₁†` are orthogonal. -/
theorem isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint [CompleteSpace F]
    [CompleteSpace G] (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ⟂
      (LinearMap.range d₁†.toFun).topologicalClosure := by
  rw [Submodule.isOrtho_iff_le, topologicalClosure_range_adjoint_eq_orthogonal_ker hc₁ hd₁]
  exact (topologicalClosure_range_le_ker hc₁ hcomplex).trans
    (Submodule.le_orthogonal_orthogonal _)

/-- **The Hodge decomposition of the closed vectors.** In a complex `range d₀ ≤ ker d₁`, with `d₀`
densely defined and `d₁` closed, the kernel of `d₁` is the sum of the closure of the range of
`d₀` and the harmonic space. -/
theorem topologicalClosure_range_sup_harmonicSpace [CompleteSpace F]
    (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed)
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ⊔ harmonicSpace d₀ d₁ = d₁.ker := by
  have : (LinearMap.range d₀.toFun).topologicalClosure.HasOrthogonalProjection :=
    have := (Submodule.isClosed_topologicalClosure (LinearMap.range d₀.toFun)).completeSpace_coe
    inferInstance
  rw [harmonicSpace_eq_ker_inf_orthogonal_range hd₀, ← Submodule.orthogonal_closure, inf_comm]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (topologicalClosure_range_le_ker hc₁ hcomplex)

/-- **The Hodge decomposition.** In a complex `range d₀ ≤ ker d₁`, with `d₀` densely defined and
`d₁` closed and densely defined, `F` is the sum of the closure of the range of `d₀`, the harmonic
space and the closure of the range of `d₁†`. The three summands are pairwise orthogonal
(`isOrtho_topologicalClosure_range_harmonicSpace`,
`isOrtho_harmonicSpace_topologicalClosure_range_adjoint` and
`isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint`). -/
theorem topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range_adjoint
    [CompleteSpace F] [CompleteSpace G] (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed)
    (hd₁ : Dense (d₁.domain : Set F)) (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ⊔ harmonicSpace d₀ d₁ ⊔
      (LinearMap.range d₁†.toFun).topologicalClosure = ⊤ := by
  have : d₁.ker.HasOrthogonalProjection :=
    have := hc₁.isClosed_ker.completeSpace_coe
    inferInstance
  rw [topologicalClosure_range_sup_harmonicSpace hd₀ hc₁ hcomplex,
    topologicalClosure_range_adjoint_eq_orthogonal_ker hc₁ hd₁]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

end Hodge

/-! ### Closed range and the Poincaré inequality -/

section Poincare

variable [CompleteSpace E] {T : E →ₗ.[𝕜] F}

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

/-- **A closed range gives a Poincaré inequality.** If a closed partial linear map `T` between
Hilbert spaces has closed range, then for some `c`, `‖u‖ ≤ c ‖T u‖` for every `u` in its domain
orthogonal to its kernel. This is the open mapping theorem for `T` on its graph space. -/
theorem exists_norm_le_mul_norm_of_isClosed_range [CompleteSpace F] (hT : T.IsClosed)
    (hR : _root_.IsClosed (LinearMap.range T.toFun : Set F)) :
    ∃ c : ℝ, ∀ u : T.domain, (u : E) ∈ T.kerᗮ → ‖(u : E)‖ ≤ c * ‖T u‖ := by
  have := hT.completeSpace_graphSpace
  have := hR.completeSpace_coe
  have hmem : ∀ z, T.graphSnd z ∈ LinearMap.range T.toFun := fun z ↦
    T.range_graphSnd ▸ LinearMap.mem_range_self _ z
  -- The bounded operator `T.graphSnd`, onto the range of `T`, is surjective.
  let S : T.graphSpace →L[𝕜] LinearMap.range T.toFun := T.graphSnd.codRestrict _ hmem
  have hS : Function.Surjective S := by
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 (T.range_graphSnd ▸ hy)
    exact ⟨z, rfl⟩
  obtain ⟨C, -, hC⟩ := S.exists_preimage_norm_le hS
  refine ⟨C, fun u hu ↦ ?_⟩
  obtain ⟨z, hz, hzle⟩ := hC ⟨T u, LinearMap.mem_range_self _ u⟩
  -- The vector `w` of the domain with graph `z` has `T w = T u`, so `w - u` lies in the kernel.
  set w := T.toGraphSpace.symm z
  have hTw : T w = T u := by
    rw [apply_toGraphSpace_symm, ← graphSnd_apply]
    exact congrArg Subtype.val hz
  have hk : (w : E) - u ∈ T.ker := by
    rw [← Submodule.coe_sub, coe_mem_ker_iff, map_sub, hTw, sub_self]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (u : E) ((w : E) - u)
    (Submodule.inner_left_of_mem_orthogonal hk hu)
  rw [add_sub_cancel] at hpyth
  have hw : ‖(w : E)‖ ≤ C * ‖T u‖ := by
    rw [coe_toGraphSpace_symm, ← graphFst_apply]
    exact (T.norm_graphFst_apply_le z).trans hzle
  nlinarith [norm_nonneg (u : E), norm_nonneg (w : E), sq_nonneg ‖(w : E) - u‖]

/-- **Closed range is a Poincaré inequality.** A closed partial linear map `T` between Hilbert
spaces has closed range if and only if, for some `c`, `‖u‖ ≤ c ‖T u‖` for every `u` in its domain
orthogonal to its kernel. -/
theorem isClosed_range_iff_exists_norm_le_mul_norm [CompleteSpace F] (hT : T.IsClosed) :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) ↔
      ∃ c : ℝ, ∀ u : T.domain, (u : E) ∈ T.kerᗮ → ‖(u : E)‖ ≤ c * ‖T u‖ :=
  ⟨exists_norm_le_mul_norm_of_isClosed_range hT, fun ⟨_, hc⟩ ↦
    isClosed_range_of_norm_le_mul_norm hT hc⟩

end Poincare

end LinearPMap
