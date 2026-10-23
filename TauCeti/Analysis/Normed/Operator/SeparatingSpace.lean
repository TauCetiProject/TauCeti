/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# The separating space of a linear map

For a linear map `T : E →ₗ[R] F` between topological modules, the *separating space*
`T.separatingSpace` is the set of `y : F` such that `(0, y)` lies in the closure of the graph
of `T`. When `E` and `F` are first countable these are exactly the limits of `T xₙ` along
sequences `xₙ → 0`. The separating space measures the failure of continuity of `T`, and it is
the basic object of automatic continuity theory for Banach algebras.

The separating space is a closed submodule, and the closure of the graph of `T` is described
fibrewise by it: `(x, y)` lies in the closure exactly when `y - T x ∈ T.separatingSpace`. Hence
the graph of `T` is closed exactly when the separating space vanishes. Between Banach spaces the
closed graph theorem turns this into the criterion `Continuous T ↔ T.separatingSpace = ⊥`, and
more precisely the separating space is the smallest closed subspace modulo which `T` becomes
continuous.

## Main definitions

* `LinearMap.separatingSpace`: the separating space of a linear map, as a submodule.

## Main results

* `LinearMap.isClosed_separatingSpace`: the separating space is closed.
* `LinearMap.mem_separatingSpace_iff_mapClusterPt`,
  `LinearMap.mem_separatingSpace_iff_exists_seq`: the filter and sequential descriptions.
* `LinearMap.mem_closure_graph_iff`: the closure of the graph, fibre by fibre.
* `LinearMap.isClosed_graph_iff_separatingSpace_eq_bot`.
* `LinearMap.separatingSpace_add`: invariance under continuous perturbations.
* `LinearMap.map_separatingSpace_le`, `LinearMap.separatingSpace_comp_le`: behaviour under
  composition with continuous linear maps.
* `LinearMap.continuous_iff_separatingSpace_eq_bot`: a linear map between Banach spaces is
  continuous if and only if its separating space is trivial.
* `LinearMap.continuous_mkQ_comp`: a linear map between Banach spaces becomes continuous
  modulo its separating space.
* `LinearMap.continuous_comp_iff_separatingSpace_le_ker`: for a continuous linear map `W`,
  the composite `W ∘ T` is continuous exactly when `W` kills the separating space of `T`.
* `LinearMap.separatingSpace_comp`: the separating space of `U ∘ T` is the closure of the
  image under `U` of the separating space of `T`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §5.2.
* A. M. Sinclair, *Automatic Continuity of Linear Operators*, London Math. Soc. Lecture Note
  Series 21.
-/

public section

open Filter Topology

namespace LinearMap

section Topological

variable {R D E F G : Type*} [Ring R]
  [AddCommGroup D] [Module R D] [TopologicalSpace D] [IsTopologicalAddGroup D]
  [ContinuousConstSMul R D]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul R E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul R F]
  [AddCommGroup G] [Module R G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul R G]
  (T : E →ₗ[R] F)

/-- The *separating space* of a linear map `T : E →ₗ[R] F` between topological modules: the
vertical fibre over `0` of the closure of the graph of `T`. For first countable spaces it
consists of the limits of `T xₙ` along sequences `xₙ → 0`
(`LinearMap.mem_separatingSpace_iff_exists_seq`). -/
def separatingSpace : Submodule R F :=
  T.graph.topologicalClosure.comap (LinearMap.inr R E F)

/-- The separating space is the vertical fibre over `0` of the closure of the graph. -/
theorem mem_separatingSpace_iff_mem_closure {y : F} :
    y ∈ T.separatingSpace ↔ ((0 : E), y) ∈ closure (T.graph : Set (E × F)) := by
  rw [separatingSpace, Submodule.mem_comap, inr_apply, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe]

/-- The separating space is closed. -/
theorem isClosed_separatingSpace : IsClosed (T.separatingSpace : Set F) := by
  rw [separatingSpace, Submodule.comap_coe, Submodule.topologicalClosure_coe]
  exact isClosed_closure.preimage (continuous_const.prodMk continuous_id)

/-- `y` lies in the separating space of `T` exactly when it is a cluster point of `T` at `0`. -/
theorem mem_separatingSpace_iff_mapClusterPt {y : F} :
    y ∈ T.separatingSpace ↔ MapClusterPt y (𝓝 0) T := by
  rw [mem_separatingSpace_iff_mem_closure,
    mem_closure_iff_nhds_basis ((𝓝 (0 : E)).basis_sets.prod_nhds (𝓝 y).basis_sets),
    mapClusterPt_iff_frequently]
  simp only [frequently_iff, id_eq, Prod.forall, Set.mem_prod, SetLike.mem_coe, mem_graph_iff]
  constructor
  · intro h V hV U hU
    obtain ⟨⟨x, z⟩, hz, hx, hz'⟩ := h U V ⟨hU, hV⟩
    exact ⟨x, hx, hz ▸ hz'⟩
  · rintro h U V ⟨hU, hV⟩
    obtain ⟨x, hx, hTx⟩ := h V hV hU
    exact ⟨(x, T x), rfl, hx, hTx⟩

/-- For first countable spaces, `y` lies in the separating space of `T` exactly when
`T xₙ → y` for some sequence `xₙ → 0`. -/
theorem mem_separatingSpace_iff_exists_seq [FirstCountableTopology E] [FirstCountableTopology F]
    {y : F} : y ∈ T.separatingSpace ↔
      ∃ x : ℕ → E, Tendsto x atTop (𝓝 0) ∧ Tendsto (T ∘ x) atTop (𝓝 y) := by
  rw [mem_separatingSpace_iff_mem_closure, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨p, hp, hlim⟩
    refine ⟨Prod.fst ∘ p, (continuous_fst.tendsto _).comp hlim, ?_⟩
    have hTp : T ∘ Prod.fst ∘ p = Prod.snd ∘ p := funext fun n ↦ (hp n).symm
    rw [hTp]
    exact (continuous_snd.tendsto _).comp hlim
  · rintro ⟨x, hx, hTx⟩
    exact ⟨fun n ↦ (x n, T (x n)), fun n ↦ rfl, hx.prodMk_nhds hTx⟩

/-- The closure of the graph of `T` is the graph of `T` thickened by the separating space. -/
theorem mem_closure_graph_iff {x : E} {y : F} :
    (x, y) ∈ closure (T.graph : Set (E × F)) ↔ y - T x ∈ T.separatingSpace := by
  have hx : (x, T x) ∈ T.graph.topologicalClosure :=
    T.graph.le_topologicalClosure ((T.mem_graph_iff _).2 rfl)
  rw [mem_separatingSpace_iff_mem_closure, ← Submodule.topologicalClosure_coe,
    SetLike.mem_coe, SetLike.mem_coe, ← Submodule.sub_mem_iff_left _ hx, Prod.mk_sub_mk,
    sub_self]

/-- The graph of a linear map is closed if and only if its separating space is trivial. -/
theorem isClosed_graph_iff_separatingSpace_eq_bot :
    IsClosed (T.graph : Set (E × F)) ↔ T.separatingSpace = ⊥ := by
  rw [Submodule.eq_bot_iff, ← closure_subset_iff_isClosed]
  constructor
  · intro h y hy
    simpa using h ((T.mem_separatingSpace_iff_mem_closure).1 hy)
  · rintro h ⟨x, y⟩ hxy
    exact (T.mem_graph_iff _).2 (sub_eq_zero.1 (h _ ((T.mem_closure_graph_iff).1 hxy)))

/-- A continuous linear map into a Hausdorff space has trivial separating space. -/
theorem separatingSpace_eq_bot_of_continuous [T2Space F] (hT : Continuous T) :
    T.separatingSpace = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun y hy ↦ ?_
  have hT0 : Tendsto T (𝓝 0) (𝓝 0) := by simpa using hT.tendsto 0
  exact eq_of_nhds_neBot (((T.mem_separatingSpace_iff_mapClusterPt).1 hy).clusterPt.mono hT0).neBot

/-- A continuous linear map `U` sends the separating space of `T` into that of `U ∘ T`. -/
theorem map_separatingSpace_le (U : F →L[R] G) :
    T.separatingSpace.map (U : F →ₗ[R] G) ≤ ((U : F →ₗ[R] G) ∘ₗ T).separatingSpace := by
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, mem_separatingSpace_iff_mapClusterPt] at hy
  rw [mem_separatingSpace_iff_mapClusterPt]
  exact hy.continuousAt_comp U.continuous.continuousAt

/-- If `U ∘ T` is continuous for a continuous linear map `U` into a Hausdorff space, then `U`
vanishes on the separating space of `T`. -/
theorem separatingSpace_le_ker_of_continuous_comp [T2Space G] (U : F →L[R] G)
    (hU : Continuous ((U : F →ₗ[R] G) ∘ₗ T)) :
    T.separatingSpace ≤ ker (U : F →ₗ[R] G) := by
  intro y hy
  have h := T.map_separatingSpace_le U ⟨y, hy, rfl⟩
  rw [separatingSpace_eq_bot_of_continuous _ hU] at h
  simpa using h

/-- Precomposing with a continuous linear map can only shrink the separating space. -/
theorem separatingSpace_comp_le (V : D →L[R] E) :
    (T ∘ₗ (V : D →ₗ[R] E)).separatingSpace ≤ T.separatingSpace := by
  intro y hy
  rw [mem_separatingSpace_iff_mapClusterPt] at hy ⊢
  have hV : Tendsto V (𝓝 0) (𝓝 0) := by simpa using V.continuous.tendsto 0
  exact hy.of_comp hV

/-- The separating space is unchanged by adding a continuous linear map. -/
@[simp]
theorem separatingSpace_add (P : E →L[R] F) :
    (T + (P : E →ₗ[R] F)).separatingSpace = T.separatingSpace := by
  let Ψ := (ContinuousLinearEquiv.refl R E).skewProd (ContinuousLinearEquiv.refl R F) P
  have hΨ : Ψ ⁻¹' ((T + (P : E →ₗ[R] F)).graph : Set (E × F)) = T.graph := by
    ext ⟨x, y⟩
    simp [Ψ]
  ext y
  rw [mem_separatingSpace_iff_mem_closure, mem_separatingSpace_iff_mem_closure, ← hΨ,
    ← Ψ.preimage_closure, Set.mem_preimage]
  simp [Ψ]

/-- The graph of `T` becomes closed after passing to the quotient by its separating space. -/
theorem isClosed_graph_mkQ_comp :
    IsClosed ((T.separatingSpace.mkQ ∘ₗ T).graph : Set (E × (F ⧸ T.separatingSpace))) := by
  have hq : IsOpenQuotientMap (Prod.map (_root_.id : E → E) T.separatingSpace.mkQ) :=
    IsOpenQuotientMap.id.prodMap T.separatingSpace.isOpenQuotientMap_mkQ
  rw [← hq.isQuotientMap.isCoinducing.isClosed_preimage]
  convert isClosed_closure (s := (T.graph : Set (E × F))) using 1
  ext ⟨x, y⟩
  simp [mem_closure_graph_iff, Submodule.Quotient.eq]

end Topological

section Banach

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  (T : E →ₗ[𝕜] F)

/-- A linear map between Banach spaces is continuous if and only if its separating space is
trivial. -/
theorem continuous_iff_separatingSpace_eq_bot : Continuous T ↔ T.separatingSpace = ⊥ :=
  ⟨T.separatingSpace_eq_bot_of_continuous, fun h ↦
    T.continuous_of_isClosed_graph ((T.isClosed_graph_iff_separatingSpace_eq_bot).2 h)⟩

/-- A linear map between Banach spaces becomes continuous modulo its separating space. -/
theorem continuous_mkQ_comp : Continuous (T.separatingSpace.mkQ ∘ₗ T) := by
  -- Closedness of the separating space makes the quotient a Banach space.
  have := T.isClosed_separatingSpace
  exact (T.separatingSpace.mkQ ∘ₗ T).continuous_of_isClosed_graph T.isClosed_graph_mkQ_comp

/-- For a linear map `T` between Banach spaces and a continuous linear map `W` into a
Hausdorff space, `W ∘ T` is continuous if and only if `W` vanishes on the separating space
of `T`. -/
theorem continuous_comp_iff_separatingSpace_le_ker [AddCommGroup G] [Module 𝕜 G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G] [T2Space G]
    (W : F →L[𝕜] G) :
    Continuous ((W : F →ₗ[𝕜] G) ∘ₗ T) ↔ T.separatingSpace ≤ ker (W : F →ₗ[𝕜] G) := by
  refine ⟨T.separatingSpace_le_ker_of_continuous_comp W, fun h ↦ ?_⟩
  have hW : (W : F →ₗ[𝕜] G) ∘ₗ T =
      (T.separatingSpace.liftQL W h : F ⧸ T.separatingSpace →ₗ[𝕜] G) ∘ₗ
        (T.separatingSpace.mkQ ∘ₗ T) := by
    ext x
    simp
  rw [hW, coe_comp]
  exact (T.separatingSpace.liftQL W h).continuous.comp T.continuous_mkQ_comp

/-- The separating space of `U ∘ T` is the closure of the image under `U` of the separating
space of `T`. -/
theorem separatingSpace_comp [NormedAddCommGroup G] [NormedSpace 𝕜 G] (U : F →L[𝕜] G) :
    ((U : F →ₗ[𝕜] G) ∘ₗ T).separatingSpace =
      (T.separatingSpace.map (U : F →ₗ[𝕜] G)).topologicalClosure := by
  set K := (T.separatingSpace.map (U : F →ₗ[𝕜] G)).topologicalClosure
  refine le_antisymm ?_ (Submodule.topologicalClosure_minimal _ (T.map_separatingSpace_le U)
    ((U : F →ₗ[𝕜] G) ∘ₗ T).isClosed_separatingSpace)
  -- Closedness of `K` makes `G ⧸ K` a normed, hence Hausdorff, space.
  have : IsClosed (K : Set G) := Submodule.isClosed_topologicalClosure _
  have hKU : T.separatingSpace ≤ ker ((K.mkQL ∘L U : F →L[𝕜] G ⧸ K) : F →ₗ[𝕜] G ⧸ K) := by
    intro y hy
    have hUy : U y ∈ K := Submodule.le_topologicalClosure _ ⟨y, hy, rfl⟩
    simpa [Submodule.Quotient.mk_eq_zero] using hUy
  have hcont := (T.continuous_comp_iff_separatingSpace_le_ker (K.mkQL ∘L U)).2 hKU
  simpa using ((U : F →ₗ[𝕜] G) ∘ₗ T).separatingSpace_le_ker_of_continuous_comp K.mkQL hcont

end Banach

end LinearMap
