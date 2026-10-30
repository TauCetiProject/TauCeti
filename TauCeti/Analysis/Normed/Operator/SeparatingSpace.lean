/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

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

Sinclair's stability lemma controls separating spaces along a sequence of composites. Given
Banach spaces `E n` and `F`, continuous linear maps `R n : E (n + 1) → E n`, and linear maps
`T n : E n → F` with `T (n + 1) = T n ∘ R n`, the separating spaces of the `T n` form a decreasing
sequence that is eventually constant. This is the analytic input to the theory of separating
ideals in automatic continuity. Applied to continuous linear maps that intertwine `T` up to
continuous errors, it shows that the closures of the images of the separating space under the
successive products stabilize.

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
* `LinearMap.map_separatingSpace_le_of_continuous_sub`: a continuous linear map `U` with
  `U ∘ T - T' ∘ V` continuous for a continuous linear map `V` sends the separating space of
  `T` into that of `T'`.
* `LinearMap.exists_norm_le_le_norm_mkQ_apply`: modulo a closed subspace not containing the
  separating space, `T` sends arbitrarily small vectors to arbitrarily large ones.
* `TauCeti.antitone_separatingSpace`, `TauCeti.eventuallyConst_separatingSpace`: Sinclair's
  stability lemma.
* `LinearMap.eventuallyConst_topologicalClosure_map_separatingSpace`: stabilization of the
  closed images of the separating space under successive intertwining products.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §5.2, in particular the
  stability lemma 5.2.5.
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

/-- Two linear maps differing by a continuous linear map have the same separating space. -/
theorem separatingSpace_eq_of_continuous_sub {T₁ T₂ : E →ₗ[R] F} (h : Continuous (T₁ - T₂)) :
    T₁.separatingSpace = T₂.separatingSpace := by
  simpa using T₂.separatingSpace_add ⟨T₁ - T₂, h⟩

/-- If `U ∘ T - T' ∘ V` is continuous for continuous linear maps `U` and `V`, then `U` maps the
separating space of `T` into that of `T'`. Taking `T' = T` and `U`, `V` the left or right
actions of an algebra on `F` and `E`, this says that the separating space of a map whose
commutators with the actions are continuous is a submodule. -/
theorem map_separatingSpace_le_of_continuous_sub (T' : D →ₗ[R] G) (U : F →L[R] G)
    (V : E →L[R] D) (h : Continuous ((U : F →ₗ[R] G) ∘ₗ T - T' ∘ₗ (V : E →ₗ[R] D))) :
    T.separatingSpace.map (U : F →ₗ[R] G) ≤ T'.separatingSpace :=
  (T.map_separatingSpace_le U).trans
    ((separatingSpace_eq_of_continuous_sub h).trans_le (T'.separatingSpace_comp_le V))

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

/-- If the separating space of a linear map `T` between Banach spaces is not contained in a
closed subspace `N`, then modulo `N` the map `T` sends arbitrarily small vectors to arbitrarily
large ones. -/
theorem exists_norm_le_le_norm_mkQ_apply {N : Submodule 𝕜 F} [IsClosed (N : Set F)]
    (hT : ¬T.separatingSpace ≤ N) {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    ∃ x, ‖x‖ ≤ δ ∧ c ≤ ‖N.mkQ (T x)‖ := by
  by_contra! h
  obtain ⟨C, hC⟩ :=
    (N.mkQ ∘ₗ T).bound_of_ball_bound hδ c fun x hx ↦ (h x (mem_ball_zero_iff.1 hx).le).le
  refine hT ?_
  simpa using (T.continuous_comp_iff_separatingSpace_le_ker N.mkQL).1
    (AddMonoidHomClass.continuous_of_bound _ C hC)

end Banach

end LinearMap

/-! ### The stability lemma -/

namespace TauCeti

open Finset LinearMap

section Topological

variable {𝕜 F : Type*} [Ring 𝕜]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  {E : ℕ → Type*} [∀ n, AddCommGroup (E n)] [∀ n, Module 𝕜 (E n)]
  [∀ n, TopologicalSpace (E n)] [∀ n, IsTopologicalAddGroup (E n)]
  [∀ n, ContinuousConstSMul 𝕜 (E n)]

/-- For linear maps `T n : E n →ₗ F` with `T (n + 1) = T n ∘ R n` for continuous linear maps
`R n : E (n + 1) → E n`, the separating spaces of the `T n` decrease. -/
theorem antitone_separatingSpace {T : ∀ n, E n →ₗ[𝕜] F} {R : ∀ n, E (n + 1) →L[𝕜] E n}
    (hT : ∀ n, T (n + 1) = T n ∘ₗ (R n : E (n + 1) →ₗ[𝕜] E n)) :
    Antitone fun n ↦ (T n).separatingSpace :=
  antitone_nat_of_succ_le fun n ↦ hT n ▸ (T n).separatingSpace_comp_le (R n)

end Topological

section Banach

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]
  (R : ∀ n, E (n + 1) →L[𝕜] E n)

/-- The composite `R m ∘ R (m + 1) ∘ ⋯ ∘ R (m + k - 1) : E (m + k) → E m`. -/
private noncomputable def descend (m : ℕ) : ∀ k, E (m + k) →L[𝕜] E m
  | 0 => ContinuousLinearMap.id 𝕜 (E m)
  | k + 1 => (descend m k).comp (R (m + k))

/-- The composite `R 0 ∘ R 1 ∘ ⋯ ∘ R (n - 1) : E n → E 0`. -/
private noncomputable def toBase : ∀ n, E n →L[𝕜] E 0
  | 0 => ContinuousLinearMap.id 𝕜 (E 0)
  | n + 1 => (toBase n).comp (R n)

private theorem descend_succ (m k : ℕ) :
    descend R m (k + 1) = (descend R m k).comp (R (m + k)) := rfl

private theorem toBase_succ (n : ℕ) : toBase R (n + 1) = (toBase R n).comp (R n) := rfl

private theorem toBase_add (m : ℕ) : ∀ k, toBase R (m + k) = (toBase R m).comp (descend R m k)
  | 0 => (ContinuousLinearMap.comp_id _).symm
  | k + 1 => by
    rw [descend_succ, ← ContinuousLinearMap.comp_assoc, ← toBase_add m k]
    -- `m + (k + 1)` is definitionally `m + k + 1`.
    exact toBase_succ R (m + k)

private theorem apply_toBase {T : ∀ n, E n →ₗ[𝕜] F}
    (hT : ∀ n, T (n + 1) = T n ∘ₗ (R n : E (n + 1) →ₗ[𝕜] E n)) :
    ∀ n (v : E n), T 0 (toBase R n v) = T n v
  | 0, _ => rfl
  | n + 1, v => by
    rw [hT, LinearMap.comp_apply, ← apply_toBase hT n, toBase_succ,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe]

/-- Splitting off the first `m` terms of `∑ⱼ R 0 ⋯ R (j - 1) (x j)`: the tail lies in the image
of `R 0 ⋯ R (m - 1)`. -/
private theorem tsum_toBase_eq (x : ∀ n, E n) (m : ℕ)
    (hx : Summable fun j ↦ toBase R j (x j))
    (hxm : Summable fun k ↦ descend R m k (x (m + k))) :
    ∑' j, toBase R j (x j) = ∑ j ∈ range m, toBase R j (x j) +
      toBase R m (∑' k, descend R m k (x (m + k))) := by
  set f : ℕ → E 0 := fun j ↦ toBase R j (x j)
  have htail : ∀ k, toBase R m (descend R m k (x (m + k))) = f (k + m) := fun k ↦ by
    rw [add_comm k m, ← ContinuousLinearMap.comp_apply, ← toBase_add]
  rw [(toBase R m).map_tsum hxm, tsum_congr htail]
  exact (hx.sum_add_tsum_nat_add m).symm

/-- Positive weights `ε j` for the gliding hump: `ε j` is small against `toBase R j` and against
every composite `descend R (n + 1) k` ending at index `j = n + 1 + k`, scaled by `a n ≥ 0`. -/
private theorem exists_pos_weights_toBase_descend (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    ∃ ε : ℕ → ℝ, (∀ j, 0 < ε j) ∧ (∀ j, ‖toBase R j‖ * ε j ≤ (1 / 2) ^ j) ∧
      ∀ n k, a n * ‖descend R (n + 1) k‖ * ε (n + 1 + k) ≤ (1 / 2) ^ (n + 1 + k) := by
  -- `B j` dominates every coefficient that meets the weight at `j`.
  let c : ℕ → ℕ → ℝ := fun m k ↦ a m * ‖descend R (m + 1) k‖
  let B : ℕ → ℝ := fun j ↦ ‖toBase R j‖ + ∑ m ∈ range j, c m (j - (m + 1))
  choose ε hε hεB using fun j ↦ exists_pos_mul_lt (pow_pos (one_half_pos (α := ℝ)) j) (B j)
  have hcoef : ∀ m k, 0 ≤ c m k := fun m k ↦ mul_nonneg (ha m) (norm_nonneg _)
  refine ⟨ε, hε, fun j ↦ ?_, fun n k ↦ ?_⟩
  · exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sum_nonneg fun m _ ↦ hcoef m _))
      (hε j).le).trans (hεB j).le
  · have h := single_le_sum (f := fun m ↦ c m (n + 1 + k - (m + 1)))
      (fun m _ ↦ hcoef m _) (mem_range.2 (by omega : n < n + 1 + k))
    simp only [Nat.add_sub_cancel_left] at h
    refine (mul_le_mul_of_nonneg_right ?_ (hε _).le).trans (hεB _).le
    exact h.trans (le_add_of_nonneg_left (norm_nonneg _))

variable {R} in
/-- The gliding-hump estimate at step `n`. Let `L` agree with `N.mkQ ∘ T (n + 1)`, and let the
summands of `y = ∑ⱼ R 0 ⋯ R (j - 1) (x j)` beyond `n` be small against `‖L‖ + 1`. Then modulo `N`
the image of the `n`-th summand is bounded by `‖T 0 y‖`, the partial sum before `n`, and `1`. -/
private theorem norm_mkQ_apply_le [∀ n, CompleteSpace (E n)] {T : ∀ n, E n →ₗ[𝕜] F}
    (hT : ∀ n, T (n + 1) = T n ∘ₗ (R n : E (n + 1) →ₗ[𝕜] E n)) {N : Submodule 𝕜 F} (n : ℕ)
    (L : E (n + 1) →L[𝕜] F ⧸ N) (hL : ∀ w, L w = N.mkQ (T (n + 1) w))
    {x : ∀ j, E j} {ε : ℕ → ℝ} (hx : ∀ j, ‖x j‖ ≤ ε j)
    (hε : ∀ k, (‖L‖ + 1) * ‖descend R (n + 1) k‖ * ε (n + 1 + k) ≤ (1 / 2) ^ (n + 1 + k))
    (hfs : Summable fun j ↦ toBase R j (x j)) :
    ‖N.mkQ (T n (x n))‖ ≤ ‖T 0 (∑' j, toBase R j (x j))‖ +
      ‖N.mkQ (T 0 (∑ j ∈ range n, toBase R j (x j)))‖ + 1 := by
  set g : ℕ → E (n + 1) := fun k ↦ descend R (n + 1) k (x (n + 1 + k))
  have hg : ∀ k, (‖L‖ + 1) * ‖g k‖ ≤ (1 / 2) ^ (k + 1) := by
    intro k
    calc (‖L‖ + 1) * ‖g k‖ ≤ (‖L‖ + 1) * (‖descend R (n + 1) k‖ * ε (n + 1 + k)) :=
          mul_le_mul_of_nonneg_left (((descend R (n + 1) k).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _))) (by positivity)
      _ = (‖L‖ + 1) * ‖descend R (n + 1) k‖ * ε (n + 1 + k) := by ring
      _ ≤ (1 / 2) ^ (n + 1 + k) := hε k
      _ ≤ (1 / 2) ^ (k + 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hgeom : HasSum (fun k : ℕ ↦ ((1 : ℝ) / 2) ^ (k + 1)) 1 := by
    have := hasSum_geometric_two.mul_right (1 / 2)
    norm_num [← pow_succ] at this
    exact this
  have hgle : ∀ k, ‖g k‖ ≤ (1 / 2) ^ (k + 1) := fun k ↦
    (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg L])).trans (hg k)
  have hgs : Summable g := Summable.of_norm_bounded hgeom.summable hgle
  have hLw : ‖L (∑' k, g k)‖ ≤ 1 :=
    (hgs.hasSum.mapL L).norm_le_of_bounded hgeom fun k ↦ (L.le_opNorm _).trans <|
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)).trans (hg k)
  set y := ∑' j, toBase R j (x j) with hy
  set s := ∑ j ∈ range n, toBase R j (x j) with hs
  -- Split `y` into the summands before `n`, the `n`-th summand, and the tail through `R n`.
  have hdec : T 0 y = T 0 s + T n (x n) + T (n + 1) (∑' k, g k) := by
    rw [hy, tsum_toBase_eq R x (n + 1) hfs hgs, sum_range_succ, ← hs, map_add, map_add,
      apply_toBase R hT, apply_toBase R hT]
  set Q := N.mkQ
  have hQ : Q (T n (x n)) = Q (T 0 y) - Q (T 0 s) - L (∑' k, g k) := by
    rw [hdec, map_add, map_add, hL]
    abel
  have h1 : ‖Q (T 0 y)‖ ≤ ‖T 0 y‖ := Submodule.Quotient.norm_mk_le N (T 0 y)
  rw [hQ]
  linarith [norm_sub_le (Q (T 0 y) - Q (T 0 s)) (L (∑' k, g k)),
    norm_sub_le (Q (T 0 y)) (Q (T 0 s))]

variable {R} in
/-- **Sinclair's stability lemma.** Let `E n` and `F` be Banach spaces, let
`R n : E (n + 1) → E n` be continuous linear maps, and let `T n : E n →ₗ F` be linear maps, not
assumed continuous, with `T (n + 1) = T n ∘ R n`, so that `T n = T 0 ∘ R 0 ∘ ⋯ ∘ R (n - 1)`.
Then the decreasing sequence of separating spaces of the `T n` is eventually constant. -/
theorem eventuallyConst_separatingSpace [CompleteSpace F] [∀ n, CompleteSpace (E n)]
    {T : ∀ n, E n →ₗ[𝕜] F} (hT : ∀ n, T (n + 1) = T n ∘ₗ (R n : E (n + 1) →ₗ[𝕜] E n)) :
    Filter.EventuallyConst (fun n ↦ (T n).separatingSpace) Filter.atTop := by
  set S : ℕ → Submodule 𝕜 F := fun n ↦ (T n).separatingSpace
  have hanti : Antitone S := antitone_separatingSpace hT
  -- The quotient map modulo `S (n + 1)` makes `T (n + 1)` continuous, giving `K n`, but it does
  -- not make `T n` continuous when `S (n + 1) ≠ S n`.
  let K : ∀ n, E (n + 1) →L[𝕜] F ⧸ S (n + 1) := fun n ↦
    ⟨(S (n + 1)).mkQ ∘ₗ T (n + 1), (T (n + 1)).continuous_mkQ_comp⟩
  have hK : ∀ n w, K n w = (S (n + 1)).mkQ (T (n + 1) w) := fun _ _ ↦ rfl
  -- The `j`-th summand is chosen of norm at most `ε j`, small against the composites used below.
  obtain ⟨ε, hε, hεb, hεK⟩ :=
    exists_pos_weights_toBase_descend R (fun m ↦ ‖K m‖ + 1) fun m ↦ by positivity
  -- At a strict step `n`, a small vector of `E n` has a large image modulo `S (n + 1)`.
  have hchoice : ∀ n (s : E 0), ∃ v : E n, ‖v‖ ≤ ε n ∧ (S (n + 1) ≠ S n →
      n + 2 + ‖(S (n + 1)).mkQ (T 0 s)‖ ≤ ‖(S (n + 1)).mkQ (T n v)‖) := by
    intro n s
    by_cases hn : S (n + 1) = S n
    · exact ⟨0, by simpa using (hε n).le, fun h ↦ (h hn).elim⟩
    have := (T (n + 1)).isClosed_separatingSpace
    obtain ⟨v, hv, hv'⟩ := (T n).exists_norm_le_le_norm_mkQ_apply
      (fun h ↦ hn (le_antisymm (hanti n.le_succ) h)) (hε n) (n + 2 + ‖(S (n + 1)).mkQ (T 0 s)‖)
    exact ⟨v, hv, fun _ ↦ hv'⟩
  -- Choose the summands recursively, each one large compared with the partial sum before it.
  choose v hv hv' using hchoice
  let s : ℕ → E 0 := fun n ↦
    Nat.rec (motive := fun _ ↦ E 0) 0 (fun j acc ↦ acc + toBase R j (v j acc)) n
  let x : ∀ n, E n := fun n ↦ v n (s n)
  -- The defining recursion of the partial sums `s`.
  have hs_succ : ∀ n, s (n + 1) = s n + toBase R n (x n) := fun _ ↦ rfl
  have hs : ∀ n, s n = ∑ j ∈ range n, toBase R j (x j) := by
    intro n
    induction n with
    | zero => simp [s]
    | succ n ih => rw [hs_succ, sum_range_succ, ih]
  have hx : ∀ j, ‖x j‖ ≤ ε j := fun j ↦ hv j (s j)
  have hfx : ∀ j, ‖toBase R j (x j)‖ ≤ (1 / 2) ^ j := fun j ↦
    ((toBase R j).le_opNorm _).trans <|
      (mul_le_mul_of_nonneg_left (hx j) (norm_nonneg _)).trans (hεb j)
  have hfs : Summable fun j ↦ toBase R j (x j) :=
    Summable.of_norm_bounded summable_geometric_two hfx
  set y := ∑' j, toBase R j (x j) with hy
  -- Gliding hump: at every strict step `n`, the norm of `T 0 y` is at least `n + 1`.
  have hkey : ∀ n, S (n + 1) ≠ S n → (n : ℝ) + 1 ≤ ‖T 0 y‖ := fun n hn ↦ by
    have h := norm_mkQ_apply_le hT n (K n) (hK n) hx (hεK n) hfs
    rw [← hs, ← hy] at h
    linarith [hv' n (s n) hn]
  -- Strict steps are unbounded unless the sequence stabilizes, contradicting `hkey`.
  rw [Filter.eventuallyConst_atTop_nat]
  by_contra! hne
  obtain ⟨m, hm, hm'⟩ := hne ⌈‖T 0 y‖⌉₊
  have h : (⌈‖T 0 y‖⌉₊ : ℝ) ≤ m := by exact_mod_cast hm
  linarith [hkey m hm', Nat.le_ceil ‖T 0 y‖]

end Banach

end TauCeti

/-! ### Stability of the images of the separating space -/

namespace LinearMap

section Intertwining

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Stability of the images of the separating space.** Let `T : E → F` be a linear map
between Banach spaces, and let `R n` on `E` and `S n` on `F` be continuous linear maps such that
each `S n ∘ T - T ∘ R n` is continuous. If `V n = S 0 ∘ ⋯ ∘ S (n - 1)`, then the closures of the
images of the separating space of `T` under `V n` are eventually constant. -/
theorem eventuallyConst_topologicalClosure_map_separatingSpace (T : E →ₗ[𝕜] F)
    (R : ℕ → E →L[𝕜] E) (S : ℕ → F →L[𝕜] F)
    (hRS : ∀ n, Continuous ((S n : F →ₗ[𝕜] F) ∘ₗ T - T ∘ₗ (R n : E →ₗ[𝕜] E)))
    {V : ℕ → F →L[𝕜] F} (hV0 : V 0 = ContinuousLinearMap.id 𝕜 F)
    (hV : ∀ n, V (n + 1) = (V n).comp (S n)) :
    Filter.EventuallyConst
      (fun n ↦ (T.separatingSpace.map (V n : F →ₗ[𝕜] F)).topologicalClosure) Filter.atTop := by
  obtain ⟨U, hU0, hU⟩ : ∃ U : ℕ → E →L[𝕜] E,
      U 0 = ContinuousLinearMap.id 𝕜 E ∧ ∀ n, U (n + 1) = (U n).comp (R n) :=
    ⟨fun n ↦ Nat.rec (ContinuousLinearMap.id 𝕜 E) (fun n Un ↦ Un.comp (R n)) n, rfl, fun _ ↦ rfl⟩
  have hsep : (fun n ↦ (T.separatingSpace.map (V n : F →ₗ[𝕜] F)).topologicalClosure) =
      fun n ↦ (T ∘ₗ (U n : E →ₗ[𝕜] E)).separatingSpace := funext fun n ↦ by
    rw [← separatingSpace_comp, separatingSpace_eq_of_continuous_sub
      (continuous_comp_sub_comp_of_continuous_sub T R S hRS hU0 hU hV0 hV n)]
  rw [hsep]
  exact TauCeti.eventuallyConst_separatingSpace (E := fun _ ↦ E) (R := R) fun n ↦ by
    rw [hU, ContinuousLinearMap.toLinearMap_comp, LinearMap.comp_assoc]

end Intertwining

end LinearMap
