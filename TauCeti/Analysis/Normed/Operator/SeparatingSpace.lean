/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import TauCeti.Analysis.Normed.Operator.GlidingHump
import TauCeti.Analysis.SpecificLimits.GeometricWeights

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

The stability lemma says that along a tower of continuous linear maps between Banach spaces the
decreasing sequence of separating spaces of the composites with `T` is eventually constant. Its
gliding-hump proof sums a series of ever smaller vectors chosen at the places where the
sequence drops. Applied to continuous linear maps that intertwine `T` up to continuous errors,
it shows that the closures of the images of the separating space under the successive
products stabilize; these are the stabilization statements behind separating ideals in
automatic continuity theory.

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
* `LinearMap.map_separatingSpace_le_self`: a continuous linear map intertwining `T` with a
  continuous linear map up to a continuous error preserves the separating space of `T`.
* `LinearMap.exists_separatingSpace_comp_eq`: the stability lemma.
* `LinearMap.exists_topologicalClosure_map_separatingSpace_eq`: stabilization of the closed
  images of the separating space under successive intertwining products.

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
separating space of `T` into that of `T'`. -/
theorem map_separatingSpace_le_of_continuous_sub (T' : D →ₗ[R] G) (U : F →L[R] G)
    (V : E →L[R] D) (h : Continuous ((U : F →ₗ[R] G) ∘ₗ T - T' ∘ₗ (V : E →ₗ[R] D))) :
    T.separatingSpace.map (U : F →ₗ[R] G) ≤ T'.separatingSpace :=
  (T.map_separatingSpace_le U).trans
    ((separatingSpace_eq_of_continuous_sub h).trans_le (T'.separatingSpace_comp_le V))

/-- If `U ∘ T - T ∘ V` is continuous for continuous linear maps `U` and `V`, then `U` maps the
separating space of `T` into itself. Applied to the left or right actions of an algebra on `E`
and `F`, this says that the separating space of a map whose commutators with the actions are
continuous is a submodule. -/
theorem map_separatingSpace_le_self (U : F →L[R] F) (V : E →L[R] E)
    (h : Continuous ((U : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (V : E →ₗ[R] E))) :
    T.separatingSpace.map (U : F →ₗ[R] F) ≤ T.separatingSpace :=
  T.map_separatingSpace_le_of_continuous_sub T U V h

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

section Tower

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul R F]

/-- Along a tower of continuous linear maps `P n : X (n + 1) → X n` and compatible maps
`U n : X n → E` with `U (n + 1) = U n ∘ P n`, the separating spaces of `T ∘ U n` decrease. -/
theorem antitone_separatingSpace_comp {X : ℕ → Type*} [∀ n, AddCommGroup (X n)]
    [∀ n, Module R (X n)] [∀ n, TopologicalSpace (X n)] [∀ n, IsTopologicalAddGroup (X n)]
    [∀ n, ContinuousConstSMul R (X n)] (T : E →ₗ[R] F) (P : ∀ n, X (n + 1) →L[R] X n)
    {U : ∀ n, X n →L[R] E} (hU : ∀ n, U (n + 1) = (U n).comp (P n)) :
    Antitone fun n ↦ (T ∘ₗ (U n : X n →ₗ[R] E)).separatingSpace := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [hU, ContinuousLinearMap.toLinearMap_comp, ← LinearMap.comp_assoc]
  exact separatingSpace_comp_le _ (P n)

end Tower

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

section Stability

variable {𝕜 G F : Type*} [NontriviallyNormedField 𝕜] {E : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (T : G →ₗ[𝕜] F) (R : ∀ n, E (n + 1) →L[𝕜] E n) {U : ∀ n, E n →L[𝕜] G}

variable [∀ n, CompleteSpace (E n)] [CompleteSpace F]

/-- **The stability lemma** for separating spaces. Let `T : G → F` be a linear map into a
Banach space, let `R n : E (n + 1) → E n` be continuous linear maps between Banach spaces, and
let `U n : E n → G` be continuous linear maps with `U (n + 1) = U n ∘ R n`, so that
`U n = U 0 ∘ R 0 ∘ ⋯ ∘ R (n - 1)`. Then the decreasing sequence of separating spaces of
`T ∘ U n` is eventually constant. -/
theorem exists_separatingSpace_comp_eq (hU : ∀ n, U (n + 1) = (U n).comp (R n)) :
    ∃ N, ∀ n ≥ N, (T ∘ₗ (U n : E n →ₗ[𝕜] G)).separatingSpace =
      (T ∘ₗ (U N : E N →ₗ[𝕜] G)).separatingSpace := by
  -- The gliding hump: if the sequence dropped at infinitely many `n`, we could choose small
  -- `y n : E n` at each drop with `T (U n (y n))` large modulo the next separating space, sum
  -- the series `x = ∑ U n (y n)`, and obtain `n ≤ ‖T x‖` at every drop `n`.
  set S : ℕ → Submodule 𝕜 F := fun n ↦ (T ∘ₗ (U n : E n →ₗ[𝕜] G)).separatingSpace
  have hSc : ∀ n, IsClosed (S n : Set F) := fun n ↦ isClosed_separatingSpace _
  -- `T ∘ U m` becomes continuous modulo `S m`, with operator norm `c m`.
  let C : ∀ m, E m →L[𝕜] F ⧸ S m := fun m ↦
    ⟨(S m).mkQ ∘ₗ T ∘ₗ (U m : E m →ₗ[𝕜] G), (T ∘ₗ (U m : E m →ₗ[𝕜] G)).continuous_mkQ_comp⟩
  -- Evaluating `C` unfolds its definition.
  have hC : ∀ m v, C m v = (S m).mkQ (T (U m v)) := fun _ _ ↦ rfl
  -- `T ∘ U n` modulo the next separating space `S (n + 1)` is discontinuous whenever the
  -- sequence drops at `n`.
  let V : ∀ n, E n →ₗ[𝕜] F ⧸ S (n + 1) := fun n ↦
    ((S (n + 1)).mkQL : F →ₗ[𝕜] F ⧸ S (n + 1)) ∘ₗ T ∘ₗ (U n : E n →ₗ[𝕜] G)
  -- Evaluating `V` unfolds its definition.
  have hVv : ∀ n v, V n v = (S (n + 1)).mkQ (T (U n v)) := fun _ _ ↦ rfl
  have hV : ∀ n, S (n + 1) ≠ S n → ¬ Continuous (V n) := by
    intro n hne hcont
    have := hSc (n + 1)
    have hle := ((T ∘ₗ (U n : E n →ₗ[𝕜] G)).continuous_comp_iff_separatingSpace_le_ker
      (S (n + 1)).mkQL).1 hcont
    rw [Submodule.toLinearMap_mkQL, Submodule.ker_mkQ] at hle
    exact hne (le_antisymm (antitone_separatingSpace_comp T R hU n.le_succ) hle)
  -- The admissible sizes `η n` of the humps.
  set c : ℕ → ℝ := fun m ↦ ‖C m‖
  have hc : ∀ m, 0 ≤ c m := fun m ↦ norm_nonneg _
  obtain ⟨η, hηpos, hη⟩ := TauCeti.exists_pos_mul_le_half_pow
    (fun m k ↦ (1 + c m) * ‖TauCeti.towerComp R m k‖) fun m k ↦
      mul_nonneg (by linarith [hc m]) (norm_nonneg _)
  -- At each drop, choose a hump of size at most `η n` whose image is large.
  have hpick : ∀ n (s : G), ∃ y : E n, ‖y‖ ≤ η n ∧
      (S (n + 1) ≠ S n → ‖T s‖ + n + 2 ≤ ‖V n y‖) := by
    intro n s
    by_cases hne : S (n + 1) = S n
    · exact ⟨0, by simpa using (hηpos n).le, fun h ↦ (h hne).elim⟩
    · by_contra! hcon
      have := hSc (n + 1)
      obtain ⟨K, hK⟩ := (V n).bound_of_ball_bound (hηpos n) (‖T s‖ + n + 2)
        fun z hz ↦ (hcon z (mem_ball_zero_iff.1 hz).le).2.le
      exact hV n hne (AddMonoidHomClass.continuous_of_bound (V n) K hK)
  choose pick hpick_le hpick_big using hpick
  -- The partial sums `s n = ∑ k < n, U k (y k)` of the gliding hump series.
  obtain ⟨s, hs0, hs_succ⟩ : ∃ s : ℕ → G, s 0 = 0 ∧ ∀ n, s (n + 1) = s n + U n (pick n (s n)) :=
    ⟨fun n ↦ Nat.rec 0 (fun n sn ↦ sn + U n (pick n sn)) n, rfl, fun _ ↦ rfl⟩
  set y : ∀ n, E n := fun n ↦ pick n (s n)
  have hs : ∀ n, s n = ∑ k ∈ Finset.range n, U k (y k) := by
    intro n
    induction n with
    | zero => rw [hs0, Finset.sum_range_zero]
    | succ n ih => rw [hs_succ, Finset.sum_range_succ, ← ih]
  have hy : ∀ m k, ‖TauCeti.towerComp R m k (y (m + k))‖ ≤ 1 / (1 + c m) * (1 / 2) ^ k := by
    intro m k
    refine ((TauCeti.towerComp R m k).le_opNorm _).trans ?_
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith [hc m])]
    calc ‖TauCeti.towerComp R m k‖ * ‖y (m + k)‖ * (1 + c m)
        ≤ ‖TauCeti.towerComp R m k‖ * η (m + k) * (1 + c m) := by
          gcongr
          exact hpick_le _ _
      _ = (1 + c m) * ‖TauCeti.towerComp R m k‖ * η (m + k) := by ring
      _ ≤ (1 / 2) ^ k := hη m k
  obtain ⟨x, hx⟩ := TauCeti.exists_norm_le_and_apply_eq_sub_sum R hU y _ hy
  -- The sequence cannot drop at any `n > ‖T x‖`.
  have hstab : ∀ n, ⌊‖T x‖⌋₊ + 1 ≤ n → S (n + 1) = S n := by
    intro n hn
    by_contra hne
    obtain ⟨z, hz, hUz⟩ := hx (n + 1)
    have hx' : x = s n + U n (y n) + U (n + 1) z := by
      rw [hUz, ← hs, hs_succ, add_sub_cancel]
    have key : V n (y n) =
        (S (n + 1)).mkQ (T x) - (S (n + 1)).mkQ (T (s n)) - C (n + 1) z := by
      simp only [hVv, hC, hx', map_add]
      abel
    have hCz : ‖C (n + 1) z‖ ≤ 2 := by
      calc ‖C (n + 1) z‖ ≤ c (n + 1) * (2 * (1 / (1 + c (n + 1)))) :=
            (C (n + 1)).le_opNorm_of_le hz
        _ ≤ 2 := by
          rw [← mul_div_assoc, mul_one, mul_div_assoc', div_le_iff₀ (by linarith [hc (n + 1)])]
          nlinarith [norm_nonneg (C (n + 1))]
    have hVy : ‖V n (y n)‖ ≤ ‖T x‖ + ‖T (s n)‖ + 2 := by
      rw [key]
      refine (norm_sub_le _ _).trans ?_
      gcongr
      refine (norm_sub_le _ _).trans ?_
      gcongr <;> exact Submodule.Quotient.norm_mk_le _ _
    have hbig := hpick_big n (s n) hne
    have hn' : (n : ℝ) ≤ ‖T x‖ := by linarith
    have := Nat.le_floor hn'
    omega
  refine ⟨⌊‖T x‖⌋₊ + 1, fun n hn ↦ ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact (hstab n hn).trans ih

end Stability

section Intertwining

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Stability of the images of the separating space.** Let `T : E → F` be a linear map
between Banach spaces, and let `R n` on `E` and `S n` on `F` be continuous linear maps such that
each `S n ∘ T - T ∘ R n` is continuous. If `V n = S 0 ∘ ⋯ ∘ S (n - 1)`, then the closures of the
images of the separating space of `T` under `V n` are eventually constant. -/
theorem exists_topologicalClosure_map_separatingSpace_eq (T : E →ₗ[𝕜] F)
    (R : ℕ → E →L[𝕜] E) (S : ℕ → F →L[𝕜] F)
    (hRS : ∀ n, Continuous ((S n : F →ₗ[𝕜] F) ∘ₗ T - T ∘ₗ (R n : E →ₗ[𝕜] E)))
    {V : ℕ → F →L[𝕜] F} (hV0 : V 0 = ContinuousLinearMap.id 𝕜 F)
    (hV : ∀ n, V (n + 1) = (V n).comp (S n)) :
    ∃ N, ∀ n ≥ N, (T.separatingSpace.map (V n : F →ₗ[𝕜] F)).topologicalClosure =
      (T.separatingSpace.map (V N : F →ₗ[𝕜] F)).topologicalClosure := by
  obtain ⟨U, hU0, hU⟩ : ∃ U : ℕ → E →L[𝕜] E,
      U 0 = ContinuousLinearMap.id 𝕜 E ∧ ∀ n, U (n + 1) = (U n).comp (R n) :=
    ⟨fun n ↦ Nat.rec (ContinuousLinearMap.id 𝕜 E) (fun n Un ↦ Un.comp (R n)) n, rfl, fun _ ↦ rfl⟩
  have hcont : ∀ n, Continuous ((V n : F →ₗ[𝕜] F) ∘ₗ T - T ∘ₗ (U n : E →ₗ[𝕜] E)) := by
    intro n
    induction n with
    | zero =>
      have : (V 0 : F →ₗ[𝕜] F) ∘ₗ T - T ∘ₗ (U 0 : E →ₗ[𝕜] E) = 0 := by
        ext
        simp [hV0, hU0]
      rw [this]
      exact continuous_zero
    | succ n ih =>
      have : (V (n + 1) : F →ₗ[𝕜] F) ∘ₗ T - T ∘ₗ (U (n + 1) : E →ₗ[𝕜] E) =
          (V n : F →ₗ[𝕜] F) ∘ₗ ((S n : F →ₗ[𝕜] F) ∘ₗ T - T ∘ₗ (R n : E →ₗ[𝕜] E)) +
            ((V n : F →ₗ[𝕜] F) ∘ₗ T - T ∘ₗ (U n : E →ₗ[𝕜] E)) ∘ₗ (R n : E →ₗ[𝕜] E) := by
        ext
        simp [hV, hU]
      have h₁ : Continuous ((V n : F →ₗ[𝕜] F) ∘ₗ
          ((S n : F →ₗ[𝕜] F) ∘ₗ T - T ∘ₗ (R n : E →ₗ[𝕜] E))) :=
        (V n).continuous.comp (hRS n)
      have h₂ : Continuous (((V n : F →ₗ[𝕜] F) ∘ₗ T - T ∘ₗ (U n : E →ₗ[𝕜] E)) ∘ₗ
          (R n : E →ₗ[𝕜] E)) :=
        ih.comp (R n).continuous
      rw [this]
      exact h₁.add h₂
  have hsep : ∀ n, (T.separatingSpace.map (V n : F →ₗ[𝕜] F)).topologicalClosure =
      (T ∘ₗ (U n : E →ₗ[𝕜] E)).separatingSpace := fun n ↦ by
    rw [← separatingSpace_comp, separatingSpace_eq_of_continuous_sub (hcont n)]
  obtain ⟨N, hN⟩ := exists_separatingSpace_comp_eq (E := fun _ ↦ E) T R hU
  exact ⟨N, fun n hn ↦ by rw [hsep, hsep, hN n hn]⟩

end Intertwining

end LinearMap
