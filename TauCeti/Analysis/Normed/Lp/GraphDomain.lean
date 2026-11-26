/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Half-spaces, epigraphs, and graphs in an ℓ² product

This file defines the open normal half-space and the open region above the graph of a continuous
function in `WithLp 2 (ℝ × E)`. These are the model domains used by graph flattening and Sobolev
trace theory. It also defines the normal graph parametrization `y ↦ (φ y, y)` and records its
elementary metric properties, and the graph map `v ↦ (v, A v)` of a continuous linear map
`A : E →L[ℝ] F` into `WithLp 2 (E × F)`.

## Main declarations

* `TauCeti.normalHalfSpace`: the region above a constant normal coordinate.
* `TauCeti.preimage_withLpMap_prodMap_id_normalHalfSpace`: maps keeping the normal coordinate
  preserve each half-space.
* `TauCeti.normalEpigraph`: the region above the graph of a continuous function.
* `TauCeti.normalGraphEmbedding`: the normal graph parametrization `y ↦ (φ y, y)`.
* `TauCeti.frontier_setOf_lt_fst`: the frontier of a continuous epigraph is its graph.
* `LipschitzWith.normalGraphEmbedding`: a `K`-Lipschitz function has a `(K + 1)`-Lipschitz
  graph parametrization.
* `ContinuousLinearMap.normalGraphL`: the continuous linear graph map `x ↦ (A x, x)`.
* `ContinuousLinearMap.injective_normalGraphL`: the linear graph map is injective.
* `ContinuousLinearMap.range_normalGraphL`: its range is the linear graph of `A`.
* `LipschitzOnWith.graph`, `LipschitzWith.graph`: a map `K`-Lipschitz on a set, or on the whole
  space, has a graph parametrization `x ↦ (x, f x)` that is `(K + 1)`-Lipschitz there.
* `ContinuousLinearMap.graphL`: the continuous linear graph map `v ↦ (v, A v)` of
  `A : E →L[ℝ] F`, in every codimension.
* `ContinuousLinearMap.injective_graphL`, `ContinuousLinearMap.range_graphL`: it is injective,
  with range the graph `LinearMap.graph A`.
* `ContinuousLinearMap.mem_range_graphL`: `z` is in that range exactly when `z.snd = A z.fst`.
-/

public section

namespace TauCeti

open Set TopologicalSpace
open scoped NNReal

variable {E : Type*}

section

variable [TopologicalSpace E]

/-- The open half-space to the right of the normal coordinate `a` in the ℓ² product `ℝ × E`. -/
def normalHalfSpace (a : ℝ) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | a < x.fst}, isOpen_lt continuous_const (by fun_prop)⟩

/-- Membership in the normal-coordinate half-space is a strict inequality. -/
@[simp]
theorem mem_normalHalfSpace (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalHalfSpace (E := E) a ↔ a < x.fst := Iff.rfl

/-- As a set, the right normal half-space is `{x | a < x.fst}`. -/
theorem coe_normalHalfSpace (a : ℝ) :
    (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) = {x | a < x.fst} :=
  Set.ext (mem_normalHalfSpace a)

/-- A map of `ℝ × E` that keeps the normal coordinate preserves each half-space `{a < t}`. -/
@[simp]
theorem preimage_withLpMap_prodMap_id_normalHalfSpace (ψ : E → E) (a : ℝ) :
    WithLp.map 2 (Prod.map (id : ℝ → ℝ) ψ) ⁻¹'
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) := by
  ext x
  simp

/-- The open region `{x | φ x.snd < x.fst}` above the graph of a continuous function
`φ : E → ℝ` in the ℓ² product `ℝ × E`. -/
def normalEpigraph (φ : C(E, ℝ)) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | φ x.snd < x.fst}, isOpen_lt (by fun_prop) (by fun_prop)⟩

/-- Membership in the region above the graph is a strict inequality. -/
@[simp]
theorem mem_normalEpigraph (φ : C(E, ℝ)) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalEpigraph φ ↔ φ x.snd < x.fst :=
  Iff.rfl

/-- As a set, the region above the graph is `{x | φ x.snd < x.fst}`. -/
theorem coe_normalEpigraph (φ : C(E, ℝ)) :
    (normalEpigraph φ : Set (WithLp 2 (ℝ × E))) = {x | φ x.snd < x.fst} :=
  Set.ext (mem_normalEpigraph φ)

/-- The region above the graph of a constant function `a` is the half-space `{a < t}`. -/
@[simp]
theorem normalEpigraph_const (a : ℝ) : normalEpigraph (.const E a) = normalHalfSpace a := by
  ext x
  simp

/-- The region above the graph of `0` is the half-space `{0 < t}`. -/
@[simp]
theorem normalEpigraph_zero : normalEpigraph (0 : C(E, ℝ)) = normalHalfSpace 0 := by
  rw [← ContinuousMap.const_zero, normalEpigraph_const]

end

/-- The normal graph parametrization `y ↦ (φ y, y)` in `WithLp 2 (ℝ × E)`. -/
def normalGraphEmbedding (φ : E → ℝ) (y : E) : WithLp 2 (ℝ × E) :=
  WithLp.toLp 2 (φ y, y)

/-- The defining equation of the normal graph parametrization. -/
theorem normalGraphEmbedding_apply (φ : E → ℝ) (y : E) :
    normalGraphEmbedding φ y = WithLp.toLp 2 (φ y, y) :=
  (rfl)

/-- The underlying pair of the normal graph parametrization is `(φ y, y)`. -/
@[simp]
theorem ofLp_normalGraphEmbedding (φ : E → ℝ) (y : E) :
    WithLp.ofLp (normalGraphEmbedding φ y) = (φ y, y) :=
  (rfl)

/-- The normal coordinate of the graph parametrization is the graphing function. -/
@[simp]
theorem normalGraphEmbedding_fst (φ : E → ℝ) (y : E) :
    (normalGraphEmbedding φ y).fst = φ y :=
  WithLp.toLp_fst _

/-- The tangential coordinate of the graph parametrization is its argument. -/
@[simp]
theorem normalGraphEmbedding_snd (φ : E → ℝ) (y : E) :
    (normalGraphEmbedding φ y).snd = y :=
  WithLp.toLp_snd _

/-- The normal graph parametrization is injective. -/
theorem injective_normalGraphEmbedding (φ : E → ℝ) :
    Function.Injective (normalGraphEmbedding φ) := fun _ _ h ↦ by
  simpa using congrArg WithLp.snd h

/-- The range of the normal graph parametrization is the graph equation `t = φ y`. -/
theorem range_normalGraphEmbedding (φ : E → ℝ) :
    range (normalGraphEmbedding φ) = {x | x.fst = φ x.snd} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨x.snd, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simp
  · simp [WithLp.ext_iff, Prod.ext_iff, hx.symm]

/-- The normal graph parametrization is `1`-antilipschitz. -/
theorem antilipschitzWith_normalGraphEmbedding [PseudoEMetricSpace E] (φ : E → ℝ) :
    AntilipschitzWith 1 (normalGraphEmbedding φ) := fun x y ↦ by
  simpa only [ENNReal.coe_one, one_mul, normalGraphEmbedding_snd] using
    WithLp.edist_snd_le (normalGraphEmbedding φ x) (normalGraphEmbedding φ y)

/-- A map that is `K`-Lipschitz on a set `s` has a graph parametrization `x ↦ (x, f x)` into the
`L²` product that is `(K + 1)`-Lipschitz on `s`. -/
theorem _root_.LipschitzOnWith.graph {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K : ℝ≥0} {f : α → β} {s : Set α} (hf : LipschitzOnWith K f s) :
    LipschitzOnWith (K + 1) (fun x ↦ WithLp.toLp 2 (x, f x)) s := fun x hx y hy ↦ by
  set a := edist (f x) (f y)
  set b := edist x y
  calc
    edist (WithLp.toLp 2 (x, f x)) (WithLp.toLp 2 (y, f y)) = (b ^ 2 + a ^ 2) ^ (1 / 2 : ℝ) := by
      simp [WithLp.prod_edist_eq_add, a, b]
    -- `b ^ 2 + a ^ 2 ≤ a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2`.
    _ ≤ ((a + b) ^ 2) ^ (1 / 2 : ℝ) := by
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [add_comm, add_sq]
      exact add_le_add le_self_add le_rfl
    _ = a + b := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ K * b + b := add_le_add (hf hx hy) le_rfl
    _ = (K + 1) * b := by rw [add_mul, one_mul]

/-- A `K`-Lipschitz map has a `(K + 1)`-Lipschitz graph parametrization `x ↦ (x, f x)` into the
`L²` product. -/
theorem _root_.LipschitzWith.graph {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K : ℝ≥0} {f : α → β} (hf : LipschitzWith K f) :
    LipschitzWith (K + 1) (fun x ↦ WithLp.toLp 2 (x, f x)) :=
  lipschitzOnWith_univ.1 (lipschitzOnWith_univ.2 hf).graph

/-- A `K`-Lipschitz function has a `(K + 1)`-Lipschitz normal graph parametrization. -/
theorem _root_.LipschitzWith.normalGraphEmbedding [PseudoEMetricSpace E] {K : ℝ≥0}
    {φ : E → ℝ} (hφ : LipschitzWith K φ) :
    LipschitzWith (K + 1) (TauCeti.normalGraphEmbedding φ) := by
  -- Swapping the coordinates of the `L²` product turns `x ↦ (x, φ x)` into `y ↦ (φ y, y)`.
  have h := (IsometryEquiv.withLpProdComm 2 E ℝ).isometry.lipschitzWith.comp hφ.graph
  simpa only [Function.comp_def, IsometryEquiv.withLpProdComm_apply, WithLp.toLp_fst,
    WithLp.toLp_snd, one_mul, ← normalGraphEmbedding_apply] using h

section

variable [TopologicalSpace E]

/-- The normal graph parametrization of a continuous function is continuous. -/
@[fun_prop]
theorem _root_.Continuous.normalGraphEmbedding {φ : E → ℝ} (hφ : Continuous φ) :
    Continuous (TauCeti.normalGraphEmbedding φ) :=
  (WithLp.prod_continuous_toLp 2 ℝ E).comp (hφ.prodMk continuous_id)

/-- A continuous normal graph is closed in the product `ℝ × E`, represented by `WithLp 2`. -/
theorem _root_.Continuous.isClosed_range_normalGraphEmbedding {φ : E → ℝ} (hφ : Continuous φ) :
    IsClosed (range (TauCeti.normalGraphEmbedding φ)) := by
  rw [range_normalGraphEmbedding]
  exact isClosed_eq (by fun_prop) (by fun_prop)

/-- The frontier of the region strictly above the graph of a continuous function is the
graph. -/
theorem frontier_setOf_lt_fst {γ : E → ℝ} (hγ : Continuous γ) :
    frontier {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} = {x | x.fst = γ x.snd} := by
  -- `x ↦ x.fst - γ x.snd` is an open map, with the continuous section `s ↦ (s + γ x.snd, x.snd)`
  -- through each point `x`, so it pulls the frontier `{0}` of `Ioi 0` back to the frontier.
  have hf : IsOpenMap fun x : WithLp 2 (ℝ × E) ↦ x.fst - γ x.snd :=
    .of_sections fun x ↦ ⟨fun s ↦ WithLp.toLp 2 (s + γ x.snd, x.snd), by fun_prop,
      by simp [WithLp.ext_iff, Prod.ext_iff], fun s ↦ by simp⟩
  simpa [frontier_Ioi, preimage, sub_pos, sub_eq_zero] using
    (hf.preimage_frontier_eq_frontier_preimage (by fun_prop) (Ioi 0)).symm

end

section Linear

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- The continuous linear graph map `x ↦ (A x, x)` associated to `A : E →L[ℝ] ℝ`. -/
def _root_.ContinuousLinearMap.normalGraphL (A : E →L[ℝ] ℝ) :
    E →L[ℝ] WithLp 2 (ℝ × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap ∘L
    A.prod (ContinuousLinearMap.id ℝ E)

/-- The continuous linear graph map is the normal graph parametrization of `A`. -/
theorem _root_.ContinuousLinearMap.normalGraphL_apply (A : E →L[ℝ] ℝ) (x : E) :
    A.normalGraphL x = normalGraphEmbedding A x := by
  simp [ContinuousLinearMap.normalGraphL, normalGraphEmbedding_apply]

/-- As a function, the continuous linear graph map is the normal graph parametrization of `A`. -/
@[simp]
theorem _root_.ContinuousLinearMap.coe_normalGraphL (A : E →L[ℝ] ℝ) :
    ⇑A.normalGraphL = normalGraphEmbedding A :=
  funext A.normalGraphL_apply

/-- A continuous linear normal graph map is injective, since its tangential coordinate is its
argument. -/
theorem _root_.ContinuousLinearMap.injective_normalGraphL (A : E →L[ℝ] ℝ) :
    Function.Injective A.normalGraphL :=
  A.coe_normalGraphL ▸ injective_normalGraphEmbedding A

/-- The range of the normal graph linear map is the graph of the functional. -/
theorem _root_.ContinuousLinearMap.range_normalGraphL (A : E →L[ℝ] ℝ) :
    (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E))) =
      {z | z.fst = A z.snd} := by
  rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, A.coe_normalGraphL,
    range_normalGraphEmbedding]

variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The continuous linear graph map `v ↦ (v, A v)` of `A : E →L[ℝ] F`, into the Euclidean
product `WithLp 2 (E × F)`. -/
def _root_.ContinuousLinearMap.graphL (A : E →L[ℝ] F) : E →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.id ℝ E).prod A

@[simp]
theorem _root_.ContinuousLinearMap.graphL_apply (A : E →L[ℝ] F) (v : E) :
    A.graphL v = WithLp.toLp 2 (v, A v) :=
  (rfl)

/-- The continuous linear graph map is injective, since its first coordinate is its argument. -/
theorem _root_.ContinuousLinearMap.injective_graphL (A : E →L[ℝ] F) :
    Function.Injective A.graphL := fun _ _ h ↦ by
  simpa using congrArg WithLp.fst h

/-- The range of the continuous linear graph map is the graph of `A`, transported to the
Euclidean product. -/
theorem _root_.ContinuousLinearMap.range_graphL (A : E →L[ℝ] F) :
    LinearMap.range A.graphL.toLinearMap =
      (LinearMap.graph (A : E →ₗ[ℝ] F)).map (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap := by
  ext z
  simp [LinearMap.mem_graph_iff, WithLp.ext_iff, Prod.ext_iff, eq_comm]

/-- A point of the Euclidean product lies in the range of the continuous linear graph map exactly
when its second coordinate is `A` of its first. -/
theorem _root_.ContinuousLinearMap.mem_range_graphL (A : E →L[ℝ] F) {z : WithLp 2 (E × F)} :
    z ∈ LinearMap.range A.graphL.toLinearMap ↔ z.snd = A z.fst := by
  simp [A.range_graphL, LinearMap.mem_graph_iff]

end Linear

end TauCeti

end
