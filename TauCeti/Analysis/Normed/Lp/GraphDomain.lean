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
elementary metric properties.

## Main declarations

* `TauCeti.normalHalfSpace`: the region above a constant normal coordinate.
* `TauCeti.normalEpigraph`: the region above the graph of a continuous function.
* `TauCeti.normalGraphEmbedding`: the normal graph parametrization `y ↦ (φ y, y)`.
* `TauCeti.frontier_setOf_lt_fst`: the frontier of a continuous epigraph is its graph.
* `LipschitzWith.normalGraphEmbedding`: a `K`-Lipschitz function has a `(K + 1)`-Lipschitz
  graph parametrization.
* `ContinuousLinearMap.normalGraphL`: the continuous linear graph map `x ↦ (A x, x)`.
* `ContinuousLinearMap.injective_normalGraphL`: the linear graph map is injective.
* `ContinuousLinearMap.range_normalGraphL`: its range is the linear graph of `A`.
-/

public section

namespace TauCeti

open Set TopologicalSpace Filter Topology
open scoped NNReal

variable {E : Type*}

section

variable [TopologicalSpace E]

/-- The open half-space to the right of the normal coordinate `a` in the ℓ² product `ℝ × E`. -/
def normalHalfSpace (a : ℝ) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | a < (WithLp.ofLp x).1},
    isOpen_lt continuous_const (WithLp.prod_continuous_ofLp 2 ℝ E).fst⟩

/-- Membership in the normal-coordinate half-space is a strict inequality. -/
@[simp]
theorem mem_normalHalfSpace (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalHalfSpace (E := E) a ↔ a < (WithLp.ofLp x).1 := Iff.rfl

/-- As a set, the right normal half-space is `{x | a < x.fst}`. -/
theorem coe_normalHalfSpace (a : ℝ) :
    (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
      {x | a < (WithLp.ofLp x).1} :=
  Set.ext (mem_normalHalfSpace a)

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

/-- The region above the graph of `0` is the half-space `{0 < t}`. -/
@[simp]
theorem normalEpigraph_zero : normalEpigraph (0 : C(E, ℝ)) = normalHalfSpace 0 := by
  ext x
  simp

end

/-- The normal graph parametrization `y ↦ (φ y, y)` in `WithLp 2 (ℝ × E)`. -/
def normalGraphEmbedding (φ : E → ℝ) (y : E) : WithLp 2 (ℝ × E) :=
  WithLp.toLp 2 (φ y, y)

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
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro hx
    refine ⟨x.snd, (WithLp.ext_iff 2).2 ?_⟩
    exact Prod.ext hx.symm rfl

/-- The second projection is a `1`-Lipschitz inverse to the graph parametrization on its range. -/
theorem antilipschitzWith_normalGraphEmbedding [PseudoMetricSpace E] (φ : E → ℝ) :
    AntilipschitzWith 1 (normalGraphEmbedding φ) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_
  simpa only [NNReal.coe_one, one_mul, normalGraphEmbedding_snd] using
    WithLp.dist_snd_le (normalGraphEmbedding φ x) (normalGraphEmbedding φ y)

/-- A `K`-Lipschitz function has a `(K + 1)`-Lipschitz normal graph parametrization. -/
theorem _root_.LipschitzWith.normalGraphEmbedding [SeminormedAddCommGroup E] {K : ℝ≥0} {φ : E → ℝ}
    (hφ : LipschitzWith K φ) :
    LipschitzWith (K + 1) (TauCeti.normalGraphEmbedding φ) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  calc
    dist (TauCeti.normalGraphEmbedding φ x) (TauCeti.normalGraphEmbedding φ y) ≤
        dist (TauCeti.normalGraphEmbedding φ x) (WithLp.toLp 2 (φ y, x)) +
          dist (WithLp.toLp 2 (φ y, x)) (TauCeti.normalGraphEmbedding φ y) :=
      dist_triangle _ _ _
    _ = dist (φ x) (φ y) + dist x y := by
      simp [TauCeti.normalGraphEmbedding, WithLp.prod_dist_eq_of_L2]
    _ ≤ K * dist x y + dist x y := add_le_add (hφ.dist_le_mul x y) le_rfl
    _ = (K + 1) * dist x y := by ring

section

variable [TopologicalSpace E]

/-- A continuous normal graph is closed in the product `ℝ × E`, represented by `WithLp 2`. -/
theorem _root_.Continuous.isClosed_range_normalGraphEmbedding {φ : E → ℝ} (hφ : Continuous φ) :
    IsClosed (range (TauCeti.normalGraphEmbedding φ)) := by
  rw [range_normalGraphEmbedding]
  exact isClosed_eq (WithLp.prod_continuous_ofLp 2 ℝ E).fst
    (hφ.comp (WithLp.prod_continuous_ofLp 2 ℝ E).snd)

/-- The frontier of the region strictly above the graph of a continuous function is the
graph. -/
theorem frontier_setOf_lt_fst {γ : E → ℝ} (hγ : Continuous γ) :
    frontier {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} = {x | x.fst = γ x.snd} := by
  have hopen : IsOpen {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  refine Subset.antisymm
    (fun x hx => (frontier_lt_subset_eq (by fun_prop) (by fun_prop) hx).symm) fun x hx => ?_
  rw [mem_ofPred_eq] at hx
  rw [hopen.frontier_eq, Set.mem_sdiff, mem_ofPred_eq]
  refine ⟨?_, fun h => h.ne' hx⟩
  -- A graph point is the limit of the points `(x.fst + t, x.snd)` above it, as `t → 0⁺`.
  have hlim : Tendsto (fun t : ℝ => WithLp.toLp 2 (x.fst + t, x.snd)) (𝓝[>] 0) (𝓝 x) := by
    have hcont : Continuous fun t : ℝ => WithLp.toLp 2 (x.fst + t, x.snd) := by fun_prop
    have h0 := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [add_zero, ← WithLp.ofLp_fst, ← WithLp.ofLp_snd, Prod.mk.eta, WithLp.toLp_ofLp] at h0
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, ← hx]
  linarith

end

section Linear

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous linear graph map `x ↦ (A x, x)` associated to `A : E →L[ℝ] ℝ`. -/
def _root_.ContinuousLinearMap.normalGraphL (A : E →L[ℝ] ℝ) :
    E →L[ℝ] WithLp 2 (ℝ × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap ∘L
    A.prod (ContinuousLinearMap.id ℝ E)

/-- The continuous linear graph map is the normal graph parametrization of `A`. -/
@[simp]
theorem _root_.ContinuousLinearMap.normalGraphL_apply (A : E →L[ℝ] ℝ) (x : E) :
    A.normalGraphL x = normalGraphEmbedding A x :=
  (WithLp.ext_iff 2).2 <| Prod.ext (normalGraphEmbedding_fst A x).symm
    (normalGraphEmbedding_snd A x).symm

/-- As a function, the continuous linear graph map is the normal graph parametrization of `A`. -/
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

end Linear

end TauCeti

end
