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

open Set TopologicalSpace
open scoped NNReal

variable {E : Type*}

section

variable [TopologicalSpace E]

/-- The open half-space to the right of the normal coordinate `a` in the ℓ² product `ℝ × E`. -/
def normalHalfSpace (a : ℝ) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | a < (WithLp.ofLp x).1}, isOpen_lt continuous_const (by fun_prop)⟩

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
  refine ⟨?_, fun hx ↦ ⟨x.snd, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simp
  · simp [WithLp.ext_iff, Prod.ext_iff, normalGraphEmbedding, hx.symm]

/-- The second projection is a `1`-Lipschitz inverse to the graph parametrization on its range. -/
theorem antilipschitzWith_normalGraphEmbedding [PseudoMetricSpace E] (φ : E → ℝ) :
    AntilipschitzWith 1 (normalGraphEmbedding φ) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_
  simpa only [NNReal.coe_one, one_mul, normalGraphEmbedding_snd] using
    WithLp.dist_snd_le (normalGraphEmbedding φ x) (normalGraphEmbedding φ y)

/-- A `K`-Lipschitz function has a `(K + 1)`-Lipschitz normal graph parametrization. -/
theorem _root_.LipschitzWith.normalGraphEmbedding [PseudoMetricSpace E] {K : ℝ≥0} {φ : E → ℝ}
    (hφ : LipschitzWith K φ) :
    LipschitzWith (K + 1) (TauCeti.normalGraphEmbedding φ) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hx := dist_nonneg (x := φ x) (y := φ y)
  have hy := dist_nonneg (x := x) (y := y)
  calc
    dist (TauCeti.normalGraphEmbedding φ x) (TauCeti.normalGraphEmbedding φ y) =
        √(dist (φ x) (φ y) ^ 2 + dist x y ^ 2) := by
      simp [WithLp.prod_dist_eq_add, Real.sqrt_eq_rpow]
    -- `a ^ 2 + b ^ 2 ≤ (a + b) ^ 2`, since `0 ≤ a * b`.
    _ ≤ dist (φ x) (φ y) + dist x y := Real.sqrt_le_iff.2 ⟨by positivity,
      by linarith [add_sq (dist (φ x) (φ y)) (dist x y), mul_nonneg hx hy]⟩
    _ ≤ K * dist x y + dist x y := add_le_add (hφ.dist_le_mul x y) le_rfl
    _ = (K + 1) * dist x y := by ring

section

variable [TopologicalSpace E]

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
