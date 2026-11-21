/-
Copyright (c) 2026 Lyu Yuwei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lyu Yuwei
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.Algebra.Module.LinearPMap

import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Orthogonal projection onto the graph of a closed operator

Projecting `(z, 0)` onto the closed graph of `T` in the Hilbert product gives
a weak equation on the domain of `T`, without assuming the domain is dense. For endomorphisms,
`LinearPMap.piLpGraph` and `LinearPMap.graphProjection` also realize the graph and its
orthogonal projection in the two-coordinate Hilbert sum, so that the projection can be treated
as a matrix of bounded operators.

Adapted from the real Hilbert space argument in the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean).
-/

public section

noncomputable section

open InnerProductSpace
open scoped LinearPMap

namespace LinearPMap

section WeakEquation

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The projection of `(z, 0)` onto the graph of a closed operator `T` has the form `(u, T u)`,
with `⟪z - u, v⟫ = ⟪T u, T v⟫` for every `v` in the domain of `T`. -/
theorem IsClosed.exists_inner_sub_eq_inner_map {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) (z : E) :
    ∃ u : T.domain, ∀ v : T.domain, ⟪z - (u : E), (v : E)⟫ = ⟪T u, T v⟫ := by
  let e := WithLp.prodContinuousLinearEquiv 2 𝕜 E F
  let K : Submodule 𝕜 (WithLp 2 (E × F)) := T.graph.comap e.toLinearMap
  have hK : _root_.IsClosed (K : Set (WithLp 2 (E × F))) := hT.preimage e.continuous
  let : CompleteSpace K := hK.completeSpace_coe
  let a : WithLp 2 (E × F) := WithLp.toLp 2 (z, (0 : F))
  let p := K.starProjection a
  have hp : e p ∈ T.graph := K.starProjection_apply_mem a
  simp only [e, WithLp.prodContinuousLinearEquiv_apply] at hp
  obtain ⟨u, hu1, hu2⟩ := T.mem_graph_iff.mp hp
  refine ⟨u, fun v ↦ ?_⟩
  have hv : WithLp.toLp 2 ((v : E), T v) ∈ K := by
    apply Submodule.mem_comap.mpr
    -- The comap uses `e.toLinearMap`, whose underlying function is `e`.
    change e (WithLp.toLp 2 ((v : E), T v)) ∈ T.graph
    simpa only [e, WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_toLp] using T.mem_graph v
  have h : ⟪z, (v : E)⟫ -
      (⟪(WithLp.ofLp p).1, (v : E)⟫ + ⟪(WithLp.ofLp p).2, T v⟫) = 0 := by
    simpa only [inner_sub_left, WithLp.prod_inner_apply, a, WithLp.ofLp_toLp, inner_zero_left,
      add_zero] using K.starProjection_inner_eq_zero a _ hv
  rw [← hu1, ← hu2] at h
  rw [inner_sub_left]
  linear_combination h

end WeakEquation

section Graph

variable {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The graph of a partial endomorphism on the `L²` sum of two copies of its ambient space,
with the input in coordinate `0` and the output in coordinate `1`. -/
def piLpGraph (T : E →ₗ.[𝕜] E) : Submodule 𝕜 (PiLp 2 fun _ : Fin 2 ↦ E) :=
  T.graph.comap ((LinearEquiv.finTwoArrow 𝕜 E).toLinearMap.comp
    (WithLp.linearEquiv 2 𝕜 (Fin 2 → E)).toLinearMap)

@[simp]
theorem mem_piLpGraph {T : E →ₗ.[𝕜] E} {x : PiLp 2 fun _ : Fin 2 ↦ E} :
    x ∈ T.piLpGraph ↔ (x 0, x 1) ∈ T.graph :=
  (Iff.rfl)

end Graph

/-- The graph of a closed operator is closed in the `L²` sum. -/
theorem IsClosed.piLpGraph {𝕜 E : Type*} [CommRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    {T : E →ₗ.[𝕜] E} (hT : T.IsClosed) :
    _root_.IsClosed (T.piLpGraph : Set (PiLp 2 fun _ : Fin 2 ↦ E)) := by
  let f : PiLp 2 (fun _ : Fin 2 ↦ E) → E × E := fun x ↦ (x 0, x 1)
  have hpre : f ⁻¹' (T.graph : Set (E × E)) = T.piLpGraph :=
    Set.ext fun _ ↦ mem_piLpGraph.symm
  rw [← hpre]
  exact hT.preimage (by fun_prop : Continuous f)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The orthogonal projection onto the graph in the two-coordinate Hilbert sum. -/
def graphProjection (T : E →ₗ.[𝕜] E) (hT : T.IsClosed) :
    PiLp 2 (fun _ : Fin 2 ↦ E) →L[𝕜] PiLp 2 (fun _ : Fin 2 ↦ E) :=
  letI := hT.piLpGraph.completeSpace_coe
  T.piLpGraph.starProjection

/-- The graph projection agrees with the submodule's star projection. -/
theorem graphProjection_eq_starProjection (T : E →ₗ.[𝕜] E) (hT : T.IsClosed)
    [T.piLpGraph.HasOrthogonalProjection] : T.graphProjection hT = T.piLpGraph.starProjection :=
  (rfl)

@[simp]
theorem range_graphProjection (T : E →ₗ.[𝕜] E) (hT : T.IsClosed) :
    (T.graphProjection hT).range = T.piLpGraph := by
  let := hT.piLpGraph.completeSpace_coe
  exact T.piLpGraph.range_starProjection

/-- The Hilbert graph projection is self-adjoint and idempotent. -/
theorem isStarProjection_graphProjection (T : E →ₗ.[𝕜] E) (hT : T.IsClosed) :
    IsStarProjection (T.graphProjection hT) := by
  let := hT.piLpGraph.completeSpace_coe
  exact isStarProjection_starProjection (U := T.piLpGraph)

end LinearPMap
