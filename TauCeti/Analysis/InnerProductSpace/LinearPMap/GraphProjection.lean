/-
Copyright (c) 2026 Lyu Yuwei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lyu Yuwei
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Orthogonal projection onto the graph of a closed operator

Projecting `(z, 0)` onto the closed graph of `T` in the Hilbert product gives
a weak equation on the domain of `T`, without assuming the domain is dense.

Adapted from the real Hilbert space argument in the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean).
-/

public section

noncomputable section

open InnerProductSpace
open scoped LinearPMap

namespace LinearPMap

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

end LinearPMap
