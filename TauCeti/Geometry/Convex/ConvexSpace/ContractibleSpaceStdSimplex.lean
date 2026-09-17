/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Topology.Homotopy.Contractible

/-!
# The standard simplex on a finite type is contractible

The straight-line homotopy towards a vertex contracts `StdSimplex ℝ M` for a finite nonempty `M`.
Contractibility upgrades the path-connectedness already recorded for the standard simplex to
simple connectedness, which is what makes transport of a local coefficient system along a path
inside a simplex independent of the path.

Finiteness of `M` is used through `StdSimplex.isEmbedding_toFun_comp_weights`: it is only for a
finite `M` that the topology of `StdSimplex ℝ M` is induced by the weights.
-/

public section

namespace Convexity.StdSimplex

instance contractibleSpace (M : Type*) [Finite M] [Nonempty M] :
    ContractibleSpace (StdSimplex ℝ M) := by
  classical
  obtain ⟨m₀⟩ := ‹Nonempty M›
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨single m₀, ⟨⟨⟨fun p ↦ convexCombPair (R := ℝ) (unitInterval.symm p.1) p.1
      (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) p.2 (single m₀), ?_⟩,
    fun _ ↦ by simp, fun _ ↦ by simp⟩⟩⟩
  rw [(isEmbedding_toFun_comp_weights ℝ M).continuous_iff]
  refine continuous_pi fun i ↦ ?_
  simp only [Function.comp_apply, weights_convexCombPair, unitInterval.coe_symm_eq,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

end Convexity.StdSimplex
