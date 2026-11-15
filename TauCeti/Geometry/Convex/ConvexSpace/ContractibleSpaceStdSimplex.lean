/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Topology.Homotopy.Contractible

/-!
# The standard simplex is contractible

The straight-line homotopy towards a vertex contracts `StdSimplex ℝ M` for any nonempty `M`.
Contractibility upgrades the path-connectedness already recorded for the standard simplex to
simple connectedness, which is what makes transport of a local coefficient system along a path
inside a simplex independent of the path.

The contraction needs the straight-line homotopy to be jointly continuous in time and in the
starting point (`StdSimplex.continuous_uncurry_convexCombPair`). For a finite `M` this follows
from `StdSimplex.isEmbedding_toFun_comp_weights`, since the topology of `StdSimplex ℝ M` is then
induced by the weights; for an arbitrary `M` the homotopy is tested on the finite faces through
`StdSimplex.continuous_iff'`.

The argument is adapted from Joël Riou's proof of `Convexity.StdSimplex.continuous_convexCombPair`
in `Mathlib/Geometry/Convex/ConvexSpace/PathConnectedSpaceStdSimplex.lean`, which establishes
continuity in the time variable alone.
-/

public section

namespace Convexity.StdSimplex

open unitInterval

/-- The straight-line homotopy from a point of the standard simplex towards a fixed point `y` is
jointly continuous in the time and the starting point. -/
@[fun_prop]
lemma continuous_uncurry_convexCombPair {M : Type*} (y : StdSimplex ℝ M) :
    Continuous (Function.uncurry fun (t : I) (x : StdSimplex ℝ M) ↦
      convexCombPair (R := ℝ) (σ t) t (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
        x y) := by
  classical
  wlog hM : Finite M generalizing M
  · let F (x : StdSimplex ℝ M) : C(I, StdSimplex ℝ M) := ⟨_, continuous_convexCombPair x y⟩
    suffices hF : Continuous F from
      continuous_eval.comp ((hF.comp continuous_snd).prodMk continuous_fst)
    rw [continuous_iff']
    intro s
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    let t : Finset M := s ∪ y.weights.support
    obtain ⟨y', hy⟩ := (mem_range_map_iff (Subtype.val : t → M) y).2 (by aesop)
    convert (continuous_map ℝ (Subtype.val : t → M)).comp ((this y' inferInstance).comp
      (continuous_snd.prodMk ((continuous_map ℝ (fun i : s ↦ (⟨i, by grind⟩ : t))).comp
        continuous_fst))) using 1
    ext ⟨x, τ⟩ : 1
    simp only [Function.comp_apply, Function.uncurry_apply_pair, F, ContinuousMap.coe_mk, ← hy]
    rw [(isAffineMap_map ℝ _).map_convexCombPair, map_map]
  rw [(isEmbedding_toFun_comp_weights ℝ M).continuous_iff]
  refine continuous_pi fun i ↦ ?_
  simp only [Function.comp_apply, Function.uncurry, weights_convexCombPair, coe_symm_eq,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- The standard simplex on a nonempty type is contractible: the straight-line homotopy towards a
vertex contracts it. -/
instance contractibleSpace (M : Type*) [Nonempty M] : ContractibleSpace (StdSimplex ℝ M) := by
  obtain ⟨m₀⟩ := ‹Nonempty M›
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨single m₀, ⟨⟨⟨_, continuous_uncurry_convexCombPair (single m₀)⟩,
    fun _ ↦ by simp, fun _ ↦ by simp⟩⟩⟩

end Convexity.StdSimplex
