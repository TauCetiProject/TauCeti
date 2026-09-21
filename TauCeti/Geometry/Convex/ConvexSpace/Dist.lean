/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.AffineSpace.Centroid
public import TauCeti.Geometry.Convex.ConvexSpace.Topology

/-!
# Weights of affine simplices in a standard simplex

A point `w` of a standard simplex on a finite type `N` is determined by its weight vector
`⇑w.weights : N → ℝ`, and Mathlib's topology on `StdSimplex ℝ N` is the one induced by this
embedding (`Convexity.StdSimplex.isEmbedding_toFun_comp_weights`). This file computes the weight
vectors of the points of the affine simplex `Convexity.StdSimplex.affineMapMk v` with vertices
`v m`:

* `Convexity.StdSimplex.weights_affineMapMk_subBarycenter`: the image of the barycenter of the
  face spanned by `S` has as weight vector the centroid of the weight vectors of the vertices
  `v m`, `m ∈ S`;
* `Convexity.StdSimplex.dist_weights_affineMapMk_le`: every point of the affine simplex lies in
  each closed ball, for the sup metric on weight vectors, containing all of its vertices.

These are the metric facts about affine simplices used to show that iterated barycentric
subdivision produces arbitrarily small simplices.
-/

public section

namespace Convexity.StdSimplex

variable {M N : Type*} [Finite M]

/-- The image under the affine map with vertices `v` of the barycenter of the face spanned by
`S` has as weight vector the centroid of the weight vectors of the vertices `v m`, `m ∈ S`. -/
lemma weights_affineMapMk_subBarycenter (v : M → StdSimplex ℝ N) (S : Finset M)
    (hS : S.Nonempty) :
    ⇑(affineMapMk (R := ℝ) v (subBarycenter S hS)).weights =
      S.centroid ℝ fun m ↦ ⇑(v m).weights := by
  classical
  have := Fintype.ofFinite M
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (S.sum_centroidWeights_eq_one_of_nonempty ℝ hS)]
  ext n
  simp [weights_affineMapMk_apply, weights_subBarycenter, Finsupp.single_apply,
    Finset.sum_apply, Finset.centroidWeights_apply]

/-- Every point of an affine simplex lies in each closed ball, for the sup metric on weight
vectors, that contains all of its vertices. -/
lemma dist_weights_affineMapMk_le [Fintype N] (v : M → StdSimplex ℝ N) {q : N → ℝ} {r : ℝ}
    (h : ∀ m, dist ⇑(v m).weights q ≤ r) (w : StdSimplex ℝ M) :
    dist ⇑(affineMapMk (R := ℝ) v w).weights q ≤ r := by
  have := Fintype.ofFinite M
  have hw : ⇑(affineMapMk (R := ℝ) v w).weights = ∑ m, w.weights m • ⇑(v m).weights := by
    ext n
    simp [weights_affineMapMk_apply, Finset.sum_apply]
  rw [hw, ← Metric.mem_closedBall]
  exact (convex_closedBall q r).sum_mem (fun m _ ↦ w.weights_nonneg m) w.total_of_fintype
    fun m _ ↦ h m

end Convexity.StdSimplex
