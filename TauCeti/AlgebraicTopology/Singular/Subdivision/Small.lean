/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import TauCeti.AlgebraicTopology.Singular.Subdivision.AffineChain
public import TauCeti.Analysis.Normed.Affine.Centroid
public import TauCeti.Geometry.Convex.ConvexSpace.Dist

/-!
# Iterated barycentric subdivision produces small simplices

Points of the standard simplex `StdSimplex ℝ N` on a finite type `N` are measured by their weight
vectors `⇑w.weights : N → ℝ` with the sup metric, which induces the topology of the simplex. If the
vertices of an affine `k`-simplex are pairwise at distance at most `d`, then the vertices of each
simplex of its barycentric subdivision are pairwise at distance at most `k / (k + 1) * d`: they
are the barycenters of a decreasing chain of faces, and the barycenter of a face with at most
`k + 1` vertices lies within `k / (k + 1) * d` of each of its vertices. Since all points of the
simplex are at distance at most `1`, the vertex tuples of the `n`-fold iterated subdivision of any
affine `k`-chain are pairwise at distance at most `(k / (k + 1)) ^ n`.

Combined with the Lebesgue number lemma, this shows that for every open cover `U` of a space `X`
and every singular simplex `σ : Δᵐ → X`, all affine simplices of a sufficiently fine iterated
subdivision are carried by `σ` into a single member of `U`. Since pushing affine chains forward
along `σ` intertwines their subdivision with the barycentric subdivision of singular chains
(`TauCeti.AffineChain.singularChain_subdivision`), this is the statement that every singular
simplex becomes subordinate to `U` after sufficiently many barycentric subdivisions.

## Main results

* `TauCeti.BarycentricSubdivision.dist_weights_affineMapMk_vertex_le`: subdivision shrinks the
  distances between the vertices of an affine simplex by the factor `k / (k + 1)`.
* `TauCeti.AffineChain.dist_weights_le_of_mem_support_subdivision_iterate`: the vertex tuples of the
  `n`-fold subdivision of an affine `k`-chain are pairwise at distance at most `(k / (k + 1)) ^ n`.
* `ContinuousMap.exists_pos_forall_range_subset_of_dist_weights_lt`: a Lebesgue number for an
  open cover pulled back along a singular simplex, bounding the distances between vertices.
* `ContinuousMap.exists_forall_mem_support_subdivision_iterate_range_subset`: every affine
  simplex of a sufficiently fine iterated subdivision is carried into a member of the cover.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, steps (2) and (4).
-/

public section

noncomputable section

open Convexity Equiv Finset Metric

namespace TauCeti

variable {N : Type*} [Fintype N]

namespace BarycentricSubdivision

/-- **Barycentric subdivision shrinks simplices.** If the vertices of an affine `k`-simplex in a
standard simplex are pairwise at distance at most `d`, then so are the vertices of each simplex of
its barycentric subdivision, up to the factor `k / (k + 1)`. -/
theorem dist_weights_affineMapMk_vertex_le {k : ℕ} (v : Fin (k + 1) → StdSimplex ℝ N) {d : ℝ}
    (hd : ∀ i j, dist ⇑(v i).weights ⇑(v j).weights ≤ d) (π : Perm (Fin (k + 1)))
    (i j : Fin (k + 1)) :
    dist ⇑(StdSimplex.affineMapMk (R := ℝ) v (vertex π i)).weights
        ⇑(StdSimplex.affineMapMk (R := ℝ) v (vertex π j)).weights ≤ k / (k + 1) * d := by
  have hd₀ : 0 ≤ d := (dist_nonneg).trans (hd 0 0)
  -- The vertices are barycenters of the decreasing chain of faces `π '' [i, k]`.
  have key {i j : Fin (k + 1)} (hij : i ≤ j) :
      dist ⇑(StdSimplex.affineMapMk (R := ℝ) v (vertex π j)).weights
          ⇑(StdSimplex.affineMapMk (R := ℝ) v (vertex π i)).weights ≤ k / (k + 1) * d := by
    rw [vertex_def, vertex_def, StdSimplex.weights_affineMapMk_subBarycenter,
      StdSimplex.weights_affineMapMk_subBarycenter]
    refine (dist_centroid_centroid_le_of_subset (fun a _ b _ ↦ hd a b)
      (map_subset_map.2 (Ici_subset_Ici.2 hij)) nonempty_Ici.map).trans ?_
    gcongr
    have hcard : #((Ici i).map π.toEmbedding) ≤ k + 1 := (card_le_univ _).trans_eq (by simp)
    have hpos : 0 < #((Ici i).map π.toEmbedding) := nonempty_Ici.map.card_pos
    have hk : (k : ℝ) / (k + 1) = 1 - ((k : ℝ) + 1)⁻¹ := by
      field_simp
      ring
    rw [hk]
    exact sub_le_sub_left (inv_anti₀ (by exact_mod_cast hpos) (by exact_mod_cast hcard)) 1
  rcases le_total i j with h | h
  · rw [dist_comm]
    exact key h
  · exact key h

end BarycentricSubdivision

namespace AffineChain

/-- If the vertex tuples in the support of an affine `k`-chain are pairwise at distance at most
`d`, then those of its barycentric subdivision are pairwise at distance at most
`k / (k + 1) * d`. -/
theorem dist_weights_le_of_mem_support_subdivision {k : ℕ}
    {c : (Fin (k + 1) → StdSimplex ℝ N) →₀ ℤ} {d : ℝ}
    (hc : ∀ v ∈ c.support, ∀ i j, dist ⇑(v i).weights ⇑(v j).weights ≤ d)
    {u : Fin (k + 1) → StdSimplex ℝ N} (hu : u ∈ (subdivision _ k c).support) (i j : Fin (k + 1)) :
    dist ⇑(u i).weights ⇑(u j).weights ≤ k / (k + 1) * d := by
  classical
  rw [← c.sum_single, map_finsuppSum] at hu
  obtain ⟨v, hv, hu⟩ := mem_biUnion.1 (Finsupp.support_sum hu)
  rw [subdivision_single] at hu
  obtain ⟨π, -, hπ⟩ := mem_biUnion.1 (Finsupp.support_finsetSum hu)
  obtain rfl := mem_singleton.1 (Finsupp.support_single_subset hπ)
  exact BarycentricSubdivision.dist_weights_affineMapMk_vertex_le v (hc v hv) π i j

/-- The vertex tuples of the `n`-fold barycentric subdivision of an affine `k`-chain in a standard
simplex are pairwise at distance at most `(k / (k + 1)) ^ n`. -/
theorem dist_weights_le_of_mem_support_subdivision_iterate {k n : ℕ}
    {c : (Fin (k + 1) → StdSimplex ℝ N) →₀ ℤ} {u : Fin (k + 1) → StdSimplex ℝ N}
    (hu : u ∈ ((subdivision _ k)^[n] c).support) (i j : Fin (k + 1)) :
    dist ⇑(u i).weights ⇑(u j).weights ≤ ((k : ℝ) / (k + 1)) ^ n := by
  induction n generalizing u i j with
  | zero =>
    rw [pow_zero]
    exact (dist_le_diam_of_mem (StdSimplex.isBounded_range_toFun_comp_weights N)
      ⟨u i, rfl⟩ ⟨u j, rfl⟩).trans (StdSimplex.diam_range_toFun_comp_weights_subset_closedBall N)
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hu
    rw [pow_succ']
    exact dist_weights_le_of_mem_support_subdivision (fun v hv ↦ ih hv) hu i j

end AffineChain

end TauCeti

namespace ContinuousMap

variable {N : Type*} [Fintype N] {X : Type*} [TopologicalSpace X]

/-- **Lebesgue number of a singular simplex.** For an open cover `U` of `X` and a singular
simplex `σ : StdSimplex ℝ N → X`, there is `δ > 0` such that every affine simplex whose vertices
are pairwise at distance less than `δ` is carried by `σ` into a single member of `U`. -/
theorem exists_pos_forall_range_subset_of_dist_weights_lt (σ : C(StdSimplex ℝ N, X))
    {ι : Type*} {U : ι → Set X} (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) :
    ∃ δ > 0, ∀ {k : ℕ} (v : Fin (k + 1) → StdSimplex ℝ N),
      (∀ i j, dist ⇑(v i).weights ⇑(v j).weights < δ) →
        ∃ i, Set.range (σ.comp (StdSimplex.continuousAffineMapMk v)) ⊆ U i := by
  have hemb := StdSimplex.isEmbedding_toFun_comp_weights ℝ N
  -- Extend the pulled-back cover of the simplex to an open cover of its image in `N → ℝ`.
  choose V hV hσV using fun i ↦ hemb.isInducing.isOpen_iff.1 ((hU i).preimage σ.continuous)
  have hcover : Set.range (fun w : StdSimplex ℝ N ↦ ⇑w.weights) ⊆ ⋃ i, V i := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov.symm ▸ Set.mem_univ (σ w))
    have hw : w ∈ (fun t : StdSimplex ℝ N ↦ ⇑t.weights) ⁻¹' V i := by
      rw [hσV i]
      exact hi
    exact Set.mem_iUnion.2 ⟨i, hw⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_range hemb.continuous) hV
    hcover
  refine ⟨δ, hδ, fun {k} v hv ↦ ?_⟩
  obtain ⟨i, hi⟩ := hball _ ⟨v 0, rfl⟩
  refine ⟨i, ?_⟩
  rintro _ ⟨w, rfl⟩
  -- Every point of the affine simplex lies within the largest distance to the vertex `v 0`.
  have hr : univ.sup' univ_nonempty (fun m ↦ dist ⇑(v m).weights ⇑(v 0).weights) < δ :=
    (sup'_lt_iff _).2 fun m _ ↦ hv m 0
  have hw : StdSimplex.affineMapMk (R := ℝ) v w ∈ σ ⁻¹' U i := by
    rw [← hσV i]
    exact hi (mem_ball.2 ((StdSimplex.dist_weights_affineMapMk_le v
      (fun m ↦ le_sup' (fun m ↦ dist ⇑(v m).weights ⇑(v 0).weights) (mem_univ m)) w).trans_lt hr))
  simpa using hw

end ContinuousMap

namespace ContinuousMap

open TauCeti.AffineChain

variable {N : Type*} [Finite N] {X : Type*} [TopologicalSpace X]

/-- **Iterated subdivision is eventually subordinate to an open cover.** For an open cover `U` of
`X`, a singular simplex `σ : StdSimplex ℝ N → X` and a dimension `k`, there is `n₀` such that for
all `n ≥ n₀` and every affine `k`-chain `c`, each affine simplex of the `n`-fold barycentric
subdivision of `c` is carried by `σ` into a single member of `U`. -/
theorem exists_forall_mem_support_subdivision_iterate_range_subset (σ : C(StdSimplex ℝ N, X))
    {ι : Type*} {U : ι → Set X} (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) (k : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, ∀ (c : (Fin (k + 1) → StdSimplex ℝ N) →₀ ℤ),
      ∀ u ∈ ((subdivision _ k)^[n] c).support,
        ∃ i, Set.range (σ.comp (StdSimplex.continuousAffineMapMk u)) ⊆ U i := by
  have := Fintype.ofFinite N
  obtain ⟨δ, hδ, hsmall⟩ := σ.exists_pos_forall_range_subset_of_dist_weights_lt hU hcov
  have hq₀ : (0 : ℝ) ≤ k / (k + 1) := by positivity
  have hq₁ : (k : ℝ) / (k + 1) < 1 := (div_lt_one (by positivity)).2 (lt_add_one _)
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hδ hq₁
  refine ⟨n₀, fun n hn c u hu ↦ hsmall u fun i j ↦ ?_⟩
  exact ((dist_weights_le_of_mem_support_subdivision_iterate hu i j).trans
    (pow_le_pow_of_le_one hq₀ hq₁.le hn)).trans_lt hn₀

end ContinuousMap
