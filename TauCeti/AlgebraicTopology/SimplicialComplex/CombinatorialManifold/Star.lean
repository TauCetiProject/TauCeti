/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Combinatorial
public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Star

/-!
# Vertex stars in combinatorial manifolds

The closed star of a vertex in a combinatorial `n`-manifold, with its vertices tagged according
to whether they are the apex, is a combinatorial `n`-ball. In positive dimension the star is
the join of the apex with its sphere-or-ball link. In dimension zero the closed star is just
the vertex itself.

This gives a standard ball model up to stellar moves for the finite local neighbourhoods used
to construct manifold charts. The tagging agrees with `map_closedStar_eq_join` and is an
injective relabeling, so distinct vertices remain distinct.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3 (joins, links, and combinatorial manifolds).
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {n : ℕ}

/-- The closed vertex star of a combinatorial manifold is a combinatorial ball after the
injective relabeling that tags the apex on the left and all other vertices on the right. -/
theorem IsCombinatorialManifold.isCombinatorialBall_map_closedStar
    (h : IsCombinatorialManifold K n) {v : ι} (hv : ({v} : Finset ι) ∈ K) :
    IsCombinatorialBall
      ((closedStar K {v}).map (TauCeti.partitionEmbedding (· ∈ ({v} : Finset ι)))) n := by
  cases n with
  | zero =>
      rw [closedStar_eq_simplex_of_link_eq_bot hv
        (isCombinatorialManifold_zero_iff.mp h hv)]
      exact (isCombinatorialBall_simplex (by simp)).map _
        (TauCeti.partitionEmbedding (· ∈ ({v} : Finset ι))).injective
  | succ n =>
      rw [map_closedStar_eq_join hv]
      have hpoint : IsCombinatorialBall (simplex ({v} : Finset ι)) 0 :=
        isCombinatorialBall_simplex (by simp)
      rcases isCombinatorialManifold_succ_iff.mp h hv with hs | hb
      · simpa only [map_join_swap, Nat.add_zero] using
          (hs.join_ball hpoint).map Sum.swap (Equiv.sumComm ι ι).injective
      · simpa only [Nat.zero_add] using hpoint.join hb

end PreAbstractSimplicialComplex
