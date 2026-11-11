/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Pure
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Manifold

/-!
# Stellar subdivision of top-dimensional manifold faces

Starring a top-dimensional face of a combinatorial manifold preserves its manifold
structure. The new vertex has the boundary of that face as its link, hence is an interior
vertex in positive dimension. The links of surviving old vertices are handled by the
existing stellar-link transport. In dimension zero the operation replaces an isolated
vertex by a fresh isolated vertex.

The local calculation applies to any face with void link, without a manifold hypothesis.
It also determines links of faces containing the new vertex: these are links in the
simplex boundary, computable by `link_stellarSubdivision_insert` and
`link_simplexBoundary`. No finiteness of the complex or ambient vertex type is needed.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (stellar moves and combinatorial manifolds).
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol.
  Monogr. 2 (1999), 299–320.
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι} {n : ℕ}

/-- Stellar subdivision at a top-dimensional face preserves a combinatorial manifold,
including dimension zero. No condition on the new vertex's link is assumed. -/
theorem IsCombinatorialManifold.stellarSubdivision_of_card
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hcard : σ.card = n + 1)
    (hv : ({v} : Finset ι) ∉ K) :
    IsCombinatorialManifold (stellarSubdivision K σ v) n := by
  have hlink : link (stellarSubdivision K σ v) {v} = simplexBoundary σ := by
    rw [link_stellarSubdivision_singleton hv,
      closedStar_inf_deletion_eq_simplexBoundary_of_link_eq_bot hσ
        ((hK.link_eq_bot_iff hσ).mpr hcard)]
  cases n with
  | zero =>
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (by simpa using hcard)
    apply hK.stellarSubdivision_zero
    rw [hlink, hw, simplexBoundary_singleton]
  | succ n =>
    apply hK.stellarSubdivision_succ hv
    rw [hlink]
    exact Or.inl (isCombinatorialSphere_simplexBoundary hcard)

end PreAbstractSimplicialComplex
