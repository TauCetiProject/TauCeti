/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Link

/-!
# Combinatorial manifolds under stellar subdivision

The link API for a stellar subdivision already transports the sphere-or-ball condition at every
old vertex. This file packages that calculation into the corresponding manifold preservation
step, leaving the link of the new vertex as an explicit hypothesis. The hypothesis is the exact
remaining local calculation: once it is supplied, every vertex link in the subdivision has the
required type.

The new-vertex link calculation is kept separate because its proof is the geometric
boundary-of-a-closed-star argument.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι} {n : ℕ}

/-- A stellar subdivision preserves a zero-dimensional combinatorial manifold once the new
vertex has void link. -/
theorem IsCombinatorialManifold.stellarSubdivision_zero
    (hK : IsCombinatorialManifold K 0)
    (hnew : link (stellarSubdivision K σ v) {v} = ⊥) :
    IsCombinatorialManifold (stellarSubdivision K σ v) 0 := by
  rw [isCombinatorialManifold_zero_iff]
  intro w hw
  by_cases hwv : w = v
  · simpa [hwv] using hnew
  · exact hK.link_stellarSubdivision_eq_bot hwv hw

/-- A positive-dimensional stellar subdivision preserves the manifold link condition provided the
new vertex has a sphere-or-ball link of the complementary dimension. -/
theorem IsCombinatorialManifold.stellarSubdivision_succ
    (hK : IsCombinatorialManifold K (n + 1))
    (hvK : ({v} : Finset ι) ∉ K)
    (hnew : IsCombinatorialSphere (link (stellarSubdivision K σ v) {v}) n ∨
      IsCombinatorialBall (link (stellarSubdivision K σ v) {v}) n) :
    IsCombinatorialManifold (stellarSubdivision K σ v) (n + 1) := by
  rw [isCombinatorialManifold_succ_iff]
  intro w hw
  by_cases hwv : w = v
  · simpa [hwv] using hnew
  · exact hK.isCombinatorialSphere_or_isCombinatorialBall_link_stellarSubdivision
      (notMem_link_of_notMem hvK) hwv hw

end PreAbstractSimplicialComplex
