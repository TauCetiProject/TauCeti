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
old vertex. This file packages that calculation into the corresponding forward manifold
preservation step (leaving the link of the new vertex as an explicit hypothesis) as well as the
unconditional backward reflection `IsCombinatorialManifold.of_stellarSubdivision`.

The new-vertex link is the join of the boundary of the starred face with its link. Showing that
it has the required type needs the links of all faces of a combinatorial manifold, which
`CombinatorialManifold.Link` computes; there the hypothesis is discharged
(`PreAbstractSimplicialComplex.IsCombinatorialManifold.stellarSubdivision`).

The inverse direction needs no such input: every old vertex link of `K` is stellar equivalent to
a vertex link of the subdivision, so if the subdivision is a combinatorial manifold then so is
`K` (`PreAbstractSimplicialComplex.IsCombinatorialManifold.of_stellarSubdivision`).
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

/-- **Inverse stellar moves preserve combinatorial manifolds.** If starring a nonempty set at a
fresh vertex gives a combinatorial `n`-manifold, then `K` is a combinatorial `n`-manifold. -/
theorem IsCombinatorialManifold.of_stellarSubdivision (hσ : σ.Nonempty)
    (hv : ({v} : Finset ι) ∉ K) (h : IsCombinatorialManifold (stellarSubdivision K σ v) n) :
    IsCombinatorialManifold K n := by
  by_cases hσK : σ ∉ K
  · rwa [stellarSubdivision_eq_self_of_notMem hv hσ hσK] at h
  rw [not_not] at hσK
  -- Every vertex link of `K` is stellar equivalent to a vertex link of the subdivision.
  have key : ∀ ⦃w : ι⦄, ({w} : Finset ι) ∈ K → ∃ u, ({u} : Finset ι) ∈ stellarSubdivision K σ v ∧
      StellarEquivalent (link K {w}) (link (stellarSubdivision K σ v) {u}) := by
    intro w hw
    have hvw : v ∉ ({w} : Finset ι) := notMem_singleton.mpr fun h => hv (h ▸ hw)
    by_cases hσw : σ = {w}
    · -- Starring a vertex renames it: the new vertex has the old link.
      subst hσw
      refine ⟨v, singleton_mem_stellarSubdivision_iff.mpr hσK, ?_⟩
      rw [link_stellarSubdivision_singleton hv, closedStar_inf_deletion_singleton]
    · have hsub : ¬ σ ⊆ {w} := fun h => hσw (hσ.subset_singleton_iff.mp h)
      exact ⟨w, (mem_stellarSubdivision_iff_of_notMem hvw).mpr ⟨hw, hsub⟩,
        stellarEquivalent_link_stellarSubdivision_of_notMem (notMem_link_of_notMem hv) hvw
          (sdiff_nonempty.mpr hsub)⟩
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun w hw => ?_
    obtain ⟨u, hu, he⟩ := key hw
    by_contra hne
    exact he.symm.ne_bot hne (isCombinatorialManifold_zero_iff.mp h hu)
  | succ n =>
    refine isCombinatorialManifold_succ_iff.mpr fun w hw => ?_
    obtain ⟨u, hu, he⟩ := key hw
    exact (isCombinatorialManifold_succ_iff.mp h hu).imp
      (·.of_stellarEquivalentUpToRelabeling he.stellarEquivalentUpToRelabeling)
      (·.of_stellarEquivalentUpToRelabeling he.stellarEquivalentUpToRelabeling)

end PreAbstractSimplicialComplex
