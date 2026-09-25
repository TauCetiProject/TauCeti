/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Cohomology
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Projective

/-!
# Cohomological dimension at most one gives projectivity

A profinite group `G` with `cd_p G ≤ 1` has vanishing `H²(G, M)` for every finite discrete
`G`-module `M` killed by `p`, since such an `M` is `p`-primary torsion. Through the cohomological
obstruction to a finite embedding problem, every finite embedding problem for `G` with elementary
abelian `p`-kernel is therefore solvable; climbing the lower `p`-central series of a finite
`p`-group kernel extends this to `p`-group kernels, and the inverse-limit assembly of compatible
finite solutions makes `G` projective: every continuous homomorphism into a quotient of a
profinite pro-`p` group lifts continuously.

This is the first step of Serre's theorem that a topologically finitely generated pro-`p` group
with `cd_p ≤ 1` is free pro-`p`, proved in
`TauCeti.Topology.Algebra.Group.Profinite.Free.Serre`.

## Main results

* `TauCeti.CohomologicalDimensionLE.hasElementaryAbelianSolutions`: `cd_p G ≤ 1` solves the
  finite embedding problems with elementary abelian `p`-kernel.
* `TauCeti.CohomologicalDimensionLE.isProjective`: `cd_p G ≤ 1` makes `G` projective.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §5.9.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
-/

public section

namespace TauCeti

universe u v w

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A profinite group with `cd_p G ≤ 1` solves every finite embedding problem whose kernel is
commutative and killed by `p`, such a kernel being a finite discrete `p`-primary torsion module. -/
theorem CohomologicalDimensionLE.hasElementaryAbelianSolutions
    (h : CohomologicalDimensionLE.{u} p G 1) : HasElementaryAbelianSolutions p G := by
  apply hasElementaryAbelianSolutions_of_subsingleton_continuousCohomology_two
  intro M _ _ _ _ _ _ hM
  exact cohomologicalDimensionLE_iff.mp h M
    (isPPrimaryTorsion_iff.mpr fun m ↦ ⟨1, by rw [pow_one]; exact hM m⟩) 2 one_lt_two

/-- **Cohomological dimension at most one gives projectivity.** A profinite group with
`cd_p G ≤ 1` is projective: every continuous homomorphism into a quotient of a profinite pro-`p`
group lifts continuously. -/
theorem CohomologicalDimensionLE.isProjective [Fact p.Prime]
    (h : CohomologicalDimensionLE.{u} p G 1) : IsProjective.{u, v, w} p G :=
  isProjective_of_hasPGroupSolutions h.hasElementaryAbelianSolutions.hasPGroupSolutions

end TauCeti
