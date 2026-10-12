/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.SingleDegree
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Cohomology

/-!
# Cohomological dimension at most one is projectivity

A profinite group `G` with `cd_p G ≤ 1` has vanishing `H²(G, M)` for every finite discrete
`G`-module `M` killed by `p`, since such an `M` is `p`-primary torsion. Through the cohomological
obstruction to a finite embedding problem, every finite embedding problem for `G` with elementary
abelian `p`-kernel is therefore solvable; climbing the lower `p`-central series of a finite
`p`-group kernel extends this to `p`-group kernels, and the inverse-limit assembly of compatible
finite solutions makes `G` projective: every continuous homomorphism into a quotient of a
profinite pro-`p` group lifts continuously.

Conversely, a projective pro-`p` group has vanishing `H²` on every finite discrete `p`-primary
module, because every profinite extension of it by such a module splits
(`TauCeti.IsProjective.subsingleton_continuousCohomology_two_of_isPPrimaryTorsion`), and the
`p`-cohomological dimension of a compact group is detected in degree two on finite coefficients
(`TauCeti.cohomologicalDimensionLE_iff_forall_finite_subsingleton_succ`). So for a pro-`p` group
projectivity and `cd_p ≤ 1` are the same condition.

This is the cohomological half of Serre's theorem that a pro-`p` group with `cd_p ≤ 1` is free
pro-`p`, proved in `TauCeti.Topology.Algebra.Group.Profinite.Free.Serre` at finite rank and in
`TauCeti.Topology.Algebra.Group.Profinite.Free.Pointed.Serre` at arbitrary rank.

## Main results

* `TauCeti.CohomologicalDimensionLE.hasElementaryAbelianSolutions`: `cd_p G ≤ 1` solves the
  finite embedding problems with elementary abelian `p`-kernel.
* `TauCeti.CohomologicalDimensionLE.isProjective`: `cd_p G ≤ 1` makes `G` projective.
* `TauCeti.IsProjective.cohomologicalDimensionLE_one`,
  `TauCeti.IsProjective.cohomologicalDimensionAt_le_one`: a projective pro-`p` group has
  `cd_p G ≤ 1`.
* `TauCeti.IsProP.isProjective_iff_cohomologicalDimensionLE_one`,
  `TauCeti.IsProP.isProjective_iff_cohomologicalDimensionAt_le_one`: **a pro-`p` group is
  projective if and only if `cd_p G ≤ 1`**.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.4 and §5.9.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
-/

public section

namespace TauCeti

universe u v w

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-! ### From `cd_p G ≤ 1` to projectivity -/

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

/-! ### From projectivity to `cd_p G ≤ 1` -/

/-- **A projective pro-`p` group has `cd_p ≤ 1`**, as the vanishing predicate: for `p ≠ 0`,
`Hⁱ(G, M)` vanishes for every `i ≥ 2` and every discrete `p`-primary torsion `G`-module `M`. -/
theorem IsProjective.cohomologicalDimensionLE_one (hp : p ≠ 0) (hproj : IsProjective.{u, u, u} p G)
    (hG : IsProP p G) : CohomologicalDimensionLE.{u} p G 1 :=
  (cohomologicalDimensionLE_iff_forall_finite_subsingleton_succ hp 1).2
    fun M _ _ _ _ _ _ hM ↦ hproj.subsingleton_continuousCohomology_two_of_isPPrimaryTorsion hG M hM

/-- **A projective pro-`p` group has cohomological dimension at most one**: `cd_p G ≤ 1` for a
projective pro-`p` group `G` and `p ≠ 0`. -/
theorem IsProjective.cohomologicalDimensionAt_le_one (hp : p ≠ 0)
    (hproj : IsProjective.{u, u, u} p G) (hG : IsProP p G) :
    cohomologicalDimensionAt.{u} p G ≤ 1 :=
  mod_cast (cohomologicalDimensionAt_le_iff p G 1).2 (hproj.cohomologicalDimensionLE_one hp hG)

/-- **A pro-`p` group is projective if and only if `cd_p G ≤ 1`**, as the vanishing predicate. -/
theorem IsProP.isProjective_iff_cohomologicalDimensionLE_one [Fact p.Prime] (hG : IsProP p G) :
    IsProjective.{u, u, u} p G ↔ CohomologicalDimensionLE.{u} p G 1 :=
  ⟨fun hproj ↦ hproj.cohomologicalDimensionLE_one (Fact.out : p.Prime).ne_zero hG,
    fun h ↦ h.isProjective⟩

/-- **A pro-`p` group is projective if and only if `cd_p G ≤ 1`.** -/
theorem IsProP.isProjective_iff_cohomologicalDimensionAt_le_one [Fact p.Prime] (hG : IsProP p G) :
    IsProjective.{u, u, u} p G ↔ cohomologicalDimensionAt.{u} p G ≤ 1 := by
  rw [hG.isProjective_iff_cohomologicalDimensionLE_one, ← cohomologicalDimensionAt_le_iff,
    Nat.cast_one]

end TauCeti
