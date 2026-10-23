/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.TrivialFp
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.AllDegrees
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Devissage

/-!
# Finiteness of the cohomology of a pro-`p` group with finite coefficients

Let `G` be a compact pro-`p` group and `n` a degree. If `Hⁿ(G, 𝔽_p)` is finite, then `Hⁿ(G, M)`
is finite for every finite discrete `p`-primary `G`-module `M`, whatever the action. This is the
finiteness dévissage `TauCeti.IsProP.finite_continuousCohomology_of_forall_natCard_eq_smul_eq_self`
with `𝔽_p` as the test module: a trivial discrete `G`-module of order `p` has the cohomology of
`𝔽_p` (`TauCeti.finite_continuousCohomology_iff_finite_cohomFp_of_natCard_eq`).

In degree `2` the statement is restated on the explicit cocycle model `H2 G M`. For a profinite
pro-`p` group, through the permutation module `Coind_U^G 𝔽_p` of an open subgroup `U` and Shapiro's
lemma in every degree, it gives that `Hⁿ(U, 𝔽_p)` is finite whenever `Hⁿ(G, 𝔽_p)` is. No bound on
the cohomological dimension of `G` enters: finiteness of `Hⁿ(G, 𝔽_p)` alone controls the finite
coefficients in degree `n`. For a finitely presented pro-`p` group `H²(G, 𝔽_p)` is finite, so
`H²(G, M)` is finite for every finite `p`-primary `M`; the case of a Demushkin group, where
`H²(G, 𝔽_p)` is one-dimensional, is the one Tate's duality argument uses.

## Main results

* `TauCeti.IsProP.finite_continuousCohomology_of_finite_cohomFp`: **finiteness of `Hⁿ` on finite
  `p`-primary modules** when `Hⁿ(G, 𝔽_p)` is finite.
* `TauCeti.IsProP.finite_H2`: the degree-`2` case on the explicit `H2 G M`.
* `TauCeti.IsProP.finite_cohomFp_openSubgroup`: `Hⁿ(U, 𝔽_p)` is finite for every open subgroup `U`
  when `Hⁿ(G, 𝔽_p)` is.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.2).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- **Finiteness of `Hⁿ` on finite `p`-primary modules.** Let `G` be a compact pro-`p` group with
`Hⁿ(G, 𝔽_p)` finite. Then `Hⁿ(G, M)` is finite for every finite discrete `p`-primary `G`-module
`M`. -/
theorem IsProP.finite_continuousCohomology_of_finite_cohomFp (hG : IsProP p G) {n : ℕ}
    [Finite (cohomFp p G n)] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (hM : IsPPrimaryTorsion p M) : Finite (continuousCohomology n (ofDiscreteModule ℤ G M)) :=
  hG.finite_continuousCohomology_of_forall_natCard_eq_smul_eq_self (n := n)
    (fun A _ _ _ _ _ _ hA htriv ↦
      (finite_continuousCohomology_iff_finite_cohomFp_of_natCard_eq A hA htriv n).2
        ‹Finite (cohomFp p G n)›) M hM

/-- **Finiteness of `H²` on finite `p`-primary modules.** Let `G` be a compact pro-`p` group
with `H²(G, 𝔽_p)` finite. Then the explicit `H²(G, M)` is finite for every finite discrete
`p`-primary `G`-module `M`. -/
theorem IsProP.finite_H2 (hG : IsProP p G) [Finite (cohomFp p G 2)] (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
    [Finite M] (hM : IsPPrimaryTorsion p M) : Finite (H2 G M) :=
  have := hG.finite_continuousCohomology_of_finite_cohomFp (n := 2) M hM
  Finite.of_equiv _ (explicitH2AddEquivContinuousCohomology G M).symm.toEquiv

variable [TotallyDisconnectedSpace G]

attribute [local instance] TopRep.distribMulAction continuousSMul_trivialFp

/-- **Finiteness of `Hⁿ(-, 𝔽_p)` on open subgroups.** Let `G` be a profinite pro-`p` group with
`Hⁿ(G, 𝔽_p)` finite. Then `Hⁿ(U, 𝔽_p)` is finite for every open subgroup `U`: it is
`Hⁿ(G, Coind_U^G 𝔽_p)` by Shapiro's lemma, and `Coind_U^G 𝔽_p` is a finite `p`-primary module. -/
theorem IsProP.finite_cohomFp_openSubgroup (hG : IsProP p G) {n : ℕ} [Finite (cohomFp p G n)]
    (U : OpenSubgroup G) : Finite (cohomFp p U.toSubgroup n) := by
  have hUc : IsClosed (U.toSubgroup : Set G) := U.isClosed
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp hUc.isCompact
  have : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : NeZero p := ⟨hp.out.ne_zero⟩
  -- `Coind_U^G 𝔽_p` is finite and `p`-primary, so its cohomology in degree `n` is finite
  have := hG.finite_continuousCohomology_of_finite_cohomFp (n := n)
    (DiscreteCoind G U.toSubgroup (trivialFp p U.toSubgroup).V)
    (isPPrimaryTorsion_discreteCoind G U.toSubgroup _ (isPPrimaryTorsion_trivialFp_V p _))
  -- Shapiro's lemma, then the identification of the carrier's `ℤ`-cohomology with `cohomFp`
  have : Finite (continuousCohomology n
      (ofDiscreteModule ℤ U.toSubgroup (trivialFp p U.toSubgroup).V)) :=
    Finite.of_equiv _
      (ContinuousCohomology.shapiroIso U.toSubgroup hUc _ n).toContinuousLinearEquiv.toEquiv
  exact Finite.of_equiv _
    (ofDiscreteModuleRestrictScalarsIntEquiv (trivialFp p U.toSubgroup) n).toEquiv

end TauCeti
