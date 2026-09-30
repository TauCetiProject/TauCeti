/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.SuccOrder
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp

/-!
# Cohomological dimension and trivial `𝔽_p` coefficients

The vanishing predicate behind the `p`-cohomological dimension
`cd_p G = cohomologicalDimensionAt p G` quantifies over all discrete `p`-primary torsion
`G`-modules `M`, with the continuous cohomology of `ofDiscreteModule ℤ G M`, while the coefficient
object of the pro-`p` theory is the representation `trivialFp p G` of `G` on `𝔽_p` over the scalars
`ZMod p`, with cohomology `cohomFp p G n`. This file connects the two. The carrier of
`trivialFp p G` is a discrete trivial `G`-module whose `Nat.card` is `p`, hence `p`-primary
torsion, and its `ℤ`-cohomology vanishes exactly when `cohomFp p G n` does
(`TauCeti.ContCohomology.subsingleton_continuousCohomology_ofDiscreteModule_iff`). Hence
`cd_p G ≤ n` forces `Hᵐ(G, 𝔽_p) = 0` for every `m > n`, and, contrapositively, a nonvanishing
`Hⁿ(G, 𝔽_p)` bounds `cd_p G` from below by `n`.

These are the two implications valid for every topological group. For a pro-`p` group the first
one is an equivalence, by dévissage; that is the pro-`p` reduction of `cd_p` in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomologicalDimension`. The dévissage runs on the
trivial discrete `G`-modules of prime order `p`, and the last result here shows that their
cohomology vanishes exactly when `cohomFp p G n` does: such a module is cyclic of order `p`, hence
`G`-equivariantly isomorphic to the carrier of `trivialFp p G`.

## Main results

* `TauCeti.isPPrimaryTorsion_trivialFp_V`: the carrier of `trivialFp p G` is `p`-primary torsion.
* `TauCeti.subsingleton_continuousCohomology_iff_subsingleton_cohomFp_of_natCard_eq`: the
  cohomology of a trivial discrete `G`-module of prime order `p` vanishes exactly when that of
  `𝔽_p` does.
* `TauCeti.CohomologicalDimensionLE.subsingleton_cohomFp`,
  `TauCeti.subsingleton_cohomFp_of_cohomologicalDimensionAt_le`: `cd_p G ≤ n` gives
  `Hᵐ(G, 𝔽_p) = 0` for `m > n`.
* `TauCeti.le_cohomologicalDimensionAt_of_nontrivial_cohomFp`: `Hⁿ(G, 𝔽_p) ≠ 0` gives
  `n ≤ cd_p G`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.1 and §4.1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.2).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable (p : ℕ) (G : Type u)

section Monoid

variable [Monoid G]

/-- The carrier of `trivialFp p G` is `p`-primary torsion, its `Nat.card` being `p`. -/
theorem isPPrimaryTorsion_trivialFp_V : IsPPrimaryTorsion p (trivialFp p G).V :=
  isPPrimaryTorsion_of_natCard_eq_pow ((natCard_trivialFp_V p G).trans (pow_one p).symm)

end Monoid

variable {p G} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction continuousSMul_trivialFp

/-- **The cohomology of a trivial discrete `G`-module of prime order `p` vanishes exactly when that
of `𝔽_p` does.** Such a module is cyclic of order `p`, hence `G`-equivariantly isomorphic to the
carrier of `trivialFp p G`. -/
theorem subsingleton_continuousCohomology_iff_subsingleton_cohomFp_of_natCard_eq [Fact p.Prime]
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
    (hA : Nat.card A = p) (htriv : ∀ (g : G) (a : A), g • a = a) (n : ℕ) :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G A)) ↔
      Subsingleton (cohomFp p G n) := by
  obtain ⟨a, ha⟩ := (isAddCyclic_of_prime_card hA).exists_generator
  let e : (trivialFp p G).V ≃ₗ[ℤ] A :=
    ((trivialFpEquiv p G).toAddEquiv.trans (zmodAddEquivOfGenerator ha hA)).toIntLinearEquiv
  have he : ∀ (g : G) (m : (trivialFp p G).V), e (g • m) = g • e m := fun g m ↦ by
    rw [smul_trivialFp_V, htriv]
  rw [← subsingleton_continuousCohomology_ofDiscreteModule_iff (trivialFp p G) n]
  exact ((ContinuousCohomology.continuousCohomologyFunctor ℤ G n).mapIso
    (ofDiscreteModuleIso e he)).toContinuousLinearEquiv.toEquiv.subsingleton_congr.symm

/-- If `Hⁱ(G, M)` vanishes for every `i > n` and every discrete `p`-primary torsion `G`-module `M`,
then `Hᵐ(G, 𝔽_p)` vanishes for every `m > n`. -/
theorem CohomologicalDimensionLE.subsingleton_cohomFp {n : ℕ}
    (h : CohomologicalDimensionLE.{u} p G n) {m : ℕ} (hm : n < m) : Subsingleton (cohomFp p G m) :=
  (subsingleton_continuousCohomology_ofDiscreteModule_iff (trivialFp p G) m).1
    (cohomologicalDimensionLE_iff.1 h _ (isPPrimaryTorsion_trivialFp_V p G) m hm)

/-- **`cd_p G ≤ n` kills `Hᵐ(G, 𝔽_p)` above `n`.** -/
theorem subsingleton_cohomFp_of_cohomologicalDimensionAt_le {n : ℕ}
    (h : cohomologicalDimensionAt.{u} p G ≤ n) {m : ℕ} (hm : n < m) :
    Subsingleton (cohomFp p G m) :=
  ((cohomologicalDimensionAt_le_iff p G n).1 h).subsingleton_cohomFp hm

/-- **A nonvanishing `Hⁿ(G, 𝔽_p)` bounds `cd_p G` from below**: `n ≤ cd_p G`. -/
theorem le_cohomologicalDimensionAt_of_nontrivial_cohomFp {n : ℕ} (h : Nontrivial (cohomFp p G n)) :
    (n : ℕ∞) ≤ cohomologicalDimensionAt.{u} p G := by
  cases n with
  | zero => simp
  | succ m =>
    refine le_of_not_gt fun hlt ↦ not_nontrivial_iff_subsingleton.2 ?_ h
    exact subsingleton_cohomFp_of_cohomologicalDimensionAt_le
      ((ENat.lt_add_one_iff (ENat.natCast_ne_top m)).1 (by exact_mod_cast hlt)) m.lt_succ_self

end TauCeti
