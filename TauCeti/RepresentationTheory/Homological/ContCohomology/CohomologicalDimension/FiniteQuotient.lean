/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Simple
public import TauCeti.RepresentationTheory.Induction.Restriction

/-!
# Testing cohomological dimension on simple representations of finite quotients

For a compact topological group `G` and a prime `p`, the bound `cd_p G ≤ n` can be tested in
degree `n + 1` on finite discrete modules that are simple representations of a finite quotient
`G ⧸ U`, where `U` is any open normal subgroup acting trivially on the module. The action on
the coefficients of cohomology remains the original action of `G`.

The test is independent of `U`: `Rep.simple_ofQuotient_iff` identifies simplicity of the
quotient representation with simplicity of the original representation, for every normal
subgroup acting trivially. Every finite discrete continuous module has such an open normal
subgroup, namely `TauCeti.openActionKernel`. Thus the quotient test is equivalent to the
irreducible-module test `TauCeti.cohomologicalDimensionLE_iff_forall_isIrreducible`.

No total-disconnectedness assumption is needed. Compactness makes the quotients by open
subgroups finite and is used by the underlying cohomological-dimension reduction. Simplicity
excludes the zero module, and a `ZMod p`-module is automatically killed by `p`.

## Main results

* `TauCeti.cohomologicalDimensionLE_iff_forall_simple_ofQuotient`: the finite-quotient test
  for the vanishing predicate.
* `TauCeti.cohomologicalDimensionAt_le_iff_forall_simple_ofQuotient`: the corresponding
  criterion for the dimension invariant.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Proposition (3.3.2).
-/

public section

namespace TauCeti

open ContCohomology CategoryTheory

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- For a prime `p` and a compact group `G`, the bound on cohomological dimension can be
tested in degree `n + 1` on finite discrete `ZMod p`-modules whose representation of a finite
quotient is simple. Any open normal subgroup acting trivially on the module may be used. -/
theorem cohomologicalDimensionLE_iff_forall_simple_ofQuotient [Fact p.Prime] (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔
      ∀ (M : Type u) [AddCommGroup M] [Module (ZMod p) M] [TopologicalSpace M]
        [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
        (U : OpenNormalSubgroup G)
        [Representation.IsTrivial
          ((Rep.ofDistribMulAction (ZMod p) G M).ρ.comp U.toSubgroup.subtype)],
        Simple ((Rep.ofDistribMulAction (ZMod p) G M).ofQuotient U.toSubgroup) →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionLE_iff_forall_isIrreducible]
  constructor
  · intro h M _ _ _ _ _ _ _ U _ hM
    exact h M ((Rep.simple_iff_isIrreducible _).1 ((Rep.simple_ofQuotient_iff _ _).1 hM))
  · intro h M _ _ _ _ _ _ _ hM
    let U := openActionKernel G M
    let : Representation.IsTrivial
        ((Rep.ofDistribMulAction (ZMod p) G M).ρ.comp U.toSubgroup.subtype) :=
      ⟨fun g ↦ LinearMap.ext fun m ↦ openActionKernel_smul_eq_self G M g m⟩
    exact h M U ((Rep.simple_ofQuotient_iff _ _).2 ((Rep.simple_iff_isIrreducible _).2 hM))

/-- For a compact group `G` and a prime `p`, `cd_p G ≤ n` if and only if `Hⁿ⁺¹(G, M)` vanishes
for every finite discrete module that is a simple `ZMod p`-representation of an open normal
quotient of `G`. Simplicity may be read through any such quotient acting on the module. -/
theorem cohomologicalDimensionAt_le_iff_forall_simple_ofQuotient (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (n : ℕ) :
    cohomologicalDimensionAt.{u} p G ≤ n ↔
      ∀ (M : Type u) [AddCommGroup M] [Module (ZMod p) M] [TopologicalSpace M]
        [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
        (U : OpenNormalSubgroup G)
        [Representation.IsTrivial
          ((Rep.ofDistribMulAction (ZMod p) G M).ρ.comp U.toSubgroup.subtype)],
        Simple ((Rep.ofDistribMulAction (ZMod p) G M).ofQuotient U.toSubgroup) →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionLE_iff_forall_simple_ofQuotient]

end TauCeti
