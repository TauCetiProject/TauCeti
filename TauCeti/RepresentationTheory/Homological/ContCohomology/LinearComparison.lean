/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree.Module
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ScalarAction
public import TauCeti.Topology.Algebra.ConstMulAction.Discrete

/-!
# The low-degree comparisons are linear

`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` and
`explicitH2AddEquivContinuousCohomology` identify the explicit `H¹(G, M)` and `H²(G, M)` of a
discrete `G`-module `M` with Mathlib's `continuousCohomology 1` and `continuousCohomology 2` of
`TauCeti.ofDiscreteModule ℤ G M`. Neither side depends on a coefficient ring. When `M` is a module
over a semiring `R` and the action of `G` commutes with the scalars, both sides are `R`-modules by
instances, the scalar `r` acting through the coefficient map of `r • ·`
(`TauCeti.ContCohomology.H1.instModule`, `H2.instModule`,
`TauCeti.ContinuousCohomology.instModuleOfDiscreteModule`). Since the comparisons are natural in
the coefficients, they are `R`-linear. This file records them as linear equivalences, whose
underlying additive equivalences are the comparisons themselves.

For a discrete `X : TopRep k G` over a commutative ring `k`, the comparisons
`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete` and
`TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete` with Mathlib's `k`-linear cohomology
`continuousCohomology n X` are the `ℤ`-comparisons of the carrier followed by
`TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv`; both pieces are `k`-linear, so
these comparisons are `k`-linear too.

## Main definitions

* `TauCeti.ContCohomology.explicitH1LinearEquivContinuousCohomology` and
  `explicitH2LinearEquivContinuousCohomology`: the comparisons as `R`-linear equivalences.
* `TopRep.explicitH1LinearEquivContinuousCohomologyOfDiscrete` and
  `TopRep.explicitH2LinearEquivContinuousCohomologyOfDiscrete`: the comparisons for a discrete
  representation over a commutative ring `k`, as `k`-linear equivalences.

## Main results

* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_smul` and
  `explicitH2AddEquivContinuousCohomology_smul`: the additive comparisons commute with the scalars.
## References

The design of defining the cohomology once and supplying the `R`-module structures by instances
follows David Loeffler's advice; see the references in
`TauCeti.RepresentationTheory.Homological.ContCohomology.ScalarAction`. The additive comparisons
made linear here are those of the existing Tau Ceti file
`TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison`.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u w

section Int

variable {R : Type w} [Semiring R] {G M : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [SMulCommClass G R M]

/-- **The degree-one comparison commutes with the scalars.** -/
theorem explicitH1AddEquivContinuousCohomology_smul (r : R) (x : H1 G M) :
    explicitH1AddEquivContinuousCohomology G M (r • x) =
      r • explicitH1AddEquivContinuousCohomology G M x := by
  -- `r • ·` as an equivariant map of `M`, which needs the scalars on the left
  have := SMulCommClass.symm G R M
  have hx : r • x = explicitCoeff1 G M (SMulCommClass.toDistribMulActionHom G M r)
      continuous_of_discreteTopology x := by
    rw [H1.smul_def, explicitCoeff1_eq_explicitMap1]
    exact DFunLike.congr_fun (explicitMap1_congr_of_eq G M G M _ _ _ _ rfl
      (AddMonoidHom.ext fun _ ↦ rfl)) x
  rw [hx, ← explicitH1AddEquivContinuousCohomology_coeffMap,
    ofDiscreteModuleMap_toDistribMulActionHom,
    ContinuousCohomology.smul_def]

variable (R G M) in
/-- **The explicit `H¹(G, M)` is `continuousCohomology 1 (ofDiscreteModule ℤ G M)` as an
`R`-module**, for a discrete `G`-module `M` that is an `R`-module with the action of `G` commuting
with the scalars: the `R`-linear form of `explicitH1AddEquivContinuousCohomology`. -/
noncomputable def explicitH1LinearEquivContinuousCohomology :
    H1 G M ≃ₗ[R] continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  { explicitH1AddEquivContinuousCohomology G M with
    map_smul' := explicitH1AddEquivContinuousCohomology_smul }

/-- The linear comparison in degree one acts as the additive comparison. -/
@[simp]
theorem explicitH1LinearEquivContinuousCohomology_apply (x : H1 G M) :
    explicitH1LinearEquivContinuousCohomology R G M x =
      explicitH1AddEquivContinuousCohomology G M x :=
  (rfl)

/-- The underlying additive equivalence of the linear comparison in degree one is
`explicitH1AddEquivContinuousCohomology`. -/
@[simp]
theorem explicitH1LinearEquivContinuousCohomology_toAddEquiv :
    (explicitH1LinearEquivContinuousCohomology R G M).toAddEquiv =
      explicitH1AddEquivContinuousCohomology G M :=
  (rfl)

variable [LocallyCompactSpace G]

/-- **The degree-two comparison commutes with the scalars.** -/
theorem explicitH2AddEquivContinuousCohomology_smul (r : R) (x : H2 G M) :
    explicitH2AddEquivContinuousCohomology G M (r • x) =
      r • explicitH2AddEquivContinuousCohomology G M x := by
  -- `r • ·` as an equivariant map of `M`, which needs the scalars on the left
  have := SMulCommClass.symm G R M
  have hx : r • x = explicitCoeff2 G M (SMulCommClass.toDistribMulActionHom G M r)
      continuous_of_discreteTopology x := by
    rw [H2.smul_def, explicitCoeff2_eq_explicitMap2]
    exact DFunLike.congr_fun (explicitMap2_congr_of_eq G M G M _ _ _ _ rfl
      (AddMonoidHom.ext fun _ ↦ rfl)) x
  rw [hx, ← explicitH2AddEquivContinuousCohomology_coeffMap,
    ofDiscreteModuleMap_toDistribMulActionHom,
    ContinuousCohomology.smul_def]

variable (R G M) in
/-- **The explicit `H²(G, M)` is `continuousCohomology 2 (ofDiscreteModule ℤ G M)` as an
`R`-module**, for a locally compact `G`: the `R`-linear form of
`explicitH2AddEquivContinuousCohomology`. -/
noncomputable def explicitH2LinearEquivContinuousCohomology :
    H2 G M ≃ₗ[R] continuousCohomology 2 (ofDiscreteModule ℤ G M) :=
  { explicitH2AddEquivContinuousCohomology G M with
    map_smul' := explicitH2AddEquivContinuousCohomology_smul }

/-- The linear comparison in degree two acts as the additive comparison. -/
@[simp]
theorem explicitH2LinearEquivContinuousCohomology_apply (x : H2 G M) :
    explicitH2LinearEquivContinuousCohomology R G M x =
      explicitH2AddEquivContinuousCohomology G M x :=
  (rfl)

/-- The underlying additive equivalence of the linear comparison in degree two is
`explicitH2AddEquivContinuousCohomology`. -/
@[simp]
theorem explicitH2LinearEquivContinuousCohomology_toAddEquiv :
    (explicitH2LinearEquivContinuousCohomology R G M).toAddEquiv =
      explicitH2AddEquivContinuousCohomology G M :=
  (rfl)

end Int

section OfDiscrete

/-! ### Discrete representations over a commutative ring -/

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {k : Type w} [CommRing k] [TopologicalSpace k] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep.{u} k G) [DiscreteTopology X.V]
  [ContinuousSMul G X.V]

/-- **The explicit `H¹` of the carrier of a discrete smooth `X : TopRep k G` is
`continuousCohomology 1 X` as a `k`-module**: the `k`-linear form of
`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete`. -/
noncomputable def _root_.TopRep.explicitH1LinearEquivContinuousCohomologyOfDiscrete :
    H1 G X.V ≃ₗ[k] continuousCohomology 1 X :=
  (explicitH1LinearEquivContinuousCohomology k G X.V).trans
    (ofDiscreteModuleRestrictScalarsIntLinearEquiv X 1)

/-- The linear comparison for a discrete representation acts as the additive comparison. -/
@[simp]
theorem _root_.TopRep.explicitH1LinearEquivContinuousCohomologyOfDiscrete_apply (x : H1 G X.V) :
    X.explicitH1LinearEquivContinuousCohomologyOfDiscrete x =
      X.explicitH1AddEquivContinuousCohomologyOfDiscrete x := by
  rw [TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_apply,
    TopRep.explicitH1LinearEquivContinuousCohomologyOfDiscrete, LinearEquiv.trans_apply,
    ofDiscreteModuleRestrictScalarsIntLinearEquiv_apply,
    explicitH1LinearEquivContinuousCohomology_apply]

/-- **The explicit `H²` of the carrier of a discrete smooth `X : TopRep k G` is
`continuousCohomology 2 X` as a `k`-module**, for a locally compact `G`: the `k`-linear form of
`TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete`. -/
noncomputable def _root_.TopRep.explicitH2LinearEquivContinuousCohomologyOfDiscrete
    [LocallyCompactSpace G] : H2 G X.V ≃ₗ[k] continuousCohomology 2 X :=
  (explicitH2LinearEquivContinuousCohomology k G X.V).trans
    (ofDiscreteModuleRestrictScalarsIntLinearEquiv X 2)

/-- The linear comparison for a discrete representation acts as the additive comparison. -/
@[simp]
theorem _root_.TopRep.explicitH2LinearEquivContinuousCohomologyOfDiscrete_apply
    [LocallyCompactSpace G] (x : H2 G X.V) :
    X.explicitH2LinearEquivContinuousCohomologyOfDiscrete x =
      X.explicitH2AddEquivContinuousCohomologyOfDiscrete x := by
  rw [TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply,
    TopRep.explicitH2LinearEquivContinuousCohomologyOfDiscrete, LinearEquiv.trans_apply,
    ofDiscreteModuleRestrictScalarsIntLinearEquiv_apply,
    explicitH2LinearEquivContinuousCohomology_apply]

end OfDiscrete

end TauCeti.ContCohomology
