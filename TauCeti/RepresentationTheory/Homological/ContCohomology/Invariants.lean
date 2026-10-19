/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Invariants
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
public import TauCeti.Topology.Algebra.GroupAction.FixedPoints

/-!
# Invariant coefficients for continuous cohomology

For a normal subgroup `H` of `G` acting distributively on an additive group `M`, the invariants
`M ^ H` carry a distributive action of `G ⧸ H`. Over a profinite `G` with `H` open normal, these
are the coefficients of the finite-quotient system computing continuous cohomology. Shrinking
`H` enlarges `M ^ H` along transition inclusions. For arbitrary normal `H`, the quotient action
also supplies the coefficients of inflation.

The invariant subgroup is Mathlib's `FixedPoints.addSubgroup H M`. Its algebraic actions,
inclusions and pairings are supplied by `TauCeti/GroupTheory/GroupAction/FixedPoints.lean`, and
their topology by `TauCeti/Topology/Algebra/GroupAction/FixedPoints.lean`. This file provides the
compatibility with the continuous finite-quotient maps and the discrete-module dictionary.

## Main results

* `TauCeti.ContCohomology.fixedPointsInclusion_continuousFiniteQuotientMap_smul`: for open normal
  subgroups `V ≤ U`, the inclusion `M^U → M^V` is equivariant along the continuous quotient map
  `G ⧸ V → G ⧸ U`. This holds for additive monoids with distributive action.
* `TauCeti.ofDiscreteModuleQuotient`: the coefficient dictionary identifies the explicit
  fixed-point module with `TopRep.quotientToInvariants`, preserving the underlying coefficients.
-/

public section

open CategoryTheory MulAction

namespace TauCeti

namespace ContCohomology

section FiniteQuotient

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : Type*) [AddMonoid M] [DistribMulAction G M]
variable {U V : OpenNormalSubgroup G}

/-- The coefficient inclusion `M^U → M^V` is equivariant after restriction along the quotient
homomorphism `G ⧸ V → G ⧸ U`. -/
@[simp]
theorem fixedPointsInclusion_continuousFiniteQuotientMap_smul (hVU : V ≤ U)
    (q : G ⧸ V.toSubgroup)
    (m : FixedPoints.addSubmonoid U.toSubgroup M) :
    fixedPointsInclusion hVU (continuousFiniteQuotientMap G hVU q • m) =
      q • fixedPointsInclusion hVU m := by
  induction q using QuotientGroup.induction_on with
  | H g => simp

end FiniteQuotient

end ContCohomology

section Dictionary

variable (G : Type*) [Group G]
variable (M : Type*) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M]

/-- **The coefficient dictionary commutes with quotient invariants.** The explicit fixed-point
module `M^H`, regarded as a discrete module over `G ⧸ H`, maps canonically to the invariants of
the restricted canonical object. Its underlying function preserves the coefficient in `M`; only
the two equivalent proofs of invariance differ.

This is the coefficient morphism used to compare explicit and canonical inflation. -/
def ofDiscreteModuleQuotient (H : Subgroup G) [H.Normal] :
    ofDiscreteModule ℤ (G ⧸ H) (FixedPoints.addSubgroup H M) ⟶
      TopRep.quotientToInvariants (ofDiscreteModule ℤ G M) H := by
  let _ : IsTopologicalAddGroup M := isTopologicalAddGroup_of_discreteTopology
  let π : ContRepresentation ℤ H M := (ofDiscreteModule ℤ G M).ρ.restrict H.subtype
  let h : ∀ m, m ∈ π.invariants ↔ m ∈ FixedPoints.addSubgroup H M := fun m ↦
    (ContRepresentation.mem_invariants m).trans (FixedPoints.mem_addSubgroup H M m).symm
  let f := ((FixedPoints.addSubgroup H M).continuousLinearEquivInvariants π h).toContinuousLinearMap
  have f_apply (x : FixedPoints.addSubgroup H M) : (f x).1 = (x : M) :=
    AddSubgroup.continuousLinearEquivInvariants_val _ π h x
  exact TopRep.ofHom
    { toContinuousLinearMap := f
      isIntertwining' q := by
        induction q using QuotientGroup.induction_on with
        | H g =>
          refine ContinuousLinearMap.ext fun m ↦ Subtype.ext ?_
          -- Apply the composed operators and cross the categorical carrier wrappers once.
          change
            (f ((ofDiscreteModule ℤ (G ⧸ H) (FixedPoints.addSubgroup H M)).ρ
                (QuotientGroup.mk g) m)).1 =
              (((ofDiscreteModule ℤ G M).ρ.quotientToInvariants H)
                (QuotientGroup.mk g) (f m)).1
          simp only [ofDiscreteModule_ρ_apply_apply, f_apply,
            coe_quotient_smul_fixedPoints_addSubgroup, coe_smul_fixedPoints_addSubgroup]
          -- State the public action formula over M: simp does not unfold the TopRep carrier.
          have haction :
              ((((ofDiscreteModule ℤ G M).ρ.quotientToInvariants H)
                (QuotientGroup.mk g) (f m)).1 : M) =
                ((ofDiscreteModule ℤ G M).ρ g (f m).1 : M) :=
            ContRepresentation.coe_quotientToInvariants_mk_apply
              (ofDiscreteModule ℤ G M).ρ H g (f m)
          simp only [ofDiscreteModule_ρ_apply_apply (R := ℤ) (G := G) (M := M),
            f_apply] at haction
          exact haction.symm }

-- `simp` reduces the carrier of the `abbrev` `TopRep.quotientToInvariants` in implicit type
-- arguments before it looks a term up, so the left-hand side is stated through `dsimp% only`, as
-- in #8315.
/-- The quotient-invariants dictionary morphism preserves the underlying coefficient. -/
@[simp]
theorem ofDiscreteModuleQuotient_apply (H : Subgroup G) [H.Normal]
    (m : FixedPoints.addSubgroup H M) :
    (dsimp% only ((ofDiscreteModuleQuotient G M H m).1)) = (m : M) := by
  let _ : IsTopologicalAddGroup M := isTopologicalAddGroup_of_discreteTopology
  let π : ContRepresentation ℤ H M := (ofDiscreteModule ℤ G M).ρ.restrict H.subtype
  let h : ∀ m, m ∈ π.invariants ↔ m ∈ FixedPoints.addSubgroup H M := fun m ↦
    (ContRepresentation.mem_invariants m).trans (FixedPoints.mem_addSubgroup H M m).symm
  exact AddSubgroup.continuousLinearEquivInvariants_val (FixedPoints.addSubgroup H M) π h m

end Dictionary

end TauCeti
