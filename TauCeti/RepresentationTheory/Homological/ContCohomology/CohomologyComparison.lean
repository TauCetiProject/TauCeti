/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CocycleComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete

/-!
# The explicit model against the canonical object, in degrees one and two

The explicit low-degree complex presents `H¹(G, M)` and `H²(G, M)` as `Z¹/B¹` and `Z²/B²`, honest
subquotients of the continuous functions on `G` and on `G × G`, while the canonical object is
Mathlib's `continuousCohomology n X` for `X` the image `TauCeti.ofDiscreteModule ℤ G M` of `M`
under the coefficient dictionary. This file identifies the two in degrees one and two.

The passage happens one level at a time. `CochainComparison.lean` identifies the inhomogeneous
cochains with the canonical homogeneous ones, and `CocycleComparison.lean` cuts that down to the
cocycles in degrees one and two. What remains, and is the content of this file, is the passage from
cocycles to classes: the
canonical homology is the cokernel of `HomologicalComplex.toCycles`, so a cocycle has trivial
canonical class exactly when it is a canonical boundary, and
`TauCeti.ContCohomology.mem_B1_iff_cocycleEquiv1_mem_range` together with its landed degree-two
counterpart says that those are precisely the explicit coboundaries.

The comparison is stated twice, and the two statements are not interchangeable. The additive
equivalence holds over an arbitrary topological group in degree one, and over a locally compact one
in degree two, the local compactness being what supplies `ContinuousMap.uncurry` for the degree-two
cochain comparison. The isomorphism in `TopModuleCat ℤ` needs `G` compact, and its source is the
**discrete** carrier `TauCeti.ContCohomology.DiscreteH1`, not the quotient topology that `H¹`
inherits from the pointwise topology on `G → M`: that inherited topology is not discrete in
general, so discreteness cannot be assumed, whereas the canonical side is discrete by
`TauCeti.discreteTopology_continuousCohomology`. A comparison stated in `TopModuleCat ℤ` against
the inherited topology would be false while its underlying additive statement stayed true, which
is why the discrete synonyms exist.

## Main definitions

* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` and
  `explicitH2AddEquivContinuousCohomology`: the comparisons as additive equivalences.
* `TauCeti.ContCohomology.explicitH1IsoContinuousCohomology` and
  `explicitH2IsoContinuousCohomology`: the comparisons as isomorphisms in `TopModuleCat ℤ`.

## Main results

* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_apply` and
  `explicitH2AddEquivContinuousCohomology_apply`: the comparisons send the class of an explicit
  cocycle to the homology class of the cocycle it corresponds to.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  identification of the inhomogeneous description of continuous cohomology with the homogeneous
  one. The isomorphisms built here are the degree-one and degree-two cases.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The canonical homology class of a continuous one-cocycle. -/
private noncomputable def cohomologyClass1 :
    Z1 G M →+ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ
      1).hom.toLinearMap.toAddMonoidHom.comp (cocycleEquiv1 G M).toAddMonoidHom

private theorem cohomologyClass1_eq_zero_iff (c : Z1 G M) :
    cohomologyClass1 G M c = 0 ↔ (c : G → M) ∈ B1 G M := by
  rw [mem_B1_iff_cocycleEquiv1_mem_range]
  exact HomologicalComplex.homologyπ_eq_zero_iff _ 1 (by simp)

private theorem cohomologyClass1_surjective : Function.Surjective (cohomologyClass1 G M) := by
  intro y
  obtain ⟨x, hx⟩ := HomologicalComplex.homologyπ_surjective _ 1 y
  refine ⟨(cocycleEquiv1 G M).symm x, ?_⟩
  simpa [cohomologyClass1] using hx

private theorem cohomologyClass1_ker :
    (B1 G M).addSubgroupOf (Z1 G M) = (cohomologyClass1 G M).ker := by
  ext c
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, cohomologyClass1_eq_zero_iff]

/-- The explicit `H¹(G, M)` is Mathlib's `continuousCohomology 1` of the canonical object attached
to `M`, as an additive equivalence.

No hypothesis on `G` beyond being a topological group is used: the cochain comparison in degree one
is a currying with no local-compactness condition, and passing to a subquotient needs none either.
The companion `TauCeti.ContCohomology.explicitH1IsoContinuousCohomology` upgrades this to
`TopModuleCat ℤ`, and that upgrade does need `G` compact. -/
noncomputable def explicitH1AddEquivContinuousCohomology :
    H1 G M ≃+ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  QuotientAddGroup.liftEquiv _ (cohomologyClass1_surjective G M) (cohomologyClass1_ker G M)

/-- The comparison sends the class of a continuous one-cocycle to the canonical homology class of
the cocycle it corresponds to. -/
@[simp]
theorem explicitH1AddEquivContinuousCohomology_apply (c : Z1 G M) :
    explicitH1AddEquivContinuousCohomology G M (c : H1 G M) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1
        (cocycleEquiv1 G M c) := by
  exact QuotientAddGroup.liftEquiv_coe _ _ _ c

/-- The inverse comparison sends a canonical homology class to the explicit class of the
corresponding inhomogeneous cocycle. -/
@[simp]
theorem explicitH1AddEquivContinuousCohomology_symm_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 1) :
    (explicitH1AddEquivContinuousCohomology G M).symm
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1 c) =
      (((cocycleEquiv1 G M).symm c : Z1 G M) : H1 G M) := by
  apply (explicitH1AddEquivContinuousCohomology G M).injective
  rw [AddEquiv.apply_symm_apply, explicitH1AddEquivContinuousCohomology_apply,
    AddEquiv.apply_symm_apply]

/-! ### Degree two -/

section LocallyCompact

variable [LocallyCompactSpace G]

/-- The canonical homology class of a continuous two-cocycle. -/
private noncomputable def cohomologyClass2 :
    Z2 G M →+ continuousCohomology 2 (ofDiscreteModule ℤ G M) :=
  ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ
      2).hom.toLinearMap.toAddMonoidHom.comp (cocycleEquiv2 G M).toAddMonoidHom

private theorem cohomologyClass2_eq_zero_iff (c : Z2 G M) :
    cohomologyClass2 G M c = 0 ↔ (c : G × G → M) ∈ B2 G M := by
  rw [mem_B2_iff_cocycleEquiv2_mem_range]
  exact HomologicalComplex.homologyπ_eq_zero_iff _ 2 (by simp)

private theorem cohomologyClass2_surjective : Function.Surjective (cohomologyClass2 G M) := by
  intro y
  obtain ⟨x, hx⟩ := HomologicalComplex.homologyπ_surjective _ 2 y
  refine ⟨(cocycleEquiv2 G M).symm x, ?_⟩
  simpa [cohomologyClass2] using hx

private theorem cohomologyClass2_ker :
    (B2 G M).addSubgroupOf (Z2 G M) = (cohomologyClass2 G M).ker := by
  ext c
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, cohomologyClass2_eq_zero_iff]

/-- The explicit `H²(G, M)` is Mathlib's `continuousCohomology 2` of the canonical object attached
to `M`, as an additive equivalence.

The group is locally compact because the inverse of the degree-two cochain comparison uncurries,
which is where the compact-open exponential law enters; a profinite group qualifies. -/
noncomputable def explicitH2AddEquivContinuousCohomology :
    H2 G M ≃+ continuousCohomology 2 (ofDiscreteModule ℤ G M) :=
  QuotientAddGroup.liftEquiv _ (cohomologyClass2_surjective G M) (cohomologyClass2_ker G M)

/-- The comparison sends the class of a continuous two-cocycle to the canonical homology class of
the cocycle it corresponds to. -/
@[simp]
theorem explicitH2AddEquivContinuousCohomology_apply (c : Z2 G M) :
    explicitH2AddEquivContinuousCohomology G M (c : H2 G M) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2
        (cocycleEquiv2 G M c) := by
  exact QuotientAddGroup.liftEquiv_coe _ _ _ c

/-- The inverse comparison sends a canonical homology class to the explicit class of the
corresponding inhomogeneous cocycle. -/
@[simp]
theorem explicitH2AddEquivContinuousCohomology_symm_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2) :
    (explicitH2AddEquivContinuousCohomology G M).symm
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2 c) =
      (((cocycleEquiv2 G M).symm c : Z2 G M) : H2 G M) := by
  apply (explicitH2AddEquivContinuousCohomology G M).injective
  rw [AddEquiv.apply_symm_apply, explicitH2AddEquivContinuousCohomology_apply,
    AddEquiv.apply_symm_apply]

end LocallyCompact

/-! ### The comparisons as isomorphisms of topological modules -/

section Compact

/-! Compactness of `G` enters only here, and only through
`TauCeti.discreteTopology_continuousCohomology`: it makes the canonical side discrete, so that the
additive equivalences above are automatically homeomorphisms onto it. Local compactness, which
degree two needs, follows from compactness for a topological group. -/

variable [CompactSpace G]

/-- The degree-one comparison in `TopModuleCat ℤ`. The source is the discrete carrier
`TauCeti.ContCohomology.DiscreteH1`, and not `H¹` with the quotient topology inherited from the
pointwise topology on `G → M`, which is not discrete in general.

The canonical side is the image of `M` under the coefficient dictionary and **not** an arbitrary
object of `TopRep ℤ G`: a general object need not be discrete, and the explicit complex is not a
description of its cohomology. -/
noncomputable def explicitH1IsoContinuousCohomology :
    TopModuleCat.of ℤ (DiscreteH1 G M) ≅ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  TopModuleCat.ofIso
    { ((discreteH1Equiv G M).trans
        (explicitH1AddEquivContinuousCohomology G M)).toIntLinearEquiv with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

-- Not `@[simp]`: the comparison is the intended normal form, and this lemma unfolds it.
/-- The degree-one isomorphism of topological modules is the additive comparison, read on the
discrete carrier. -/
theorem explicitH1IsoContinuousCohomology_hom_apply (x : DiscreteH1 G M) :
    (explicitH1IsoContinuousCohomology G M).hom x =
      explicitH1AddEquivContinuousCohomology G M (discreteH1Equiv G M x) := (rfl)

/-- The inverse degree-one isomorphism sends a canonical homology class to the discrete carrier
of the corresponding explicit cocycle class. -/
@[simp]
theorem explicitH1IsoContinuousCohomology_inv_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 1) :
    (explicitH1IsoContinuousCohomology G M).inv
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1 c) =
      (discreteH1Equiv G M).symm
        (((cocycleEquiv1 G M).symm c : Z1 G M) : H1 G M) := by
  -- Unfold the `TopModuleCat.ofIso` inverse to expose the two composed additive equivalences.
  change (discreteH1Equiv G M).symm
    ((explicitH1AddEquivContinuousCohomology G M).symm
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1 c)) = _
  rw [explicitH1AddEquivContinuousCohomology_symm_apply]

/-- The degree-two comparison in `TopModuleCat ℤ`. -/
noncomputable def explicitH2IsoContinuousCohomology :
    TopModuleCat.of ℤ (DiscreteH2 G M) ≅ continuousCohomology 2 (ofDiscreteModule ℤ G M) :=
  TopModuleCat.ofIso
    { ((discreteH2Equiv G M).trans
        (explicitH2AddEquivContinuousCohomology G M)).toIntLinearEquiv with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

-- Not `@[simp]`: the comparison is the intended normal form, and this lemma unfolds it.
/-- The degree-two isomorphism of topological modules is the additive comparison, read on the
discrete carrier. -/
theorem explicitH2IsoContinuousCohomology_hom_apply (x : DiscreteH2 G M) :
    (explicitH2IsoContinuousCohomology G M).hom x =
      explicitH2AddEquivContinuousCohomology G M (discreteH2Equiv G M x) := (rfl)

/-- The inverse degree-two isomorphism sends a canonical homology class to the discrete carrier
of the corresponding explicit cocycle class. -/
@[simp]
theorem explicitH2IsoContinuousCohomology_inv_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2) :
    (explicitH2IsoContinuousCohomology G M).inv
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2 c) =
      (discreteH2Equiv G M).symm
        (((cocycleEquiv2 G M).symm c : Z2 G M) : H2 G M) := by
  -- Unfold the `TopModuleCat.ofIso` inverse to expose the two composed additive equivalences.
  change (discreteH2Equiv G M).symm
    ((explicitH2AddEquivContinuousCohomology G M).symm
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2 c)) = _
  rw [explicitH2AddEquivContinuousCohomology_symm_apply]

end Compact

end TauCeti.ContCohomology
