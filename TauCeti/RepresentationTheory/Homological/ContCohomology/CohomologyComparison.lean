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
cochains with the canonical homogeneous ones, `CocycleComparison.lean` cuts that down to the
cocycles in degree two, and `TauCeti.ContCohomology.cocycleEquiv1` does the same in degree one
here. What remains, and is the content of this file, is the passage from cocycles to classes: the
canonical homology is the cokernel of `HomologicalComplex.toCycles`, so a cocycle has trivial
canonical class exactly when it is a canonical boundary, and
`TauCeti.ContCohomology.mem_B1_iff_cocycleEquiv1_mem_range` together with its landed degree-two
counterpart says that those are precisely the explicit coboundaries.

The comparison is stated twice, and the two statements are not interchangeable. The additive
equivalence holds over an arbitrary topological group in degree one, and over a locally compact one
in degree two, the local compactness being what supplies `ContinuousMap.uncurry` for the degree-two
cochain comparison. The isomorphism in `TopModuleCat ℤ` needs `G` compact, and its source is the
**discrete** carrier `TauCeti.ContCohomology.DiscreteH1`, not the quotient topology that `H¹`
inherits from the pointwise topology on `G → M`: that inherited topology is not discrete for an
infinite profinite `G`, whereas the canonical side is, by
`TauCeti.discreteTopology_continuousCohomology`. A comparison stated in `TopModuleCat ℤ` against
the inherited topology would be false while its underlying additive statement stayed true, which
is why the discrete synonyms exist.

## Main definitions

* `TauCeti.ContCohomology.cocycleEquiv1`: continuous inhomogeneous one-cocycles are the cycles of
  the canonical homogeneous complex in degree one.
* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` and
  `explicitH2AddEquivContinuousCohomology`: the comparisons as additive equivalences.
* `TauCeti.ContCohomology.explicitH1IsoContinuousCohomology` and
  `explicitH2IsoContinuousCohomology`: the comparisons as isomorphisms in `TopModuleCat ℤ`.

## Main results

* `TauCeti.ContCohomology.mem_B1_iff_cocycleEquiv1_mem_range`: the cycle-level dictionary between
  explicit coboundaries and canonical boundaries in degree one.
* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_apply` and
  `explicitH2AddEquivContinuousCohomology_apply`: the comparisons send the class of an explicit
  cocycle to the homology class of the cocycle it corresponds to.

## Roadmap

This implements the degree-one and degree-two parts of the "inhomogeneous against canonical"
milestone of Layer 3 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`, whose `Suggested.lean` fixes the names
`explicitH1IsoContinuousCohomology`, `explicitH2IsoContinuousCohomology` and
`explicitH1AddEquivContinuousCohomology`. Degree zero of the same milestone, which needs neither
the cochain comparison nor any hypothesis on `G`, is in the sibling file
`ContinuousCohomologyIso.lean`; the transports of restriction, inflation and the coefficient maps
across the isomorphisms built here are separate milestones of the same layer and are not in this
file.

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

/-! ### Degree one -/

/-- Continuous one-cocycles in inhomogeneous coordinates are the cycles of the canonical
homogeneous cochain complex. The forward formula is `g • c (g⁻¹ * h)`; the inverse evaluates at
`(1, g)`.

This is the degree-one counterpart of `TauCeti.ContCohomology.cocycleEquiv2`, and unlike it needs
no local compactness: the degree-one cochain comparison is a plain currying, whose inverse is
evaluation. -/
noncomputable def cocycleEquiv1 :
    Z1 G M ≃+ _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 1 :=
  ({ toFun c := ⟨cochainEquiv1 G M ⟨c.val, Z1_le_C1 G M c.property⟩,
        (d_cochainEquiv1_eq_zero_iff G M _).mpr c.property⟩
     invFun c := ⟨((cochainEquiv1 G M).symm c.val).val,
        (d_cochainEquiv1_eq_zero_iff G M _).mp (by
          rw [AddEquiv.apply_symm_apply]
          exact c.property)⟩
     left_inv c := by
       apply Subtype.ext
       exact congrArg (fun b : C1 G M => b.val)
         ((cochainEquiv1 G M).symm_apply_apply ⟨c.val, Z1_le_C1 G M c.property⟩)
     right_inv c := by
       apply Subtype.ext
       exact (cochainEquiv1 G M).apply_symm_apply c.val
     map_add' c d := by
       apply Subtype.ext
       exact (cochainEquiv1 G M).map_add
         ⟨c.val, Z1_le_C1 G M c.property⟩ ⟨d.val, Z1_le_C1 G M d.property⟩ } :
      Z1 G M ≃+ TopModuleCat.ker
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2)).trans
    (Limits.IsLimit.conePointUniqueUpToIso (TopModuleCat.isLimitKer _)
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).cyclesIsKernel 1 2
        (by simp))).toContinuousLinearEquiv.toAddEquiv

/-- The inclusion of a compared one-cocycle is the existing cochain comparison. -/
@[simp]
theorem iCycles_cocycleEquiv1 (c : Z1 G M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).sc 1).iCycles.hom
        (cocycleEquiv1 G M c) =
      cochainEquiv1 G M ⟨c.val, Z1_le_C1 G M c.property⟩ :=
  ConcreteCategory.congr_hom
    (Limits.IsLimit.conePointUniqueUpToIso_hom_comp (TopModuleCat.isLimitKer _)
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).cyclesIsKernel 1 2 (by simp))
      Limits.WalkingParallelPair.zero) _

/-- The inverse one-cocycle comparison reads the canonical cocycle at `(1, g)`. -/
@[simp]
theorem cocycleEquiv1_symm_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 1) (g : G) :
    ((cocycleEquiv1 G M).symm c).val g =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 1 c).val 1 g := by
  obtain ⟨c, rfl⟩ := (cocycleEquiv1 G M).surjective c
  -- Read the short-complex inclusion as the inclusion of the homogeneous complex.
  have e : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 1
      (cocycleEquiv1 G M c) =
      cochainEquiv1 G M ⟨c.val, Z1_le_C1 G M c.property⟩ := iCycles_cocycleEquiv1 G M c
  rw [AddEquiv.symm_apply_apply, e, cochainEquiv1_apply]
  simp

/-- The comparison sends the explicit coboundary of an element of `M` to its canonical boundary,
with the same primitive under the degree-zero cochain comparison. -/
theorem cocycleEquiv1_d0 (m : M) :
    cocycleEquiv1 G M ⟨d0 G M m, B1_le_Z1 G M (d0_mem_B1 m)⟩ =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).toCycles 0 1
        (cochainEquiv0 G M m) := by
  apply (cocycleEquiv1 G M).symm.injective
  apply Subtype.ext
  funext g
  rw [AddEquiv.symm_apply_apply, cocycleEquiv1_symm_apply]
  have e := ConcreteCategory.congr_hom
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).toCycles_i 0 1)
    (cochainEquiv0 G M m)
  simp only [ConcreteCategory.comp_apply] at e
  rw [e, d_cochainEquiv0]
  simp

/-- A continuous one-cocycle is an explicit coboundary exactly when its canonical image is a
boundary. -/
theorem mem_B1_iff_cocycleEquiv1_mem_range (c : Z1 G M) :
    c.val ∈ B1 G M ↔ cocycleEquiv1 G M c ∈ Set.range
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).toCycles 0 1) := by
  constructor
  · intro hc
    obtain ⟨m, hm⟩ := mem_B1_iff.mp hc
    refine ⟨cochainEquiv0 G M m, ?_⟩
    rw [← cocycleEquiv1_d0]
    exact congrArg (cocycleEquiv1 G M) (Subtype.ext (funext fun g => (d0_apply m g).trans (hm g)))
  · rintro ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := (cochainEquiv0 G M).surjective b
    rw [← cocycleEquiv1_d0] at hb
    have hd := congrArg Subtype.val ((cocycleEquiv1 G M).injective hb)
    exact mem_B1_iff.mpr ⟨b, fun g => (d0_apply b g).symm.trans (congrFun hd g)⟩

/-- The canonical homology class of a continuous one-cocycle. -/
private noncomputable def cohomologyClass1 :
    Z1 G M →+ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ
      1).hom.toLinearMap.toAddMonoidHom.comp (cocycleEquiv1 G M).toAddMonoidHom

private theorem cohomologyClass1_eq_zero_iff (c : Z1 G M) :
    cohomologyClass1 G M c = 0 ↔ (c : G → M) ∈ B1 G M := by
  rw [mem_B1_iff_cocycleEquiv1_mem_range]
  exact HomologicalComplex.homologyπ_eq_zero_iff _ 1 (by simp)

private noncomputable def explicitH1Lift :
    H1 G M →+ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  QuotientAddGroup.lift _ (cohomologyClass1 G M) fun c hc =>
    (cohomologyClass1_eq_zero_iff G M c).mpr (AddSubgroup.mem_addSubgroupOf.mp hc)

private theorem explicitH1Lift_bijective : Function.Bijective (explicitH1Lift G M) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    refine fun q => QuotientAddGroup.induction_on q fun c hq => ?_
    exact H1pi_eq_zero_iff.mpr ((cohomologyClass1_eq_zero_iff G M c).mp hq)
  · intro y
    obtain ⟨x, hx⟩ := HomologicalComplex.homologyπ_surjective _ 1 y
    refine ⟨(((cocycleEquiv1 G M).symm x : Z1 G M) : H1 G M), ?_⟩
    change (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1
      (cocycleEquiv1 G M ((cocycleEquiv1 G M).symm x)) = y
    rw [AddEquiv.apply_symm_apply]
    exact hx

/-- **Layer 3, degree one against the canonical object, additively.** The explicit `H¹(G, M)` is
Mathlib's `continuousCohomology 1` of the canonical object attached to `M`.

No hypothesis on `G` beyond being a topological group is used: the cochain comparison in degree one
is a currying with no local-compactness condition, and passing to a subquotient needs none either.
The companion `TauCeti.ContCohomology.explicitH1IsoContinuousCohomology` upgrades this to
`TopModuleCat ℤ`, and that upgrade does need `G` compact. -/
noncomputable def explicitH1AddEquivContinuousCohomology :
    H1 G M ≃+ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  AddEquiv.ofBijective (explicitH1Lift G M) (explicitH1Lift_bijective G M)

/-- The comparison sends the class of a continuous one-cocycle to the canonical homology class of
the cocycle it corresponds to. -/
@[simp]
theorem explicitH1AddEquivContinuousCohomology_apply (c : Z1 G M) :
    explicitH1AddEquivContinuousCohomology G M (c : H1 G M) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1
        (cocycleEquiv1 G M c) := (rfl)

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

private noncomputable def explicitH2Lift :
    H2 G M →+ continuousCohomology 2 (ofDiscreteModule ℤ G M) :=
  QuotientAddGroup.lift _ (cohomologyClass2 G M) fun c hc =>
    (cohomologyClass2_eq_zero_iff G M c).mpr (AddSubgroup.mem_addSubgroupOf.mp hc)

private theorem explicitH2Lift_bijective : Function.Bijective (explicitH2Lift G M) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    refine fun q => QuotientAddGroup.induction_on q fun c hq => ?_
    exact H2pi_eq_zero_iff.mpr ((cohomologyClass2_eq_zero_iff G M c).mp hq)
  · intro y
    obtain ⟨x, hx⟩ := HomologicalComplex.homologyπ_surjective _ 2 y
    refine ⟨(((cocycleEquiv2 G M).symm x : Z2 G M) : H2 G M), ?_⟩
    change (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2
      (cocycleEquiv2 G M ((cocycleEquiv2 G M).symm x)) = y
    rw [AddEquiv.apply_symm_apply]
    exact hx

/-- **Layer 3, degree two against the canonical object, additively.** The explicit `H²(G, M)` is
Mathlib's `continuousCohomology 2` of the canonical object attached to `M`.

The group is locally compact because the inverse of the degree-two cochain comparison uncurries,
which is where the compact-open exponential law enters; a profinite group qualifies. -/
noncomputable def explicitH2AddEquivContinuousCohomology :
    H2 G M ≃+ continuousCohomology 2 (ofDiscreteModule ℤ G M) :=
  AddEquiv.ofBijective (explicitH2Lift G M) (explicitH2Lift_bijective G M)

/-- The comparison sends the class of a continuous two-cocycle to the canonical homology class of
the cocycle it corresponds to. -/
@[simp]
theorem explicitH2AddEquivContinuousCohomology_apply (c : Z2 G M) :
    explicitH2AddEquivContinuousCohomology G M (c : H2 G M) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2
        (cocycleEquiv2 G M c) := (rfl)

end LocallyCompact

/-! ### The comparisons as isomorphisms of topological modules -/

section Compact

/-! Compactness of `G` enters only here, and only through
`TauCeti.discreteTopology_continuousCohomology`: it makes the canonical side discrete, so that the
additive equivalences above are automatically homeomorphisms onto it. Local compactness, which
degree two needs, follows from compactness for a topological group. -/

variable [CompactSpace G]

/-- **Layer 3, degree one against the canonical object,** in `TopModuleCat ℤ`. The source is the
discrete carrier `TauCeti.ContCohomology.DiscreteH1`, and not `H¹` with the quotient topology it
inherits from the pointwise topology on `G → M`, which is not discrete for an infinite profinite
`G`.

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

/-- **Layer 3, degree two against the canonical object,** in `TopModuleCat ℤ`. -/
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

end Compact

end TauCeti.ContCohomology
