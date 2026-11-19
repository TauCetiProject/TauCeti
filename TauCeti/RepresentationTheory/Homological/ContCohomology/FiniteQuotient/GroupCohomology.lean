/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Explicit
public import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso.Map
public import TauCeti.RepresentationTheory.Rep.OfDistribMulAction

/-!
# The explicit finite-quotient transitions in discrete group cohomology

Let `G` be a topological group acting on a discrete additive group `M`. For open normal subgroups
`V ≤ U` there are two descriptions of the transition map `Hⁱ(G ⧸ U, M^U) → Hⁱ(G ⧸ V, M^V)` of
the finite-quotient system, `i = 0, 1, 2`:

* the explicit transitions `explicitFiniteQuotientTransition0`, `explicitFiniteQuotientTransition1`
  and `explicitFiniteQuotientTransition2`, compatible-pair maps of explicit cochains;
* `TauCeti.finiteLevelTransition`, Mathlib's `groupCohomology.map` along a transition pair, on the
  discrete group cohomology of the representations
  `(Rep.ofDistribMulAction ℤ G M).quotientToInvariants U`.

Each finite level `G ⧸ U` is a discrete group, so `explicitH0IsoGroupCohomology`,
`explicitH1IsoGroupCohomology` and `explicitH2IsoGroupCohomology` compare the explicit group
`Hⁱ(G ⧸ U, M^U)` with the group cohomology of `Rep.ofDistribMulAction ℤ (G ⧸ U) (M^U)`, and
`TauCeti.ofDistribMulActionFixedPointsIso` identifies that representation with the quotient
representation on the invariants. This file proves that the resulting levelwise comparisons carry
the explicit transitions to `TauCeti.finiteLevelTransition`, so that the two finite-quotient
systems have the same arrows and not only isomorphic objects.

These comparisons need `G` and `M` in `Type`, because Mathlib's comparison with `groupCohomology`
over `ℤ` does; neither compactness of `G` nor continuity of the action is used.

## Main statements

* `TauCeti.ContCohomology.finiteLevelTransition_explicitH0IsoGroupCohomology`,
  `TauCeti.ContCohomology.finiteLevelTransition_explicitH1IsoGroupCohomology` and
  `TauCeti.ContCohomology.finiteLevelTransition_explicitH2IsoGroupCohomology`: the comparisons in
  degrees zero, one and two intertwine the explicit transitions with `finiteLevelTransition`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.2.5).
* L. Ribes and P. Zalesskii, *Profinite Groups*, Cor. 6.5.6(a).
-/

public section

open CategoryTheory groupCohomology

namespace TauCeti.ContCohomology

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [DistribMulAction G M]
variable {U V : OpenNormalSubgroup G}

/-- The explicit transition pair `(G ⧸ V → G ⧸ U, M^U ↪ M^V)` as a morphism of representations
of `G ⧸ V`. -/
private noncomputable def transitionRepHom (hVU : V ≤ U) :
    Rep.res (continuousFiniteQuotientMap G hVU : G ⧸ V.toSubgroup →* G ⧸ U.toSubgroup)
        (Rep.ofDistribMulAction ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) ⟶
      Rep.ofDistribMulAction ℤ (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
  Rep.ofHom
    { toLinearMap := (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
        FixedPoints.addSubgroup V.toSubgroup M).toIntLinearMap
      -- Elaborated as a tactic block so that the linear map above is known by then.
      isIntertwining' q := LinearMap.ext fun m ↦ by
        exact fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU q m }

private theorem transitionRepHom_hom_apply (hVU : V ≤ U)
    (m : FixedPoints.addSubgroup U.toSubgroup M) :
    (transitionRepHom G M hVU).hom m = fixedPointsInclusion hVU m :=
  (rfl)

/-- The square of representations underlying every degree: the explicit transition pair followed
by the coefficient identification at `V` is the coefficient identification at `U` followed by the
transition pair of `TauCeti.finiteLevelTransition`. -/
private theorem map_transitionRepHom_comp (hVU : V ≤ U) (n : ℕ) :
    groupCohomology.map _ (transitionRepHom G M hVU) n ≫
        groupCohomology.map (MonoidHom.id _)
          (ofDistribMulActionFixedPointsIso M V.toSubgroup).hom n =
      groupCohomology.map (MonoidHom.id _)
          (ofDistribMulActionFixedPointsIso M U.toSubgroup).hom n ≫
        finiteLevelTransition (Rep.ofDistribMulAction ℤ G M) hVU n := by
  rw [finiteLevelTransition_eq_map, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ n
  · refine MonoidHom.ext fun q ↦ ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      exact (continuousFiniteQuotientMap_mk G hVU g).trans (QuotientGroup.mapOfLE_mk hVU g).symm
  · -- Every map in both composites is the identity on the underlying elements of `M`.
    refine LinearMap.ext fun m ↦ Subtype.ext ?_
    simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
      LinearMap.coe_comp, Function.comp_apply, transitionPair_hom_toLinearMap,
      invariantsInclusion_apply_coe]
    -- `simp` cannot use `ofDistribMulActionFixedPointsIso_hom_hom_apply_coe` here, since `m` lives
    -- in the carrier of a restricted representation, so the remaining steps are applied directly.
    exact (ofDistribMulActionFixedPointsIso_hom_hom_apply_coe M V.toSubgroup _).trans
      ((coe_fixedPointsInclusion hVU m).trans
        (ofDistribMulActionFixedPointsIso_hom_hom_apply_coe M U.toSubgroup m).symm)

/-- The degree-zero comparisons with `groupCohomology` carry the explicit finite-quotient transition
to `TauCeti.finiteLevelTransition`. Not `@[simp]`: `simp` first unfolds the comparison by
`explicitH0IsoGroupCohomology_apply`. -/
theorem finiteLevelTransition_explicitH0IsoGroupCohomology (hVU : V ≤ U)
    (x : H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    finiteLevelTransition (Rep.ofDistribMulAction ℤ G M) hVU 0
        (groupCohomology.map (MonoidHom.id _)
          (ofDistribMulActionFixedPointsIso M U.toSubgroup).hom 0
          (explicitH0IsoGroupCohomology _ _ x)) =
      groupCohomology.map (MonoidHom.id _) (ofDistribMulActionFixedPointsIso M V.toSubgroup).hom 0
        (explicitH0IsoGroupCohomology _ _ (explicitFiniteQuotientTransition0 G M U V hVU x)) := by
  refine (ConcreteCategory.congr_hom (map_transitionRepHom_comp G M hVU 0) _).symm.trans ?_
  refine (congrArg _ (explicitH0IsoGroupCohomology_map _ _
    (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) _
    (transitionRepHom_hom_apply G M hVU) x)).trans ?_
  exact congrArg _ (congrArg _
    (DFunLike.congr_fun (explicitFiniteQuotientTransition0_eq_explicitMap0 G M hVU) x).symm)

variable [TopologicalSpace M] [DiscreteTopology M]

/-- The degree-one comparisons with `groupCohomology` carry the explicit finite-quotient transition
to `TauCeti.finiteLevelTransition`. -/
@[simp]
theorem finiteLevelTransition_explicitH1IsoGroupCohomology (hVU : V ≤ U)
    (x : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    finiteLevelTransition (Rep.ofDistribMulAction ℤ G M) hVU 1
        (groupCohomology.map (MonoidHom.id _)
          (ofDistribMulActionFixedPointsIso M U.toSubgroup).hom 1
          (explicitH1IsoGroupCohomology _ _ x)) =
      groupCohomology.map (MonoidHom.id _) (ofDistribMulActionFixedPointsIso M V.toSubgroup).hom 1
        (explicitH1IsoGroupCohomology _ _ (explicitFiniteQuotientTransition1 G M U V hVU x)) := by
  refine (ConcreteCategory.congr_hom (map_transitionRepHom_comp G M hVU 1) _).symm.trans ?_
  refine (congrArg _ (explicitH1IsoGroupCohomology_map _ _ continuous_of_discreteTopology
    (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) _
    (transitionRepHom_hom_apply G M hVU) x)).trans ?_
  exact congrArg _ (congrArg _
    (DFunLike.congr_fun (explicitFiniteQuotientTransition1_eq_explicitMap1 G M hVU) x).symm)

/-- The degree-two comparisons with `groupCohomology` carry the explicit finite-quotient transition
to `TauCeti.finiteLevelTransition`. -/
@[simp]
theorem finiteLevelTransition_explicitH2IsoGroupCohomology (hVU : V ≤ U)
    (x : H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    finiteLevelTransition (Rep.ofDistribMulAction ℤ G M) hVU 2
        (groupCohomology.map (MonoidHom.id _)
          (ofDistribMulActionFixedPointsIso M U.toSubgroup).hom 2
          (explicitH2IsoGroupCohomology _ _ x)) =
      groupCohomology.map (MonoidHom.id _) (ofDistribMulActionFixedPointsIso M V.toSubgroup).hom 2
        (explicitH2IsoGroupCohomology _ _ (explicitFiniteQuotientTransition2 G M U V hVU x)) := by
  refine (ConcreteCategory.congr_hom (map_transitionRepHom_comp G M hVU 2) _).symm.trans ?_
  refine (congrArg _ (explicitH2IsoGroupCohomology_map _ _ continuous_of_discreteTopology
    (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) _
    (transitionRepHom_hom_apply G M hVU) x)).trans ?_
  exact congrArg _ (congrArg _
    (DFunLike.congr_fun (explicitFiniteQuotientTransition2_eq_explicitMap2 G M hVU) x).symm)

end TauCeti.ContCohomology
