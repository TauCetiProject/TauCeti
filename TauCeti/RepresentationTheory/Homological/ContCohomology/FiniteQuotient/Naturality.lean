/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Canonical

/-!
# Naturality of the canonical finite-quotient system

An equivariant homomorphism `f : M →+[G] N` restricts at every open normal subgroup `U` to a
homomorphism `M^U →+ N^U`. Applying continuous cohomology at each finite level gives a natural
transformation between the canonical finite-quotient systems. This file constructs that
transformation in every degree, proves its identity and composition laws, and proves that the
inflation-and-inclusion comparison maps commute with it.

Thus the finite-quotient presentation

```text
Hⁿ(G, M) = colim_U Hⁿ(G ⧸ U, M^U)
```

is natural in the discrete coefficient module. The construction is the coefficient-functoriality
of the system in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (1.2.5).

## Main definitions

* `TauCeti.ContCohomology.continuousFiniteQuotientCoeffPair`: the coefficient morphism
  `M^U → N^U` at one level.
* `TauCeti.ContCohomology.continuousFiniteQuotientSystemMap`: the resulting natural
  transformation of finite-quotient systems.

## Main statements

* `TauCeti.ContCohomology.continuousFiniteQuotientTransition_naturality`: coefficient maps
  commute with transition maps.
* `TauCeti.ContCohomology.continuousFiniteQuotientSystemMap_id` and
  `continuousFiniteQuotientSystemMap_comp`: the construction is functorial in the coefficients.
* `TauCeti.ContCohomology.continuousFiniteQuotientComparisonApp_naturality`: the comparison to
  `Hⁿ(G, -)` is natural in the coefficients.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M N P : Type u}
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction G N]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P] [DistribMulAction G P]

section Level

/-- The canonical coefficient morphism `M^U → N^U` induced by an equivariant homomorphism
`M →+[G] N`, regarded as a morphism of topological representations of `G ⧸ U`. -/
def continuousFiniteQuotientCoeffPair (f : M →+[G] N) (U : OpenNormalSubgroup G) :
    ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) ⟶
      ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup N) :=
  ofDiscreteModuleMap (fixedPointsMap f U.toSubgroup).toIntLinearMap
    (by
      intro q m
      -- The goal differs from the quotient-equivariance lemma only by the `\mathbb{Z}`-linear
      -- wrapper used by `ofDiscreteModuleMap`; unfolding that wrapper is definitional.
      change fixedPointsMap f U.toSubgroup (q • m) = q • fixedPointsMap f U.toSubgroup m
      exact fixedPointsMap_quotient_smul f U.toSubgroup q m)

omit [IsTopologicalGroup G] in
/-- The finite-level coefficient morphism acts as `f` on underlying elements. -/
@[simp]
theorem continuousFiniteQuotientCoeffPair_hom_apply (f : M →+[G] N)
    (U : OpenNormalSubgroup G) (m : FixedPoints.addSubgroup U.toSubgroup M) :
    (continuousFiniteQuotientCoeffPair f U).hom m = fixedPointsMap f U.toSubgroup m :=
  ofDiscreteModuleMap_hom_apply _ _ m

omit [IsTopologicalGroup G] in
/-- The finite-level coefficient morphism associated to the identity is the identity. -/
@[simp]
theorem continuousFiniteQuotientCoeffPair_id (U : OpenNormalSubgroup G) :
    continuousFiniteQuotientCoeffPair (DistribMulActionHom.id G : M →+[G] M) U = 𝟙 _ := by
  refine TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ ?_)
  exact (continuousFiniteQuotientCoeffPair_hom_apply _ _ m).trans
    ((DFunLike.congr_fun (fixedPointsMap_id (M := M) U.toSubgroup) m).trans
      (TopRep.id_apply _ m).symm)

omit [IsTopologicalGroup G] in
/-- Finite-level coefficient morphisms preserve composition. -/
@[simp]
theorem continuousFiniteQuotientCoeffPair_comp (f : M →+[G] N) (g : N →+[G] P)
    (U : OpenNormalSubgroup G) :
    continuousFiniteQuotientCoeffPair f U ≫ continuousFiniteQuotientCoeffPair g U =
      continuousFiniteQuotientCoeffPair (g.comp f) U := by
  refine TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ ?_)
  -- Composition in `TopRep` is definitionally composition of the underlying homomorphisms.
  change (continuousFiniteQuotientCoeffPair g U).hom
      ((continuousFiniteQuotientCoeffPair f U).hom m) =
    (continuousFiniteQuotientCoeffPair (g.comp f) U).hom m
  rw [continuousFiniteQuotientCoeffPair_hom_apply f U m,
    continuousFiniteQuotientCoeffPair_hom_apply g U
      (fixedPointsMap f U.toSubgroup m),
    continuousFiniteQuotientCoeffPair_hom_apply (g.comp f) U m]
  exact DFunLike.congr_fun (fixedPointsMap_comp_fixedPointsMap f g U.toSubgroup) m

/-- Restriction of an equivariant coefficient map to fixed points commutes with the coefficient
pairs defining the transition from the `U`-level to a deeper `V`-level. -/
theorem continuousFiniteQuotientCoeffPair_transition_square (f : M →+[G] N)
    {U V : OpenNormalSubgroup G} (hVU : V ≤ U) :
    (TopRep.resFunctor (continuousFiniteQuotientMap G hVU :
          G ⧸ V.toSubgroup →* G ⧸ U.toSubgroup)).map
          (continuousFiniteQuotientCoeffPair f U) ≫
        continuousFiniteQuotientPair G N hVU =
      continuousFiniteQuotientPair G M hVU ≫
        continuousFiniteQuotientCoeffPair f V := by
  refine TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ ?_)
  -- Restriction and composition in `TopRep` are definitionally the displayed nested maps.
  change (continuousFiniteQuotientPair G N hVU).hom
      ((continuousFiniteQuotientCoeffPair f U).hom m) =
    (continuousFiniteQuotientCoeffPair f V).hom
      ((continuousFiniteQuotientPair G M hVU).hom m)
  rw [continuousFiniteQuotientCoeffPair_hom_apply f U m,
    continuousFiniteQuotientPair_hom_apply G N hVU
      (fixedPointsMap f U.toSubgroup m),
    continuousFiniteQuotientPair_hom_apply G M hVU m,
    continuousFiniteQuotientCoeffPair_hom_apply f V (fixedPointsInclusion hVU m)]
  exact (DFunLike.congr_fun (fixedPointsMap_comp_fixedPointsInclusion f hVU) m).symm

end Level

section System

/-- The map on degree-`n` continuous cohomology induced at the `U`-level by an equivariant
coefficient homomorphism. -/
noncomputable def continuousFiniteQuotientCoeffApp (f : M →+[G] N)
    (U : OpenNormalSubgroup G) (n : ℕ) :
    continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) ⟶
      continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup N)) :=
  TauCeti.ContinuousCohomology.coeffMap (continuousFiniteQuotientCoeffPair f U) n

/-- The finite-level coefficient map is the canonical continuous-cohomology coefficient map. -/
theorem continuousFiniteQuotientCoeffApp_eq_coeffMap (f : M →+[G] N)
    (U : OpenNormalSubgroup G) (n : ℕ) :
    continuousFiniteQuotientCoeffApp f U n =
      TauCeti.ContinuousCohomology.coeffMap (continuousFiniteQuotientCoeffPair f U) n :=
  (rfl)

/-- **Naturality of the canonical transition in the coefficients**: the maps induced by
`M →+[G] N` commute with passage from the `U`-level to a deeper `V`-level. -/
@[reassoc]
theorem continuousFiniteQuotientTransition_naturality (f : M →+[G] N)
    {U V : OpenNormalSubgroup G} (hVU : V ≤ U) (n : ℕ) :
    continuousFiniteQuotientTransition G M hVU n ≫
        continuousFiniteQuotientCoeffApp f V n =
      continuousFiniteQuotientCoeffApp f U n ≫
        continuousFiniteQuotientTransition G N hVU n := by
  rw [continuousFiniteQuotientTransition_eq_map,
    continuousFiniteQuotientTransition_eq_map,
    continuousFiniteQuotientCoeffApp_eq_coeffMap,
    continuousFiniteQuotientCoeffApp_eq_coeffMap]
  exact TauCeti.ContinuousCohomology.map_comp_coeffMap
    (continuousFiniteQuotientMap G hVU)
    (continuousFiniteQuotientPair G M hVU)
    (continuousFiniteQuotientPair G N hVU)
    (continuousFiniteQuotientCoeffPair f U)
    (continuousFiniteQuotientCoeffPair f V)
    (continuousFiniteQuotientCoeffPair_transition_square f hVU) n

/-- An equivariant homomorphism of discrete coefficient modules induces a natural transformation
between their canonical finite-quotient systems in every degree. -/
noncomputable def continuousFiniteQuotientSystemMap (f : M →+[G] N) (n : ℕ) :
    continuousFiniteQuotientSystem G M n ⟶ continuousFiniteQuotientSystem G N n where
  app U := eqToHom (continuousFiniteQuotientSystem_obj G M n U.unop) ≫
    continuousFiniteQuotientCoeffApp f U.unop n ≫
    eqToHom (continuousFiniteQuotientSystem_obj G N n U.unop).symm
  naturality := by
    intro U V h
    apply (cancel_epi
      (eqToHom (continuousFiniteQuotientSystem_obj G M n U.unop).symm)).1
    apply (cancel_mono
      (eqToHom (continuousFiniteQuotientSystem_obj G N n V.unop))).1
    have hcancelM :
        eqToHom (continuousFiniteQuotientSystem_obj G M n U.unop).symm ≫
          eqToHom (continuousFiniteQuotientSystem_obj G M n U.unop) = 𝟙 _ := by
      simp
    simp only [Category.assoc,
      reassoc_of% (continuousFiniteQuotientSystem_map G M n h),
      eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [reassoc_of% hcancelM]
    rw [continuousFiniteQuotientSystem_map G N n h]
    exact continuousFiniteQuotientTransition_naturality f (leOfHom h.unop) n

/-- At every open normal subgroup, the system map is the finite-level coefficient map. -/
@[simp]
theorem continuousFiniteQuotientSystemMap_app (f : M →+[G] N) (n : ℕ)
    (U : OpenNormalSubgroup G) :
    eqToHom (continuousFiniteQuotientSystem_obj G M n U).symm ≫
        (continuousFiniteQuotientSystemMap f n).app (Opposite.op U) ≫
      eqToHom (continuousFiniteQuotientSystem_obj G N n U) =
      continuousFiniteQuotientCoeffApp f U n :=
  by simp [continuousFiniteQuotientSystemMap]

/-- The system map associated to the identity coefficient homomorphism is the identity natural
transformation. -/
@[simp]
theorem continuousFiniteQuotientSystemMap_id (n : ℕ) :
    continuousFiniteQuotientSystemMap (DistribMulActionHom.id G : M →+[G] M) n = 𝟙 _ := by
  refine NatTrans.ext (funext fun U ↦ ?_)
  apply (cancel_epi
    (eqToHom (continuousFiniteQuotientSystem_obj G M n U.unop).symm)).1
  apply (cancel_mono
    (eqToHom (continuousFiniteQuotientSystem_obj G M n U.unop))).1
  have hs := continuousFiniteQuotientSystemMap_app
    (DistribMulActionHom.id G : M →+[G] M) n U.unop
  simp only [Opposite.op_unop] at hs
  rw [Category.assoc, hs,
    continuousFiniteQuotientCoeffApp_eq_coeffMap,
    continuousFiniteQuotientCoeffPair_id, TauCeti.ContinuousCohomology.coeffMap_id]
  simp

/-- System maps preserve composition of equivariant coefficient homomorphisms. -/
@[simp]
theorem continuousFiniteQuotientSystemMap_comp (f : M →+[G] N) (g : N →+[G] P)
    (n : ℕ) :
    continuousFiniteQuotientSystemMap f n ≫ continuousFiniteQuotientSystemMap g n =
      continuousFiniteQuotientSystemMap (g.comp f) n := by
  refine NatTrans.ext (funext fun U ↦ ?_)
  simp only [continuousFiniteQuotientSystemMap, NatTrans.comp_app, Category.assoc]
  have hcancel :
      eqToHom (continuousFiniteQuotientSystem_obj G N n U.unop).symm ≫
        eqToHom (continuousFiniteQuotientSystem_obj G N n U.unop) = 𝟙 _ := by
    simp
  rw [reassoc_of% hcancel]
  rw [continuousFiniteQuotientCoeffApp_eq_coeffMap,
    continuousFiniteQuotientCoeffApp_eq_coeffMap,
    continuousFiniteQuotientCoeffApp_eq_coeffMap]
  rw [← reassoc_of% (TauCeti.ContinuousCohomology.coeffMap_comp
    (continuousFiniteQuotientCoeffPair f U.unop)
    (continuousFiniteQuotientCoeffPair g U.unop) n),
    continuousFiniteQuotientCoeffPair_comp]

end System

section Comparison

omit [IsTopologicalGroup G] in
/-- The coefficient square formed by the inclusion `M^U → M`, the inclusion `N^U → N`,
and an equivariant homomorphism `M →+[G] N` commutes. -/
private theorem continuousFiniteQuotientCoeffPair_comparison_square (f : M →+[G] N)
    (U : OpenNormalSubgroup G) :
    (TopRep.resFunctor (ContinuousMonoidHom.quotientMk U.toSubgroup :
          G →* G ⧸ U.toSubgroup)).map (continuousFiniteQuotientCoeffPair f U) ≫
        ofDiscreteModulePair
          (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup N).subtype.toIntLinearMap
          (fun g m ↦ subtype_quotientMk_smul G N U.toSubgroup g m) =
      ofDiscreteModulePair
          (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M).subtype.toIntLinearMap
          (fun g m ↦ subtype_quotientMk_smul G M U.toSubgroup g m) ≫
        ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap
          (fun g m ↦ map_smul f g m) := by
  refine TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ ?_)
  -- The restriction functor and both compatible pairs retain the displayed underlying maps
  -- definitionally, so expose those maps before applying their evaluation lemmas.
  let m' : FixedPoints.addSubgroup U.toSubgroup M := m
  change (ofDiscreteModulePair
      (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup N).subtype.toIntLinearMap
      (fun g m ↦ subtype_quotientMk_smul G N U.toSubgroup g m)).hom
      ((continuousFiniteQuotientCoeffPair f U).hom m') =
    (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap
      (fun g m ↦ map_smul f g m)).hom
      ((ofDiscreteModulePair
        (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup M).subtype.toIntLinearMap
        (fun g m ↦ subtype_quotientMk_smul G M U.toSubgroup g m)).hom m')
  rw [continuousFiniteQuotientCoeffPair_hom_apply f U m',
    ofDiscreteModulePair_hom_apply
      (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup N).subtype.toIntLinearMap
      (fun g m ↦ subtype_quotientMk_smul G N U.toSubgroup g m)
      (fixedPointsMap f U.toSubgroup m'),
    ofDiscreteModulePair_hom_apply
      (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup M).subtype.toIntLinearMap
      (fun g m ↦ subtype_quotientMk_smul G M U.toSubgroup g m) m',
    ofDiscreteModuleMap_hom_apply f.toAddMonoidHom.toIntLinearMap
      (fun g m ↦ map_smul f g m)
      ((FixedPoints.addSubgroup U.toSubgroup M).subtype.toIntLinearMap m')]
  exact coe_fixedPointsMap f U.toSubgroup m'

/-- **Naturality of the finite-quotient comparison in the coefficients**: mapping coefficients at
a finite level and then comparing with `Hⁿ(G, N)` is the same as first comparing with
`Hⁿ(G, M)` and then applying the coefficient map induced by `f`. -/
@[reassoc]
theorem continuousFiniteQuotientComparisonApp_naturality (f : M →+[G] N)
    (U : OpenNormalSubgroup G) (n : ℕ) :
    continuousFiniteQuotientCoeffApp f U n ≫
        continuousFiniteQuotientComparisonApp G N U n =
      continuousFiniteQuotientComparisonApp G M U n ≫
        TauCeti.ContinuousCohomology.coeffMap
          (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap
            (fun g m ↦ map_smul f g m)) n := by
  rw [continuousFiniteQuotientCoeffApp_eq_coeffMap,
    continuousFiniteQuotientComparisonApp_eq_map,
    continuousFiniteQuotientComparisonApp_eq_map]
  exact (TauCeti.ContinuousCohomology.map_comp_coeffMap
    (ContinuousMonoidHom.quotientMk U.toSubgroup)
    (ofDiscreteModulePair
      (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup M).subtype.toIntLinearMap
      (fun g m ↦ subtype_quotientMk_smul G M U.toSubgroup g m))
    (ofDiscreteModulePair
      (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup N).subtype.toIntLinearMap
      (fun g m ↦ subtype_quotientMk_smul G N U.toSubgroup g m))
    (continuousFiniteQuotientCoeffPair f U)
    (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap
      (fun g m ↦ map_smul f g m))
    (continuousFiniteQuotientCoeffPair_comparison_square f U) n).symm

end Comparison

end TauCeti.ContCohomology
