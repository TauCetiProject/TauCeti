/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.AlexandrovDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Canonical
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Explicit

/-!
# Comparing the explicit and canonical finite-quotient systems

The explicit systems `U ↦ Hⁱ(G ⧸ U, M^U)` and the canonical continuous-cohomology systems
have the same transition maps under the explicit-to-canonical comparisons, for `i = 0, 1, 2`.
This file packages those comparisons as natural isomorphisms in `AddCommGrpCat`, after forgetting
the topology and scalar structure on canonical cohomology. The comparison maps from each level
into the cohomology of `G` also commute with these identifications. Thus the two finite-quotient
colimit descriptions identify the same classes, not just abstractly isomorphic groups.

The levelwise comparisons need no compactness: every quotient by an open normal subgroup is
discrete, hence locally compact. For comparison with the cohomology of `G` in degree two, only
local compactness of `G` is needed. No comparison with discrete `groupCohomology` is used, so
all statements remain polymorphic in the universe of `G`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (1.2.5), for the finite-quotient description of continuous cohomology.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M]

/-- The degree-zero comparison intertwines the explicit and canonical finite-level transitions. -/
@[simp]
theorem continuousFiniteQuotientTransition_explicitH0Iso {U V : OpenNormalSubgroup G}
    (hVU : V ≤ U) (x : H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    continuousFiniteQuotientTransition G M hVU 0
        ((explicitH0IsoContinuousCohomology (G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M)).hom x) =
      (explicitH0IsoContinuousCohomology (G ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup M)).hom
        (explicitFiniteQuotientTransition0 G M U V hVU x) := by
  rw [continuousFiniteQuotientTransition_eq_map,
    continuousFiniteQuotientPair_eq_ofDiscreteModulePair,
    explicitFiniteQuotientTransition0_eq_explicitMap0]
  exact explicitH0Iso_map _ _ _ _ (continuousFiniteQuotientMap G hVU) _
    (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) x

/-- The degree-one comparison intertwines the explicit and canonical finite-level transitions. -/
@[simp]
theorem continuousFiniteQuotientTransition_explicitH1AddEquivContinuousCohomology
    {U V : OpenNormalSubgroup G}
    (hVU : V ≤ U) (x : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    continuousFiniteQuotientTransition G M hVU 1
        (explicitH1AddEquivContinuousCohomology (G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M) x) =
      explicitH1AddEquivContinuousCohomology (G ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup M)
        (explicitFiniteQuotientTransition1 G M U V hVU x) := by
  rw [continuousFiniteQuotientTransition_eq_map,
    continuousFiniteQuotientPair_eq_ofDiscreteModulePair,
    explicitFiniteQuotientTransition1_eq_explicitMap1]
  exact explicitH1AddEquivContinuousCohomology_map _ _ _ _
    (continuousFiniteQuotientMap G hVU) _
    (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) x

/-- The degree-two comparison intertwines the explicit and canonical finite-level transitions. -/
@[simp]
theorem continuousFiniteQuotientTransition_explicitH2AddEquivContinuousCohomology
    {U V : OpenNormalSubgroup G}
    (hVU : V ≤ U) (x : H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    continuousFiniteQuotientTransition G M hVU 2
        (explicitH2AddEquivContinuousCohomology (G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M) x) =
      explicitH2AddEquivContinuousCohomology (G ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup M)
        (explicitFiniteQuotientTransition2 G M U V hVU x) := by
  rw [continuousFiniteQuotientTransition_eq_map,
    continuousFiniteQuotientPair_eq_ofDiscreteModulePair,
    explicitFiniteQuotientTransition2_eq_explicitMap2]
  exact explicitH2AddEquivContinuousCohomology_map _ _ _ _
    (continuousFiniteQuotientMap G hVU) _
    (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) x

private noncomputable def finiteQuotientSystemIsoContinuous
    (E : (OpenNormalSubgroup G)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (A : OpenNormalSubgroup G → AddCommGrpCat.{u})
    (eobj : ∀ U, E.obj (Opposite.op U) = A U)
    (t : ∀ {U V : OpenNormalSubgroup G}, V ≤ U → (A U →+ A V))
    (emap : ∀ {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V),
      eqToHom (eobj U.unop).symm ≫ E.map f ≫ eqToHom (eobj V.unop) =
        AddCommGrpCat.ofHom (t (leOfHom f.unop)))
    (n : ℕ)
    (e : ∀ U, A U ≃+ continuousCohomology n
      (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)))
    (he : ∀ {U V} (h : V ≤ U) (x : A U),
      continuousFiniteQuotientTransition G M h n (e U x) = e V (t h x)) :
    E ≅ continuousFiniteQuotientSystem G M n ⋙
      (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat) :=
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat
  NatIso.ofComponents (fun U ↦
    eqToIso (eobj U.unop) ≪≫ (e U.unop).toAddCommGrpIso ≪≫
      (F.mapIso (eqToIso (continuousFiniteQuotientSystem_obj G M n U.unop))).symm) (by
    intro U V f
    apply (cancel_epi (eqToHom (eobj U.unop).symm)).1
    apply (cancel_mono (F.map (eqToHom (continuousFiniteQuotientSystem_obj G M n V.unop)))).1
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, eqToIso.hom, eqToIso.inv,
      F, Category.assoc, Functor.comp_map, ← Functor.map_comp, eqToHom_trans_assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, reassoc_of% (emap f)]
    rw [continuousFiniteQuotientSystem_map]
    ext x
    -- Both forgetful functors preserve the underlying function, and toAddCommGrpIso.hom
    -- acts by the original additive equivalence, so this is precisely he in reverse.
    exact (he (leOfHom f.unop) x).symm)

/-- The explicit and canonical degree-zero systems are naturally isomorphic after forgetting
canonical cohomology to abelian groups. The components are the existing degree-zero comparisons. -/
noncomputable def explicitFiniteQuotientSystem0IsoContinuous :
    explicitFiniteQuotientSystem0 G M ≅ continuousFiniteQuotientSystem G M 0 ⋙
      (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat) :=
  finiteQuotientSystemIsoContinuous G M _ _ (explicitFiniteQuotientSystem0_obj G M)
    (fun h ↦ explicitFiniteQuotientTransition0 G M _ _ h)
    (fun f ↦ explicitFiniteQuotientSystem0_map G M f) 0
    (fun U ↦ (explicitH0IsoContinuousCohomology (G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup M)).toContinuousLinearEquiv.toAddEquiv)
    (fun h x ↦ continuousFiniteQuotientTransition_explicitH0Iso G M h x)

/-- Under the object identifications, the degree-zero system isomorphism is the usual comparison
on each finite level. -/
@[simp]
theorem explicitFiniteQuotientSystem0IsoContinuous_hom_app (U : OpenNormalSubgroup G) :
    let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat
    (explicitFiniteQuotientSystem0IsoContinuous G M).hom.app (Opposite.op U) =
      eqToHom (explicitFiniteQuotientSystem0_obj G M U) ≫
        ((explicitH0IsoContinuousCohomology (G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M)).toContinuousLinearEquiv.toAddEquiv
          ).toAddCommGrpIso.hom ≫
        F.map (eqToHom (continuousFiniteQuotientSystem_obj G M 0 U).symm) :=
  (rfl)

/-- The explicit and canonical degree-one systems are naturally isomorphic after forgetting
canonical cohomology to abelian groups. The components are the existing degree-one comparisons. -/
noncomputable def explicitFiniteQuotientSystem1IsoContinuous :
    explicitFiniteQuotientSystem1 G M ≅ continuousFiniteQuotientSystem G M 1 ⋙
      (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat) :=
  finiteQuotientSystemIsoContinuous G M _ _ (explicitFiniteQuotientSystem1_obj G M)
    (fun h ↦ explicitFiniteQuotientTransition1 G M _ _ h)
    (fun f ↦ explicitFiniteQuotientSystem1_map G M f) 1
    (fun U ↦ explicitH1AddEquivContinuousCohomology (G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup M))
    (fun h x ↦ continuousFiniteQuotientTransition_explicitH1AddEquivContinuousCohomology G M h x)

/-- Under the object identifications, the degree-one system isomorphism is the usual comparison
on each finite level. -/
@[simp]
theorem explicitFiniteQuotientSystem1IsoContinuous_hom_app (U : OpenNormalSubgroup G) :
    let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat
    (explicitFiniteQuotientSystem1IsoContinuous G M).hom.app (Opposite.op U) =
      eqToHom (explicitFiniteQuotientSystem1_obj G M U) ≫
        (explicitH1AddEquivContinuousCohomology (G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M)).toAddCommGrpIso.hom ≫
        F.map (eqToHom (continuousFiniteQuotientSystem_obj G M 1 U).symm) :=
  (rfl)

/-- The explicit and canonical degree-two systems are naturally isomorphic after forgetting
canonical cohomology to abelian groups. Each finite-level group is discrete, so no local
compactness assumption on the ambient group is needed. -/
noncomputable def explicitFiniteQuotientSystem2IsoContinuous :
    explicitFiniteQuotientSystem2 G M ≅ continuousFiniteQuotientSystem G M 2 ⋙
      (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat) :=
  finiteQuotientSystemIsoContinuous G M _ _ (explicitFiniteQuotientSystem2_obj G M)
    (fun h ↦ explicitFiniteQuotientTransition2 G M _ _ h)
    (fun f ↦ explicitFiniteQuotientSystem2_map G M f) 2
    (fun U ↦ explicitH2AddEquivContinuousCohomology (G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup M))
    (fun h x ↦ continuousFiniteQuotientTransition_explicitH2AddEquivContinuousCohomology G M h x)

/-- Under the object identifications, the degree-two system isomorphism is the usual comparison
on each finite level. -/
@[simp]
theorem explicitFiniteQuotientSystem2IsoContinuous_hom_app (U : OpenNormalSubgroup G) :
    let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat
    (explicitFiniteQuotientSystem2IsoContinuous G M).hom.app (Opposite.op U) =
      eqToHom (explicitFiniteQuotientSystem2_obj G M U) ≫
        (explicitH2AddEquivContinuousCohomology (G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M)).toAddCommGrpIso.hom ≫
        F.map (eqToHom (continuousFiniteQuotientSystem_obj G M 2 U).symm) :=
  (rfl)

/-- The degree-zero comparison identifies canonical inflation-and-inclusion from a finite level
with explicit inflation. -/
@[simp]
theorem continuousFiniteQuotientComparisonApp_explicitH0Iso (U : OpenNormalSubgroup G)
    (x : H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    continuousFiniteQuotientComparisonApp G M U 0
        ((explicitH0IsoContinuousCohomology (G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M)).hom x) =
      (explicitH0IsoContinuousCohomology G M).hom (explicitInfl0 G M U.toSubgroup x) := by
  rw [continuousFiniteQuotientComparisonApp_eq_map,
    ← coeffMap_ofDiscreteModuleQuotient_comp_infl, ConcreteCategory.comp_apply]
  exact explicitH0Iso_infl G M U.toSubgroup x

variable [ContinuousSMul G M]

/-- The degree-one comparison identifies canonical inflation-and-inclusion from a finite level
with explicit inflation. -/
@[simp]
theorem continuousFiniteQuotientComparisonApp_explicitH1AddEquivContinuousCohomology
    (U : OpenNormalSubgroup G)
    (x : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    continuousFiniteQuotientComparisonApp G M U 1
        (explicitH1AddEquivContinuousCohomology (G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M) x) =
      explicitH1AddEquivContinuousCohomology G M (explicitInfl1 G M U.toSubgroup x) := by
  rw [continuousFiniteQuotientComparisonApp_eq_map, explicitInfl1_eq_explicitMap1]
  exact explicitH1AddEquivContinuousCohomology_map _ _ _ _
    (Subgroup.quotientMkContinuousMonoidHom U.toSubgroup)
    _ U.toSubgroup.fixedPoints_subtype_quotientMk_smul x

/-- The degree-two comparison identifies canonical inflation-and-inclusion from a finite level
with explicit inflation. Local compactness is needed only for the comparison over `G`. -/
@[simp]
theorem continuousFiniteQuotientComparisonApp_explicitH2AddEquivContinuousCohomology
    [LocallyCompactSpace G]
    (U : OpenNormalSubgroup G)
    (x : H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    continuousFiniteQuotientComparisonApp G M U 2
        (explicitH2AddEquivContinuousCohomology (G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M) x) =
      explicitH2AddEquivContinuousCohomology G M (explicitInfl2 G M U.toSubgroup x) := by
  rw [continuousFiniteQuotientComparisonApp_eq_map, explicitInfl2_eq_explicitMap2]
  exact explicitH2AddEquivContinuousCohomology_map _ _ _ _
    (Subgroup.quotientMkContinuousMonoidHom U.toSubgroup)
    _ U.toSubgroup.fixedPoints_subtype_quotientMk_smul x

end TauCeti.ContCohomology
