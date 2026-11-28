/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LocalCohomology.RightDerived
public import TauCeti.AlgebraicGeometry.Cohomology.SupportedCohomology.DegreeZero
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Flasque
public import TauCeti.CategoryTheory.Abelian.AcyclicResolution
public import TauCeti.Topology.Sheaves.SupportedCohomology.Derived
public import TauCeti.Topology.Sheaves.SupportedCohomology.Resolution

/-!
# Algebraic local cohomology and sheaf cohomology with closed supports

Over a Noetherian ring `R`, `tildeSheafFunctor R : M ↦ M~` is exact and sends injectives to
flasque sheaves (`isFlasque_tilde_of_injective`), which are adapted to
`supportedSubmoduleSectionsFunctor`. Right deriving `tildeCompSupportedSubmoduleSectionsTopIso`
via `Functor.compRightDerivedIsoOfResolution` gives `tildeCompRightDerivedSupportedSectionsIso`
(Stacks 0955), and combining with `rightDerivedSupportedSubmoduleSectionsIso` and
`localCohomology.isoRightDerivedPrimaryComponent` gives `H^q_{V(I)}(Spec R, M~) ≃ₗ[R] H^q_I(M)`
(`supportedModuleHTopTildeLinearEquivLocalCohomology`, Stacks 0A6T).

## Main definitions

* `TauCeti.AlgebraicGeometry.tildeCompRightDerivedSupportedSectionsIso` (Stacks 0955):
  `(R^q Γ_{V(I)}(Spec R, -)) ∘ (~) ≅ R^q Γ_I` over a Noetherian ring `R`.
* `TauCeti.AlgebraicGeometry.tildeCompSupportedModuleHTopIsoLocalCohomology` and
  `TauCeti.AlgebraicGeometry.supportedModuleHTopTildeLinearEquivLocalCohomology` (Stacks 0A6T):
  `H^q_{V(I)}(Spec R, M~) ≃ₗ[R] H^q_I(M)` over a Noetherian ring `R`.

## Main results

* `TauCeti.AlgebraicGeometry.supportedModuleHTopTildeLinearEquivLocalCohomology_naturality`:
  naturality of the comparison with respect to `R`-module morphisms.

## References

* [The Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [The Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* A. Grothendieck, *Local Cohomology*, Lecture Notes in Mathematics 41, Proposition 2.2.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, §3.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open CategoryTheory.Sheaf

section Comparison

variable {R : CommRingCat.{u}}

/-- Injective sheaves of `R`-modules on `Spec R` are flasque. -/
lemma isFlasque_injective (F : Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R))
    [Injective F] : isFlasque (Spec R) (ModuleCat.{u} R) F :=
  isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _)

/-- In a short exact sequence of sheaves of `R`-modules on `Spec R`, if the first two terms are
flasque, then so is the third. -/
lemma isFlasque_X₃_of_shortExact
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)))
    (hT : T.ShortExact) (h₁ : isFlasque (Spec R) (ModuleCat.{u} R) T.X₁)
    (h₂ : isFlasque (Spec R) (ModuleCat.{u} R) T.X₂) :
    isFlasque (Spec R) (ModuleCat.{u} R) T.X₃ :=
  have := isFlasque_iff.mp h₁; have := isFlasque_iff.mp h₂
  isFlasque_iff.mpr hT.isFlasque_X₃_of_isFlasque

/-- Taking global sections supported in `V(I)` preserves short exact sequences whose first term
is flasque. -/
lemma shortExact_map_supportedSubmodule_of_isFlasque (I : Ideal R)
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)))
    (hT : T.ShortExact) (h₁ : isFlasque (Spec R) (ModuleCat.{u} R) T.X₁)
    (_ : isFlasque (Spec R) (ModuleCat.{u} R) T.X₂) :
    (T.map (supportedSubmoduleSectionsFunctor (R := R)
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤)).ShortExact :=
  have := isFlasque_iff.mp h₁
  shortExact_map_supportedSubmoduleSectionsFunctor_of_isFlasque _ ⊤ hT

/-- Over a Noetherian ring `R`, the quasi-coherent sheaf `M~` associated with an injective
`R`-module `M` is flasque. -/
lemma isFlasque_tilde_injective [IsNoetherianRing R] (M : ModuleCat.{u} R) (_ : Injective M) :
    isFlasque (Spec R) (ModuleCat.{u} R) ((tildeSheafFunctor R).obj M) :=
  isFlasque_iff.mpr (isFlasque_modulesSpecToSheaf_tilde_of_injective M)

/-- **Derived supported global sections agree with derived `I`-power torsion (Stacks 0955).**
Over a Noetherian ring `R`, composing `M ↦ M~` with the `q`-th right derived functor of
`Γ_{V(I)}(Spec R, -)` is naturally isomorphic to `(R^q Γ_I)`. -/
@[stacks 0955]
def tildeCompRightDerivedSupportedSectionsIso [IsNoetherianRing R] (I : Ideal R) (q : ℕ) :
    tildeSheafFunctor R ⋙
        (supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).rightDerived q ≅
      I.primaryComponentFunctor.{u}.rightDerived q :=
  Functor.compRightDerivedIsoOfResolution
    (supportedSubmoduleSectionsFunctor (R := R) (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤)
    (isFlasque (Spec R) (ModuleCat.{u} R)) (fun _ _ ↦ isFlasque_injective _)
    isFlasque_X₃_of_shortExact (shortExact_map_supportedSubmodule_of_isFlasque I)
    (tildeSheafFunctor R) I.primaryComponentFunctor.{u}
    (tildeCompSupportedSubmoduleSectionsTopIso (IsNoetherian.noetherian I))
    isFlasque_tilde_injective q

/-- At each module `M`, `tildeCompRightDerivedSupportedSectionsIso` is computed by
`Functor.compRightDerivedIsoOfResolution_hom_app` from the chosen injective resolution of `M`. -/
lemma tildeCompRightDerivedSupportedSectionsIso_hom_app [IsNoetherianRing R]
    (I : Ideal R) (q : ℕ) (M : ModuleCat.{u} R) :
    (tildeCompRightDerivedSupportedSectionsIso I q).hom.app M =
      ((supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).rightDerivedObjIsoOfResolution
          (isFlasque (Spec R) (ModuleCat.{u} R)) (fun _ _ ↦ isFlasque_injective _)
          isFlasque_X₃_of_shortExact (shortExact_map_supportedSubmodule_of_isFlasque I)
          ((injectiveResolution M).mapι (tildeSheafFunctor R))
          (fun m ↦ isFlasque_tilde_injective _ ((injectiveResolution M).injective m)) q).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) _ q).map
          ((Functor.mapHomologicalComplexCompIso
            (tildeCompSupportedSubmoduleSectionsTopIso (IsNoetherian.noetherian I))
            (ComplexShape.up ℕ)).app (injectiveResolution M).cocomplex).hom ≫
        ((injectiveResolution M).isoRightDerivedObj I.primaryComponentFunctor.{u} q).inv :=
  Functor.compRightDerivedIsoOfResolution_hom_app _ _ _ _ _ _ _ _ _ q M

/-- For any injective resolution `J` of `M`, `tildeCompRightDerivedSupportedSectionsIso` agrees
with `Functor.rightDerivedObjIsoOfResolution` on `J.mapι (tildeSheafFunctor R)` followed by
`tildeCompSupportedSubmoduleSectionsTopIso` on `J.cocomplex`. -/
@[reassoc]
lemma tildeCompRightDerivedSupportedSectionsIso_hom_app_comp_isoRightDerivedObj
    [IsNoetherianRing R] (I : Ideal R) (q : ℕ) {M : ModuleCat.{u} R} (J : InjectiveResolution M) :
    (tildeCompRightDerivedSupportedSectionsIso I q).hom.app M ≫
        (J.isoRightDerivedObj I.primaryComponentFunctor.{u} q).hom =
      ((supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).rightDerivedObjIsoOfResolution
          (isFlasque (Spec R) (ModuleCat.{u} R)) (fun _ _ ↦ isFlasque_injective _)
          isFlasque_X₃_of_shortExact (shortExact_map_supportedSubmodule_of_isFlasque I)
          (J.mapι (tildeSheafFunctor R))
          (fun m ↦ isFlasque_tilde_injective _ (J.injective m)) q).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) _ q).map
          ((Functor.mapHomologicalComplexCompIso
            (tildeCompSupportedSubmoduleSectionsTopIso (IsNoetherian.noetherian I))
            (ComplexShape.up ℕ)).app J.cocomplex).hom :=
  Functor.compRightDerivedIsoOfResolution_hom_app_comp_isoRightDerivedObj _ _ _ _ _ _ _ _ _ q J

/-- In degree zero, `tildeCompRightDerivedSupportedSectionsIso` is compatible with the canonical
morphisms `Functor.toRightDerivedZero` along `tildeCompSupportedSubmoduleSectionsTopIso`. -/
@[reassoc]
lemma toRightDerivedZero_app_comp_tildeCompRightDerivedSupportedSectionsIso_hom
    [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R) :
    (supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).toRightDerivedZero.app
        ((tildeSheafFunctor R).obj M) ≫
      (tildeCompRightDerivedSupportedSectionsIso I 0).hom.app M =
    (tildeCompSupportedSubmoduleSectionsTopIso (IsNoetherian.noetherian I)).hom.app M ≫
      I.primaryComponentFunctor.{u}.toRightDerivedZero.app M :=
  Functor.toRightDerivedZero_app_comp_compRightDerivedIsoOfResolution_hom _ _ _ _ _ _ _ _ _ M

private lemma toRightDerivedZero_app_comp_rightDerivedSupportedSubmoduleSectionsIso_hom
    (S : Closeds (Spec R)) (W : Opens (Spec R))
    (F : Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)) :
    (supportedSubmoduleSectionsFunctor (R := R) S W).toRightDerivedZero.app F ≫
        (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W 0).hom.app F =
      (F.supportedModuleHPresheafZeroIso S).inv.app (op W) := by
  refine (cancel_epi ((supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.app F)).1 ?_
  have hnat := NatTrans.congr_app (NatTrans.toRightDerivedZero_comp_rightDerived_zero
    (supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom) F
  have hr := NatTrans.congr_app
    (rightDerivedSupportedSubmoduleSectionsIso_hom_comp (R := R) S W 0) F
  simp only [NatTrans.comp_app] at hnat hr
  -- `supportedModuleHPresheafFunctor` is unexposed, so the domain/codomain equality between
  -- `ModuleCat.ofHom Abelian.Ext.linearEquiv₀.symm` and the RHS only holds definitionally.
  have hL : (supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.app F ≫
      (supportedSubmoduleSectionsFunctor (R := R) S W).toRightDerivedZero.app F ≫
        (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W 0).hom.app F =
      ((linearCoyoneda R _).obj
          (op ((S.supportedFreeModuleSheafFunctor R).obj W))).toRightDerivedZero.app F ≫
        (rightDerivedLinearCoyonedaIsoExt R
          ((S.supportedFreeModuleSheafFunctor R).obj W) 0).hom.app F := by
    rw [← Category.assoc, ← hnat, Category.assoc]; erw [hr]; rfl
  erw [hL, toRightDerivedZero_app_comp_rightDerivedLinearCoyonedaIsoExt_hom_app]
  ext g; apply (F.supportedModuleHZeroEquiv S W).injective
  erw [supportedModuleHZeroEquiv_supportedModuleHPresheafZeroIso_inv_app_apply,
    supportedSubmoduleSectionsRepresentableIso_hom_app_apply]
  change (F.supportedModuleHZeroEquiv S W) (Abelian.Ext.mk₀ g) = _
  apply Subtype.ext
  erw [coe_supportedModuleHZeroEquiv_apply,
    TauCeti.CategoryTheory.coe_relativeFreeModuleYonedaExtZeroEquiv_apply,
    ← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply,
    Closeds.coe_supportedFreeModuleSheafHomEquiv_apply,
    TauCeti.CategoryTheory.coe_relativeFreeModuleYonedaSheafHomEquiv_apply]

private lemma rightDerivedSupportedSubmoduleSectionsIso_inv_app_zero
    (S : Closeds (Spec R)) (W : Opens (Spec R))
    (F : Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)) :
    (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W 0).inv.app F =
      (F.supportedModuleHPresheafZeroIso S).hom.app (op W) ≫
        (supportedSubmoduleSectionsFunctor (R := R) S W).toRightDerivedZero.app F := by
  refine (cancel_mono ((rightDerivedSupportedSubmoduleSectionsIso (R := R) S W 0).hom.app F)).1 ?_
  rw [Iso.inv_hom_id_app]
  erw [Category.assoc, toRightDerivedZero_app_comp_rightDerivedSupportedSubmoduleSectionsIso_hom,
    Iso.hom_inv_id_app]; rfl

/-- **Algebraic local cohomology agrees with sheaf cohomology with supports (Stacks 0A6T).**
Over a Noetherian ring `R`, the functor `M ↦ H^q_{V(I)}(Spec R, M~)` is naturally isomorphic to
`localCohomology I q`. -/
@[stacks 0A6T]
def tildeCompSupportedModuleHTopIsoLocalCohomology [IsNoetherianRing R] (I : Ideal R) (q : ℕ) :
    tildeSheafFunctor R ⋙
        supportedModuleHPresheafFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) q ⋙
        (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat.{u} R)).obj (op ⊤) ≅
      localCohomology I q :=
  (Functor.isoWhiskerLeft (tildeSheafFunctor R) (rightDerivedSupportedSubmoduleSectionsIso
    (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q)).symm ≪≫
    tildeCompRightDerivedSupportedSectionsIso I q ≪≫
    (localCohomology.isoRightDerivedPrimaryComponent I q).symm

/-- `tildeCompSupportedModuleHTopIsoLocalCohomology` is the composite of
`rightDerivedSupportedSubmoduleSectionsIso`, `tildeCompRightDerivedSupportedSectionsIso`, and
`localCohomology.isoRightDerivedPrimaryComponent`. -/
@[simp]
lemma tildeCompSupportedModuleHTopIsoLocalCohomology_hom [IsNoetherianRing R]
    (I : Ideal R) (q : ℕ) :
    (tildeCompSupportedModuleHTopIsoLocalCohomology I q).hom =
      (Functor.isoWhiskerLeft (tildeSheafFunctor R) (rightDerivedSupportedSubmoduleSectionsIso
        (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q)).inv ≫
        (tildeCompRightDerivedSupportedSectionsIso I q).hom ≫
        (localCohomology.isoRightDerivedPrimaryComponent I q).inv := (rfl)

/-- In degree zero, `tildeCompSupportedModuleHTopIsoLocalCohomology` factors through
`supportedModuleHPresheafZeroIso`, `tildeCompSupportedSubmoduleSectionsTopIso`, and
`localCohomology.degreeZeroIsoPrimaryComponentFunctor`. -/
@[reassoc]
lemma tildeCompSupportedModuleHTopIsoLocalCohomology_hom_app_zero
    [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R) :
    (tildeCompSupportedModuleHTopIsoLocalCohomology I 0).hom.app M =
      (((tildeSheafFunctor R).obj M).supportedModuleHPresheafZeroIso
          (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤) ≫
        (tildeCompSupportedSubmoduleSectionsTopIso (IsNoetherian.noetherian I)).hom.app M ≫
        (localCohomology.degreeZeroIsoPrimaryComponentFunctor I).inv.app M := by
  have hloc : I.primaryComponentFunctor.{u}.toRightDerivedZero ≫
      (localCohomology.isoRightDerivedPrimaryComponent I 0).inv =
      (localCohomology.degreeZeroIsoPrimaryComponentFunctor I).inv := by
    rw [← cancel_mono (localCohomology.isoRightDerivedPrimaryComponent I 0).hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id,
      ← localCohomology.degreeZeroIsoPrimaryComponentFunctor_hom_comp_toRightDerivedZero,
      Iso.inv_hom_id_assoc]
  rw [tildeCompSupportedModuleHTopIsoLocalCohomology_hom, NatTrans.comp_app, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    rightDerivedSupportedSubmoduleSectionsIso_inv_app_zero]
  erw [Category.assoc,
    toRightDerivedZero_app_comp_tildeCompRightDerivedSupportedSectionsIso_hom_assoc,
    ← NatTrans.comp_app, hloc]; rfl

/-- In degree zero, `tildeCompSupportedModuleHTopIsoLocalCohomology` followed by
`localCohomology.degreeZeroIsoPrimaryComponentFunctor` agrees with
`supportedModuleHPresheafZeroIso` followed by `tildeCompSupportedSubmoduleSectionsTopIso`. -/
@[reassoc]
lemma tildeCompSupportedModuleHTopIsoLocalCohomology_hom_app_zero_comp
    [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R) :
    (tildeCompSupportedModuleHTopIsoLocalCohomology I 0).hom.app M ≫
        (localCohomology.degreeZeroIsoPrimaryComponentFunctor I).hom.app M =
      (((tildeSheafFunctor R).obj M).supportedModuleHPresheafZeroIso
          (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤) ≫
        (tildeCompSupportedSubmoduleSectionsTopIso (IsNoetherian.noetherian I)).hom.app M := by
  rw [tildeCompSupportedModuleHTopIsoLocalCohomology_hom_app_zero]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]; rfl

/-- **Module-level local cohomology comparison (Stacks 0A6T).** Over a Noetherian ring `R`,
`H^q_{V(I)}(Spec R, M~)` is `R`-linearly equivalent to `H^q_I(M)`. -/
@[stacks 0A6T]
def supportedModuleHTopTildeLinearEquivLocalCohomology [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (q : ℕ) :
    (modulesSpecToSheaf.obj (tilde M)).supportedModuleH
        (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q ≃ₗ[R]
      (localCohomology I q).obj M :=
  ((tildeCompSupportedModuleHTopIsoLocalCohomology I q).app M).toLinearEquiv

/-- `supportedModuleHTopTildeLinearEquivLocalCohomology` acts by the component of
`tildeCompSupportedModuleHTopIsoLocalCohomology`. -/
@[simp]
lemma supportedModuleHTopTildeLinearEquivLocalCohomology_apply [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (q : ℕ)
    (x : (modulesSpecToSheaf.obj (tilde M)).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q) :
    supportedModuleHTopTildeLinearEquivLocalCohomology I M q x =
      (tildeCompSupportedModuleHTopIsoLocalCohomology I q).hom.app M x := (rfl)

/-- In degree zero, `supportedModuleHTopTildeLinearEquivLocalCohomology` identifies
`supportedModuleHZeroEquiv` with `primaryComponentEquivSupportedSubmoduleTop` and
`localCohomology.degreeZeroEquivPrimaryComponent`. -/
lemma degreeZeroEquivPrimaryComponent_supportedModuleHTopTildeLinearEquivLocalCohomology
    [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (x : (modulesSpecToSheaf.obj (tilde M)).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ 0) :
    localCohomology.degreeZeroEquivPrimaryComponent I M
        (supportedModuleHTopTildeLinearEquivLocalCohomology I M 0 x) =
      (primaryComponentEquivSupportedSubmoduleTop (IsNoetherian.noetherian I) M).symm
        ((modulesSpecToSheaf.obj (tilde M)).supportedModuleHZeroEquiv
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ x) := by
  let hI : I.FG := IsNoetherian.noetherian I
  refine (primaryComponentEquivSupportedSubmoduleTop hI M).injective ?_
  rw [LinearEquiv.apply_symm_apply]; apply Subtype.ext
  rw [coe_primaryComponentEquivSupportedSubmoduleTop_apply,
    localCohomology.coe_degreeZeroEquivPrimaryComponent_apply,
    supportedModuleHTopTildeLinearEquivLocalCohomology_apply]
  have h1 := ConcreteCategory.congr_hom
    (NatTrans.congr_app (localCohomology.degreeZeroIsoPrimaryComponentFunctor_hom_comp_ι I) M)
    ((tildeCompSupportedModuleHTopIsoLocalCohomology I 0).hom.app M x)
  have h2 := ConcreteCategory.congr_hom
    (tildeCompSupportedModuleHTopIsoLocalCohomology_hom_app_zero_comp I M) x
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    tildeSheafFunctor_obj] at h1 h2
  rw [← h1]
  -- Expose `(tildeSheafFunctor R).obj M` as `modulesSpecToSheaf.obj (tilde M)`.
  change tilde.toOpen M ⊤ (I.primaryComponentFunctorι.app M
      ((localCohomology.degreeZeroIsoPrimaryComponentFunctor I).hom.app M
        ((tildeCompSupportedModuleHTopIsoLocalCohomology I 0).hom.app M x))) = _
  erw [← ModuleCat.comp_apply, h2, ModuleCat.comp_apply]
  let s := (((tildeSheafFunctor R).obj M).supportedModuleHPresheafZeroIso
    (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤) x
  change ((tildeCompSupportedSubmoduleSectionsTopIso hI).hom.app M ≫
      I.primaryComponentFunctorι.app M ≫ tilde.toOpen M ⊤) s = _
  erw [← tildeCompSupportedSubmoduleSectionsTopIso_inv_app_comp_supportedSubmoduleι hI M,
    ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact (supportedSubmoduleι_hom_app_apply _ _ (op ⊤) s).trans
    (coe_supportedModuleHPresheafZeroIso_hom_app_apply _ _ (op ⊤) x)

/-- `supportedModuleHTopTildeLinearEquivLocalCohomology` commutes with morphisms `f : M ⟶ N` of
`R`-modules. -/
lemma supportedModuleHTopTildeLinearEquivLocalCohomology_naturality [IsNoetherianRing R]
    (I : Ideal R) {M N : ModuleCat.{u} R} (f : M ⟶ N) (q : ℕ)
    (x : (modulesSpecToSheaf.obj (tilde M)).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q) :
    (localCohomology I q).map f (supportedModuleHTopTildeLinearEquivLocalCohomology I M q x) =
      supportedModuleHTopTildeLinearEquivLocalCohomology I N q
        (((supportedModuleHPresheafFunctor (Spec.zeroLocusClosed (R := R) (I : Set R)) q).map
          ((tildeSheafFunctor R).map f)).app (op ⊤) x) :=
  (ConcreteCategory.congr_hom
    ((tildeCompSupportedModuleHTopIsoLocalCohomology I q).hom.naturality f) x).symm

end Comparison

end TauCeti.AlgebraicGeometry
