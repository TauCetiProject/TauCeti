/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Localization
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic

/-!
# Affine comparison for exterior powers

Exterior powers of quasicoherent modules on a spectrum are computed by exterior powers
of modules. The comparison sends a wedge of module elements to the sheafified wedge of
their associated global sections.

The affine computation uses the localization of exterior powers on basic opens and
Mathlib's equivalence between morphisms into a sheaf and their restrictions to a basis.
The local scalar-linearity argument adapts
`AlgebraicGeometry.SpecModulesToSheafFullyFaithful` to a presheaf source.

## References

* [The Stacks Project, Lemma 10.13.6](https://stacks.math.columbia.edu/tag/0C6F).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2.
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace TauCeti.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}}

private abbrev exteriorPresheaf (M : ModuleCat.{u} R) (n : ℕ) :=
  (PresheafOfModulesOfCommRing.exteriorPower (R := (Spec R).presheaf) n).obj (tilde M).val

private abbrev specPresheaf (P : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj) :
    (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  (PresheafOfModules.forgetToPresheafModuleCat (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj P ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom

private def exteriorToOpen (M : ModuleCat.{u} R) (n : ℕ) (U : (Spec R).Opens) :
    M.exteriorPower n ⟶ (specPresheaf (exteriorPresheaf M n)).obj (.op U) := by
  let N := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U)
  let A := (Spec R).presheaf.obj (.op U)
  let : Module A N := N.isModule
  let NR : Module R N := Module.compHom N (algebraMap R A)
  let NT : @IsScalarTower R A N _ N.isModule.toSMul NR.toSMul :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : M →ₗ[R] N := (tilde.toOpen M U).hom
  let E := (specPresheaf (exteriorPresheaf M n)).obj (.op U)
  let AE : Module A E := (⋀[A]^n N).module
  let : @IsScalarTower R A E _ AE.toSMul
      E.isModule.toSMul := by
    -- The first action in the tower is the action of the ring of sections.
    exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine ModuleCat.exteriorPower.desc
    { toFun m := exteriorPower.ιMulti A n (fun i ↦ φ (m i))
      map_update_add' m i a b := by
        simp only [Function.apply_update (fun _ ↦ φ), map_add]
        exact (exteriorPower.ιMulti A n).map_update_add _ _ _ _
      map_update_smul' m i r a := by
        simp only [Function.apply_update (fun _ ↦ φ), map_smul]
        rw [← IsScalarTower.algebraMap_smul (Γ(Spec R, U)) r (φ a)]
        rw [(exteriorPower.ιMulti A n).map_update_smul]
        exact IsScalarTower.algebraMap_smul A r _
      map_eq_zero_of_eq' m i j h hij :=
        (exteriorPower.ιMulti A n).map_eq_zero_of_eq _
          (congrArg φ h) hij }

private lemma exteriorToOpen_mk (M : ModuleCat.{u} R) (n : ℕ) (U : (Spec R).Opens)
    (m : Fin n → M) :
    exteriorToOpen M n U (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk
        (M := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
        (fun i ↦ tilde.toOpen M U (m i)) :=
  ModuleCat.exteriorPower.desc_mk _ _

private lemma exteriorToOpen_res (M : ModuleCat.{u} R) (n : ℕ)
    {U V : (Spec R).Opens} (i : V ⟶ U) :
    exteriorToOpen M n U ≫ (specPresheaf (exteriorPresheaf M n)).map i.op =
      exteriorToOpen M n V := by
  apply ModuleCat.exteriorPower.hom_ext
  ext m
  simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.comp_apply,
    exteriorToOpen_mk]
  -- The forgetful functor only changes scalar structures, retaining the restriction map.
  change (exteriorPresheaf M n).map i.op
    (ModuleCat.exteriorPower.mk
      (M := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
      (fun j ↦ tilde.toOpen M U (m j))) = _
  erw [PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk]
  exact congrArg (ModuleCat.exteriorPower.mk
    (M := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op V)))
    (funext fun j ↦ ConcreteCategory.congr_hom (tilde.toOpen_res M U V i) (m j))

private instance exteriorToOpen_isLocalized (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    IsLocalizedModule (.powers f) (exteriorToOpen M n (PrimeSpectrum.basicOpen f)).hom := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let N := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U)
  let A := (Spec R).presheaf.obj (.op U)
  let : Module A N := N.isModule
  let NR : Module R N := Module.compHom N (algebraMap R A)
  let NT : @IsScalarTower R A N _ N.isModule.toSMul NR.toSMul :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : M →ₗ[R] N := (tilde.toOpen M U).hom
  let : IsLocalizedModule (.powers f) φ := inferInstanceAs
    (IsLocalizedModule (.powers f) (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)
  let E := (specPresheaf (exteriorPresheaf M n)).obj (.op U)
  let AE : Module A E := (⋀[A]^n N).module
  let ET : @IsScalarTower R A E _ AE.toSMul E.isModule.toSMul :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact @LinearMap.isLocalizedModule_exteriorPower R A M N _ _ _ _ M.isModule _ NR
    N.isModule NT φ (.powers f) inferInstance inferInstance n E.isModule ET
    (exteriorToOpen M n U).hom (exteriorToOpen_mk M n U)

private def exteriorBasicIso (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    (specPresheaf (exteriorPresheaf M n)).obj (.op (PrimeSpectrum.basicOpen f)) ≅
      (modulesSpecToSheaf.obj (tilde (M.exteriorPower n))).obj.obj
        (.op (PrimeSpectrum.basicOpen f)) :=
  (IsLocalizedModule.linearEquiv (.powers f)
    (exteriorToOpen M n (PrimeSpectrum.basicOpen f)).hom
    (tilde.toOpen (M.exteriorPower n) (PrimeSpectrum.basicOpen f)).hom).toModuleIso

private lemma exteriorBasicIso_comp (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    exteriorToOpen M n (PrimeSpectrum.basicOpen f) ≫ (exteriorBasicIso M n f).hom =
      tilde.toOpen (M.exteriorPower n) (PrimeSpectrum.basicOpen f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact IsLocalizedModule.linearEquiv_apply (.powers f)
    (exteriorToOpen M n (PrimeSpectrum.basicOpen f)).hom
    (tilde.toOpen (M.exteriorPower n) (PrimeSpectrum.basicOpen f)).hom x

private def exteriorBasisComparison (M : ModuleCat.{u} R) (n : ℕ) :
    (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        specPresheaf (exteriorPresheaf M n) ⟶
      (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        (modulesSpecToSheaf.obj (tilde (M.exteriorPower n))).obj where
  app f := (exteriorBasicIso M n f.unop).hom
  naturality {f g} i := by
    ext1
    apply IsLocalizedModule.ext (.powers (M := R) f.unop)
      (exteriorToOpen M n (PrimeSpectrum.basicOpen f.unop)).hom
    · rw [Subtype.forall]
      -- Inverting the defining function on a smaller basic open makes all its powers units.
      change Submonoid.powers (M := R) f.unop ≤ (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap]
      exact (tilde (M.exteriorPower n)).isUnit_algebraMap_end_of_le_basicOpen
        f.unop i.unop.hom.le
    · -- Convert composition of linear maps to composition in `ModuleCat`.
      change (exteriorToOpen M n (PrimeSpectrum.basicOpen f.unop) ≫
        (specPresheaf (exteriorPresheaf M n)).map
          ((inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op.map i) ≫
        (exteriorBasicIso M n g.unop).hom).hom =
        (exteriorToOpen M n (PrimeSpectrum.basicOpen f.unop) ≫
          (exteriorBasicIso M n f.unop).hom ≫
          (modulesSpecToSheaf.obj (tilde (M.exteriorPower n))).obj.map
            ((inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op.map i)).hom
      erw [← Category.assoc, exteriorToOpen_res, exteriorBasicIso_comp,
        ← Category.assoc, exteriorBasicIso_comp]
      exact congrArg ModuleCat.Hom.hom (tilde.toOpen_res (M.exteriorPower n) _ _ i.unop.hom).symm

private def exteriorComparisonR (M : ModuleCat.{u} R) (n : ℕ) :
    specPresheaf (exteriorPresheaf M n) ⟶
      (modulesSpecToSheaf.obj (tilde (M.exteriorPower n))).obj :=
  TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens
    (exteriorBasisComparison M n)

private lemma exteriorComparisonR_app_basic (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    (exteriorComparisonR M n).app (.op (PrimeSpectrum.basicOpen f)) =
      (exteriorBasicIso M n f).hom :=
  TopCat.Sheaf.extend_hom_app _ _ PrimeSpectrum.isBasis_basic_opens _ f

private def exteriorComparison (M : ModuleCat.{u} R) (n : ℕ) :
    exteriorPresheaf M n ⟶ (tilde (M.exteriorPower n)).val :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (exteriorComparisonR M n) (forget₂ (ModuleCat R) AddCommGrpCat))
    (fun U t m ↦ by
      let : Module (((Spec R).presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
          ((tilde (M.exteriorPower n)).val.obj U) :=
        ((tilde (M.exteriorPower n)).val.obj U).isModule
      -- Linearity over a ring of sections can be checked on the basic-open basis,
      -- where every `R`-linear map between section modules is localization-linear.
      apply TopCat.Presheaf.IsSheaf.section_ext (tilde (M.exteriorPower n)).isSheaf
      intro x hxU
      obtain ⟨V, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩ :=
        PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
      refine ⟨_, hfU, hxf, ?_⟩
      let i : PrimeSpectrum.basicOpen f ⟶ U.unop := homOfLE hfU
      have hn (z : (exteriorPresheaf M n).obj U) :
          (exteriorComparisonR M n).app (.op (PrimeSpectrum.basicOpen f))
              ((exteriorPresheaf M n).map i.op z) =
            (tilde (M.exteriorPower n)).val.map i.op ((exteriorComparisonR M n).app U z) :=
        ConcreteCategory.congr_hom ((exteriorComparisonR M n).naturality i.op) z
      -- Forgetting to abelian groups retains these component functions.
      change (tilde (M.exteriorPower n)).val.map i.op
        ((exteriorComparisonR M n).app U (t • m)) =
        (tilde (M.exteriorPower n)).val.map i.op
          (t • (show (tilde (M.exteriorPower n)).val.obj U from
            (exteriorComparisonR M n).app U m))
      erw [← hn, (exteriorPresheaf M n).map_smul,
        (tilde (M.exteriorPower n)).val.map_smul, ← hn]
      let A := (Spec R).presheaf.obj (.op (PrimeSpectrum.basicOpen f))
      let : Algebra R A := inferInstanceAs
        (Algebra R ((Spec.structureSheaf R).presheaf.obj (.op (PrimeSpectrum.basicOpen f))))
      let : IsLocalization (.powers f) A := inferInstanceAs
        (IsLocalization (.powers f)
          ((Spec.structureSheaf R).presheaf.obj (.op (PrimeSpectrum.basicOpen f))))
      let E := (specPresheaf (exteriorPresheaf M n)).obj (.op (PrimeSpectrum.basicOpen f))
      let F := (modulesSpecToSheaf.obj (tilde (M.exteriorPower n))).obj.obj
        (.op (PrimeSpectrum.basicOpen f))
      let EA : Module A E := ((exteriorPresheaf M n).obj (.op (PrimeSpectrum.basicOpen f))).isModule
      let FA : Module A F := ((tilde (M.exteriorPower n)).val.obj
        (.op (PrimeSpectrum.basicOpen f))).isModule
      let : @IsScalarTower R A E _ EA.toSMul E.isModule.toSMul :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      let : @IsScalarTower R A F _ FA.toSMul F.isModule.toSMul :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      exact (IsLocalization.linearMap_compatibleSMul (.powers f) A E F).map_smul
        ((exteriorComparisonR M n).app (.op (PrimeSpectrum.basicOpen f))).hom _ _)

private lemma exteriorComparison_basic_bijective (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    Function.Bijective ((exteriorComparison M n).app (.op (PrimeSpectrum.basicOpen f))) := by
  -- The constructor keeps the functions of the basis extension.
  change Function.Bijective ((exteriorComparisonR M n).app (.op (PrimeSpectrum.basicOpen f)))
  rw [exteriorComparisonR_app_basic]
  exact ConcreteCategory.bijective_of_isIso _

private def exteriorToOpenNatTrans (M : ModuleCat.{u} R) (n : ℕ) :
    (Functor.const (Spec R).Opensᵒᵖ).obj (M.exteriorPower n) ⟶
      specPresheaf (exteriorPresheaf M n) where
  app U := exteriorToOpen M n U.unop
  naturality _ _ i :=
    (Category.id_comp _).trans (exteriorToOpen_res M n i.unop).symm

private def tildeToOpenNatTrans (M : ModuleCat.{u} R) :
    (Functor.const (Spec R).Opensᵒᵖ).obj M ⟶ (modulesSpecToSheaf.obj (tilde M)).obj where
  app U := tilde.toOpen M U.unop
  naturality _ _ i :=
    (Category.id_comp _).trans (tilde.toOpen_res M _ _ i.unop).symm

private lemma exteriorComparisonR_comp_toOpen (M : ModuleCat.{u} R) (n : ℕ) :
    exteriorToOpenNatTrans M n ≫ exteriorComparisonR M n =
      tildeToOpenNatTrans (M.exteriorPower n) := by
  apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
  intro f
  -- These components are the two maps on basic opens used to define the comparison.
  change exteriorToOpen M n (PrimeSpectrum.basicOpen f) ≫
    (exteriorComparisonR M n).app (.op (PrimeSpectrum.basicOpen f)) = _
  rw [exteriorComparisonR_app_basic]
  exact exteriorBasicIso_comp M n f

private instance exteriorComparison_locallyInjective (M : ModuleCat.{u} R) (n : ℕ) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Spec R))
      ((PresheafOfModules.toPresheaf _).map (exteriorComparison M n)) where
  equalizerSieve_mem {U} a b h := by
    intro x hxU
    obtain ⟨V, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
    refine ⟨_, homOfLE hfU, ?_, hxf⟩
    apply (exteriorComparison_basic_bijective M n f).1
    have hab : (exteriorComparison M n).app U a = (exteriorComparison M n).app U b := h
    -- The underlying abelian-group restrictions are the restrictions of the module presheaf.
    change (exteriorComparison M n).app _ ((exteriorPresheaf M n).map (homOfLE hfU).op a) =
      (exteriorComparison M n).app _ ((exteriorPresheaf M n).map (homOfLE hfU).op b)
    erw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg ((tilde (M.exteriorPower n)).val.map (homOfLE hfU).op) hab

private instance exteriorComparison_locallySurjective (M : ModuleCat.{u} R) (n : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Spec R))
      ((PresheafOfModules.toPresheaf _).map (exteriorComparison M n)) where
  imageSieve_mem {U} a := by
    intro x hxU
    obtain ⟨V, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.2
    exact ⟨_, homOfLE hfU,
      (exteriorComparison_basic_bijective M n f).2
        ((tilde (M.exteriorPower n)).val.map (homOfLE hfU).op a), hxf⟩

private lemma exteriorComparisonR_toOpen (M : ModuleCat.{u} R) (n : ℕ)
    (U : (Spec R).Opens) :
    exteriorToOpen M n U ≫ (exteriorComparisonR M n).app (.op U) =
      tilde.toOpen (M.exteriorPower n) U :=
  congrArg (fun α ↦ α.app (.op U)) (exteriorComparisonR_comp_toOpen M n)

private def specPresheafMap {P Q : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj}
    (φ : P ⟶ Q) : specPresheaf P ⟶ specPresheaf Q :=
  Functor.whiskerRight
    ((PresheafOfModules.forgetToPresheafModuleCat (.op ⊤)
      (Limits.initialOpOfTerminal Limits.isTerminalTop)).map φ)
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)

private lemma exteriorToOpen_map (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N)
    (U : (Spec R).Opens) :
    exteriorToOpen M n U ≫ (specPresheafMap
      ((PresheafOfModulesOfCommRing.exteriorPower (R := (Spec R).presheaf) n).map
        (tilde.map φ).val)).app (.op U) =
      ModuleCat.exteriorPower.map φ n ≫ exteriorToOpen N n U := by
  apply ModuleCat.exteriorPower.hom_ext
  ext m
  simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.comp_apply]
  let ψ := PresheafOfModules.Hom.app' (R := (Spec R).presheaf) (tilde.map φ).val (.op U)
  -- The restriction of scalars keeps the underlying exterior-power map.
  change ModuleCat.exteriorPower.map ψ n (exteriorToOpen M n U
      (ModuleCat.exteriorPower.mk m)) =
    exteriorToOpen N n U (ModuleCat.exteriorPower.map φ n (ModuleCat.exteriorPower.mk m))
  have hm : (fun i ↦ ψ (tilde.toOpen M U (m i))) =
      (fun i ↦ tilde.toOpen N U (φ (m i))) := by
    funext i
    exact ConcreteCategory.congr_hom (tilde.toOpen_map_app φ U) (m i)
  exact (congrArg (ModuleCat.exteriorPower.map ψ n) (exteriorToOpen_mk M n U m)).trans
    ((ModuleCat.exteriorPower.map_mk ψ _).trans
      ((congrArg (ModuleCat.exteriorPower.mk
        (M := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde N).val (.op U)))
        hm).trans
        ((congrArg (exteriorToOpen N n U) (ModuleCat.exteriorPower.map_mk φ m)).trans
          (exteriorToOpen_mk N n U (fun i ↦ φ (m i)))).symm))

private lemma exteriorComparisonR_naturality (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    specPresheafMap ((PresheafOfModulesOfCommRing.exteriorPower
      (R := (Spec R).presheaf) n).map (tilde.map φ).val) ≫ exteriorComparisonR N n =
      exteriorComparisonR M n ≫ (modulesSpecToSheaf.map (tilde.map
        (ModuleCat.exteriorPower.map φ n))).hom := by
  apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
  intro f
  simp only [NatTrans.comp_app]
  have h : exteriorToOpen M n (PrimeSpectrum.basicOpen f) ≫
      (specPresheafMap ((PresheafOfModulesOfCommRing.exteriorPower
        (R := (Spec R).presheaf) n).map (tilde.map φ).val)).app
          (.op (PrimeSpectrum.basicOpen f)) ≫
        (exteriorComparisonR N n).app (.op (PrimeSpectrum.basicOpen f)) =
      exteriorToOpen M n (PrimeSpectrum.basicOpen f) ≫
        (exteriorComparisonR M n).app (.op (PrimeSpectrum.basicOpen f)) ≫
        (modulesSpecToSheaf.map (tilde.map (ModuleCat.exteriorPower.map φ n))).hom.app
          (.op (PrimeSpectrum.basicOpen f)) := by
    have h₁ := congrArg (fun t ↦ t ≫
      (exteriorComparisonR N n).app (.op (PrimeSpectrum.basicOpen f)))
      (exteriorToOpen_map n φ (PrimeSpectrum.basicOpen f))
    have h₂ := congrArg (fun t ↦ ModuleCat.exteriorPower.map φ n ≫ t)
      (exteriorComparisonR_toOpen N n (PrimeSpectrum.basicOpen f))
    have h₃ := congrArg (fun t ↦ t ≫
      (modulesSpecToSheaf.map (tilde.map (ModuleCat.exteriorPower.map φ n))).hom.app
        (.op (PrimeSpectrum.basicOpen f)))
      (exteriorComparisonR_toOpen M n (PrimeSpectrum.basicOpen f))
    exact (Category.assoc _ _ _).symm.trans
      (h₁.trans ((Category.assoc _ _ _).trans
        (h₂.trans ((tilde.toOpen_map_app (ModuleCat.exteriorPower.map φ n) _).symm.trans
          (h₃.symm.trans (Category.assoc _ _ _))))))
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.linearMap_ext (.powers f)
    (exteriorToOpen M n (PrimeSpectrum.basicOpen f)).hom
    (tilde.toOpen (N.exteriorPower n) (PrimeSpectrum.basicOpen f)).hom
  exact congrArg ModuleCat.Hom.hom h

private lemma exteriorComparison_naturality (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    (PresheafOfModulesOfCommRing.exteriorPower (R := (Spec R).presheaf) n).map
        (tilde.map φ).val ≫ exteriorComparison N n =
      exteriorComparison M n ≫ (tilde.map (ModuleCat.exteriorPower.map φ n)).val := by
  ext U x
  have h := ConcreteCategory.congr_hom
    (congrArg (fun α ↦ α.app U) (exteriorComparisonR_naturality n φ))
  exact h x

private instance exteriorComparison_sheafification_isIso (M : ModuleCat.{u} R) (n : ℕ) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).map
      (exteriorComparison M n)) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  erw [NatIso.isIso_map_iff (PresheafOfModules.sheafificationCompToSheaf _)]
  exact ((Opens.grothendieckTopology (Spec R)).W_iff _).mp
    ((Opens.grothendieckTopology (Spec R)).W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf _).map (exteriorComparison M n)))

/-- Exterior powers commute with the affine tilde construction over arbitrary commutative
rings and modules. No finite-generation, freeness or flatness assumption is needed. -/
def tildeExteriorPowerIso (n : ℕ) (M : ModuleCat.{u} R) :
    tilde (M.exteriorPower n) ≅ (SheafOfModules.exteriorPower (Spec R).sheaf n).obj (tilde M) :=
  (asIso ((PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).map
    (exteriorComparison M n)) ≪≫
    TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
      (tilde (M.exteriorPower n))).symm ≪≫
    (SheafOfModules.exteriorPowerIso n (tilde M)).symm

/-- On sections over any open, the inverse affine comparison sends the sheafified wedge
of the associated sections of `m₁, …, mₙ` to the associated section of their wedge.
The sheafification unit is necessary: exterior-power sections are sheafified sections,
rather than exterior powers of sections on arbitrary opens. -/
theorem tildeExteriorPowerIso_inv_toOpen_mk (n : ℕ) (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (m : Fin n → M) :
    (tildeExteriorPowerIso n M).inv.val.app (.op U)
      ((SheafOfModules.exteriorPowerIso n (tilde M)).inv.val.app (.op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower (R := (Spec R).presheaf) n).obj
            (tilde M).val)).app (.op U)
          (ModuleCat.exteriorPower.mk
            (M := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
            (fun i ↦ tilde.toOpen M U (m i))))) =
      tilde.toOpen (M.exteriorPower n) U (ModuleCat.exteriorPower.mk m) := by
  let F := PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)
  have h₁ : adj.unit.app (exteriorPresheaf M n) ≫
      (SheafOfModules.forget (Spec R).ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 (Spec R).ringCatSheaf.obj)).map
        (F.map (exteriorComparison M n) ≫
          (TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
            (tilde (M.exteriorPower n))).hom) = exteriorComparison M n :=
    (adj.unit_comp_map_eq_iff _ _).2 (congrArg (fun g ↦ F.map (exteriorComparison M n) ≫ g)
      (TauCeti.SheafOfModules.sheafificationIso_hom (Spec R).ringCatSheaf
        (tilde (M.exteriorPower n))))
  have hmap : (SheafOfModules.exteriorPowerIso n (tilde M)).inv ≫
      (tildeExteriorPowerIso n M).inv = F.map (exteriorComparison M n) ≫
        (TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
          (tilde (M.exteriorPower n))).hom := by
    dsimp only [tildeExteriorPowerIso, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, asIso_hom]
    exact Iso.inv_hom_id_assoc _ _
  have h₂ := congrArg (fun g ↦ adj.unit.app (exteriorPresheaf M n) ≫
    (SheafOfModules.forget (Spec R).ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 (Spec R).ringCatSheaf.obj)).map g) hmap
  have h := ConcreteCategory.congr_hom
    (congrArg (fun α ↦ α.app (.op U)) (h₂.trans h₁))
    (ModuleCat.exteriorPower.mk
      (M := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
      (fun i ↦ tilde.toOpen M U (m i)))
  have hw := ConcreteCategory.congr_hom
    (congrArg (fun α ↦ α.app (.op U)) (exteriorComparisonR_comp_toOpen M n))
    (ModuleCat.exteriorPower.mk m)
  dsimp only [exteriorToOpenNatTrans, tildeToOpenNatTrans] at hw
  simp only [NatTrans.comp_app, ModuleCat.comp_apply] at hw
  exact h.trans ((congrArg ((exteriorComparisonR M n).app (.op U))
    (exteriorToOpen_mk M n U m)).symm.trans hw)

/-- The affine comparison sends the associated section of a wedge to the sheafified wedge
of its associated sections, over every open. -/
theorem tildeExteriorPowerIso_hom_toOpen_mk (n : ℕ) (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (m : Fin n → M) :
    (tildeExteriorPowerIso n M).hom.val.app (.op U)
        (tilde.toOpen (M.exteriorPower n) U (ModuleCat.exteriorPower.mk m)) =
      (SheafOfModules.exteriorPowerIso n (tilde M)).inv.val.app (.op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower (R := (Spec R).presheaf) n).obj
            (tilde M).val)).app (.op U)
          (ModuleCat.exteriorPower.mk
            (M := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
            (fun i ↦ tilde.toOpen M U (m i)))) := by
  have h := congrArg ((tildeExteriorPowerIso n M).hom.val.app (.op U))
    (tildeExteriorPowerIso_inv_toOpen_mk n M U m)
  exact h.symm.trans (ModuleCat.hom_inv_apply
    ((SheafOfModules.evaluation (Spec R).ringCatSheaf (.op U)).mapIso
      (tildeExteriorPowerIso n M)) _)

/-- The inverse affine exterior-power comparison is natural in the module. -/
@[reassoc]
theorem tildeExteriorPowerIso_inv_naturality (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    (SheafOfModules.exteriorPower (Spec R).sheaf n).map (tilde.map φ) ≫
        (tildeExteriorPowerIso n N).inv =
      (tildeExteriorPowerIso n M).inv ≫ tilde.map (ModuleCat.exteriorPower.map φ n) := by
  let F : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj ⥤ (Spec R).Modules :=
    PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)
  let A : (Spec R).Modules := (SheafOfModules.exteriorPower (Spec R).sheaf n).obj (tilde M)
  let B : (Spec R).Modules := (SheafOfModules.exteriorPower (Spec R).sheaf n).obj (tilde N)
  let eM : A ≅ F.obj (exteriorPresheaf M n) := SheafOfModules.exteriorPowerIso n (tilde M)
  let eN : B ≅ F.obj (exteriorPresheaf N n) := SheafOfModules.exteriorPowerIso n (tilde N)
  let iM : A ⟶ tilde (M.exteriorPower n) := (tildeExteriorPowerIso n M).inv
  let iN : B ⟶ tilde (N.exteriorPower n) := (tildeExteriorPowerIso n N).inv
  let aM := F.map (exteriorComparison M n)
  let aN := F.map (exteriorComparison N n)
  let cM := (TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
    (tilde (M.exteriorPower n))).hom
  let cN := (TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
    (tilde (N.exteriorPower n))).hom
  let d := F.map ((PresheafOfModulesOfCommRing.exteriorPower
    (R := (Spec R).presheaf) n).map (tilde.map φ).val)
  let k := tilde.map (ModuleCat.exteriorPower.map φ n)
  let f : A ⟶ B := (SheafOfModules.exteriorPower (Spec R).sheaf n).map (tilde.map φ)
  have he : f = eM.hom ≫ d ≫ eN.inv :=
    SheafOfModules.exteriorPower_map (R := (Spec R).sheaf) n (tilde.map φ)
  have hiM : iM = eM.hom ≫ aM ≫ cM := (rfl)
  have hiN : iN = eN.hom ≫ aN ≫ cN := (rfl)
  have h := F.congr_map (exteriorComparison_naturality n φ)
  have hc : F.map k.val ≫ cN = cM ≫ k :=
    TauCeti.SheafOfModules.sheafificationIso_hom_naturality k
  have hd : d ≫ aN = aM ≫ F.map k.val :=
    (F.map_comp _ _).symm.trans (h.trans (F.map_comp _ _))
  have hh : d ≫ aN ≫ cN = (aM ≫ cM) ≫ k :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ cN) hd).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t ↦ aM ≫ t) hc).trans (Category.assoc _ _ _).symm)))
  -- Named morphisms keep the categorical calculation within the actual section carriers.
  change f ≫ iN = iM ≫ k
  rw [he, hiM, hiN]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (congrArg (fun t ↦ eM.hom ≫ t) hh).trans (Category.assoc _ _ _).symm

/-- The affine exterior-power comparison is natural in the module. -/
@[reassoc]
theorem tildeExteriorPowerIso_hom_naturality (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    tilde.map (ModuleCat.exteriorPower.map φ n) ≫ (tildeExteriorPowerIso n N).hom =
      (tildeExteriorPowerIso n M).hom ≫
        (SheafOfModules.exteriorPower (Spec R).sheaf n).map (tilde.map φ) := by
  exact (Iso.eq_comp_inv (tildeExteriorPowerIso n N)).mp
    (((Iso.inv_comp_eq (tildeExteriorPowerIso n M)).mp
      (tildeExteriorPowerIso_inv_naturality n φ).symm).trans
        (Category.assoc _ _ _).symm)

end TauCeti.AlgebraicGeometry
