/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Localization
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Basic

/-!
# Affine comparison for symmetric powers

Symmetric powers of quasicoherent modules on a spectrum are computed by symmetric powers
of modules. The comparison sends a product of module elements to the sheafified product of
their associated global sections.

The affine computation uses the localization of symmetric powers on basic opens and
Mathlib's equivalence between morphisms into a sheaf and their restrictions to a basis.
The construction follows `TauCeti/AlgebraicGeometry/Modules/ExteriorPower/Affine.lean`.
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

private abbrev symmetricPresheaf (M : ModuleCat.{u} R) (n : ℕ) :=
  (PresheafOfModulesOfCommRing.symmetricPower (R := (Spec R).presheaf) n).obj (tilde M).val

private abbrev specPresheaf (P : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj) :
    (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  (PresheafOfModules.forgetToPresheafModuleCat (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj P ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom

private def symmetricToOpenSemilinear (M : ModuleCat.{u} R) (U : (Spec R).Opens) :
    M →ₛₗ[algebraMap R ((Spec R).presheaf.obj (.op U))]
      PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U) :=
  { toFun := fun m ↦ tilde.toOpen M U m
    map_add' := (tilde.toOpen M U).hom.map_add
    map_smul' := (tilde.toOpen M U).hom.map_smul }

private def symmetricToOpen (M : ModuleCat.{u} R) (n : ℕ) (U : (Spec R).Opens) :
    M.symmetricPower n ⟶ (specPresheaf (symmetricPresheaf M n)).obj (.op U) := by
  let A := (Spec R).presheaf.obj (.op U)
  let N := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U)
  let E := (specPresheaf (symmetricPresheaf M n)).obj (.op U)
  let AE : Module A E := (TauCeti.SymmetricAlgebra.homogeneousSubmodule A N n).module
  let : @IsScalarTower R A E _ AE.toSMul E.isModule.toSMul :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact ModuleCat.ofHom (Y := E)
    { toFun := TauCeti.SymmetricAlgebra.homogeneousSubmoduleMapₛₗ
        (symmetricToOpenSemilinear M U) n
      map_add' := map_add _
      map_smul' := fun r x ↦ by
        exact (LinearMap.map_smulₛₗ
          (TauCeti.SymmetricAlgebra.homogeneousSubmoduleMapₛₗ
            (symmetricToOpenSemilinear M U) n) r x).trans
          (IsScalarTower.algebraMap_smul A (M := E) r _)}

private lemma coe_symmetricToOpen (M : ModuleCat.{u} R) (n : ℕ) (U : (Spec R).Opens)
    (x : M.symmetricPower n) :
    Subtype.val (symmetricToOpen M n U x) =
      SymmetricAlgebra.mapₛₗ (symmetricToOpenSemilinear M U) x.1 :=
  TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n x

private lemma symmetricToOpen_res (M : ModuleCat.{u} R) (n : ℕ)
    {U V : (Spec R).Opens} (i : V ⟶ U) :
    symmetricToOpen M n U ≫ (specPresheaf (symmetricPresheaf M n)).map i.op =
      symmetricToOpen M n V := by
  let ψ := (ModuleCat.semilinearMapAddEquiv
    ((Spec R).presheaf.map i.op).hom _ _).symm
      (PresheafOfModulesOfCommRing.map (R := (Spec R).presheaf) (tilde M).val i.op)
  have h := SymmetricAlgebra.mapₛₗ_comp_mapₛₗ (symmetricToOpenSemilinear M U) ψ
    (symmetricToOpenSemilinear M V)
    (fun r ↦ ConcreteCategory.congr_hom
      (StructureSheaf.algebraMap_self_map R (.op V) (.op U) i.op) r)
    (fun m ↦ ConcreteCategory.congr_hom (tilde.toOpen_res M U V i) m)
  ext x
  apply Subtype.ext
  -- Restriction of scalars retains the underlying semilinear map of homogeneous pieces.
  change Subtype.val ((symmetricPresheaf M n).map i.op (symmetricToOpen M n U x)) = _
  erw [PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply,
    coe_symmetricToOpen, coe_symmetricToOpen]
  exact RingHom.congr_fun h x.1

private instance symmetricToOpen_isLocalized (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    IsLocalizedModule (.powers f) (symmetricToOpen M n (PrimeSpectrum.basicOpen f)).hom := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let N := PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U)
  let A := (Spec R).presheaf.obj (.op U)
  let NR : Module R N := Module.compHom N (algebraMap R A)
  let NT : @IsScalarTower R A N _ N.isModule.toSMul NR.toSMul :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : M →ₗ[R] N := (tilde.toOpen M U).hom
  let : IsLocalizedModule (.powers f) φ := inferInstanceAs
    (IsLocalizedModule (.powers f) (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)
  let E := (specPresheaf (symmetricPresheaf M n)).obj (.op U)
  let AE : Module A E := (TauCeti.SymmetricAlgebra.homogeneousSubmodule A N n).module
  let ET : @IsScalarTower R A E _ AE.toSMul E.isModule.toSMul :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact @LinearMap.isLocalizedModule_symmetricPower R A M N _ _ _ _ M.isModule _ NR
    N.isModule NT φ (.powers f) inferInstance inferInstance n E.isModule ET
    (symmetricToOpenSemilinear M U) (fun _ ↦ rfl)
    (symmetricToOpen M n U).hom (coe_symmetricToOpen M n U)

private instance symmetricTildeToOpen_isLocalized (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    IsLocalizedModule (.powers f)
      (tilde.toOpen (M.symmetricPower n) (PrimeSpectrum.basicOpen f)).hom := by
  -- Abstract the bundled module before synthesis: reducing its homogeneous-submodule
  -- presentation first changes the typeclass matching problem.
  have h (N : ModuleCat.{u} R) : IsLocalizedModule.Away f
      (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom := inferInstance
  exact h (M.symmetricPower n)

private def symmetricBasicIso (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    (specPresheaf (symmetricPresheaf M n)).obj (.op (PrimeSpectrum.basicOpen f)) ≅
      (modulesSpecToSheaf.obj (tilde (M.symmetricPower n))).obj.obj
        (.op (PrimeSpectrum.basicOpen f)) :=
  (IsLocalizedModule.linearEquiv (.powers f)
    (symmetricToOpen M n (PrimeSpectrum.basicOpen f)).hom
    (tilde.toOpen (M.symmetricPower n) (PrimeSpectrum.basicOpen f)).hom).toModuleIso

private lemma symmetricBasicIso_comp (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    symmetricToOpen M n (PrimeSpectrum.basicOpen f) ≫ (symmetricBasicIso M n f).hom =
      tilde.toOpen (M.symmetricPower n) (PrimeSpectrum.basicOpen f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact IsLocalizedModule.linearEquiv_apply (.powers f)
    (symmetricToOpen M n (PrimeSpectrum.basicOpen f)).hom
    (tilde.toOpen (M.symmetricPower n) (PrimeSpectrum.basicOpen f)).hom x

private def symmetricBasisComparison (M : ModuleCat.{u} R) (n : ℕ) :
    (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        specPresheaf (symmetricPresheaf M n) ⟶
      (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        (modulesSpecToSheaf.obj (tilde (M.symmetricPower n))).obj where
  app f := (symmetricBasicIso M n f.unop).hom
  naturality {f g} i := by
    ext1
    apply IsLocalizedModule.ext (.powers (M := R) f.unop)
      (symmetricToOpen M n (PrimeSpectrum.basicOpen f.unop)).hom
    · rw [Subtype.forall]
      -- Inverting the defining function on a smaller basic open makes all its powers units.
      change Submonoid.powers (M := R) f.unop ≤ (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap]
      exact (tilde (M.symmetricPower n)).isUnit_algebraMap_end_of_le_basicOpen
        f.unop i.unop.hom.le
    · -- Convert composition of linear maps to composition in `ModuleCat`.
      change (symmetricToOpen M n (PrimeSpectrum.basicOpen f.unop) ≫
        (specPresheaf (symmetricPresheaf M n)).map
          ((inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op.map i) ≫
        (symmetricBasicIso M n g.unop).hom).hom =
        (symmetricToOpen M n (PrimeSpectrum.basicOpen f.unop) ≫
          (symmetricBasicIso M n f.unop).hom ≫
          (modulesSpecToSheaf.obj (tilde (M.symmetricPower n))).obj.map
            ((inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op.map i)).hom
      erw [← Category.assoc, symmetricToOpen_res, symmetricBasicIso_comp,
        ← Category.assoc, symmetricBasicIso_comp]
      exact congrArg ModuleCat.Hom.hom (tilde.toOpen_res (M.symmetricPower n) _ _ i.unop.hom).symm

private def symmetricComparisonR (M : ModuleCat.{u} R) (n : ℕ) :
    specPresheaf (symmetricPresheaf M n) ⟶
      (modulesSpecToSheaf.obj (tilde (M.symmetricPower n))).obj :=
  TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens
    (symmetricBasisComparison M n)

private lemma symmetricComparisonR_app_basic (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    (symmetricComparisonR M n).app (.op (PrimeSpectrum.basicOpen f)) =
      (symmetricBasicIso M n f).hom :=
  TopCat.Sheaf.extend_hom_app _ _ PrimeSpectrum.isBasis_basic_opens _ f

private def symmetricComparison (M : ModuleCat.{u} R) (n : ℕ) :
    symmetricPresheaf M n ⟶ (tilde (M.symmetricPower n)).val :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (symmetricComparisonR M n) (forget₂ (ModuleCat R) AddCommGrpCat))
    (fun U t m ↦ by
      let : Module (((Spec R).presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
          ((tilde (M.symmetricPower n)).val.obj U) :=
        ((tilde (M.symmetricPower n)).val.obj U).isModule
      -- Linearity over a ring of sections can be checked on the basic-open basis,
      -- where every `R`-linear map between section modules is localization-linear.
      apply TopCat.Presheaf.IsSheaf.section_ext (tilde (M.symmetricPower n)).isSheaf
      intro x hxU
      obtain ⟨V, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩ :=
        PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
      refine ⟨_, hfU, hxf, ?_⟩
      let i : PrimeSpectrum.basicOpen f ⟶ U.unop := homOfLE hfU
      have hn (z : (symmetricPresheaf M n).obj U) :
          (symmetricComparisonR M n).app (.op (PrimeSpectrum.basicOpen f))
              ((symmetricPresheaf M n).map i.op z) =
            (tilde (M.symmetricPower n)).val.map i.op ((symmetricComparisonR M n).app U z) :=
        ConcreteCategory.congr_hom ((symmetricComparisonR M n).naturality i.op) z
      -- Forgetting to abelian groups retains these component functions.
      change (tilde (M.symmetricPower n)).val.map i.op
        ((symmetricComparisonR M n).app U (t • m)) =
        (tilde (M.symmetricPower n)).val.map i.op
          (t • (show (tilde (M.symmetricPower n)).val.obj U from
            (symmetricComparisonR M n).app U m))
      erw [← hn, (symmetricPresheaf M n).map_smul,
        (tilde (M.symmetricPower n)).val.map_smul, ← hn]
      let A := (Spec R).presheaf.obj (.op (PrimeSpectrum.basicOpen f))
      let : Algebra R A := inferInstanceAs
        (Algebra R ((Spec.structureSheaf R).presheaf.obj (.op (PrimeSpectrum.basicOpen f))))
      let : IsLocalization (.powers f) A := inferInstanceAs
        (IsLocalization (.powers f)
          ((Spec.structureSheaf R).presheaf.obj (.op (PrimeSpectrum.basicOpen f))))
      let E := (specPresheaf (symmetricPresheaf M n)).obj (.op (PrimeSpectrum.basicOpen f))
      let F := (modulesSpecToSheaf.obj (tilde (M.symmetricPower n))).obj.obj
        (.op (PrimeSpectrum.basicOpen f))
      let EA : Module A E :=
        ((symmetricPresheaf M n).obj (.op (PrimeSpectrum.basicOpen f))).isModule
      let FA : Module A F := ((tilde (M.symmetricPower n)).val.obj
        (.op (PrimeSpectrum.basicOpen f))).isModule
      let : @IsScalarTower R A E _ EA.toSMul E.isModule.toSMul :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      let : @IsScalarTower R A F _ FA.toSMul F.isModule.toSMul :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      exact (IsLocalization.linearMap_compatibleSMul (.powers f) A E F).map_smul
        ((symmetricComparisonR M n).app (.op (PrimeSpectrum.basicOpen f))).hom _ _)

private lemma symmetricComparison_basic_bijective (M : ModuleCat.{u} R) (n : ℕ) (f : R) :
    Function.Bijective ((symmetricComparison M n).app (.op (PrimeSpectrum.basicOpen f))) := by
  -- The constructor keeps the functions of the basis extension.
  change Function.Bijective ((symmetricComparisonR M n).app (.op (PrimeSpectrum.basicOpen f)))
  rw [symmetricComparisonR_app_basic]
  exact ConcreteCategory.bijective_of_isIso _

private def symmetricToOpenNatTrans (M : ModuleCat.{u} R) (n : ℕ) :
    (Functor.const (Spec R).Opensᵒᵖ).obj (M.symmetricPower n) ⟶
      specPresheaf (symmetricPresheaf M n) where
  app U := symmetricToOpen M n U.unop
  naturality _ _ i :=
    (Category.id_comp _).trans (symmetricToOpen_res M n i.unop).symm

private def tildeToOpenNatTrans (M : ModuleCat.{u} R) :
    (Functor.const (Spec R).Opensᵒᵖ).obj M ⟶ (modulesSpecToSheaf.obj (tilde M)).obj where
  app U := tilde.toOpen M U.unop
  naturality _ _ i :=
    (Category.id_comp _).trans (tilde.toOpen_res M _ _ i.unop).symm

private lemma symmetricComparisonR_comp_toOpen (M : ModuleCat.{u} R) (n : ℕ) :
    symmetricToOpenNatTrans M n ≫ symmetricComparisonR M n =
      tildeToOpenNatTrans (M.symmetricPower n) := by
  apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
  intro f
  -- These components are the two maps on basic opens used to define the comparison.
  change symmetricToOpen M n (PrimeSpectrum.basicOpen f) ≫
    (symmetricComparisonR M n).app (.op (PrimeSpectrum.basicOpen f)) = _
  rw [symmetricComparisonR_app_basic]
  exact symmetricBasicIso_comp M n f

private instance symmetricComparison_locallyInjective (M : ModuleCat.{u} R) (n : ℕ) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Spec R))
      ((PresheafOfModules.toPresheaf _).map (symmetricComparison M n)) where
  equalizerSieve_mem {U} a b h := by
    intro x hxU
    obtain ⟨V, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
    refine ⟨_, homOfLE hfU, ?_, hxf⟩
    apply (symmetricComparison_basic_bijective M n f).1
    have hab : (symmetricComparison M n).app U a = (symmetricComparison M n).app U b := h
    -- The underlying abelian-group restrictions are the restrictions of the module presheaf.
    change (symmetricComparison M n).app _ ((symmetricPresheaf M n).map (homOfLE hfU).op a) =
      (symmetricComparison M n).app _ ((symmetricPresheaf M n).map (homOfLE hfU).op b)
    erw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg ((tilde (M.symmetricPower n)).val.map (homOfLE hfU).op) hab

private instance symmetricComparison_locallySurjective (M : ModuleCat.{u} R) (n : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Spec R))
      ((PresheafOfModules.toPresheaf _).map (symmetricComparison M n)) where
  imageSieve_mem {U} a := by
    intro x hxU
    obtain ⟨V, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.2
    exact ⟨_, homOfLE hfU,
      (symmetricComparison_basic_bijective M n f).2
        ((tilde (M.symmetricPower n)).val.map (homOfLE hfU).op a), hxf⟩

private lemma symmetricComparisonR_toOpen (M : ModuleCat.{u} R) (n : ℕ)
    (U : (Spec R).Opens) :
    symmetricToOpen M n U ≫ (symmetricComparisonR M n).app (.op U) =
      tilde.toOpen (M.symmetricPower n) U :=
  congrArg (fun α ↦ α.app (.op U)) (symmetricComparisonR_comp_toOpen M n)

private def specPresheafMap {P Q : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj}
    (φ : P ⟶ Q) : specPresheaf P ⟶ specPresheaf Q :=
  Functor.whiskerRight
    ((PresheafOfModules.forgetToPresheafModuleCat (.op ⊤)
      (Limits.initialOpOfTerminal Limits.isTerminalTop)).map φ)
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)

private lemma symmetricToOpen_map (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N)
    (U : (Spec R).Opens) :
    symmetricToOpen M n U ≫ (specPresheafMap
      ((PresheafOfModulesOfCommRing.symmetricPower (R := (Spec R).presheaf) n).map
        (tilde.map φ).val)).app (.op U) =
      ModuleCat.symmetricPower.map φ n ≫ symmetricToOpen N n U := by
  let ψ := PresheafOfModules.Hom.app' (R := (Spec R).presheaf) (tilde.map φ).val (.op U)
  have h : (SymmetricAlgebra.map _ ψ.hom : _ →+* _).comp
      (SymmetricAlgebra.mapₛₗ (symmetricToOpenSemilinear M U)) =
      (SymmetricAlgebra.mapₛₗ (symmetricToOpenSemilinear N U)).comp
        (SymmetricAlgebra.map R φ.hom : _ →+* _) := by
    apply SymmetricAlgebra.ringHom_ext
    · ext r
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes,
        SymmetricAlgebra.mapₛₗ_algebraMap]
    · intro m
      simp only [RingHom.comp_apply, RingHom.coe_coe, SymmetricAlgebra.map_apply_ι,
        SymmetricAlgebra.mapₛₗ_ι]
      exact congrArg (SymmetricAlgebra.ι _ _)
        (ConcreteCategory.congr_hom (tilde.toOpen_map_app φ U) m)
  ext x
  apply Subtype.ext
  -- Restriction of scalars retains the underlying symmetric-algebra map.
  change Subtype.val (ModuleCat.symmetricPower.map ψ n (symmetricToOpen M n U x)) = _
  erw [ModuleCat.symmetricPower.coe_map_apply, coe_symmetricToOpen,
    coe_symmetricToOpen, ModuleCat.symmetricPower.coe_map_apply]
  exact RingHom.congr_fun h x.1

private lemma symmetricComparisonR_naturality (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    specPresheafMap ((PresheafOfModulesOfCommRing.symmetricPower
      (R := (Spec R).presheaf) n).map (tilde.map φ).val) ≫ symmetricComparisonR N n =
      symmetricComparisonR M n ≫ (modulesSpecToSheaf.map (tilde.map
        (ModuleCat.symmetricPower.map φ n))).hom := by
  apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
  intro f
  simp only [NatTrans.comp_app]
  have h : symmetricToOpen M n (PrimeSpectrum.basicOpen f) ≫
      (specPresheafMap ((PresheafOfModulesOfCommRing.symmetricPower
        (R := (Spec R).presheaf) n).map (tilde.map φ).val)).app
          (.op (PrimeSpectrum.basicOpen f)) ≫
        (symmetricComparisonR N n).app (.op (PrimeSpectrum.basicOpen f)) =
      symmetricToOpen M n (PrimeSpectrum.basicOpen f) ≫
        (symmetricComparisonR M n).app (.op (PrimeSpectrum.basicOpen f)) ≫
        (modulesSpecToSheaf.map (tilde.map (ModuleCat.symmetricPower.map φ n))).hom.app
          (.op (PrimeSpectrum.basicOpen f)) := by
    calc
      _ = ModuleCat.symmetricPower.map φ n ≫
          symmetricToOpen N n (PrimeSpectrum.basicOpen f) ≫
          (symmetricComparisonR N n).app (.op (PrimeSpectrum.basicOpen f)) := by
        simpa only [Category.assoc] using congrArg (fun t ↦ t ≫
          (symmetricComparisonR N n).app (.op (PrimeSpectrum.basicOpen f)))
          (symmetricToOpen_map n φ (PrimeSpectrum.basicOpen f))
      _ = ModuleCat.symmetricPower.map φ n ≫
          tilde.toOpen (N.symmetricPower n) (PrimeSpectrum.basicOpen f) :=
        congrArg (fun t ↦ ModuleCat.symmetricPower.map φ n ≫ t)
          (symmetricComparisonR_toOpen N n (PrimeSpectrum.basicOpen f))
      _ = tilde.toOpen (M.symmetricPower n) (PrimeSpectrum.basicOpen f) ≫
          (modulesSpecToSheaf.map (tilde.map (ModuleCat.symmetricPower.map φ n))).hom.app
            (.op (PrimeSpectrum.basicOpen f)) :=
        (tilde.toOpen_map_app (ModuleCat.symmetricPower.map φ n) _).symm
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun t ↦ t ≫
          (modulesSpecToSheaf.map (tilde.map (ModuleCat.symmetricPower.map φ n))).hom.app
            (.op (PrimeSpectrum.basicOpen f)))
          (symmetricComparisonR_toOpen M n (PrimeSpectrum.basicOpen f)).symm
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.linearMap_ext (.powers f)
    (symmetricToOpen M n (PrimeSpectrum.basicOpen f)).hom
    (tilde.toOpen (N.symmetricPower n) (PrimeSpectrum.basicOpen f)).hom
  exact congrArg ModuleCat.Hom.hom h

private lemma symmetricComparison_naturality (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    (PresheafOfModulesOfCommRing.symmetricPower (R := (Spec R).presheaf) n).map
        (tilde.map φ).val ≫ symmetricComparison N n =
      symmetricComparison M n ≫ (tilde.map (ModuleCat.symmetricPower.map φ n)).val := by
  ext U x
  have h := ConcreteCategory.congr_hom
    (congrArg (fun α ↦ α.app U) (symmetricComparisonR_naturality n φ))
  exact h x

private instance symmetricComparison_sheafification_isIso (M : ModuleCat.{u} R) (n : ℕ) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).map
      (symmetricComparison M n)) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  erw [NatIso.isIso_map_iff (PresheafOfModules.sheafificationCompToSheaf _)]
  exact ((Opens.grothendieckTopology (Spec R)).W_iff _).mp
    ((Opens.grothendieckTopology (Spec R)).W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf _).map (symmetricComparison M n)))

/-- Symmetric powers commute with the affine tilde construction over arbitrary commutative
rings and modules. No finite-generation, freeness or flatness assumption is needed. -/
def tildeSymmetricPowerIso (n : ℕ) (M : ModuleCat.{u} R) :
    tilde (M.symmetricPower n) ≅ (SheafOfModules.symmetricPower (Spec R).sheaf n).obj (tilde M) :=
  (asIso ((PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).map
    (symmetricComparison M n)) ≪≫
    TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
      (tilde (M.symmetricPower n))).symm ≪≫
    (SheafOfModules.symmetricPowerIso n (tilde M)).symm

private lemma tildeSymmetricPowerIso_inv_toOpen (n : ℕ) (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (x : M.symmetricPower n) :
    (tildeSymmetricPowerIso n M).inv.val.app (.op U)
      ((SheafOfModules.symmetricPowerIso n (tilde M)).inv.val.app (.op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)).unit.app
          (symmetricPresheaf M n)).app (.op U) (symmetricToOpen M n U x))) =
      tilde.toOpen (M.symmetricPower n) U x := by
  let F := PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)
  have h₁ : adj.unit.app (symmetricPresheaf M n) ≫
      (SheafOfModules.forget (Spec R).ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 (Spec R).ringCatSheaf.obj)).map
        (F.map (symmetricComparison M n) ≫
          (TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
            (tilde (M.symmetricPower n))).hom) = symmetricComparison M n :=
    (adj.unit_comp_map_eq_iff _ _).2 (congrArg (fun g ↦ F.map (symmetricComparison M n) ≫ g)
      (TauCeti.SheafOfModules.sheafificationIso_hom (Spec R).ringCatSheaf
        (tilde (M.symmetricPower n))))
  have hmap : (SheafOfModules.symmetricPowerIso n (tilde M)).inv ≫
      (tildeSymmetricPowerIso n M).inv = F.map (symmetricComparison M n) ≫
        (TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
          (tilde (M.symmetricPower n))).hom := by
    dsimp only [tildeSymmetricPowerIso, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, asIso_hom]
    exact Iso.inv_hom_id_assoc _ _
  have h₂ := congrArg (fun g ↦ adj.unit.app (symmetricPresheaf M n) ≫
    (SheafOfModules.forget (Spec R).ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 (Spec R).ringCatSheaf.obj)).map g) hmap
  exact (ConcreteCategory.congr_hom
    (congrArg (fun α ↦ α.app (.op U)) (h₂.trans h₁)) (symmetricToOpen M n U x)).trans
      (ConcreteCategory.congr_hom (symmetricComparisonR_toOpen M n U) x)

/-- On every open, the inverse affine comparison sends a sheafified monomial in associated
sections to the associated section of the same monomial. The empty list includes degree zero. -/
theorem tildeSymmetricPowerIso_inv_toOpen_prod (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (l : List M) :
    (tildeSymmetricPowerIso l.length M).inv.val.app (.op U)
      ((SheafOfModules.symmetricPowerIso l.length (tilde M)).inv.val.app (.op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower (R := (Spec R).presheaf) l.length).obj
            (tilde M).val)).app (.op U) ⟨(l.map (fun m ↦ SymmetricAlgebra.ι
              ((Spec R).presheaf.obj (.op U))
              (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
              (tilde.toOpen M U m))).prod, by
            have h := TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule
                ((Spec R).presheaf.obj (.op U))
                (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
                (l.map (fun m ↦ tilde.toOpen M U m))
            erw [List.map_map, List.length_map] at h
            exact h⟩)) =
      tilde.toOpen (M.symmetricPower l.length) U
        ⟨(l.map (SymmetricAlgebra.ι R M)).prod,
        TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule R M l⟩ := by
  have hp : symmetricToOpen M l.length U
      ⟨(l.map (SymmetricAlgebra.ι R M)).prod,
        TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule R M l⟩ =
      ⟨(l.map (fun m ↦ SymmetricAlgebra.ι
              ((Spec R).presheaf.obj (.op U))
              (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
              (tilde.toOpen M U m))).prod, by
            have h := TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule
                ((Spec R).presheaf.obj (.op U))
                (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
                (l.map (fun m ↦ tilde.toOpen M U m))
            erw [List.map_map, List.length_map] at h
            exact h⟩ := by
    apply Subtype.ext
    rw [coe_symmetricToOpen]
    simp only [map_list_prod, List.map_map, Function.comp_def, SymmetricAlgebra.mapₛₗ_ι]
    rfl
  rw [← hp]
  exact tildeSymmetricPowerIso_inv_toOpen l.length M U _

/-- On every open, the affine comparison sends the associated section of a monomial to the
sheafified monomial in its associated sections. -/
theorem tildeSymmetricPowerIso_hom_toOpen_prod (M : ModuleCat.{u} R)
    (U : (Spec R).Opens) (l : List M) :
    (tildeSymmetricPowerIso l.length M).hom.val.app (.op U)
      (tilde.toOpen (M.symmetricPower l.length) U
        ⟨(l.map (SymmetricAlgebra.ι R M)).prod,
        TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule R M l⟩) =
      (SheafOfModules.symmetricPowerIso l.length (tilde M)).inv.val.app (.op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower (R := (Spec R).presheaf) l.length).obj
            (tilde M).val)).app (.op U) ⟨(l.map (fun m ↦ SymmetricAlgebra.ι
              ((Spec R).presheaf.obj (.op U))
              (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
              (tilde.toOpen M U m))).prod, by
            have h := TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule
                ((Spec R).presheaf.obj (.op U))
                (PresheafOfModulesOfCommRing.obj (R := (Spec R).presheaf) (tilde M).val (.op U))
                (l.map (fun m ↦ tilde.toOpen M U m))
            erw [List.map_map, List.length_map] at h
            exact h⟩) := by
  have h := congrArg ((tildeSymmetricPowerIso l.length M).hom.val.app (.op U))
    (tildeSymmetricPowerIso_inv_toOpen_prod M U l)
  exact h.symm.trans (ModuleCat.hom_inv_apply
    ((SheafOfModules.evaluation (Spec R).ringCatSheaf (.op U)).mapIso
      (tildeSymmetricPowerIso l.length M)) _)

/-- The inverse affine symmetric-power comparison is natural in the module. -/
@[reassoc]
theorem tildeSymmetricPowerIso_inv_naturality (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    (SheafOfModules.symmetricPower (Spec R).sheaf n).map (tilde.map φ) ≫
        (tildeSymmetricPowerIso n N).inv =
      (tildeSymmetricPowerIso n M).inv ≫ tilde.map (ModuleCat.symmetricPower.map φ n) := by
  let F : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj ⥤ (Spec R).Modules :=
    PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)
  let A : (Spec R).Modules := (SheafOfModules.symmetricPower (Spec R).sheaf n).obj (tilde M)
  let B : (Spec R).Modules := (SheafOfModules.symmetricPower (Spec R).sheaf n).obj (tilde N)
  let eM : A ≅ F.obj (symmetricPresheaf M n) := SheafOfModules.symmetricPowerIso n (tilde M)
  let eN : B ≅ F.obj (symmetricPresheaf N n) := SheafOfModules.symmetricPowerIso n (tilde N)
  let iM : A ⟶ tilde (M.symmetricPower n) := (tildeSymmetricPowerIso n M).inv
  let iN : B ⟶ tilde (N.symmetricPower n) := (tildeSymmetricPowerIso n N).inv
  let aM := F.map (symmetricComparison M n)
  let aN := F.map (symmetricComparison N n)
  let cM := (TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
    (tilde (M.symmetricPower n))).hom
  let cN := (TauCeti.SheafOfModules.sheafificationIso (Spec R).ringCatSheaf
    (tilde (N.symmetricPower n))).hom
  let d := F.map ((PresheafOfModulesOfCommRing.symmetricPower
    (R := (Spec R).presheaf) n).map (tilde.map φ).val)
  let k := tilde.map (ModuleCat.symmetricPower.map φ n)
  let f : A ⟶ B := (SheafOfModules.symmetricPower (Spec R).sheaf n).map (tilde.map φ)
  have he : f = eM.hom ≫ d ≫ eN.inv :=
    SheafOfModules.symmetricPower_map (R := (Spec R).sheaf) n (tilde.map φ)
  have hiM : iM = eM.hom ≫ aM ≫ cM := (rfl)
  have hiN : iN = eN.hom ≫ aN ≫ cN := (rfl)
  have h := F.congr_map (symmetricComparison_naturality n φ)
  have hc : F.map k.val ≫ cN = cM ≫ k :=
    TauCeti.SheafOfModules.sheafificationIso_hom_naturality k
  have hd : d ≫ aN = aM ≫ F.map k.val :=
    (F.map_comp _ _).symm.trans (h.trans (F.map_comp _ _))
  have hh : d ≫ aN ≫ cN = (aM ≫ cM) ≫ k := by
    calc
      _ = (d ≫ aN) ≫ cN := (Category.assoc _ _ _).symm
      _ = (aM ≫ F.map k.val) ≫ cN := congrArg (fun t ↦ t ≫ cN) hd
      _ = aM ≫ F.map k.val ≫ cN := Category.assoc _ _ _
      _ = aM ≫ cM ≫ k := congrArg (fun t ↦ aM ≫ t) hc
      _ = _ := (Category.assoc _ _ _).symm
  -- Named morphisms keep the categorical calculation within the actual section carriers.
  change f ≫ iN = iM ≫ k
  rw [he, hiM, hiN]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (congrArg (fun t ↦ eM.hom ≫ t) hh).trans (Category.assoc _ _ _).symm

/-- The affine symmetric-power comparison is natural in the module. -/
@[reassoc]
theorem tildeSymmetricPowerIso_hom_naturality (n : ℕ) {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    tilde.map (ModuleCat.symmetricPower.map φ n) ≫ (tildeSymmetricPowerIso n N).hom =
      (tildeSymmetricPowerIso n M).hom ≫
        (SheafOfModules.symmetricPower (Spec R).sheaf n).map (tilde.map φ) := by
  exact (Iso.eq_comp_inv (tildeSymmetricPowerIso n N)).mp
    (((Iso.inv_comp_eq (tildeSymmetricPowerIso n M)).mp
      (tildeSymmetricPowerIso_inv_naturality n φ).symm).trans
        (Category.assoc _ _ _).symm)

/-- The affine symmetric-power comparisons form a natural isomorphism between taking the
symmetric power before and after associating a sheaf to a module. -/
def tildeSymmetricPowerNatIso (n : ℕ) :
    ModuleCat.symmetricPower.functor R n ⋙ tilde.functor R ≅
      tilde.functor R ⋙ SheafOfModules.symmetricPower (Spec R).sheaf n :=
  NatIso.ofComponents (tildeSymmetricPowerIso n)
    (fun φ ↦ tildeSymmetricPowerIso_hom_naturality n φ)

/-- The forward components of the natural affine comparison. -/
theorem tildeSymmetricPowerNatIso_hom_app (n : ℕ) (M : ModuleCat.{u} R) :
    (tildeSymmetricPowerNatIso (R := R) n).hom.app M =
      (tildeSymmetricPowerIso n M).hom :=
  (rfl)

/-- The inverse components of the natural affine comparison. -/
theorem tildeSymmetricPowerNatIso_inv_app (n : ℕ) (M : ModuleCat.{u} R) :
    (tildeSymmetricPowerNatIso (R := R) n).inv.app M =
      (tildeSymmetricPowerIso n M).inv :=
  (rfl)

end TauCeti.AlgebraicGeometry
