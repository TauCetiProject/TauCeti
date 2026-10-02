/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.FinitePresentationDescent
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Base change of the sheaf associated with a module

For a ring map `φ : R ⟶ S` and an `R`-module `M`, the pullback of the quasi-coherent sheaf `M~`
along `Spec φ : Spec S ⟶ Spec R` is the sheaf associated with the base change `S ⊗_R M`:
`(Spec φ)^* M~ ≅ (S ⊗_R M)~`, naturally in `M`.

Both functors `M ↦ (Spec φ)^* M~` and `M ↦ (S ⊗_R M)~` are left adjoint to taking global sections
followed by restriction of scalars along `φ`, so the isomorphism is the uniqueness of left
adjoints. On global sections it sends the pullback of the section `m` of `M~` to the section
`1 ⊗ m`.

As an application, the sheaf associated with a finitely generated projective `R`-module is
finite locally free. Every prime `p` of `R` has a basic open neighbourhood `D(r)` on which `M_r`
is a finite free `R_r`-module. Since `D(r) ≅ Spec R_r`, the restriction of `M~` to `D(r)` is the
pullback of `M~` to `Spec R_r`, which is the sheaf associated with `R_r ⊗_R M ≅ M_r`, hence
free of finite rank.

## Main declarations

* `TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso`: the isomorphism
  `(Spec φ)^* M~ ≅ (S ⊗_R M)~`, natural in `M`;
* `TauCeti.AlgebraicGeometry.unit_tildeFunctorCompPullbackIso_hom_app`: its characterization
  on global sections;
* `TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde`: `M~` is finite locally free when `M`
  is finitely generated and projective.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 (e)
* [The Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

section BaseChange

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Global sections of the pushforward along `Spec φ` are the global sections upstairs, with
scalars restricted along `φ`. -/
def pushforwardCompModuleSpecΓFunctorIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤))

private lemma pushforwardCompModulesSpecToSheafIso_hom_app_top_apply
    (N : (Spec S).Modules)
    (x : (modulesSpecToSheaf.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N)).obj.obj
      (.op ⊤)) :
    ((pushforwardCompModulesSpecToSheafIso φ).hom.app N).1.app (.op ⊤) x = x := rfl

private lemma pushforwardCompModulesSpecToSheafIso_inv_app_top_apply
    (N : (Spec S).Modules)
    (x : ((modulesSpecToSheaf.obj N).obj.obj (.op ⊤))) :
    ((pushforwardCompModulesSpecToSheafIso φ).inv.app N).1.app (.op ⊤) x = x := rfl

/-- `pushforwardCompModuleSpecΓFunctorIso` is the identity on global sections. -/
@[simp]
lemma pushforwardCompModuleSpecΓFunctorIso_hom_app_apply (N : (Spec S).Modules)
    (x : (moduleSpecΓFunctor (R := R)).obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) :
    (_root_.ModuleCat.Hom.hom ((pushforwardCompModuleSpecΓFunctorIso φ).hom.app N) :
      (moduleSpecΓFunctor (R := R)).obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N) →ₗ[R]
        (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := S)).obj N)) x = x :=
  pushforwardCompModulesSpecToSheafIso_hom_app_top_apply φ N x

/-- The inverse of `pushforwardCompModuleSpecΓFunctorIso` is the identity on global sections. -/
@[simp]
lemma pushforwardCompModuleSpecΓFunctorIso_inv_app_apply (N : (Spec S).Modules)
    (x : (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := S)).obj N)) :
    (_root_.ModuleCat.Hom.hom ((pushforwardCompModuleSpecΓFunctorIso φ).inv.app N) :
      (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := S)).obj N) →ₗ[R]
        (moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) x = x :=
  pushforwardCompModulesSpecToSheafIso_inv_app_top_apply φ N x

/-- The pullback along `Spec φ` of the sheaf associated with an `R`-module `M` is the sheaf
associated with the base change `S ⊗_R M`, naturally in `M`. -/
def tildeFunctorCompPullbackIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  Adjunction.leftAdjointUniq
    (((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
        (pushforwardCompModuleSpecΓFunctorIso φ))
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S)))

/-- The characteristic property of `tildeFunctorCompPullbackIso` on global sections: it sends the
pullback of the section `m` of `M~` to the section `1 ⊗ m` of `(S ⊗_R M)~`. -/
@[simp]
theorem unit_tildeFunctorCompPullbackIso_hom_app (M : ModuleCat.{u} R) :
    (tilde.adjunction (R := R)).unit.app M ≫
      (moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)) ≫
      (pushforwardCompModuleSpecΓFunctorIso φ).hom.app _ ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((moduleSpecΓFunctor (R := S)).map ((tildeFunctorCompPullbackIso φ).hom.app M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map ((tilde.adjunction (R := S)).unit.app _) := by
  have := Adjunction.unit_leftAdjointUniq_hom_app
    (((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
        (pushforwardCompModuleSpecΓFunctorIso φ))
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))) M
  simp only [Adjunction.comp_unit_app, Functor.comp_map] at this
  exact this

end BaseChange

section FiniteLocallyFree

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- A basis of `M_r` over `R_r` trivializes `M~` over the basic open `D(r)`: the restriction of
`M~` to `D(r) ≅ Spec R_r` is the pullback of `M~` to `Spec R_r`, which is the sheaf associated
with `R_r ⊗_R M ≅ M_r`. -/
private def overBasicOpenIsoFree (r : R) {ι : Type u}
    (b : Module.Basis ι (Localization.Away r) (LocalizedModule.Away r M)) :
    -- `Spec R` is definitionally `PrimeSpectrum R`, but the `Opens` type carries the
    -- scheme category instance needed by `over`.
    (tilde M).over (show (Spec R).Opens from PrimeSpectrum.basicOpen r) ≅
      SheafOfModules.free ι :=
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let φ : R ⟶ CommRingCat.of (Localization.Away r) := CommRingCat.ofHom (algebraMap _ _)
  let e := basicOpenIsoSpecAway r
  let E := Scheme.Modules.overEquiv U
  let N := tilde M
  -- Pullbacks and the inverse of `E` are left adjoints, so they preserve free sheaves of modules;
  -- the functors are rebound with their types as functors between categories of sheaves of
  -- modules, where the colimit-preservation instances are sought.
  let P : SheafOfModules.{u} (Spec (.of (Localization.Away r))).ringCatSheaf ⥤
      SheafOfModules.{u} (U : Scheme.{u}).ringCatSheaf := Scheme.Modules.pullback e.hom
  let F : SheafOfModules.{u} (U : Scheme.{u}).ringCatSheaf ⥤
      SheafOfModules.{u} ((Spec R).ringCatSheaf.over U) := E.inverse
  have : Limits.PreservesColimitsOfShape (Discrete ι) P :=
    (Scheme.Modules.pullbackPushforwardAdjunction e.hom).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : Limits.PreservesColimitsOfShape (Discrete ι) F :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  E.unitIso.app _ ≪≫ E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app N ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫
    (Scheme.Modules.pullbackCongr (basicOpenIsoSpecAway_hom_SpecMap r).symm).app N ≪≫
    ((Scheme.Modules.pullbackComp e.hom (Spec.map φ)).app N).symm ≪≫
    P.mapIso ((tildeFunctorCompPullbackIso φ).app M ≪≫
      (tilde.functor _).mapIso (M.extendScalarsLocalizationIso _ ≪≫
        b.repr.toModuleIso) ≪≫ tildeFinsupp ι) ≪≫
    (SheafOfModules.mapFreeIso P ι (Scheme.Modules.pullbackObjUnitIso e.hom).symm).symm) ≪≫
  (SheafOfModules.mapFreeIso F ι (E.unitIso.app _)).symm

/-- The sheaf associated with a finitely generated projective `R`-module is a finite locally free
`𝒪_{Spec R}`-module. -/
theorem isFiniteLocallyFree_tilde [Module.Finite R M] [Module.Projective R M] :
    Scheme.Modules.isFiniteLocallyFree (Spec R) (tilde M) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  -- Every prime `p` has a basic open neighbourhood `D(r)` on which `M_r` is free of finite rank:
  -- `M_p` is free since `M` is projective, and a finite basis of `M_p` spreads out to some `M_r`.
  have hbasis (p : PrimeSpectrum R) : ∃ r ∉ p.asIdeal, ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (Module.Basis ι (Localization.Away r) (LocalizedModule.Away r M)) := by
    have : Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) :=
      Set.eq_univ_iff_forall.mp (Module.freeLocus_eq_univ_iff.mpr inferInstance) p
    obtain ⟨r, hr, b, -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ M) (Localization.AtPrime p.asIdeal)
      (Module.Free.chooseBasis (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M))
    exact ⟨r, hr, _, inferInstance, ⟨b⟩⟩
  choose r hr ι _ b using hbasis
  let U (p : PrimeSpectrum R) : (Spec R).Opens := PrimeSpectrum.basicOpen (r p)
  have hU : (Opens.grothendieckTopology (Spec R)).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact .mk <| top_le_iff.mp fun p _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hr p⟩
  have h (p : PrimeSpectrum R) : SheafOfModules.isFiniteLocallyFree
      ((Spec R).ringCatSheaf.over (U p)) ((tilde M).over (U p)) :=
    (SheafOfModules.isFiniteLocallyFree ((Spec R).ringCatSheaf.over (U p))).prop_of_iso
      (overBasicOpenIsoFree M (r p) (b p).some).symm
      ⟨inferInstance, TauCeti.SheafOfModules.isFinitePresentation_free (ι p)⟩
  have (p : PrimeSpectrum R) : ((tilde M).over (U p)).IsLocallyFree := (h p).1
  have (p : PrimeSpectrum R) : ((tilde M).over (U p)).IsFinitePresentation := (h p).2
  exact ⟨SheafOfModules.IsLocallyFree.of_coversTop (M := tilde M) U hU,
    SheafOfModules.IsFinitePresentation.of_coversTop (tilde M) U hU⟩

end FiniteLocallyFree

end

end AlgebraicGeometry

end TauCeti
