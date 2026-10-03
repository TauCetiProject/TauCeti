/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Presentation
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Finite presentation of modules and their associated sheaves

An `R`-module is finitely presented if and only if its associated sheaf on `Spec R` is finitely
presented. More generally, the sections of a finitely presented sheaf over any affine open are
a finitely presented module over its ring of functions. On an affine scheme, the sheaf admits
a global presentation with finitely many generators and relations.

The forward implication uses Mathlib's `presentationTilde`, whose generating and relation
families are precisely those of the module presentation. For the converse, finite local sheaf
presentations can be refined to basic opens. A finite global presentation on an affine scheme
gives a finite module presentation, and Mathlib's localization descent glues these finite
presentations of modules. This supplies the affine algebraic description of coherent sheaves
on locally Noetherian schemes without imposing a Noetherian hypothesis on the affine result.

The module-cokernel construction follows Mathlib's
`AlgebraicGeometry.isIso_fromTildeΓ_of_presentation`, using the fully faithful tilde functor
and its preservation of cokernels.

## References

* The Stacks Project, *Properties of Schemes*, Section 28.17 (Tag 01PA),
  Lemma 28.17.2 (Tag 01PC).
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- Finite generating and relation sets give a finite presentation of the associated sheaf. -/
instance isFinite_presentationTilde (s : Set M) (hs : Submodule.span R s = ⊤)
    (t : Set (s →₀ R))
    (ht : Submodule.span R t = LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M)))
    [Finite s] [Finite t] : (presentationTilde M s hs t ht).IsFinite where
  isFiniteType_generators := ⟨by simpa [presentationTilde] using inferInstanceAs (Finite s)⟩
  isFiniteType_relations := ⟨by simpa [presentationTilde] using inferInstanceAs (Finite t)⟩

/-- The sheaf associated with a finitely presented module is finitely presented. -/
instance isFinitePresentation_tilde [Module.FinitePresentation R M] :
    (tilde M).IsFinitePresentation := by
  obtain ⟨s, hs, t, ht⟩ := Module.FinitePresentation.out (R := R) (M := M)
  let P := presentationTilde M (s : Set M) hs (t : Set (s →₀ R)) ht
  have : P.IsFinite := isFinite_presentationTilde M _ hs _ ht
  let q := P.quasicoherentData
  have : q.IsFinitePresentation := by
    refine { isFinite_presentation := ?_ }
    intro U
    dsimp [q, SheafOfModules.Presentation.quasicoherentData]
    apply +allowSynthFailures SheafOfModules.Presentation.isFinite_map
  exact SheafOfModules.IsFinitePresentation.mk (M := tilde M) ⟨q, inferInstance⟩

/-- A finite global presentation on `Spec R` gives a finitely presented module of global
sections over `R`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finitePresentation_moduleSpecΓ_of_presentation
    (M : (Spec R).Modules) (P : M.Presentation) [P.IsFinite] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  let π := P.generators.π
  let A : (Spec R).Modules := SheafOfModules.free P.relations.I
  let B : (Spec R).Modules := SheafOfModules.free P.generators.I
  let f : A ⟶ B := P.relations.π ≫ kernel.ι π
  have : P.generators.IsFiniteType := SheafOfModules.Presentation.IsFinite.isFiniteType_generators
  have : P.relations.IsFiniteType := SheafOfModules.Presentation.IsFinite.isFiniteType_relations
  have : Finite P.generators.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have : Finite P.relations.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  let eA : tilde (ModuleCat.of R (P.relations.I →₀ R)) ≅ A := tildeFinsupp _
  let eB : tilde (ModuleCat.of R (P.generators.I →₀ R)) ≅ B := tildeFinsupp _
  let g : ModuleCat.of R (P.relations.I →₀ R) ⟶ ModuleCat.of R (P.generators.I →₀ R) :=
    (tilde.functor R).preimage (eA.hom ≫ f ≫ eB.inv)
  let S := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel g)
  have hex : Function.Exact g.hom (cokernel.π g).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
  have : Module.FinitePresentation R (cokernel g : ModuleCat R) :=
    Module.finitePresentation_of_surjective (S.g).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      ((LinearMap.exact_iff.mp hex).symm ▸ Submodule.fg_range g.hom)
  have hg : (tilde.functor R).map g = eA.hom ≫ f ≫ eB.inv :=
    Functor.map_preimage _ _
  have hg' : (tilde.functor R).map g ≫ eB.hom = eA.hom ≫ f := by
    exact eB.eq_comp_inv.mp (hg.trans (Category.assoc _ _ _).symm)
  let e : tilde (cokernel g) ≅ M :=
    PreservesCokernel.iso (tilde.functor R) g ≪≫
      cokernel.mapIso _ f eA eB hg' ≪≫
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit
  let eΓ : (cokernel g : ModuleCat R) ≅ moduleSpecΓFunctor.obj M :=
    (tilde.toTildeΓNatIso (R := R)).app (cokernel g) ≪≫
      (moduleSpecΓFunctor (R := R)).mapIso e
  exact Module.FinitePresentation.of_equiv eΓ.toLinearEquiv

/-- A finite presentation on the slice site of an affine open gives a finitely presented
module of sections over that open. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finitePresentation_sections_of_presentation
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (P : (M.over U).Presentation) [P.IsFinite] :
    Module.FinitePresentation Γ(X, U) Γ(M, U) := by
  let F : SheafOfModules (X.ringCatSheaf.over U) ⥤ SheafOfModules U.toScheme.ringCatSheaf :=
    (Scheme.Modules.overEquiv U).functor
  have : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.overEquiv U).toAdjunction.leftAdjoint_preservesColimits
  -- The isomorphism instances are passed explicitly because the presentation API uses
  -- sheaves of modules, while the comparison isomorphisms use scheme modules.
  let P₀ := P.map F (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm
  have : P₀.IsFinite := SheafOfModules.Presentation.isFinite_map _ _ _
  let e₀ : F.obj (M.over U) ≅ M.restrict U.ι := (Scheme.Modules.overFunctorEquiv U).app M
  let P₁ := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e₀.hom (Iso.isIso_hom e₀) P₀
  have : P₁.IsFinite :=
    @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _ (Iso.isIso_hom e₀) P₀ inferInstance
  let P₂ := Scheme.Modules.presentationRestrict hU.isoSpec.inv P₁
  have : P₂.IsFinite := by
    dsimp [P₂, Scheme.Modules.presentationRestrict]
    apply +allowSynthFailures SheafOfModules.Presentation.isFinite_map
  let e₂ : (M.restrict U.ι).restrict hU.isoSpec.inv ≅ M.restrict hU.fromSpec :=
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hU.isoSpec_inv_ι).app M
  let P₃ := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e₂.hom (Iso.isIso_hom e₂) P₂
  have : P₃.IsFinite :=
    @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _ (Iso.isIso_hom e₂) P₂ inferInstance
  have h : Module.FinitePresentation Γ(X, U)
      (moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)) :=
    Scheme.Modules.finitePresentation_moduleSpecΓ_of_presentation _ P₃
  exact @Module.FinitePresentation.of_equiv _ _ _ _ _ _ _ _
    (M.fromSpecSectionsEquiv hU).symm h

/-- The sections of a finitely presented sheaf over an affine open form a finitely presented
module over the ring of functions on that open. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finitePresentation_sections_of_isAffineOpen
    {X : Scheme.{u}} (M : X.Modules) [M.IsFinitePresentation] (U : X.Opens)
    (hU : IsAffineOpen U) : Module.FinitePresentation Γ(X, U) Γ(M, U) := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have : M.IsQuasicoherent := q.isQuasicoherent
  let s : Set Γ(X, U) := {f | ∃ i, X.basicOpen f ≤ q.X i}
  have hcov : iSup q.X = ⊤ := by
    simpa only [Opens.coversTop_iff, IsOpenCover] using q.coversTop
  have hs : Ideal.span s = ⊤ := by
    apply hU.iSup_basicOpen_eq_self_iff.mp
    refine le_antisymm (iSup_le fun f : s => X.basicOpen_le f.1) ?_
    intro x hxU
    have hx : x ∈ iSup q.X := by simp [hcov]
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hi⟩ hxU
    exact Opens.mem_iSup.mpr ⟨⟨f, i, hf⟩, hxf⟩
  have loc (f : s) : IsLocalization.Away f.1 Γ(X, X.basicOpen f.1) :=
    hU.isLocalization_basicOpen f.1
  have modloc (f : s) : IsLocalizedModule.Away f.1 (M.basicOpenRestrict f.1) :=
    M.isLocalizedModule_basicOpenRestrict hU f.1
  apply Module.FinitePresentation.of_localizationSpan' s hs
    (Rₚ := fun f => Γ(X, X.basicOpen f.1))
    (Mₚ := fun f => Γ(M, X.basicOpen f.1)) (fun f => M.basicOpenRestrict f.1)
  intro f
  obtain ⟨i, hi⟩ := f.2
  let D := X.basicOpen f.1
  let a : D ⟶ q.X i := homOfLE hi
  let P := (q.presentation i).map (SheafOfModules.overMap X.ringCatSheaf a)
    (SheafOfModules.overMapUnitIso a).symm
  let e := (SheafOfModules.overFunctorMap X.ringCatSheaf a).app M
  let P' := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom (Iso.isIso_hom e) P
  have : (q.presentation i).IsFinite := hq.isFinite_presentation i
  have : P.IsFinite := SheafOfModules.Presentation.isFinite_map _ _ _
  have : P'.IsFinite :=
    @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _ (Iso.isIso_hom e) P inferInstance
  exact Scheme.Modules.finitePresentation_sections_of_presentation M D
    (hU.basicOpen f.1) P'

/-- The global sections of a finitely presented sheaf on an affine scheme form a finitely
presented module over its ring of global functions. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finitePresentation_globalSections_of_isAffine
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsFinitePresentation] :
    Module.FinitePresentation Γ(X, ⊤) Γ(M, ⊤) :=
  M.finitePresentation_sections_of_isAffineOpen ⊤ (isAffineOpen_top X)

/-- A finitely presented sheaf on `Spec R` has finitely presented global sections as an
`R`-module. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finitePresentation_moduleSpecΓ
    (M : (Spec R).Modules) [M.IsFinitePresentation] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  have : Module.FinitePresentation Γ(Spec R, ⊤) Γ(M, ⊤) :=
    M.finitePresentation_globalSections_of_isAffine
  have hbij : Function.Bijective (Algebra.linearMap R Γ(Spec R, ⊤)) := by
    simpa [Algebra.coe_linearMap, IsAffineOpen.algebraMap_Spec_obj] using
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)
  have : Module.FinitePresentation R Γ(Spec R, ⊤) :=
    Module.FinitePresentation.of_equiv (LinearEquiv.ofBijective _ hbij)
  exact Module.FinitePresentation.trans R Γ(M, ⊤) Γ(Spec R, ⊤)

/-- A module is finitely presented if and only if its associated sheaf on the spectrum is
finitely presented. -/
@[simp]
theorem _root_.ModuleCat.isFinitePresentation_tilde_iff (M : ModuleCat.{u} R) :
    (tilde M).IsFinitePresentation ↔ Module.FinitePresentation R M := by
  constructor
  · intro h
    let := h
    have hΓ : Module.FinitePresentation R (moduleSpecΓFunctor.obj (tilde M)) :=
      Scheme.Modules.finitePresentation_moduleSpecΓ (tilde M)
    exact @Module.FinitePresentation.of_equiv _ _ _ _ _ _ _ _
      ((tilde.toTildeΓNatIso (R := R)).app M).symm.toLinearEquiv hΓ
  · intro h
    let := h
    exact inferInstance

/-- A finitely presented sheaf on an affine scheme admits a global presentation with
finitely many generators and finitely many relations. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isAffine
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsFinitePresentation] :
    ∃ P : M.Presentation, P.IsFinite := by
  let e := X.isoSpec
  let N := (Scheme.Modules.pullback e.inv).obj M
  have : N.IsFinitePresentation := Scheme.Modules.isFinitePresentation_pullback e.inv M
  have : N.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation N
  let A := moduleSpecΓFunctor.obj N
  have : Module.FinitePresentation Γ(X, ⊤) A :=
    Scheme.Modules.finitePresentation_moduleSpecΓ N
  obtain ⟨s, hs, t, ht⟩ := Module.FinitePresentation.out (R := Γ(X, ⊤)) (M := A)
  let P := presentationTilde A (s : Set A) hs (t : Set (s →₀ Γ(X, ⊤))) ht
  have : P.IsFinite := isFinite_presentationTilde A _ hs _ ht
  -- `fromTildeΓ` uses scheme modules; `Presentation.ofIsIso` uses sheaves of modules.
  let Q := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    (Scheme.Modules.fromTildeΓ N)
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N) P
  have : Q.IsFinite := @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N) P
    (isFinite_presentationTilde A _ hs _ ht)
  exact ⟨M.presentationOfIsoSpec Q,
    Scheme.Modules.isFinite_presentationOfIsoSpec M Q⟩

end

end TauCeti.AlgebraicGeometry
