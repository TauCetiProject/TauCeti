/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# Coherent sheaves on the spectrum of a Noetherian ring

For a Noetherian ring `R`, finitely presented sheaves on `Spec R` are precisely the sheaves
associated with finite `R`-modules. Restricting the tilde/global-sections adjunction gives an
equivalence with `FGModuleCat R`. In particular, this category of coherent sheaves is abelian,
and its inclusion into all sheaves of modules is exact.

The kernel and cokernel of a morphism of coherent sheaves, computed in all module sheaves,
are again coherent. Thus short exact sequences of coherent sheaves can be used in sheaf
cohomology without changing their ambient kernels or cokernels. The cokernel result needs no
Noetherian hypothesis; the kernel result does.

The construction follows Mathlib's `AlgebraicGeometry.tildeEquiv` and uses the finite-presentation
comparison for tilde sheaves, rather than a new definition of coherence.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.4.
* The Stacks Project, *Schemes*, Section 26.7 (Tag 01HI).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace FinitelyPresentedSheaf

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Associate a coherent sheaf on `Spec R` to a finite module over the Noetherian ring `R`. -/
-- Expose the object maps so unit and counit computation equations have homogeneous types.
@[expose]
def tildeFunctor : FGModuleCat.{u} R ⥤ FinitelyPresentedSheaf (Spec R) :=
  ObjectProperty.lift _ ((forget₂ (FGModuleCat R) (ModuleCat R)) ⋙ tilde.functor R)
    (fun M ↦ by
      have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
      exact isFinitePresentation_tilde M.obj)

/-- Global sections of a finitely presented sheaf on `Spec R`, as a finite `R`-module. -/
@[expose]
def globalSectionsFunctor : FinitelyPresentedSheaf (Spec R) ⥤ FGModuleCat.{u} R :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ moduleSpecΓFunctor (R := R))
    (fun M ↦ by
      have := Scheme.Modules.finitePresentation_moduleSpecΓ M.obj
      exact inferInstanceAs (Module.Finite R (moduleSpecΓFunctor.obj M.obj)))

/-- After forgetting finite presentation, this is the usual associated-sheaf functor. -/
@[simp]
lemma tildeFunctor_comp_inclusion :
    tildeFunctor R ⋙ ObjectProperty.ι
        (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf) =
      (forget₂ (FGModuleCat R) (ModuleCat R)) ⋙ tilde.functor R :=
  (rfl)

omit [IsNoetherianRing R] in
/-- After forgetting finiteness, this is the usual global-section functor. -/
@[simp]
lemma globalSectionsFunctor_comp_forget :
    globalSectionsFunctor R ⋙ forget₂ (FGModuleCat R) (ModuleCat R) =
      ObjectProperty.ι (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf) ⋙
        moduleSpecΓFunctor (R := R) :=
  (rfl)

/-- Coherent sheaves on `Spec R` are equivalent to finite `R`-modules. The functors are tilde
and global sections, with the unit and counit inherited from the tilde adjunction. -/
-- Expose the object maps so the unit and counit equations have homogeneous types.
@[expose]
def tildeEquiv : FGModuleCat.{u} R ≌ FinitelyPresentedSheaf (Spec R) where
  functor := tildeFunctor R
  inverse := globalSectionsFunctor R
  unitIso := NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((tilde.toTildeΓNatIso (R := R)).app M.obj))
    (fun f ↦ ObjectProperty.hom_ext _ ((tilde.toTildeΓNatIso (R := R)).hom.naturality f.hom))
  counitIso := NatIso.ofComponents
    (fun (M : FinitelyPresentedSheaf (Spec R)) ↦
      letI : M.obj.IsQuasicoherent := inferInstance
      ObjectProperty.isoMk _
        (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := R) M.obj)
          (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M.obj)))
    (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (tilde.adjunction (R := R)).counit.naturality f.hom)
  functor_unitIso_comp M :=
    ObjectProperty.hom_ext _ ((tilde.adjunction (R := R)).left_triangle_components M.obj)

/-- The forward equivalence functor associates a sheaf to a finite module. -/
@[simp]
lemma tildeEquiv_functor : (tildeEquiv R).functor = tildeFunctor R :=
  (rfl)

/-- The inverse equivalence functor takes global sections. -/
@[simp]
lemma tildeEquiv_inverse : (tildeEquiv R).inverse = globalSectionsFunctor R :=
  (rfl)

/-- The underlying unit component is the unit of the tilde adjunction. -/
@[simp]
lemma tildeEquiv_unitIso_hom_app_hom (M : FGModuleCat.{u} R) :
    ((tildeEquiv R).unitIso.hom.app M).hom =
      (tilde.toTildeΓNatIso (R := R)).hom.app M.obj :=
  (rfl)

/-- The underlying inverse unit component is the inverse of the tilde unit. -/
@[simp]
lemma tildeEquiv_unitIso_inv_app_hom (M : FGModuleCat.{u} R) :
    ((tildeEquiv R).unitIso.inv.app M).hom =
      (tilde.toTildeΓNatIso (R := R)).inv.app M.obj :=
  (rfl)

/-- The underlying counit component is the canonical map from the tilde of global sections. -/
@[simp]
lemma tildeEquiv_counitIso_hom_app_hom (M : FinitelyPresentedSheaf (Spec R)) :
    ((tildeEquiv R).counitIso.hom.app M).hom = Scheme.Modules.fromTildeΓ M.obj :=
  (rfl)

/-- The underlying inverse counit component is the inverse of the canonical tilde map. -/
@[simp]
lemma tildeEquiv_counitIso_inv_app_hom (M : FinitelyPresentedSheaf (Spec R)) :
    ((tildeEquiv R).counitIso.inv.app M).hom =
      (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ M.obj)
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M.obj)).inv :=
  (rfl)

/-- Coherent sheaves on the spectrum of a Noetherian ring form an abelian category. -/
instance : Abelian (FinitelyPresentedSheaf (Spec R)) := by
  let e := (tildeEquiv R).symm
  letI : HasFiniteProducts (FinitelyPresentedSheaf (Spec R)) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  exact abelianOfEquivalence e.functor

/-- Associating a sheaf to a finite module is an additive functor. -/
instance : (tildeFunctor R).Additive := by
  have : (tildeFunctor R ⋙ ObjectProperty.ι _).Additive := by
    rw [tildeFunctor_comp_inclusion]
    exact inferInstanceAs (Functor.Additive
      ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) ⋙ tilde.functor R))
  exact Functor.additive_of_comp_faithful _ (ObjectProperty.ι _)

omit [IsNoetherianRing R] in
/-- Taking global sections of a finitely presented sheaf is additive. -/
instance : (globalSectionsFunctor R).Additive := by
  have : (moduleSpecΓFunctor (R := R)).Additive :=
    (moduleSpecΓFunctor (R := R)).additive_of_preserves_binary_products
  dsimp only [globalSectionsFunctor]
  constructor
  intro M N f g
  exact ObjectProperty.hom_ext _
    ((moduleSpecΓFunctor (R := R)).map_add (f := f.hom) (g := g.hom))

/-- The inclusion of coherent sheaves into all module sheaves preserves finite limits. -/
instance preservesFiniteLimits_inclusion :
    PreservesFiniteLimits
      (ObjectProperty.ι (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf)) := by
  let F := ObjectProperty.ι (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf)
  have : PreservesFiniteLimits (tildeFunctor R ⋙ F) := by
    dsimp only [F]
    rw [tildeFunctor_comp_inclusion]
    exact inferInstanceAs (PreservesFiniteLimits
      ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) ⋙ tilde.functor R))
  have : PreservesFiniteLimits ((tildeEquiv R).functor ⋙ F) := by
    rw [tildeEquiv_functor]
    infer_instance
  have : PreservesFiniteLimits (((tildeEquiv R).inverse ⋙ (tildeEquiv R).functor) ⋙ F) :=
    preservesFiniteLimits_of_natIso
      (Functor.associator (tildeEquiv R).inverse (tildeEquiv R).functor F).symm
  exact preservesFiniteLimits_of_natIso (Functor.isoWhiskerRight (tildeEquiv R).counitIso F)

/-- The inclusion of coherent sheaves into all module sheaves preserves finite colimits. -/
instance preservesFiniteColimits_inclusion :
    PreservesFiniteColimits
      (ObjectProperty.ι (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf)) := by
  let F := ObjectProperty.ι (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf)
  have : PreservesFiniteColimits (tildeFunctor R ⋙ F) := by
    dsimp only [F]
    rw [tildeFunctor_comp_inclusion]
    exact inferInstanceAs (PreservesFiniteColimits
      ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) ⋙ tilde.functor R))
  have : PreservesFiniteColimits ((tildeEquiv R).functor ⋙ F) := by
    rw [tildeEquiv_functor]
    infer_instance
  have : PreservesFiniteColimits (((tildeEquiv R).inverse ⋙ (tildeEquiv R).functor) ⋙ F) :=
    preservesFiniteColimits_of_natIso
      (Functor.associator (tildeEquiv R).inverse (tildeEquiv R).functor F).symm
  exact preservesFiniteColimits_of_natIso (Functor.isoWhiskerRight (tildeEquiv R).counitIso F)

end FinitelyPresentedSheaf

end

end TauCeti.AlgebraicGeometry
