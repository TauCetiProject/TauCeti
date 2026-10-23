/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Basic
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Modules.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk
import all TauCeti.AlgebraicGeometry.Modules.Differentials.Basic

/-!
# Stalks of relative differentials

For a scheme `X` over a commutative ring `R`, the stalk of the sheaf of relative differentials
at `x` is canonically the module of Kähler differentials of the local ring `𝒪_{X,x}` over `R`.
The comparison sends the germ of `d a` to the differential of the germ of `a`, and its inverse
has the corresponding computation rule. No finiteness, smoothness, or integrality assumption is
needed. This comparison connects local-ring regularity criteria for rational differentials
with the sheaf of differentials used to represent the canonical line bundle.

## References

* The Stacks Project, Lemma 17.28.7, Tag 08TE.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf
open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))] (x : X)

private abbrev P := X.presheafRelativeDifferentials R
private abbrev M := X.relativeDifferentials R
private abbrev PP : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat := (P R X).presheaf
private abbrev A := X.presheaf.stalk x
private abbrev T := Ω[A X x⁄R]

private abbrev unitStalkEquiv :
    (PP R X).stalk x ≃ₗ[A X x] (M R X).presheaf.stalk x :=
  (P R X).sheafificationStalkEquiv X.sheaf x

private abbrev unitStalk := (unitStalkEquiv R X x).toLinearMap

private def sectionMap (U : X.Opens) (hx : x ∈ U) :
    let : Module Γ(X, U) (T R X x) :=
      Module.compHom _ (X.presheaf.germ U x hx).hom
    (P R X).obj (op U) →ₗ[Γ(X, U)] T R X x :=
  let : Module Γ(X, U) (T R X x) :=
    Module.compHom _ (X.presheaf.germ U x hx).hom
  (ModuleCat.Derivation.mk (f := (X.baseRingToStructurePresheaf R).app (op U))
    (M := ModuleCat.of Γ(X, U) (T R X x))
    (fun a ↦ KaehlerDifferential.D R (A X x) (X.presheaf.germ U x hx a))
    (by simp) (fun a b ↦ by
      simp only [map_mul, Derivation.leibniz]
      exact congrArg₂ (· + ·)
        (MulAction.compHom_smul_def (X.presheaf.germ U x hx).hom.toMonoidHom a _).symm
        (MulAction.compHom_smul_def (X.presheaf.germ U x hx).hom.toMonoidHom b _).symm)
    (fun r ↦ by
      have h : X.presheaf.germ U x hx ((X.baseRingToStructurePresheaf R).app (op U) r) =
          algebraMap R (A X x) r := by
        rw [Scheme.algebraMap_stalk_eq_baseRingToStalk, Scheme.baseRingToStalk_apply,
          Scheme.baseRingToStructurePresheaf_app, CommRingCat.comp_apply,
          CommRingCat.ofHom_apply, TopCat.Presheaf.germ_res_apply]
      rw [h, Derivation.map_algebraMap])).desc.hom

private lemma sectionMap_d (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    sectionMap R X x U hx
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (X.baseRingToStructurePresheaf R)).d a) =
      KaehlerDifferential.D R (A X x) (X.presheaf.germ U x hx a) := by
  exact ModuleCat.Derivation.desc_d _ a

private lemma sectionMap_res {U V : X.Opens} (i : U ⟶ V) (hx : x ∈ U)
    (m : (P R X).obj (op V)) :
    sectionMap R X x U hx ((P R X).map i.op m) = sectionMap R X x V (i.le hx) m := by
  let : Module Γ(X, U) (T R X x) :=
    Module.compHom _ (X.presheaf.germ U x hx).hom
  let : Module Γ(X, V) (T R X x) :=
    Module.compHom _ (X.presheaf.germ V x (i.le hx)).hom
  let f : (P R X).obj (op V) →ₗ[Γ(X, V)] T R X x :=
    { toFun m := sectionMap R X x U hx ((P R X).map i.op m)
      map_add' a b :=
        (congrArg (sectionMap R X x U hx) (((P R X).map i.op).hom.map_add a b)).trans
          ((sectionMap R X x U hx).map_add _ _)
      map_smul' r m :=
        (congrArg (sectionMap R X x U hx) ((P R X).map_smul i.op r m)).trans
          (((sectionMap R X x U hx).map_smul (X.presheaf.map i.op r) _).trans
            (congrArg (fun t : A X x ↦ t • sectionMap R X x U hx ((P R X).map i.op m))
              (X.presheaf.germ_res_apply i x hx r))) }
  have h : ModuleCat.ofHom f = ModuleCat.ofHom (sectionMap R X x V (i.le hx)) := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    exact (congrArg (sectionMap R X x U hx)
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (X.baseRingToStructurePresheaf R)).d_map i.op a).symm).trans
          ((sectionMap_d R X x U hx _).trans
            ((congrArg (KaehlerDifferential.D R (A X x))
              (X.presheaf.germ_res_apply i x hx a)).trans
                (sectionMap_d R X x V (i.le hx) a).symm))
  exact congrArg (fun g ↦ g m) h

private def presheafStalkMap : (PP R X).stalk x →ₗ[A X x] T R X x :=
  (P R X).stalkLiftCommRing (S := X.presheaf) x
    (fun U hx ↦ (sectionMap R X x U hx).toAddMonoidHom)
    (fun i hx m ↦ sectionMap_res R X x i hx m)
    (fun U hx r m ↦ by
      let : Module Γ(X, U) (T R X x) :=
        Module.compHom _ (X.presheaf.germ U x hx).hom
      exact (sectionMap R X x U hx).map_smul r m)

private lemma presheafStalkMap_germ (U : X.Opens) (hx : x ∈ U)
    (m : (P R X).obj (op U)) :
    presheafStalkMap R X x ((PP R X).germ U x hx m) = sectionMap R X x U hx m := by
  unfold presheafStalkMap
  apply PresheafOfModules.stalkLiftCommRing_germ

private lemma presheafStalkMap_germ_d (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    presheafStalkMap R X x ((PP R X).germ U x hx
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (X.baseRingToStructurePresheaf R)).d a)) =
      KaehlerDifferential.D R (A X x) (X.presheaf.germ U x hx a) :=
  (presheafStalkMap_germ R X x U hx _).trans (sectionMap_d R X x U hx a)

private def stalkMap : (M R X).presheaf.stalk x →ₗ[A X x] T R X x :=
  (presheafStalkMap R X x).comp (unitStalkEquiv R X x).symm.toLinearMap

private lemma stalkMap_germ_d (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    stalkMap R X x ((M R X).presheaf.germ U x hx ((X.universalDerivation R).d a)) =
      KaehlerDifferential.D R (A X x) (X.presheaf.germ U x hx a) := by
  have h := (P R X).sheafificationStalkEquiv_germ X.sheaf x U hx
    ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
      (X.baseRingToStructurePresheaf R)).d a)
  erw [← h]
  exact (congrArg (presheafStalkMap R X x)
    ((unitStalkEquiv R X x).symm_apply_apply _)).trans
      (presheafStalkMap_germ_d R X x U hx a)

private abbrev additivePresheaf : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat :=
  X.presheaf ⋙ forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u}

private def stalkDerivationSection (U : X.Opens) (hx : x ∈ U) :
    Γ(X, U) →+ (M R X).presheaf.stalk x :=
  (TopCat.Presheaf.germ (M R X).presheaf U x hx).hom.comp (X.universalDerivation R).d

private lemma stalkDerivationSection_res {U V : X.Opens} (i : U ⟶ V) (hx : x ∈ U)
    (a : Γ(X, V)) :
    stalkDerivationSection R X x U hx (X.presheaf.map i.op a) =
      stalkDerivationSection R X x V (i.le hx) a :=
  (congrArg (fun t ↦ (M R X).presheaf.germ U x hx t)
    ((X.universalDerivation R).d_map i.op a)).trans
      ((M R X).presheaf.germ_res_apply i x hx _)

private def stalkDerivationLift :
    (additivePresheaf X).stalk x →+ (M R X).presheaf.stalk x :=
  TopCat.Presheaf.stalkLiftAddHom (additivePresheaf X) x
    (stalkDerivationSection R X x) (stalkDerivationSection_res R X x)

private lemma stalkDerivationLift_germ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    stalkDerivationLift R X x ((additivePresheaf X).germ U x hx a) =
      (M R X).presheaf.germ U x hx ((X.universalDerivation R).d a) :=
  TopCat.Presheaf.stalkLiftAddHom_germ (additivePresheaf X) x
    (stalkDerivationSection R X x) (stalkDerivationSection_res R X x) U hx a

private def stalkDerivationAdd : A X x →+ (M R X).presheaf.stalk x :=
  (stalkDerivationLift R X x).comp
    (preservesColimitIso (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ X.presheaf)).hom.hom

private lemma stalkDerivationAdd_germ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    stalkDerivationAdd R X x (X.presheaf.germ U x hx a) =
      (M R X).presheaf.germ U x hx ((X.universalDerivation R).d a) := by
  have h := ConcreteCategory.congr_hom
    (ι_preservesColimitIso_hom
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ X.presheaf) (op ⟨U, hx⟩)) a
  exact (congrArg (stalkDerivationLift R X x) h).trans
    (stalkDerivationLift_germ R X x U hx a)

private lemma stalkDerivationAdd_mul (a b : A X x) :
    stalkDerivationAdd R X x (a * b) =
      a • stalkDerivationAdd R X x b + b • stalkDerivationAdd R X x a := by
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hVU, hxV, b, rfl⟩ := X.presheaf.exists_le_germ_eq b hxU
  erw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV a, ← map_mul,
    stalkDerivationAdd_germ, stalkDerivationAdd_germ, stalkDerivationAdd_germ]
  exact (congrArg (fun t ↦ (M R X).presheaf.germ V x hxV t)
    ((X.universalDerivation R).d_mul (X.presheaf.map (homOfLE hVU).op a) b)).trans
      ((((M R X).presheaf.germ V x hxV).hom.map_add _ _).trans
        (congrArg₂ (· + ·)
          ((M R X).germ_smul x V hxV _ _) ((M R X).germ_smul x V hxV _ _)))

private lemma stalkDerivationAdd_base (r : R) :
    stalkDerivationAdd R X x (algebraMap R (A X x) r) = 0 := by
  rw [Scheme.algebraMap_stalk_eq_baseRingToStalk, Scheme.baseRingToStalk_apply]
  erw [stalkDerivationAdd_germ]
  have h : Scheme.Modules.baseRingToGlobalSections R X r =
      (X.baseRingToStructurePresheaf R).app (op ⊤) r := by
    rw [Scheme.baseRingToStructurePresheaf_app]
    exact (congrArg (fun f ↦ f (Scheme.Modules.baseRingToGlobalSections R X r))
      (X.presheaf.map_id (op ⊤))).symm
  erw [h, PresheafOfModulesOfCommRing.Derivation.d_app, map_zero]

private def stalkDerivation :
    letI : Module R ((M R X).presheaf.stalk x) :=
      Module.compHom _ (algebraMap R (A X x))
    Derivation R (A X x) ((M R X).presheaf.stalk x) :=
  letI : Module R ((M R X).presheaf.stalk x) :=
    Module.compHom _ (algebraMap R (A X x))
  Derivation.mk'
    { toFun := stalkDerivationAdd R X x
      map_add' := map_add _
      map_smul' r a := by
        rw [Algebra.smul_def, stalkDerivationAdd_mul, stalkDerivationAdd_base,
          smul_zero, add_zero]
        exact (MulAction.compHom_smul_def
          (algebraMap R (A X x)).toMonoidHom r _).symm }
    (stalkDerivationAdd_mul R X x)

private def stalkInv : T R X x →ₗ[A X x] (M R X).presheaf.stalk x :=
  letI : Module R ((M R X).presheaf.stalk x) :=
    Module.compHom _ (algebraMap R (A X x))
  haveI : IsScalarTower R (A X x) ((M R X).presheaf.stalk x) :=
    IsScalarTower.of_compHom R (A X x) ((M R X).presheaf.stalk x)
  (stalkDerivation R X x).liftKaehlerDifferential

private lemma stalkInv_D (a : A X x) :
    stalkInv R X x (KaehlerDifferential.D R (A X x) a) = stalkDerivationAdd R X x a := by
  let : Module R ((M R X).presheaf.stalk x) :=
    Module.compHom _ (algebraMap R (A X x))
  have : IsScalarTower R (A X x) ((M R X).presheaf.stalk x) :=
    IsScalarTower.of_compHom R (A X x) ((M R X).presheaf.stalk x)
  exact Derivation.liftKaehlerDifferential_comp_D (stalkDerivation R X x) a

private lemma stalkMap_stalkInv : (stalkMap R X x).comp (stalkInv R X x) = LinearMap.id := by
  apply (KaehlerDifferential.linearMapEquivDerivation R (A X x) (M := T R X x)).injective
  ext a
  obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq a
  exact (congrArg (stalkMap R X x) (stalkInv_D R X x _)).trans
    ((congrArg (stalkMap R X x) (stalkDerivationAdd_germ R X x U hx a)).trans
      (stalkMap_germ_d R X x U hx a))

private lemma stalkInv_stalkMap : (stalkInv R X x).comp (stalkMap R X x) = LinearMap.id := by
  ext m
  obtain ⟨m, rfl⟩ := (unitStalkEquiv R X x).surjective m
  obtain ⟨U, hx, m, rfl⟩ := (PP R X).exists_germ_eq m
  let : Module Γ(X, U) ((M R X).presheaf.stalk x) :=
    Module.compHom _ (X.presheaf.germ U x hx).hom
  let : Module Γ(X, U) (T R X x) :=
    Module.compHom _ (X.presheaf.germ U x hx).hom
  let f : (P R X).obj (op U) →ₗ[Γ(X, U)] (M R X).presheaf.stalk x :=
    { toFun m := stalkInv R X x (sectionMap R X x U hx m)
      map_add' := by simp
      map_smul' r m := by
        exact (congrArg (stalkInv R X x) ((sectionMap R X x U hx).map_smul r m)).trans
          ((stalkInv R X x).map_smul (X.presheaf.germ U x hx r) _) }
  let g : (P R X).obj (op U) →ₗ[Γ(X, U)] (M R X).presheaf.stalk x :=
    { toFun m := unitStalk R X x ((PP R X).germ U x hx m)
      map_add' a b :=
        (congrArg (unitStalk R X x) (((PP R X).germ U x hx).hom.map_add a b)).trans
          ((unitStalk R X x).map_add _ _)
      map_smul' r m :=
        (congrArg (unitStalk R X x)
          (PresheafOfModules.germ_smul (R := X.presheaf) (P R X) x U hx r m)).trans
            ((unitStalk R X x).map_smul (X.presheaf.germ U x hx r) _) }
  have h : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    exact (congrArg (stalkInv R X x) (sectionMap_d R X x U hx a)).trans
      ((stalkInv_D R X x _).trans ((stalkDerivationAdd_germ R X x U hx a).trans
        ((P R X).sheafificationStalkEquiv_germ X.sheaf x U hx _).symm))
  exact (congrArg (stalkInv R X x)
    (congrArg (presheafStalkMap R X x) ((unitStalkEquiv R X x).symm_apply_apply _))).trans
      ((congrArg (stalkInv R X x) (presheafStalkMap_germ R X x U hx m)).trans
        (congrArg (fun k ↦ k m) h))

/-- The stalk of relative differentials is canonically the Kähler differential module of the
local ring over the base ring. The base algebra is the canonical `Scheme.stalkBaseAlgebra`. -/
def _root_.AlgebraicGeometry.Scheme.relativeDifferentialsStalkEquiv :
    (X.relativeDifferentials R).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      Ω[X.presheaf.stalk x⁄R] :=
  LinearEquiv.ofLinearMap (stalkMap R X x) (stalkInv R X x)
    (stalkMap_stalkInv R X x) (stalkInv_stalkMap R X x)

/-- The stalk comparison sends the germ of a differential to the differential of the germ. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.relativeDifferentialsStalkEquiv_germ_d
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    X.relativeDifferentialsStalkEquiv R x
      ((X.relativeDifferentials R).presheaf.germ U x hx ((X.universalDerivation R).d a)) =
      KaehlerDifferential.D R (X.presheaf.stalk x) (X.presheaf.germ U x hx a) :=
  stalkMap_germ_d R X x U hx a

/-- The inverse stalk comparison sends the differential of a germ to the germ of a differential. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.relativeDifferentialsStalkEquiv_symm_D_germ
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    (X.relativeDifferentialsStalkEquiv R x).symm
      (KaehlerDifferential.D R (X.presheaf.stalk x) (X.presheaf.germ U x hx a)) =
      (X.relativeDifferentials R).presheaf.germ U x hx ((X.universalDerivation R).d a) :=
  (stalkInv_D R X x _).trans (stalkDerivationAdd_germ R X x U hx a)

end

end TauCeti.AlgebraicGeometry
