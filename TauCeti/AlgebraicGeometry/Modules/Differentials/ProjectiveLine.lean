/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.AffineRestriction
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Hom
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Differentials of the projective line

The relative differential sheaf of `ℙ¹_R` is `𝒪(-2)` for every commutative ring `R`.
The comparison is normalized on the standard coordinates `t = X₁/X₀`, `s = X₀/X₁`:
it sends `dt` to the first twisting generator and `ds` to the negative of the second.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite Polynomial

namespace TauCeti.AlgebraicGeometry.projectiveLine

noncomputable section

universe u v

variable (R : Type u) [CommRing R]

private abbrev chartOpen (i : Fin 2) : (projectiveLine R).Opens :=
  awayι R i ''ᵁ ⊤

/-- The chart algebra over the base is induced by the structure morphism. -/
private instance chartAlgebra (i : Fin 2) : Algebra R Γ(projectiveLine R, chartOpen R i) :=
  (((projectiveLine R).baseRingToStructurePresheaf R).app (op (chartOpen R i))).hom.toAlgebra

private def chartAlgEquiv (i : Fin 2) : Γ(projectiveLine R, chartOpen R i) ≃ₐ[R] R[X] where
  __ := chartSectionsEquiv R i
  commutes' r := by
    -- The chart algebra was defined from this structure-ring map, so its algebra map is
    -- evaluated by the canonical `RingHom.algebraMap_toAlgebra` equation.
    simp only [RingHom.algebraMap_toAlgebra]
    -- The algebra-equivalence field presents its ring map by `toFun`; identify that
    -- coercion with the named chart equivalence before applying its computation law.
    change chartSectionsEquiv R i
      ((((projectiveLine R).baseRingToStructurePresheaf R).app (op (chartOpen R i))) r) = _
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.comp_apply,
      chartSectionsEquiv_appLE, Iso.inv_hom_id_apply]
    rfl

private def chartCoordinate (i : Fin 2) : Γ(projectiveLine R, chartOpen R i) :=
  (chartSectionsEquiv R i).symm Polynomial.X

private def chartDifferential (i : Fin 2) :
    Γ((projectiveLine R).relativeDifferentials R, chartOpen R i) :=
  ((projectiveLine R).universalDerivation R).d (chartCoordinate R i)

private def chartDifferentialEquiv (i : Fin 2) :
    Γ(projectiveLine R, chartOpen R i) ≃ₗ[Γ(projectiveLine R, chartOpen R i)]
      Γ((projectiveLine R).relativeDifferentials R, chartOpen R i) := by
  let S := Γ(projectiveLine R, chartOpen R i)
  let e := (chartAlgEquiv R i).symm
  letI : Algebra R[X] S := e.toAlgHom.toAlgebra
  haveI : IsScalarTower R R[X] S := IsScalarTower.of_algHom e.toAlgHom
  let e' : R[X] ≃ₐ[R[X]] S := { __ := e.toRingEquiv, commutes' _ := rfl }
  haveI : Algebra.FormallyEtale R[X] S :=
    Algebra.FormallyEtale.of_equiv e'
  exact (TensorProduct.AlgebraTensorModule.rid R[X] S S).symm ≪≫ₗ
    (LinearEquiv.baseChange R[X] S _ _ (KaehlerDifferential.polynomialEquiv R).symm) ≪≫ₗ
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R R[X] S ≪≫ₗ
    relativeDifferentialsSectionsEquiv R (projectiveLine R)
      ⟨chartOpen R i, isAffineOpen_image_awayι_top R i⟩

private lemma chartDifferentialEquiv_apply (i : Fin 2)
    (a : Γ(projectiveLine R, chartOpen R i)) :
    chartDifferentialEquiv R i a = a • chartDifferential R i := by
  simp only [chartDifferentialEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.rid_symm_apply, LinearEquiv.baseChange_tmul,
    KaehlerDifferential.polynomialEquiv_symm, one_smul,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, map_smul]
  exact congrArg (a • ·) (relativeDifferentialsSectionsEquiv_D R (projectiveLine R)
    ⟨chartOpen R i, isAffineOpen_image_awayι_top R i⟩ (chartCoordinate R i))

private def fromTwistLocal (i : Fin 2) :
    (Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2)).over
        (chartOpen R i) ⟶
      ((projectiveLine R).relativeDifferentials R).over (chartOpen R i) :=
  (Proj.twistingSheaf.chartIso (-2) (coord R i) (coord_mem R i)
    (chartOpen R i) (image_awayι_top R i).le).inv ≫
    (((projectiveLine R).relativeDifferentials R).over (chartOpen R i)).unitHomEquiv.symm
      ((((projectiveLine R).relativeDifferentials R).overSectionsEquiv (chartOpen R i)).symm
        ((if i = 0 then (1 : ℤ) else -1) • chartDifferential R i))


private lemma chartCoordinate_eq (i : Fin 2) : chartCoordinate R i =
    (projectiveLine R).presheaf.map (eqToHom (image_awayι_top R i)).op
      (affineCoordinate R i) := by
  apply (chartSectionsEquiv R i).injective
  rw [chartCoordinate, RingEquiv.apply_symm_apply, affineCoordinate_def,
    chartSectionsEquiv_awayToSection,
    AlgEquiv.apply_symm_apply]

private lemma chartCoordinate_res_val (i : Fin 2) (V : (projectiveLine R).Opens)
    (hi : V ≤ chartOpen R i) (x : V) :
    (((projectiveLine R).presheaf.map (homOfLE hi).op (chartCoordinate R i)).val x).val =
      Localization.mk (coord R i.rev)
        ⟨coord R i, (hi.trans (image_awayι_top R i).le) x.property⟩ := by
  rw [chartCoordinate_eq, ← Functor.map_comp_apply]
  exact val_res_affineCoordinate R i V (hi.trans (image_awayι_top R i).le) x

private lemma chartCoordinate_res_mul (V : (projectiveLine R).Opens)
    (h₀ : V ≤ chartOpen R 0) (h₁ : V ≤ chartOpen R 1) :
    (projectiveLine R).presheaf.map (homOfLE h₀).op (chartCoordinate R 0) *
      (projectiveLine R).presheaf.map (homOfLE h₁).op (chartCoordinate R 1) = 1 := by
  rw [chartCoordinate_eq, chartCoordinate_eq, ← Functor.map_comp_apply,
    ← Functor.map_comp_apply]
  exact affineCoordinate_res_mul R V (h₀.trans (image_awayι_top R 0).le)
    (h₁.trans (image_awayι_top R 1).le)

private lemma twistGenerator_transition (V : (projectiveLine R).Opens)
    (h₀ : V ≤ chartOpen R 0) (h₁ : V ≤ chartOpen R 1) :
    Proj.twistingSheaf.chartGenerator (-2) (coord R 0) (coord_mem R 0)
        V (h₀.trans (image_awayι_top R 0).le) =
      ((projectiveLine R).presheaf.map (homOfLE h₀).op (chartCoordinate R 0)) ^ 2 •
        Proj.twistingSheaf.chartGenerator (-2) (coord R 1) (coord_mem R 1)
          V (h₁.trans (image_awayι_top R 1).le) := by
  apply Proj.twistingSheaf.ext
  intro x
  let := x.val.isPrime
  erw [Proj.twistingSheaf.smul_apply, Proj.twistingSheaf.chartGenerator_apply,
    HomogeneousLocalization.val_pow, chartCoordinate_res_val,
    Proj.twistingSheaf.chartGenerator_apply]
  norm_num only at *
  rw [Localization.mk_pow, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  norm_num [Fin.rev]

private lemma differential_transition (V : (projectiveLine R).Opens)
    (h₀ : V ≤ chartOpen R 0) (h₁ : V ≤ chartOpen R 1) :
    (((projectiveLine R).relativeDifferentials R).val.map (homOfLE h₀).op
        (chartDifferential R 0) : Γ((projectiveLine R).relativeDifferentials R, V)) =
      ((projectiveLine R).presheaf.map (homOfLE h₀).op (chartCoordinate R 0)) ^ 2 •
        -(((projectiveLine R).relativeDifferentials R).val.map (homOfLE h₁).op
          (chartDifferential R 1) : Γ((projectiveLine R).relativeDifferentials R, V)) := by
  let D := (projectiveLine R).universalDerivation R
  let t := (projectiveLine R).presheaf.map (homOfLE h₀).op (chartCoordinate R 0)
  let s := (projectiveLine R).presheaf.map (homOfLE h₁).op (chartCoordinate R 1)
  have hts : t * s = 1 := chartCoordinate_res_mul R V h₀ h₁
  have hD : t • D.d s + s • D.d t = 0 := by
    rw [← D.d_mul, hts, D.d_one]
  have hDt : D.d t = t ^ 2 • -D.d s := by
    calc
      D.d t = (t * s) • D.d t := by rw [hts, one_smul]
      _ = t • (s • D.d t) := (smul_smul _ _ _).symm
      _ = t • -(t • D.d s) := by rw [eq_neg_of_add_eq_zero_right hD]
      _ = t ^ 2 • -D.d s := by simp only [smul_neg, smul_smul, pow_two]
  exact (D.d_map (homOfLE h₀).op _).symm.trans
    (hDt.trans (congrArg (fun a : Γ((projectiveLine R).relativeDifferentials R, V) ↦
      t ^ 2 • -a) (D.d_map (homOfLE h₁).op _)))

private lemma fromTwistLocal_app (i : Fin 2) (V : (projectiveLine R).Opens)
    (hi : V ≤ chartOpen R i)
    (m : Γ(Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2), V)) :
    (fromTwistLocal R i).val.app (op (Over.mk (homOfLE hi))) m =
      (Proj.twistingSheaf.chartSectionsLinearEquiv (-2) (coord R i) (coord_mem R i)
        V (hi.trans (image_awayι_top R i).le)).symm m •
          ((projectiveLine R).relativeDifferentials R).val.map (homOfLE hi).op
            ((if i = 0 then (1 : ℤ) else -1) • chartDifferential R i) := by
  -- The composite is evaluated on the common carrier of the restricted modules. Rewriting
  -- the categorical composition laws here exceeds the default elaboration budget because
  -- their dependent scalar restrictions expand; this reduction keeps those restrictions fixed.
  dsimp only [fromTwistLocal]
  change (((((projectiveLine R).relativeDifferentials R).over (chartOpen R i)).unitHomEquiv.symm
    ((((projectiveLine R).relativeDifferentials R).overSectionsEquiv (chartOpen R i)).symm
      ((if i = 0 then (1 : ℤ) else -1) • chartDifferential R i))).val.app
        (op (Over.mk (homOfLE hi))))
    ((Proj.twistingSheaf.chartIso (-2) (coord R i) (coord_mem R i)
      (chartOpen R i) (image_awayι_top R i).le).inv.val.app
        (op (Over.mk (homOfLE hi))) m) = _
  rw [Proj.twistingSheaf.chartIso_inv_app_apply]
  erw [TauCeti.SheafOfModules.unitHomEquiv_symm_val_app,
    SheafOfModules.overSectionsEquiv_symm_apply_eval]
  rfl

private lemma fromTwistLocal_generator (i : Fin 2) (V : (projectiveLine R).Opens)
    (hi : V ≤ chartOpen R i) :
    (fromTwistLocal R i).val.app (op (Over.mk (homOfLE hi)))
      (Proj.twistingSheaf.chartGenerator (-2) (coord R i) (coord_mem R i)
        V (hi.trans (image_awayι_top R i).le)) =
      ((projectiveLine R).relativeDifferentials R).val.map (homOfLE hi).op
        ((if i = 0 then (1 : ℤ) else -1) • chartDifferential R i) := by
  rw [fromTwistLocal_app]
  have hgen : Proj.twistingSheaf.chartGenerator (-2) (coord R i) (coord_mem R i)
      V (hi.trans (image_awayι_top R i).le) =
      Proj.twistingSheaf.chartSectionsLinearEquiv (-2) (coord R i) (coord_mem R i)
        V (hi.trans (image_awayι_top R i).le) 1 := by
    rw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply, one_smul]
  rw [hgen, LinearEquiv.symm_apply_apply, one_smul]

private lemma fromTwistLocal_zero_one (V : (projectiveLine R).Opens)
    (h₀ : V ≤ chartOpen R 0) (h₁ : V ≤ chartOpen R 1)
    (m : Γ(Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2), V)) :
    (fromTwistLocal R 0).val.app (op (Over.mk (homOfLE h₀))) m =
      (fromTwistLocal R 1).val.app (op (Over.mk (homOfLE h₁))) m := by
  let f₀ : Γ(Proj.twistingSheaf
      (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2), V) →ₗ[Γ(projectiveLine R, V)]
      Γ((projectiveLine R).relativeDifferentials R, V) :=
    ((fromTwistLocal R 0).val.app (op (Over.mk (homOfLE h₀)))).hom
  let f₁ : Γ(Proj.twistingSheaf
      (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2), V) →ₗ[Γ(projectiveLine R, V)]
      Γ((projectiveLine R).relativeDifferentials R, V) :=
    ((fromTwistLocal R 1).val.app (op (Over.mk (homOfLE h₁)))).hom
  let e := Proj.twistingSheaf.chartSectionsLinearEquiv (-2) (coord R 0)
    (coord_mem R 0) V (h₀.trans (image_awayι_top R 0).le)
  let g₀ := Proj.twistingSheaf.chartGenerator (-2) (coord R 0) (coord_mem R 0)
    V (h₀.trans (image_awayι_top R 0).le)
  let g₁ := Proj.twistingSheaf.chartGenerator (-2) (coord R 1) (coord_mem R 1)
    V (h₁.trans (image_awayι_top R 1).le)
  let t := (projectiveLine R).presheaf.map (homOfLE h₀).op (chartCoordinate R 0)
  have hgen : f₀ g₀ = f₁ g₀ := by
    have hf₀ := fromTwistLocal_generator R 0 V h₀
    have hf₁ := fromTwistLocal_generator R 1 V h₁
    -- The component maps `f₀`, `f₁` use native section modules. The local morphisms use
    -- their restrictions to a slice; these conversions identify their common carriers.
    change f₀ g₀ = _ at hf₀
    change f₁ g₁ = _ at hf₁
    simp only [ite_true, one_smul] at hf₀
    simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, neg_one_zsmul] at hf₁
    have hf₁' := hf₁.trans
      ((((projectiveLine R).relativeDifferentials R).val.map (homOfLE h₁).op).hom.map_neg
        (chartDifferential R 1))
    exact hf₀.trans ((differential_transition R V h₀ h₁).trans
      ((congrArg (fun a ↦ t ^ 2 • a) hf₁'.symm).trans
        ((f₁.map_smul (t ^ 2) g₁).symm.trans
          (congrArg f₁ (twistGenerator_transition R V h₀ h₁).symm))))
  have hm : e.symm m • g₀ = m := by
    simpa only [e, Proj.twistingSheaf.chartSectionsLinearEquiv_apply] using e.apply_symm_apply m
  -- The same carrier identification lets the linear-map scalar law prove the local
  -- morphism equality, without unfolding the opaque relative differential sheaf.
  change f₀ m = f₁ m
  exact (congrArg f₀ hm.symm).trans ((f₀.map_smul (e.symm m) g₀).trans
    ((congrArg (fun a ↦ e.symm m • a) hgen).trans
      ((f₁.map_smul (e.symm m) g₀).symm.trans (congrArg f₁ hm))))

private lemma fromTwistLocal_compatible (i j : Fin 2) (V : (projectiveLine R).Opens)
    (hi : V ≤ chartOpen R i) (hj : V ≤ chartOpen R j)
    (m : Γ(Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2), V)) :
    (fromTwistLocal R i).val.app (op (Over.mk (homOfLE hi))) m =
      (fromTwistLocal R j).val.app (op (Over.mk (homOfLE hj))) m := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact fromTwistLocal_zero_one R V hi hj m
  · exact (fromTwistLocal_zero_one R V hj hi m).symm
  · rfl

private lemma iSup_chartOpen : ⨆ i, chartOpen R i = ⊤ := by
  simpa only [chartOpen, image_awayι_top] using iSup_basicOpen_coord_eq_top R

private def fromTwist :
    Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2) ⟶
      (projectiveLine R).relativeDifferentials R :=
  SheafOfModules.glueOfOpenCover (X := (projectiveLine R).toTopCat) (ι := Fin 2)
    (Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2) :
      (projectiveLine R).Modules) ((projectiveLine R).relativeDifferentials R)
    (chartOpen R) (iSup_chartOpen R) (fromTwistLocal R)
    (fromTwistLocal_compatible R)

private lemma fromTwist_app (i : Fin 2) (V : (projectiveLine R).Opens)
    (hi : V ≤ chartOpen R i)
    (m : Γ(Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2), V)) :
    (fromTwist R).val.app (op V) m =
      (fromTwistLocal R i).val.app (op (Over.mk (homOfLE hi))) m :=
  SheafOfModules.glueOfOpenCover_app (X := (projectiveLine R).toTopCat) (ι := Fin 2)
    (Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2) :
      (projectiveLine R).Modules) ((projectiveLine R).relativeDifferentials R)
    (chartOpen R) (iSup_chartOpen R) (fromTwistLocal R)
    (fromTwistLocal_compatible R) i V hi m

private lemma fromTwist_app_chart (i : Fin 2)
    (m : Γ(Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2),
      chartOpen R i)) :
    (fromTwist R).val.app (op (chartOpen R i)) m =
      (if i = 0 then (1 : ℤ) else -1) • chartDifferentialEquiv R i
        ((Proj.twistingSheaf.chartSectionsLinearEquiv (-2) (coord R i) (coord_mem R i)
          (chartOpen R i) (image_awayι_top R i).le).symm m) := by
  rw [fromTwist_app R i _ le_rfl, fromTwistLocal_app, chartDifferentialEquiv_apply]
  have hid : homOfLE (show chartOpen R i ≤ chartOpen R i from le_rfl) =
      𝟙 (chartOpen R i) := Subsingleton.elim _ _
  rw [hid]
  let a := (Proj.twistingSheaf.chartSectionsLinearEquiv (-2) (coord R i) (coord_mem R i)
    (chartOpen R i) (image_awayι_top R i).le).symm m
  let s := (if i = 0 then (1 : ℤ) else -1) • chartDifferential R i
  have hrest : ((projectiveLine R).relativeDifferentials R).val.map
      (𝟙 (op (chartOpen R i))) s = s :=
    (((projectiveLine R).relativeDifferentials R).val.presheaf_map_apply_coe
      (𝟙 (op (chartOpen R i))) s).symm.trans
        (ConcreteCategory.congr_hom
          (((projectiveLine R).relativeDifferentials R).val.presheaf.map_id _) s)
  refine (congrArg (fun x : Γ((projectiveLine R).relativeDifferentials R, chartOpen R i) ↦
    a • x) hrest).trans ?_
  -- `s` names the signed differential; the remaining equality concerns only its sign.
  dsimp only [s]
  split_ifs <;> simp only [one_smul, neg_one_zsmul, smul_neg, a]

/-- The glued morphism is invertible because its components on the affine charts are bijective. -/
private instance fromTwist_isIso : IsIso (fromTwist R) := by
  refine Scheme.Modules.Hom.isIso_of_bijective_app (fromTwist R)
    (isAffineOpen_image_awayι_top R) (iSup_chartOpen R) fun i ↦ ?_
  let e := (Proj.twistingSheaf.chartSectionsLinearEquiv (-2) (coord R i) (coord_mem R i)
    (chartOpen R i) (image_awayι_top R i).le).symm ≪≫ₗ chartDifferentialEquiv R i
  have hfun : (fromTwist R).app (chartOpen R i) =
      (fun m ↦ (if i = 0 then (1 : ℤ) else -1) • e m) := by
    funext m
    exact fromTwist_app_chart R i m
  rw [hfun]
  by_cases hi : i = 0
  · simpa only [hi, ite_true, one_smul] using e.bijective
  · simpa only [hi, ite_false, neg_one_zsmul, Function.comp_def] using
      neg_bijective.comp e.bijective

/-- Relative differentials on the projective line over a commutative ring are `𝒪(-2)`.
The inverse sends the standard generators to `dt` and `-ds`. -/
def relativeDifferentialsIsoTwistingSheaf : (projectiveLine R).relativeDifferentials R ≅
    Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2) :=
  (asIso (fromTwist R)).symm

/-- On every open in a standard chart, the inverse comparison sends the twisting generator
to the differential of the affine coordinate, with a negative sign on the second chart. -/
@[simp]
lemma relativeDifferentialsIsoTwistingSheaf_inv_chartGenerator (i : Fin 2)
    (V : (projectiveLine R).Opens)
    (hi : V ≤ Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (coord R i)) :
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((relativeDifferentialsIsoTwistingSheaf R).inv.val.app (op V)
      (Proj.twistingSheaf.chartGenerator (-2) (coord R i) (coord_mem R i) V hi) =
      (if i = 0 then (1 : ℤ) else -1) •
        PresheafOfModulesOfCommRing.map ((projectiveLine R).relativeDifferentials R).val
          (homOfLE hi).op
          (((projectiveLine R).universalDerivation R).d (affineCoordinate R i))) := by
  let hi' : V ≤ chartOpen R i := hi.trans (image_awayι_top R i).ge
  have h := (fromTwist_app R i V hi'
    (Proj.twistingSheaf.chartGenerator (-2) (coord R i) (coord_mem R i) V hi)).trans
      (fromTwistLocal_generator R i V hi')
  have hcoord : (projectiveLine R).presheaf.map (homOfLE hi').op (chartCoordinate R i) =
      (projectiveLine R).presheaf.map (homOfLE hi).op (affineCoordinate R i) := by
    rw [chartCoordinate_eq, ← Functor.map_comp_apply]
    rfl
  let D := (projectiveLine R).universalDerivation R
  have hformula := h.trans ((map_zsmul
    (((projectiveLine R).relativeDifferentials R).val.map (homOfLE hi').op).hom
      (if i = 0 then (1 : ℤ) else -1) (chartDifferential R i)).trans
    (congrArg (fun a : Γ((projectiveLine R).relativeDifferentials R, V) ↦
      (if i = 0 then (1 : ℤ) else -1) • a)
      ((D.d_map (homOfLE hi').op _).symm.trans (congrArg D.d hcoord))))
  exact hformula.trans (congrArg (fun a ↦ (if i = 0 then (1 : ℤ) else -1) • a)
    (D.d_map (homOfLE hi).op (affineCoordinate R i)))

/-- The comparison sends `dt` to the first standard twisting generator and `ds` to the
negative of the second, on every subopen of the corresponding chart. -/
@[simp]
lemma relativeDifferentialsIsoTwistingSheaf_hom_d_affineCoordinate (i : Fin 2)
    (V : (projectiveLine R).Opens)
    (hi : V ≤ Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (coord R i)) :
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
      ObjectProperty.ι_obj, homOfLE_leOfHom]
    ((relativeDifferentialsIsoTwistingSheaf R).hom.val.app (op V)
      (PresheafOfModulesOfCommRing.map ((projectiveLine R).relativeDifferentials R).val
        (homOfLE hi).op
        (((projectiveLine R).universalDerivation R).d (affineCoordinate R i))) =
      (if i = 0 then (1 : ℤ) else -1) •
        Proj.twistingSheaf.chartGenerator (-2) (coord R i) (coord_mem R i) V hi) := by
  let L : (projectiveLine R).Modules :=
    Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)) (-2)
  let g := Proj.twistingSheaf.chartGenerator (-2) (coord R i) (coord_mem R i) V hi
  let d := PresheafOfModulesOfCommRing.map ((projectiveLine R).relativeDifferentials R).val
    (homOfLE hi).op (((projectiveLine R).universalDerivation R).d (affineCoordinate R i))
  let f : Γ((projectiveLine R).relativeDifferentials R, V) →ₗ[Γ(projectiveLine R, V)] Γ(L, V) :=
    ((relativeDifferentialsIsoTwistingSheaf R).hom.val.app (op V)).hom
  have hid : f ((relativeDifferentialsIsoTwistingSheaf R).inv.val.app (op V) g) = g :=
    congrArg (fun φ : L ⟶ L ↦ φ.val.app (op V) g)
      (relativeDifferentialsIsoTwistingSheaf R).inv_hom_id
  have h := (map_zsmul f (if i = 0 then (1 : ℤ) else -1) d).symm.trans
    ((congrArg f (relativeDifferentialsIsoTwistingSheaf_inv_chartGenerator R i V hi)).symm.trans
      hid)
  -- These local names carry the component linear map, coordinate differential and generator.
  dsimp only [f, d, g] at h ⊢
  by_cases hindex : i = 0
  · rw [ite_eq_left hindex, one_smul] at h ⊢
    exact h
  · rw [ite_eq_right hindex, neg_one_zsmul] at h ⊢
    exact neg_eq_iff_eq_neg.mp h

end

end TauCeti.AlgebraicGeometry.projectiveLine
