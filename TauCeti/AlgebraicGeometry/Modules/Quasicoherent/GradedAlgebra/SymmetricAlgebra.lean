/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Mul
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Quasicoherent

/-!
# The graded symmetric algebra of a quasicoherent sheaf

For a quasicoherent sheaf `F` on a scheme `X`, the symmetric powers `Symⁿ F` are quasicoherent,
and the multiplications `Symⁱ F ⊗ Symʲ F ⟶ Symⁱ⁺ʲ F` together with the unit `𝒪_X ≅ Sym⁰ F` make
`Sym F = ⨁ₙ Symⁿ F` a commutative nonnegatively graded quasicoherent `𝒪_X`-algebra. This file
packages that construction as a functor

`gradedSymmetricAlgebra X : QuasicoherentSheaf X ⥤ GradedQuasicoherentAlgebra X`,

whose value on a morphism `φ : F ⟶ G` is the family of symmetric powers `Symⁿ φ`. Its degree-`n`
component is naturally the symmetric power functor `QuasicoherentSheaf.symmetricPower X n`
(`gradedSymmetricAlgebraDegreeIso`), and its degree-one component recovers `F`
(`gradedSymmetricAlgebraDegreeOneIso`), so the functor is faithful. The
graded algebras isomorphic to some `Sym F` are the coordinate algebras of linear schemes
`Spec_X Sym F` over `X` (Stacks Project, tag 01M1).

## Main declarations

* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebra`: the graded symmetric algebra functor;
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebra_obj_obj_X`,
  `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebra_map_hom_hom_hom`,
  `TauCeti.AlgebraicGeometry.mul_gradedSymmetricAlgebra` and
  `TauCeti.AlgebraicGeometry.one_gradedSymmetricAlgebra`: its homogeneous components, its action
  on morphisms, its homogeneous multiplication and its unit;
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraDegreeIso`: the natural isomorphism between
  the degree-`n` component of `Sym F` and the quasicoherent symmetric power `Symⁿ F`;
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraDegreeOneIso`: the natural isomorphism between
  the degree-one component of `Sym F` and `F`.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry GradedQuasicoherentAlgebra

universe u

noncomputable section

variable (X : Scheme.{u})

/-- The graded symmetric algebra of a single quasicoherent sheaf, assembled from its homogeneous
components by `GradedQuasicoherentAlgebra.ofHomogeneous`. -/
private def gradedSymmetricAlgebraObj (F : QuasicoherentSheaf X) : GradedQuasicoherentAlgebra X :=
  ofHomogeneous (fun n ↦ (SheafOfModules.symmetricPower X.sheaf n).obj F.obj)
    ((SheafOfModules.symmetricPowerZeroIso X.sheaf).inv.app F.obj)
    (SheafOfModules.symmetricPowerMul F.obj) (SheafOfModules.symmetricPowerMul_one_mul F.obj)
    (SheafOfModules.symmetricPowerMul_mul_one F.obj)
    (SheafOfModules.symmetricPowerMul_assoc F.obj) (SheafOfModules.symmetricPowerMul_comm F.obj)

variable {X} in
/-- The homogeneous components of `gradedSymmetricAlgebraObj X F` are the symmetric powers. -/
private theorem gradedSymmetricAlgebraObj_X (F : QuasicoherentSheaf X) :
    (gradedSymmetricAlgebraObj X F).obj.X =
      fun n ↦ (SheafOfModules.symmetricPower X.sheaf n).obj F.obj :=
  ofHomogeneous_obj_X _ _ _ _ _ _ _

variable {X} in
/-- The unit of `gradedSymmetricAlgebraObj X F` is the identification `𝒪_X ≅ Sym⁰ F`. -/
private theorem one_gradedSymmetricAlgebraObj (F : QuasicoherentSheaf X) :
    (gradedSymmetricAlgebraObj X F).obj.toMon.one =
      (SheafOfModules.symmetricPowerZeroIso X.sheaf).inv.app F.obj ≫
        eqToHom (congrFun (gradedSymmetricAlgebraObj_X F) 0).symm :=
  one_ofHomogeneous _ _ _ _ _ _ _

variable {X} in
/-- The multiplication of `gradedSymmetricAlgebraObj X F` is the multiplication of symmetric
powers. -/
private theorem mul_gradedSymmetricAlgebraObj (F : QuasicoherentSheaf X) (i j : ℕ) :
    (gradedSymmetricAlgebraObj X F).obj.toMon.mul i j =
      (eqToHom (by rw [gradedSymmetricAlgebraObj_X]; rfl) :
        (gradedSymmetricAlgebraObj X F).obj.X i ⊗ (gradedSymmetricAlgebraObj X F).obj.X j ⟶ _) ≫
        SheafOfModules.symmetricPowerMul F.obj i j ≫
        eqToHom (congrFun (gradedSymmetricAlgebraObj_X F) (i + j)).symm :=
  mul_ofHomogeneous _ _ _ _ _ _ _ i j

/-- The graded symmetric algebra `Sym F = ⨁ₙ Symⁿ F` of a quasicoherent sheaf `F`, as a graded
quasicoherent algebra, functorially in `F`: its homogeneous components are the symmetric powers
`Symⁿ F`, its unit is `𝒪_X ≅ Sym⁰ F`, its homogeneous multiplication is the multiplication of
symmetric powers `Symⁱ F ⊗ Symʲ F ⟶ Symⁱ⁺ʲ F`, and a morphism `φ : F ⟶ G` acts by `Symⁿ φ` in
degree `n`. -/
def gradedSymmetricAlgebra : QuasicoherentSheaf X ⥤ GradedQuasicoherentAlgebra X where
  obj := gradedSymmetricAlgebraObj X
  map {F G} φ := homMkOfEq (gradedSymmetricAlgebraObj_X F) (gradedSymmetricAlgebraObj_X G)
    (one_gradedSymmetricAlgebraObj F) (one_gradedSymmetricAlgebraObj G)
    (mul_gradedSymmetricAlgebraObj F) (mul_gradedSymmetricAlgebraObj G)
    (fun n ↦ (SheafOfModules.symmetricPower X.sheaf n).map φ.hom)
    (((SheafOfModules.symmetricPowerZeroIso X.sheaf).inv.naturality φ.hom).symm.trans
      (Category.id_comp _))
    (SheafOfModules.symmetricPowerMul_naturality φ.hom)
  map_id F := homMkOfEq_id _ _ _ _ _ _ fun n ↦
    (SheafOfModules.symmetricPower X.sheaf n).map_id F.obj
  map_comp φ ψ := homMkOfEq_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun n ↦
    ((SheafOfModules.symmetricPower X.sheaf n).map_comp φ.hom ψ.hom).symm

variable {X}

/-- The degree-`n` component of the graded symmetric algebra of `F` is the symmetric power
`Symⁿ F`. -/
@[simp]
theorem gradedSymmetricAlgebra_obj_obj_X (F : QuasicoherentSheaf X) (n : ℕ) :
    ((gradedSymmetricAlgebra X).obj F).obj.X n =
      (SheafOfModules.symmetricPower X.sheaf n).obj F.obj :=
  congrFun (gradedSymmetricAlgebraObj_X F) n

/-- In degree `n`, the graded symmetric algebra acts on a morphism `φ` by `Symⁿ φ`, up to the
identifications `gradedSymmetricAlgebra_obj_obj_X` of the homogeneous components with the
symmetric powers. -/
@[simp]
theorem gradedSymmetricAlgebra_map_hom_hom_hom {F G : QuasicoherentSheaf X} (φ : F ⟶ G) (n : ℕ) :
    ((gradedSymmetricAlgebra X).map φ).hom.hom.hom n =
      eqToHom (gradedSymmetricAlgebra_obj_obj_X F n) ≫
        (SheafOfModules.symmetricPower X.sheaf n).map φ.hom ≫
        eqToHom (gradedSymmetricAlgebra_obj_obj_X G n).symm :=
  homMkOfEq_hom_hom_hom _ _ _ _ _ _ _ _ _ n

/-- The homogeneous multiplication of the graded symmetric algebra of `F` is the multiplication
of symmetric powers `Symⁱ F ⊗ Symʲ F ⟶ Symⁱ⁺ʲ F`, up to the identifications
`gradedSymmetricAlgebra_obj_obj_X`. -/
@[simp]
theorem mul_gradedSymmetricAlgebra (F : QuasicoherentSheaf X) (i j : ℕ) :
    ((gradedSymmetricAlgebra X).obj F).obj.toMon.mul i j =
      (eqToHom (by rw [gradedSymmetricAlgebra_obj_obj_X, gradedSymmetricAlgebra_obj_obj_X]; rfl) :
        ((gradedSymmetricAlgebra X).obj F).obj.X i ⊗ ((gradedSymmetricAlgebra X).obj F).obj.X j ⟶
          _) ≫
        SheafOfModules.symmetricPowerMul F.obj i j ≫
        eqToHom (gradedSymmetricAlgebra_obj_obj_X F (i + j)).symm :=
  mul_gradedSymmetricAlgebraObj F i j

/-- The unit of the graded symmetric algebra of `F` is the identification `𝒪_X ≅ Sym⁰ F`, up to
the identification `gradedSymmetricAlgebra_obj_obj_X`. -/
@[simp]
theorem one_gradedSymmetricAlgebra (F : QuasicoherentSheaf X) :
    ((gradedSymmetricAlgebra X).obj F).obj.toMon.one =
      (SheafOfModules.symmetricPowerZeroIso X.sheaf).inv.app F.obj ≫
        eqToHom (gradedSymmetricAlgebra_obj_obj_X F 0).symm :=
  one_gradedSymmetricAlgebraObj F

/-- The degree-`n` component of the graded symmetric algebra of `F`, as a quasicoherent sheaf, has
underlying module sheaf the symmetric power `Symⁿ F`. -/
theorem degree_obj_gradedSymmetricAlgebra_obj (F : QuasicoherentSheaf X) (n : ℕ) :
    ((degree n).obj ((gradedSymmetricAlgebra X).obj F)).obj =
      (SheafOfModules.symmetricPower X.sheaf n).obj F.obj :=
  (degree_obj_obj _ n).trans (gradedSymmetricAlgebra_obj_obj_X F n)

/-- The degree-`n` component functor acts on the graded symmetric algebra of a morphism `φ` by
`Symⁿ φ`, up to the identifications `degree_obj_gradedSymmetricAlgebra_obj`.

This is not a `simp` lemma: `degree_map_hom` and `gradedSymmetricAlgebra_map_hom_hom_hom` already
rewrite its left-hand side, so pass it to `simp` explicitly in place of `degree_map_hom`. -/
theorem degree_map_gradedSymmetricAlgebra_map_hom {F G : QuasicoherentSheaf X} (φ : F ⟶ G)
    (n : ℕ) :
    ((degree n).map ((gradedSymmetricAlgebra X).map φ)).hom =
      eqToHom (degree_obj_gradedSymmetricAlgebra_obj F n) ≫
        (SheafOfModules.symmetricPower X.sheaf n).map φ.hom ≫
        eqToHom (degree_obj_gradedSymmetricAlgebra_obj G n).symm := by
  rw [degree_map_hom, gradedSymmetricAlgebra_map_hom_hom_hom]
  -- The outer transports are composed in `SheafOfModules X.ringCatSheaf` and the inner ones in
  -- `X.Modules`, whose instances `simp` does not identify, so the transports are removed up to
  -- heterogeneous equality.
  exact eq_of_heq (((eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans
    ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)))).trans
      ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm)

variable (X) in
/-- The degree-`n` component of the graded symmetric algebra of a quasicoherent sheaf `F` is
naturally isomorphic to the symmetric power `Symⁿ F` of quasicoherent sheaves. -/
def gradedSymmetricAlgebraDegreeIso (n : ℕ) :
    gradedSymmetricAlgebra X ⋙ degree n ≅ QuasicoherentSheaf.symmetricPower X n :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (eqToIso ((degree_obj_gradedSymmetricAlgebra_obj F n).trans
      (QuasicoherentSheaf.symmetricPower_obj_obj X n F).symm)))
    (fun φ ↦ ObjectProperty.hom_ext _ (by
      simp [-degree_map_hom, degree_map_gradedSymmetricAlgebra_map_hom]))

/-- The component of `gradedSymmetricAlgebraDegreeIso` at `F` is the identification of the
degree-`n` component of the graded symmetric algebra of `F` with `Symⁿ F`. -/
@[simp]
theorem gradedSymmetricAlgebraDegreeIso_hom_app_hom (n : ℕ) (F : QuasicoherentSheaf X) :
    ((gradedSymmetricAlgebraDegreeIso X n).hom.app F).hom =
      eqToHom ((degree_obj_gradedSymmetricAlgebra_obj F n).trans
        (QuasicoherentSheaf.symmetricPower_obj_obj X n F).symm) :=
  (rfl)

/-- The inverse component of `gradedSymmetricAlgebraDegreeIso` at `F` is the identification of
`Symⁿ F` with the degree-`n` component of the graded symmetric algebra of `F`. -/
@[simp]
theorem gradedSymmetricAlgebraDegreeIso_inv_app_hom (n : ℕ) (F : QuasicoherentSheaf X) :
    ((gradedSymmetricAlgebraDegreeIso X n).inv.app F).hom =
      eqToHom ((QuasicoherentSheaf.symmetricPower_obj_obj X n F).trans
        (degree_obj_gradedSymmetricAlgebra_obj F n).symm) :=
  (rfl)

variable (X)

/-- The degree-one component of the graded symmetric algebra of a quasicoherent sheaf `F` is
naturally isomorphic to `F`, through the identification `Sym¹ F ≅ F`. -/
def gradedSymmetricAlgebraDegreeOneIso :
    gradedSymmetricAlgebra X ⋙ degreeOne ≅ 𝟭 (QuasicoherentSheaf X) :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (eqToIso (degree_obj_gradedSymmetricAlgebra_obj F 1) ≪≫
      (SheafOfModules.symmetricPowerOneIso X.sheaf).app F.obj))
    (fun φ ↦ ObjectProperty.hom_ext _ (by
      simp [-degree_map_hom, degree_map_gradedSymmetricAlgebra_map_hom]))

variable {X}

/-- The component of `gradedSymmetricAlgebraDegreeOneIso` at `F` is the identification
`Sym¹ F ≅ F`, after identifying the degree-one component with `Sym¹ F`. -/
@[simp]
theorem gradedSymmetricAlgebraDegreeOneIso_hom_app_hom (F : QuasicoherentSheaf X) :
    ((gradedSymmetricAlgebraDegreeOneIso X).hom.app F).hom =
      eqToHom (degree_obj_gradedSymmetricAlgebra_obj F 1) ≫
        (SheafOfModules.symmetricPowerOneIso X.sheaf).hom.app F.obj :=
  (rfl)

/-- The inverse component of `gradedSymmetricAlgebraDegreeOneIso` at `F` is the identification
`F ≅ Sym¹ F`, followed by the identification of `Sym¹ F` with the degree-one component. -/
@[simp]
theorem gradedSymmetricAlgebraDegreeOneIso_inv_app_hom (F : QuasicoherentSheaf X) :
    ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F).hom =
      (SheafOfModules.symmetricPowerOneIso X.sheaf).inv.app F.obj ≫
        eqToHom (degree_obj_gradedSymmetricAlgebra_obj F 1).symm :=
  (rfl)

/-- The graded symmetric algebra functor is faithful: a morphism of quasicoherent sheaves is
recovered from its action in degree one. -/
instance : (gradedSymmetricAlgebra X).Faithful :=
  Functor.Faithful.of_comp_iso (gradedSymmetricAlgebraDegreeOneIso X)

end

end AlgebraicGeometry

end TauCeti
