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

whose value on a morphism `φ : F ⟶ G` is the family of symmetric powers `Symⁿ φ`. Its degree-one
component recovers `F` (`gradedSymmetricAlgebraDegreeOneIso`), so the functor is faithful. The
graded algebras isomorphic to some `Sym F` are the coordinate algebras of linear schemes
`Spec_X Sym F` over `X` (Stacks Project, tag 01M1).

## Main declarations

* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebra`: the graded symmetric algebra functor;
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebra_obj_obj_X`,
  `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebra_map_hom_hom_hom`,
  `TauCeti.AlgebraicGeometry.mul_gradedSymmetricAlgebra` and
  `TauCeti.AlgebraicGeometry.one_gradedSymmetricAlgebra`: its homogeneous components, its action
  on morphisms, its homogeneous multiplication and its unit;
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

variable {X} in
/-- A morphism of graded quasicoherent algebras whose homogeneous components are identified with
families `M` and `N` carrying units and multiplications, given by componentwise maps `M n ⟶ N n`
preserving those units and multiplications. This transports `GradedQuasicoherentAlgebra.homMk`
along the identifications of components provided by `GradedQuasicoherentAlgebra.ofHomogeneous`. -/
private def homMkOfEq {A B : GradedQuasicoherentAlgebra X} {M N : ℕ → X.Modules}
    (hA : A.obj.X = M) (hB : B.obj.X = N) {oneM : 𝟙_ X.Modules ⟶ M 0}
    {oneN : 𝟙_ X.Modules ⟶ N 0} {mulM : ∀ i j, M i ⊗ M j ⟶ M (i + j)}
    {mulN : ∀ i j, N i ⊗ N j ⟶ N (i + j)}
    (hoA : A.one = oneM ≫ eqToHom (congrFun hA 0).symm)
    (hoB : B.one = oneN ≫ eqToHom (congrFun hB 0).symm)
    (hmA : ∀ i j, A.mul i j = eqToHom (by rw [hA]) ≫ mulM i j ≫ eqToHom (congrFun hA (i + j)).symm)
    (hmB : ∀ i j, B.mul i j = eqToHom (by rw [hB]) ≫ mulN i j ≫ eqToHom (congrFun hB (i + j)).symm)
    (f : ∀ n, M n ⟶ N n) (one_f : oneM ≫ f 0 = oneN)
    (mul_f : ∀ i j, (f i ⊗ₘ f j) ≫ mulN i j = mulM i j ≫ f (i + j)) : A ⟶ B :=
  homMk (fun n ↦ eqToHom (congrFun hA n) ≫ f n ≫ eqToHom (congrFun hB n).symm)
    (by subst hA hB; simp_all) (fun i j ↦ by subst hA hB; simp_all)

/-- The symmetric powers of a quasicoherent sheaf are quasicoherent. This restates
`Scheme.Modules.isQuasicoherent_symmetricPower`, which instance search does not find
on these components. -/
private instance isQuasicoherent_symmetricPower_obj (F : QuasicoherentSheaf X) (n : ℕ) :
    ((SheafOfModules.symmetricPower X.sheaf n).obj F.obj).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_symmetricPower n F.obj

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
    (gradedSymmetricAlgebraObj X F).one =
      (SheafOfModules.symmetricPowerZeroIso X.sheaf).inv.app F.obj ≫
        eqToHom (congrFun (gradedSymmetricAlgebraObj_X F) 0).symm :=
  one_ofHomogeneous _ _ _ _ _ _ _

variable {X} in
/-- The multiplication of `gradedSymmetricAlgebraObj X F` is the multiplication of symmetric
powers. -/
private theorem mul_gradedSymmetricAlgebraObj (F : QuasicoherentSheaf X) (i j : ℕ) :
    (gradedSymmetricAlgebraObj X F).mul i j =
      eqToHom (by rw [gradedSymmetricAlgebraObj_X]; rfl) ≫
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
  map_id F := hom_ext _ _ fun n ↦ by
    simp only [homMkOfEq, homMk_hom_hom_hom, ObjectProperty.FullSubcategory.id_hom, CommMon.id_hom]
    -- The symmetric powers and the graded components use the categories of sheaves of modules
    -- over `ringCatSheaf X.sheaf` and of `X.Modules`, whose instances `simp` does not identify.
    exact (congrArg (fun g ↦ eqToHom _ ≫ g ≫ eqToHom _)
      ((SheafOfModules.symmetricPower X.sheaf n).map_id F.obj)).trans
        ((congrArg (eqToHom _ ≫ ·) (Category.id_comp _)).trans (eqToHom_trans _ _))
  map_comp φ ψ := hom_ext _ _ fun n ↦ by
    simp only [homMkOfEq, homMk_hom_hom_hom, ObjectProperty.FullSubcategory.comp_hom,
      CommMon.comp_hom, Functor.map_comp]
    -- As for `map_id`, the transports are cancelled in `X.Modules`, and the result is matched
    -- against the goal up to the identification of the two categories of sheaves of modules.
    have h {a b c a' b' c' : X.Modules} (ha : a = a') (hb : b = b') (hc : c = c') (f : a' ⟶ b')
        (g : b' ⟶ c') : eqToHom ha ≫ (f ≫ g) ≫ eqToHom hc.symm =
          (eqToHom ha ≫ f ≫ eqToHom hb.symm) ≫ eqToHom hb ≫ g ≫ eqToHom hc.symm := by
      simp
    exact h _ _ (congrFun (gradedSymmetricAlgebraObj_X _) n) _ _

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
  congrFun (homMk_hom_hom_hom _ _ _) n

/-- The homogeneous multiplication of the graded symmetric algebra of `F` is the multiplication
of symmetric powers `Symⁱ F ⊗ Symʲ F ⟶ Symⁱ⁺ʲ F`, up to the identifications
`gradedSymmetricAlgebra_obj_obj_X`. -/
@[simp]
theorem mul_gradedSymmetricAlgebra (F : QuasicoherentSheaf X) (i j : ℕ) :
    ((gradedSymmetricAlgebra X).obj F).mul i j =
      eqToHom (by rw [gradedSymmetricAlgebra_obj_obj_X, gradedSymmetricAlgebra_obj_obj_X]; rfl) ≫
        SheafOfModules.symmetricPowerMul F.obj i j ≫
        eqToHom (gradedSymmetricAlgebra_obj_obj_X F (i + j)).symm :=
  mul_gradedSymmetricAlgebraObj F i j

/-- The unit of the graded symmetric algebra of `F` is the identification `𝒪_X ≅ Sym⁰ F`, up to
the identification `gradedSymmetricAlgebra_obj_obj_X`. -/
@[simp]
theorem one_gradedSymmetricAlgebra (F : QuasicoherentSheaf X) :
    ((gradedSymmetricAlgebra X).obj F).one =
      (SheafOfModules.symmetricPowerZeroIso X.sheaf).inv.app F.obj ≫
        eqToHom (gradedSymmetricAlgebra_obj_obj_X F 0).symm :=
  one_gradedSymmetricAlgebraObj F

/-- The degree-one component of the graded symmetric algebra of `F` is the first symmetric power
`Sym¹ F`. -/
theorem degreeOne_obj_gradedSymmetricAlgebra_obj (F : QuasicoherentSheaf X) :
    (degreeOne.obj ((gradedSymmetricAlgebra X).obj F)).obj =
      (SheafOfModules.symmetricPower X.sheaf 1).obj F.obj :=
  (degree_obj_obj _ 1).trans (gradedSymmetricAlgebra_obj_obj_X F 1)

variable (X)

/-- The degree-one component of the graded symmetric algebra of a quasicoherent sheaf `F` is
naturally isomorphic to `F`, through the identification `Sym¹ F ≅ F`. -/
def gradedSymmetricAlgebraDegreeOneIso :
    gradedSymmetricAlgebra X ⋙ degreeOne ≅ 𝟭 (QuasicoherentSheaf X) :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (eqToIso (degreeOne_obj_gradedSymmetricAlgebra_obj F) ≪≫
      (SheafOfModules.symmetricPowerOneIso X.sheaf).app F.obj))
    (fun {F G} φ ↦ ObjectProperty.hom_ext _ (by
      simp only [Functor.comp_map, degree_map_hom, gradedSymmetricAlgebra_map_hom_hom_hom,
        ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.isoMk_hom, Iso.trans_hom,
        eqToIso.hom, Iso.app_hom, Functor.id_map]
      -- The transports live in the categories `X.Modules` and `SheafOfModules X.ringCatSheaf`,
      -- whose instances `simp` does not identify, so they are cancelled in a generic statement.
      have h {a b c d e f g' g : X.Modules} (e₁ : a = b) (e₂ : b = c) (m : c ⟶ d) (e₃ : d = e)
          (e₄ : e = f) (e₅ : f = d) (e₆ : a = c) (iY : d ⟶ g) (iX : c ⟶ g') (ψ : g' ⟶ g)
          (hm : m ≫ iY = iX ≫ ψ) :
          (eqToHom e₁ ≫ (eqToHom e₂ ≫ m ≫ eqToHom e₃) ≫ eqToHom e₄) ≫ eqToHom e₅ ≫ iY =
            eqToHom e₆ ≫ iX ≫ ψ := by
        subst e₁ e₂ e₃ e₄
        simpa using hm
      exact h _ _ _ _ _ _ _ _ _ _
        ((SheafOfModules.symmetricPowerOneIso X.sheaf).hom.naturality φ.hom)))

variable {X}

/-- The component of `gradedSymmetricAlgebraDegreeOneIso` at `F` is the identification
`Sym¹ F ≅ F`, after identifying the degree-one component with `Sym¹ F`. -/
@[simp]
theorem gradedSymmetricAlgebraDegreeOneIso_hom_app_hom (F : QuasicoherentSheaf X) :
    ((gradedSymmetricAlgebraDegreeOneIso X).hom.app F).hom =
      eqToHom (degreeOne_obj_gradedSymmetricAlgebra_obj F) ≫
        (SheafOfModules.symmetricPowerOneIso X.sheaf).hom.app F.obj :=
  (rfl)

/-- The inverse component of `gradedSymmetricAlgebraDegreeOneIso` at `F` is the identification
`F ≅ Sym¹ F`, followed by the identification of `Sym¹ F` with the degree-one component. -/
@[simp]
theorem gradedSymmetricAlgebraDegreeOneIso_inv_app_hom (F : QuasicoherentSheaf X) :
    ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F).hom =
      (SheafOfModules.symmetricPowerOneIso X.sheaf).inv.app F.obj ≫
        eqToHom (degreeOne_obj_gradedSymmetricAlgebra_obj F).symm :=
  (rfl)

/-- The graded symmetric algebra functor is faithful: a morphism of quasicoherent sheaves is
recovered from its action in degree one. -/
instance : (gradedSymmetricAlgebra X).Faithful :=
  Functor.Faithful.of_comp_iso (gradedSymmetricAlgebraDegreeOneIso X)

end

end AlgebraicGeometry

end TauCeti
