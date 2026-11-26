/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Abelian
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.LeftAdjunction
public import TauCeti.CategoryTheory.Monoidal.Center.Pivotal
public import TauCeti.CategoryTheory.Monoidal.Center.Simple
public import TauCeti.CategoryTheory.Monoidal.Pivotal.GlobalDim
public import TauCeti.CategoryTheory.Semisimple.Finite
public import TauCeti.CategoryTheory.Semisimple.Split
import TauCeti.CategoryTheory.Adjunction.Linear
import TauCeti.CategoryTheory.Monoidal.Pivotal.Character

/-!
# Semisimplicity and global dimension of the Drinfeld centre

For a fusion category `C` over an algebraically closed field `k`, `Center.induction k C` is both
right adjoint (`forgetInductionAdjunction k C`) and left adjoint (`inductionForgetAdjunction k C`)
to `Center.forget C`. Composing the unit of `forgetInductionAdjunction k C` with the counit of
`inductionForgetAdjunction k C` at `Z : Center C` cancels the half-braiding on every simple summand
and acts as scalar multiplication by the pivot-free global dimension `TauCeti.normGlobalDim C a`
for any family `a S : S.repr ≅ S.reprᘁᘁ`.

This yields the arbitrary-characteristic structural theorems of Etingof–Nikshych–Ostrik and Müger:
* `finite_simpleClasses`: whenever `Center C` is finite semisimple, it has finitely many simple
  isomorphism classes (without assuming simplicity of `𝟙_ C` or a pivotal structure).
* `simpleMultiplicities_inductionCenterObj_apply`, `simpleMultiplicities_induction_obj_apply`:
  Frobenius reciprocity for simple multiplicities of induced objects.
* `forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app`: pivot-free
  averaging identity (`= normGlobalDim C a • 𝟙 Z`);
* `isSplitMono_forgetInductionAdjunction_unit_app_of_normGlobalDim_ne_zero`,
  `isSplitEpi_inductionForgetAdjunction_counit_app_of_normGlobalDim_ne_zero`,
  `isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero`,
  `finite_simpleClasses_of_normGlobalDim_ne_zero`: pivot-free Maschke splittings, semisimplicity,
  and finiteness when `normGlobalDim C a ≠ 0` (necessary in characteristic `p > 0`, e.g. `ℤ/p`-
  graded vector spaces have `dim C = p = 0` and non-semisimple centre).
* `forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_f_of_pivotal`,
  `forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_of_pivotal`,
  `isSplitMono_forgetInductionAdjunction_unit_app_of_globalDim_ne_zero`,
  `isSplitEpi_inductionForgetAdjunction_counit_app_of_globalDim_ne_zero`,
  `isFiniteSemisimpleCategory_of_globalDim_ne_zero`,
  `finite_simpleClasses_of_globalDim_ne_zero`: pivotal corollaries when `globalDim C ≠ 0`.
* `leftDim_induction_obj_f`, `rightDim_induction_obj_f`, `endAlgEquivOfSimple_globalDim`,
  `globalDim_f`: `dim((induction k C).obj X) = dim(C) · dim(X)` and `dim(Center C) = (dim C)²`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  Thm. 2.15
* M. Müger, *From subfactors to categories and topology II*, J. Pure Appl. Algebra **180** (2003),
  Thm. 3.16
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], Thm. 9.3.2
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti

universe w v u

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

/-- If `C` is a rigid `k`-linear finite semisimple abelian monoidal category over an algebraically
closed field `k` with finitely many simple isomorphism classes and finite-dimensional morphism
spaces, and `Center C` is finite semisimple, then `Center C` has finitely many isomorphism classes
of simple objects. -/
theorem finite_simpleClasses (k : Type w) [Field k] [IsAlgClosed k]
    {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
    [IsFiniteSemisimpleCategory C] [Finite (SimpleClasses C)]
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] [IsFiniteSemisimpleCategory (Center C)] :
    Finite (SimpleClasses (Center C)) := by
  classical
  let _ := Fintype.ofFinite (SimpleClasses C)
  exact (forget C).finite_simpleClasses_of_faithful_leftAdjoint (forgetInductionAdjunction k C)

section Fusion

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Fintype (SimpleClasses C)]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- **Frobenius reciprocity for centre induction**: when `Center C` is finite semisimple, the
multiplicity of a simple isomorphism class `M` of `Center C` in `inductionCenterObj k X` (for a
simple object `X : C`) equals the multiplicity of the class of `X` in `M.repr.1`. -/
@[simp]
theorem simpleMultiplicities_inductionCenterObj_apply [IsFiniteSemisimpleCategory (Center C)]
    (X : C) [Simple X] (M : SimpleClasses (Center C)) :
    simpleMultiplicities (inductionCenterObj k X) M =
      simpleMultiplicities M.repr.1 (SimpleClasses.classOf X) := by
  have : ∀ Z W : Center C, FiniteDimensional k (Z ⟶ W) := inferInstance
  calc simpleMultiplicities (inductionCenterObj k X) M
      = Module.finrank k (M.repr ⟶ (induction k C).obj X) := by
        rw [← induction_obj, finrank_hom_simple_eq_simpleMultiplicities k,
          SimpleClasses.classOf_repr]
    _ = Module.finrank k (M.repr.1 ⟶ X) :=
        ((forgetInductionAdjunction k C).homLinearEquiv k M.repr X).finrank_eq.symm
    _ = simpleMultiplicities M.repr.1 (SimpleClasses.classOf X) :=
        finrank_homTo_simple_eq_simpleMultiplicities k _ _

/-- **Frobenius reciprocity for centre induction**: when `Center C` is finite semisimple, the
multiplicity of a simple isomorphism class `M` of `Center C` in `(induction k C).obj X` (for a
simple object `X : C`) equals the multiplicity of the class of `X` in `M.repr.1`. -/
theorem simpleMultiplicities_induction_obj_apply [IsFiniteSemisimpleCategory (Center C)]
    (X : C) [Simple X] (M : SimpleClasses (Center C)) :
    simpleMultiplicities ((induction k C).obj X) M =
      simpleMultiplicities M.repr.1 (SimpleClasses.classOf X) := by
  rw [induction_obj, simpleMultiplicities_inductionCenterObj_apply]

variable [Simple (𝟙_ C)]

/-- In a fusion category `C` over an algebraically closed field `k`, the composite of the unit of
`forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` at `Z : Center C` is
scalar multiplication by the pivot-free global dimension `TauCeti.normGlobalDim C a` (read in `k`),
for any family `a S : S.repr ≅ S.reprᘁᘁ`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (Z : Center C) :
    (forgetInductionAdjunction k C).unit.app Z ≫
        (inductionForgetAdjunction k C).counit.app Z =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a)) • 𝟙 Z := by
  refine Center.ext _ _ ?_
  set d := endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a))
  have hg : normGlobalDim C a = d • 𝟙 (𝟙_ C) :=
    (endAlgEquivOfSimple_smul_id (k := k) (End.of (normGlobalDim C a))).symm
  rw [smul_f, id_f,
    forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_f k Z a, hg]
  simp [MonoidalLinear.smul_whiskerRight]

private theorem inv_endAlgEquivOfSimple_normGlobalDim_smul_unit_comp_counit
    {a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ}
    (hdim : normGlobalDim C a ≠ 0) (Z : Center C) :
    (endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a)))⁻¹ •
        ((forgetInductionAdjunction k C).unit.app Z ≫
          (inductionForgetAdjunction k C).counit.app Z) =
      𝟙 Z := by
  have hd : endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a)) ≠ 0 := fun h ↦
    hdim (by simpa using (endAlgEquivOfSimple_apply_eq_iff (End.of (normGlobalDim C a)) 0).1 h)
  rw [forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app k a,
    smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- In a fusion category `C` over an algebraically closed field `k` with
`TauCeti.normGlobalDim C a ≠ 0` (for some family `a S : S.repr ≅ S.reprᘁᘁ`), every component of
`(forgetInductionAdjunction k C).unit` is a split monomorphism. -/
theorem isSplitMono_forgetInductionAdjunction_unit_app_of_normGlobalDim_ne_zero
    {a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ}
    (hdim : normGlobalDim C a ≠ 0) (Z : Center C) :
    IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) :=
  IsSplitMono.mk'
    { retraction := (endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a)))⁻¹ •
        (inductionForgetAdjunction k C).counit.app Z
      id := (Linear.comp_smul _ _ _ _ _ _).trans
        (inv_endAlgEquivOfSimple_normGlobalDim_smul_unit_comp_counit k hdim Z) }

/-- In a fusion category `C` over an algebraically closed field `k` with
`TauCeti.normGlobalDim C a ≠ 0` (for some family `a S : S.repr ≅ S.reprᘁᘁ`), every component of
`(inductionForgetAdjunction k C).counit` is a split epimorphism. -/
theorem isSplitEpi_inductionForgetAdjunction_counit_app_of_normGlobalDim_ne_zero
    {a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ}
    (hdim : normGlobalDim C a ≠ 0) (Z : Center C) :
    IsSplitEpi ((inductionForgetAdjunction k C).counit.app Z) :=
  IsSplitEpi.mk'
    { section_ := (endAlgEquivOfSimple k (𝟙_ C) (End.of (normGlobalDim C a)))⁻¹ •
        (forgetInductionAdjunction k C).unit.app Z
      id := (Linear.smul_comp _ _ _ _ _ _).trans
        (inv_endAlgEquivOfSimple_normGlobalDim_smul_unit_comp_counit k hdim Z) }

include k in
/-- **Maschke's theorem for the Drinfeld centre** (Etingof–Nikshych–Ostrik, Müger): if `C` is a
fusion category over an algebraically closed field `k` with `TauCeti.normGlobalDim C a ≠ 0` (for
some family `a S : S.repr ≅ S.reprᘁᘁ`), then `Center C` is finite semisimple. -/
theorem isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero
    {a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ}
    (hdim : normGlobalDim C a ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) := by
  have := isSplitMono_forgetInductionAdjunction_unit_app_of_normGlobalDim_ne_zero k hdim
  exact IsFiniteSemisimpleCategory.of_natTrans (forget C) (induction k C)
    (forgetInductionAdjunction k C).unit

include k in
/-- If `C` is a fusion category over an algebraically closed field `k` with
`TauCeti.normGlobalDim C a ≠ 0` (for some family `a S : S.repr ≅ S.reprᘁᘁ`), then `Center C` has
finitely many isomorphism classes of simple objects. -/
theorem finite_simpleClasses_of_normGlobalDim_ne_zero
    {a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ}
    (hdim : normGlobalDim C a ≠ 0) :
    Finite (SimpleClasses (Center C)) := by
  have := isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero k hdim
  exact finite_simpleClasses k

section Pivotal

variable [PivotalCategory C]

/-- On underlying objects in a pivotal fusion category `C` over an algebraically closed field `k`,
the composite of the unit of `forgetInductionAdjunction` with the counit of
`inductionForgetAdjunction` at `Z : Center C` is multiplication by `globalDim C`. -/
theorem forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_f_of_pivotal
    (Z : Center C) :
    ((forgetInductionAdjunction k C).unit.app Z ≫
        (inductionForgetAdjunction k C).counit.app Z).f =
      (λ_ Z.1).inv ≫ globalDim C ▷ Z.1 ≫ (λ_ Z.1).hom := by
  rw [← normGlobalDim_eq_globalDim C k (fun S ↦ pivotalIsoApp S.repr)]
  exact forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_f
    k Z (fun S ↦ pivotalIsoApp S.repr)

/-- In a pivotal fusion category `C` over an algebraically closed field `k`, the composite of the
unit of `forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` at
`Z : Center C` is scalar multiplication by `globalDim C` (read in `k`). -/
@[reassoc]
theorem forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_of_pivotal
    (Z : Center C) :
    (forgetInductionAdjunction k C).unit.app Z ≫
        (inductionForgetAdjunction k C).counit.app Z =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) • 𝟙 Z := by
  rw [← normGlobalDim_eq_globalDim C k (fun S ↦ pivotalIsoApp S.repr)]
  exact forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app
    k (fun S ↦ pivotalIsoApp S.repr) Z

omit [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] in
include k in
private theorem normGlobalDim_pivotalIsoApp_ne_zero (hdim : globalDim C ≠ 0) :
    normGlobalDim C (fun S ↦ pivotalIsoApp S.repr) ≠ 0 := by
  rwa [normGlobalDim_eq_globalDim C k (fun S ↦ pivotalIsoApp S.repr)]

/-- In a pivotal fusion category `C` over an algebraically closed field `k` with `globalDim C ≠ 0`,
every component of `(forgetInductionAdjunction k C).unit` is a split monomorphism. -/
theorem isSplitMono_forgetInductionAdjunction_unit_app_of_globalDim_ne_zero
    (hdim : globalDim C ≠ 0) (Z : Center C) :
    IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) :=
  isSplitMono_forgetInductionAdjunction_unit_app_of_normGlobalDim_ne_zero k
    (normGlobalDim_pivotalIsoApp_ne_zero k hdim) Z

/-- In a pivotal fusion category `C` over an algebraically closed field `k` with `globalDim C ≠ 0`,
every component of `(inductionForgetAdjunction k C).counit` is a split epimorphism. -/
theorem isSplitEpi_inductionForgetAdjunction_counit_app_of_globalDim_ne_zero
    (hdim : globalDim C ≠ 0) (Z : Center C) :
    IsSplitEpi ((inductionForgetAdjunction k C).counit.app Z) :=
  isSplitEpi_inductionForgetAdjunction_counit_app_of_normGlobalDim_ne_zero k
    (normGlobalDim_pivotalIsoApp_ne_zero k hdim) Z

include k in
/-- **Maschke's theorem for the Drinfeld centre** (Etingof–Nikshych–Ostrik, Müger): if `C` is a
pivotal fusion category over an algebraically closed field `k` with `globalDim C ≠ 0`, then
`Center C` is finite semisimple. -/
theorem isFiniteSemisimpleCategory_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) :=
  isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero k
    (normGlobalDim_pivotalIsoApp_ne_zero k hdim)

include k in
/-- If `C` is a pivotal fusion category over an algebraically closed field `k` with
`globalDim C ≠ 0`, then `Center C` has finitely many isomorphism classes of simple objects. -/
theorem finite_simpleClasses_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    Finite (SimpleClasses (Center C)) :=
  finite_simpleClasses_of_normGlobalDim_ne_zero k
    (normGlobalDim_pivotalIsoApp_ne_zero k hdim)

omit [Simple (𝟙_ C)] in
private theorem dim_induction_obj_f (X : C) (d : C → (𝟙_ C ⟶ 𝟙_ C))
    (hd_biprod : d (⨁ inductionSummand X) = ∑ T, d (inductionSummand X T))
    (hd_tensor : ∀ A B : C, d (A ⊗ B) = d A ≫ d B)
    (hd_dual : ∀ T : SimpleClasses C, d T.repr ≫ d T.reprᘁ = leftDim T.repr ≫ rightDim T.repr) :
    d ((induction k C).obj X).1 = globalDim C ≫ d X := by
  rw [induction_obj, inductionCenterObj_fst, hd_biprod,
    globalDim_eq_sum_leftDim_comp_rightDim, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  calc d (inductionSummand X T)
      = d T.repr ≫ (d X ≫ d T.reprᘁ) := by rw [inductionSummand, hd_tensor, hd_tensor]
    _ = (d T.repr ≫ d T.reprᘁ) ≫ d X := by rw [scalar_comm (d X) (d T.reprᘁ), Category.assoc]
    _ = (leftDim T.repr ≫ rightDim T.repr) ≫ d X := by rw [hd_dual]

/-- In a pivotal fusion category `C` over an algebraically closed field `k`, the left dimension of
`(induction k C).obj X`, read in `C`, is `globalDim C ≫ leftDim X`. -/
theorem leftDim_induction_obj_f (X : C) :
    (leftDim ((induction k C).obj X)).f = globalDim C ≫ leftDim X :=
  (leftDim_f ((induction k C).obj X)).trans <|
    dim_induction_obj_f k X leftDim leftDim_biproduct
      (leftDim_tensor_eq_comp_of_simple k) fun T ↦ by rw [leftDim_rightDual]

/-- In a pivotal fusion category `C` over an algebraically closed field `k`, the right dimension of
`(induction k C).obj X`, read in `C`, is `globalDim C ≫ rightDim X`. -/
theorem rightDim_induction_obj_f (X : C) :
    (rightDim ((induction k C).obj X)).f = globalDim C ≫ rightDim X :=
  (rightDim_f ((induction k C).obj X)).trans <|
    dim_induction_obj_f k X rightDim rightDim_biproduct
      (rightDim_tensor_eq_comp_of_simple k) fun T ↦ by rw [rightDim_rightDual, scalar_comm]

omit [IsFiniteSemisimpleCategory C] [Fintype (SimpleClasses C)] in
private theorem leftDimChar_center_of
    [EssentiallySmall.{max u v} (Center C)] (Z : Center C) :
    SplitK0.leftDimChar k (Center C) (SplitK0.of Z) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim Z).f) := by
  rw [SplitK0.leftDimChar_of, endAlgEquivOfSimple_unit_apply]

private theorem sum_simpleMultiplicities_mul_leftDimChar_eq
    [IsFiniteSemisimpleCategory (Center C)] [Fintype (SimpleClasses (Center C))]
    [EssentiallySmall.{max u v} C] [EssentiallySmall.{max u v} (Center C)]
    (S : SimpleClasses C) :
    ∑ M : SimpleClasses (Center C),
        (simpleMultiplicities M.repr.1 S : k) *
          SplitK0.leftDimChar k (Center C) (SplitK0.of M.repr) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) *
        SplitK0.leftDimChar k C (SplitK0.of S.repr) := by
  calc _ = SplitK0.leftDimChar k (Center C) (SplitK0.of ((induction k C).obj S.repr)) := by
          rw [SplitK0.ringHom_apply_of]
          simp_rw [simpleMultiplicities_induction_obj_apply k, SimpleClasses.classOf_repr]
    _ = _ := by
          rw [leftDimChar_center_of, leftDim_induction_obj_f]
          simp [mul_comm]

variable (C)

/-- **Global dimension of the Drinfeld centre** (Müger, Etingof–Nikshych–Ostrik): for a pivotal
fusion category `C` over an algebraically closed field `k` whose centre `Center C` is finite
semisimple with finitely many simple classes, the global dimension of `Center C` in `k` is the
square of the global dimension of `C`. -/
theorem endAlgEquivOfSimple_globalDim [IsFiniteSemisimpleCategory (Center C)]
    [Fintype (SimpleClasses (Center C))] :
    endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (globalDim (Center C))) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 := by
  have : EssentiallySmall.{max u v} C := essentiallySmall_of_small_of_locallySmall C
  have : EssentiallySmall.{max u v} (Center C) :=
    essentiallySmall_of_small_of_locallySmall (Center C)
  let χC := SplitK0.leftDimChar k C
  let ψC := SplitK0.rightDimChar k C
  let χZ := SplitK0.leftDimChar k (Center C)
  let d := endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C))
  have hd : d = ∑ S : SimpleClasses C, χC (SplitK0.of S.repr) * ψC (SplitK0.of S.repr) := by
    simp only [d, globalDim_eq_sum_leftDimChar_smul k, End.of_smul, End.of_id, map_smul,
      map_one, smul_eq_mul, mul_one, ← SplitK0.dual_of, SplitK0.leftDimChar_dual, χC, ψC]
  have hM (M : SimpleClasses (Center C)) :
      ∑ S : SimpleClasses C, (simpleMultiplicities M.repr.1 S : k) * ψC (SplitK0.of S.repr) =
        χZ (SplitK0.of (M.repr)ᘁ) := by
    calc ∑ S : SimpleClasses C, (simpleMultiplicities M.repr.1 S : k) * ψC (SplitK0.of S.repr)
        = ψC (SplitK0.of M.repr.1) := (SplitK0.ringHom_apply_of ψC M.repr.1).symm
      _ = χZ (SplitK0.of (M.repr)ᘁ) := by
          -- Normal form: scalar of `rightDim M.repr.1` in `k`
          simp only [ψC, χZ, leftDimChar_center_of, leftDim_rightDual, rightDim_f,
            SplitK0.rightDimChar_of]
  calc endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (globalDim (Center C)))
      = ∑ M : SimpleClasses (Center C), χZ (SplitK0.of M.repr) *
          (∑ S : SimpleClasses C, (simpleMultiplicities M.repr.1 S : k) * ψC (SplitK0.of S.repr)) :=
        by simp_rw [hM]; simp [globalDim_eq_sum_leftDimChar_smul k, χZ]
    _ = ∑ S : SimpleClasses C,
          (∑ M : SimpleClasses (Center C),
            (simpleMultiplicities M.repr.1 S : k) * χZ (SplitK0.of M.repr)) *
          ψC (SplitK0.of S.repr) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun M _ ↦ by ring
    _ = d ^ 2 := by
        rw [Finset.sum_congr rfl fun S _ ↦ by
            rw [sum_simpleMultiplicities_mul_leftDimChar_eq k S, mul_assoc],
          ← Finset.mul_sum, ← hd, sq]

include k in
/-- For a pivotal fusion category `C` over an algebraically closed field `k` such that `Center C`
is finite semisimple with finitely many simple classes, on underlying endomorphisms of the unit
`globalDim (Center C)` is the composite `globalDim C ≫ globalDim C`. -/
theorem globalDim_f [IsFiniteSemisimpleCategory (Center C)]
    [Fintype (SimpleClasses (Center C))] :
    (globalDim (Center C)).f = globalDim C ≫ globalDim C := by
  set d := endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C))
  have hd : globalDim C = d • 𝟙 (𝟙_ C) :=
    (endAlgEquivOfSimple_smul_id (k := k) (End.of (globalDim C))).symm
  have hZ : (globalDim (Center C)).f = d ^ 2 • 𝟙 (𝟙_ C) := by
    have h1 := congrArg Hom.f
      (endAlgEquivOfSimple_smul_id (k := k) (End.of (globalDim (Center C)))).symm
    rwa [endAlgEquivOfSimple_globalDim k C, smul_f, id_f] at h1
  rw [hZ, hd]
  simp [sq, smul_smul]
  rfl

end Pivotal

end Fusion

end CategoryTheory.Center
