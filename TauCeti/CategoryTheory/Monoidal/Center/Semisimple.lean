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
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Character
public import TauCeti.CategoryTheory.Monoidal.Pivotal.GlobalDim
public import TauCeti.CategoryTheory.Semisimple.Finite
public import TauCeti.CategoryTheory.Semisimple.Split
import TauCeti.CategoryTheory.Adjunction.Linear

/-!
# Semisimplicity and global dimension of the Drinfeld centre

Let `C` be a fusion category over an algebraically closed field `k`: a rigid `k`-linear finite
semisimple abelian monoidal category with simple unit, finitely many simple classes and
finite-dimensional morphism spaces. Its Drinfeld centre `Center C` is abelian, and the induction
functor `Center.induction k C : C ⥤ Center C` is adjoint to the forgetful functor on both sides.
By the averaging identity, the unit `Z ⟶ I (forget Z)` of the right adjunction followed by the
counit `I (forget Z) ⟶ Z` of the left adjunction is multiplication by the global dimension
`TauCeti.normGlobalDim C a`, an endomorphism of the simple unit, hence a scalar.

When the global dimension is nonzero, dividing the counit by it gives a retraction of the unit,
and dividing the unit by it gives a section of the counit. So every object of the centre is a
retract of an induced object, and the Maschke-type criterion
`TauCeti.IsFiniteSemisimpleCategory.of_natTrans` shows that `Center C` is finite semisimple. Since
the forgetful functor is a faithful left adjoint, the centre then has finitely many simple classes,
by `CategoryTheory.Functor.finite_simpleClasses_of_faithful_leftAdjoint`.

No pivotal structure is assumed for semisimplicity: the hypothesis is the nonvanishing of the
pivot-free global dimension. When `C` admits a pivotal structure and `k` has characteristic zero,
this hypothesis holds by the theorem of Etingof, Nikshych and Ostrik (`TauCeti.globalDim_ne_zero`,
transported by `TauCeti.normGlobalDim_eq_globalDim`). In characteristic `p` it can fail: for
`C = Vec(C₂)` in characteristic `2` the global dimension is `0` and the centre is not semisimple.
In the pivotal case, the biproduct decomposition of induction gives
`leftDim ((induction k C).obj X) = dim(C) · leftDim(X)` and
`rightDim ((induction k C).obj X) = dim(C) · rightDim(X)` (read on underlying endomorphisms of
`𝟙_ C`). When `Center C` is finite semisimple with finitely many simple classes, Frobenius
reciprocity yields `dim(Center C) = (dim C)²`.

## Main declarations

* `CategoryTheory.Center.finite_simpleClasses`: whenever `Center C` is finite semisimple, it has
  finitely many simple isomorphism classes (without assuming simplicity of `𝟙_ C` or a pivotal
  structure);
* `CategoryTheory.Center.simpleMultiplicities_inductionCenterObj_apply`: Frobenius reciprocity for
  simple multiplicities of induced objects;
* `forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app`:
  the pivot-free averaging identity in `Center C`;
* `CategoryTheory.Center.isSplitMono_forgetInductionAdjunction_unit_app` and
  `CategoryTheory.Center.isSplitEpi_inductionForgetAdjunction_counit_app`: the unit of the right
  adjunction is a split monomorphism and the counit of the left adjunction is a split epimorphism
  when the global dimension is nonzero;
* `CategoryTheory.Center.isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero` and
  `CategoryTheory.Center.finite_simpleClasses_of_normGlobalDim_ne_zero`: the centre is finite
  semisimple with finitely many simple classes when the global dimension is nonzero;
* `CategoryTheory.Center.isFiniteSemisimpleCategory_of_charZero` and
  `CategoryTheory.Center.finite_simpleClasses_of_charZero`: the same conclusions for a pivotal
  fusion category over a field of characteristic zero;
* `CategoryTheory.Center.isFiniteSemisimpleCategory_of_globalDim_ne_zero`: Maschke semisimplicity
  for a pivotal fusion category when `globalDim C ≠ 0`;
* `CategoryTheory.Center.leftDim_induction_obj_f`, `CategoryTheory.Center.rightDim_induction_obj_f`,
  `CategoryTheory.Center.endAlgEquivOfSimple_globalDim`, `CategoryTheory.Center.globalDim_f`:
  left and right dimensions of `(induction k C).obj X` (`globalDim C ≫ leftDim X` and
  `globalDim C ≫ rightDim X`) and, when `Center C` is finite semisimple with finitely many simple
  classes, `dim(Center C) = (dim C)²`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  Theorem 2.15
* M. Müger, *From subfactors to categories and topology II*, J. Pure Appl. Algebra **180** (2003),
  Theorem 3.16
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.3
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

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- **Frobenius reciprocity for centre induction**: when `Center C` is finite semisimple, the
multiplicity of a simple isomorphism class `M` of `Center C` in `inductionCenterObj k X` (for a
simple object `X : C`) equals the multiplicity of the class of `X` in `M.repr.1`. -/
@[simp]
theorem simpleMultiplicities_inductionCenterObj_apply [Fintype (SimpleClasses C)]
    [IsFiniteSemisimpleCategory (Center C)] (X : C) [Simple X] (M : SimpleClasses (Center C)) :
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

variable [Simple (𝟙_ C)]

section GlobalDim

variable [Fintype (SimpleClasses C)]

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

/-- When the global dimension `TauCeti.normGlobalDim C a` of a fusion category is nonzero, the unit
`Z ⟶ I (forget Z)` of the right adjunction `Center.forget C ⊣ Center.induction k C` is a split
monomorphism: the counit of the left adjunction `Center.induction k C ⊣ Center.forget C`, divided
by the global dimension, is a retraction. -/
theorem isSplitMono_forgetInductionAdjunction_unit_app
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (ha : normGlobalDim C a ≠ 0)
    (Z : Center C) : IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) := by
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k (normGlobalDim C a)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha (by rw [← hc, zero_smul])
  refine IsSplitMono.mk' ⟨c⁻¹ • (inductionForgetAdjunction k C).counit.app Z, ?_⟩
  ext
  rw [Linear.comp_smul, smul_f,
    forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_f k Z a, ← hc]
  simp [smul_smul, inv_mul_cancel₀ hc0]

/-- When the global dimension `TauCeti.normGlobalDim C a` of a fusion category is nonzero, the
counit `I (forget Z) ⟶ Z` of the left adjunction `Center.induction k C ⊣ Center.forget C` is a
split epimorphism: the unit of the right adjunction `Center.forget C ⊣ Center.induction k C`,
divided by the global dimension, is a section. -/
theorem isSplitEpi_inductionForgetAdjunction_counit_app
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (ha : normGlobalDim C a ≠ 0)
    (Z : Center C) : IsSplitEpi ((inductionForgetAdjunction k C).counit.app Z) := by
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k (normGlobalDim C a)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha (by rw [← hc, zero_smul])
  refine IsSplitEpi.mk' ⟨c⁻¹ • (forgetInductionAdjunction k C).unit.app Z, ?_⟩
  ext
  rw [Linear.smul_comp, smul_f,
    forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_f k Z a, ← hc]
  simp [smul_smul, inv_mul_cancel₀ hc0]

include k in
/-- **The centre of a fusion category of nonzero global dimension is finite semisimple**
(Etingof–Nikshych–Ostrik). Here `C` is a fusion category over an algebraically closed field `k`,
with no pivotal structure assumed, and `TauCeti.normGlobalDim C a` is its global dimension for any
family of isomorphisms `a S : S ≅ Sᘁᘁ`. -/
theorem isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (ha : normGlobalDim C a ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) :=
  have := isSplitMono_forgetInductionAdjunction_unit_app k a ha
  IsFiniteSemisimpleCategory.of_natTrans (forget C) (induction k C)
    (forgetInductionAdjunction k C).unit

include k in
/-- **The centre of a fusion category of nonzero global dimension has finitely many simple
classes**, with no pivotal structure assumed. -/
theorem finite_simpleClasses_of_normGlobalDim_ne_zero
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) (ha : normGlobalDim C a ≠ 0) :
    Finite (SimpleClasses (Center C)) :=
  have := isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero k a ha
  (forget C).finite_simpleClasses_of_faithful_leftAdjoint (forgetInductionAdjunction k C)

end GlobalDim

section CharZero

variable [CharZero k] [PivotalCategory C] [Finite (SimpleClasses C)]

include k

/-- **The centre of a pivotal fusion category over a field of characteristic zero is finite
semisimple**, since its global dimension is nonzero (`TauCeti.globalDim_ne_zero`). -/
theorem isFiniteSemisimpleCategory_of_charZero : IsFiniteSemisimpleCategory (Center C) :=
  let := Fintype.ofFinite (SimpleClasses C)
  isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero k (fun S ↦ pivotalIsoApp S.repr)
    (by rw [normGlobalDim_eq_globalDim C k]; exact globalDim_ne_zero k C)

/-- **The centre of a pivotal fusion category over a field of characteristic zero has finitely many
simple classes**, since its global dimension is nonzero (`TauCeti.globalDim_ne_zero`). -/
theorem finite_simpleClasses_of_charZero : Finite (SimpleClasses (Center C)) :=
  let := Fintype.ofFinite (SimpleClasses C)
  finite_simpleClasses_of_normGlobalDim_ne_zero k (fun S ↦ pivotalIsoApp S.repr)
    (by rw [normGlobalDim_eq_globalDim C k]; exact globalDim_ne_zero k C)

end CharZero

section Pivotal

variable [PivotalCategory C] [Fintype (SimpleClasses C)]

omit [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] in
include k in
private theorem normGlobalDim_pivotalIsoApp_ne_zero (hdim : globalDim C ≠ 0) :
    normGlobalDim C (fun S ↦ pivotalIsoApp S.repr) ≠ 0 := by
  rwa [normGlobalDim_eq_globalDim C k (fun S ↦ pivotalIsoApp S.repr)]

include k in
/-- **Maschke's theorem for the Drinfeld centre** (Etingof–Nikshych–Ostrik, Müger): if `C` is a
pivotal fusion category over an algebraically closed field `k` with `globalDim C ≠ 0`, then
`Center C` is finite semisimple. -/
theorem isFiniteSemisimpleCategory_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) :=
  isFiniteSemisimpleCategory_of_normGlobalDim_ne_zero k (fun S ↦ pivotalIsoApp S.repr)
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
          simp_rw [induction_obj, simpleMultiplicities_inductionCenterObj_apply k,
            SimpleClasses.classOf_repr]
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
  rw [hZ, hd, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, sq]

end Pivotal

end CategoryTheory.Center
