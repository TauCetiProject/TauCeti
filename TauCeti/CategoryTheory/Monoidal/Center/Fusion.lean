/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.Adjunction
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.LeftAdjunction
public import TauCeti.CategoryTheory.Monoidal.Center.Ribbon
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Biproduct
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Character
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Semisimple
public import TauCeti.CategoryTheory.Semisimple.Finite
public import TauCeti.CategoryTheory.Semisimple.Finrank
public import TauCeti.CategoryTheory.Semisimple.Split

/-!
# The Drinfeld centre of a fusion category is a fusion category

Let `C` be a fusion category over an algebraically closed field `k`, equipped with a pivotal
structure. The forgetful functor `forget C : Center C ⥤ C` has both a right adjoint and a left
adjoint given by the induction functor `induction k C : C ⥤ Center C`
(`forgetInductionAdjunction k C` and `inductionForgetAdjunction k C`).

Evaluating the composite
`Z ⟶ (induction k C).obj Z.1 ⟶ Z`
of the unit of `forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` on each
simple summand `S ⊗ Z.1 ⊗ Sᘁ` cancels the half-braiding `(Z.2.β S).hom` against `(Z.2.β S).inv`
and closes the `S`-strand with the swapped simple pairing, producing the loop
`leftDim S ≫ rightDim S`. Summing over all simple classes `S` yields the **averaging identity**

`(forgetInductionAdjunction k C).unit.app Z ≫ (inductionForgetAdjunction k C).counit.app Z =
  dim(C) • 𝟙 Z`,

where `dim(C) ∈ k` is `globalDim C` read as a scalar via `endAlgEquivOfSimple k (𝟙_ C)`.

Whenever `globalDim C ≠ 0`, dividing the counit by `dim(C)` splits the unit of
`forgetInductionAdjunction` at every `Z : Center C`. Applying the Maschke-type criterion
`IsFiniteSemisimpleCategory.of_natTrans` along `forget C` then shows that `Center C` is finite
semisimple, and `(forget C).finite_simpleClasses_of_faithful_leftAdjoint` transfers finiteness of
simple isomorphism classes from `C` to `Center C`. Over a field of characteristic zero,
`TauCeti.globalDim_ne_zero` supplies `globalDim C ≠ 0` unconditionally, so `Center C` is a fusion
category (and a modular/ribbon fusion category when `C` is spherical, by Müger's theorem).

Finally, Frobenius reciprocity along `forgetInductionAdjunction` identifies the multiplicity of a
simple object `Z` of `Center C` in `(induction k C).obj S` with the multiplicity of `S` in `Z.1`.
Comparing `leftDim (inductionObj S) = leftDim S ≫ globalDim C` with the simple decomposition of
`(induction k C).obj S` in `Center C` and summing against `rightDim S` proves
`globalDim (Center C) = (globalDim C)²` (`CategoryTheory.Center.endAlgEquivOfSimple_globalDim` and
`CategoryTheory.Center.globalDim_f`).

## Main declarations

* `CategoryTheory.Center.endAlgEquivOfSimple_tensorUnit_apply`: reading an endomorphism of
  `𝟙_ (Center C)` in `k` agrees with reading its underlying endomorphism of `𝟙_ C`;
* `CategoryTheory.Center.finite_simpleClasses_of_isFiniteSemisimpleCategory`: if `Center C` is
  finite semisimple, it has finitely many simple isomorphism classes;
* `CategoryTheory.Center.simpleMultiplicities_induction_obj`: Frobenius reciprocity for simple
  multiplicities between `C` and `Center C`;
* `CategoryTheory.Center.forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit`:
  the averaging identity `η_Z ≫ ε'_Z = dim(C) • 𝟙 Z`;
* `CategoryTheory.Center.isFiniteSemisimpleCategory_of_globalDim_ne_zero` and
  `CategoryTheory.Center.finite_simpleClasses_of_globalDim_ne_zero`: `Center C` is a fusion
  category whenever `globalDim C ≠ 0`;
* `CategoryTheory.Center.isFiniteSemisimpleCategory` and
  `CategoryTheory.Center.finite_simpleClasses`: `Center C` is a fusion category in characteristic
  zero;
* `CategoryTheory.Center.ribbonCategory_of_sphericalCategory_of_globalDim_ne_zero` and
  `CategoryTheory.Center.ribbonCategory_of_sphericalCategory_of_charZero`: Müger's ribbon theorem
  on `Center C` under `globalDim C ≠ 0` and unconditionally in characteristic zero;
* `CategoryTheory.Center.leftDim_inductionObj`, `CategoryTheory.Center.rightDim_inductionObj`,
  `CategoryTheory.Center.endAlgEquivOfSimple_globalDim`,
  `CategoryTheory.Center.globalDim_eq_smul_id`, and `CategoryTheory.Center.globalDim_f`:
  `dim(I(X)) = dim(X) · dim(C)` and `globalDim (Center C) = (globalDim C)²`.

## References

* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra **180** (2003), 159–219
* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  Theorem 2.15
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13,
  Theorem 7.16.6, Proposition 9.3.4
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti

universe w v u

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

section UnitScalar

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- Reading an endomorphism of `𝟙_ (Center C)` as a scalar in `k` agrees with reading its
underlying endomorphism of `𝟙_ C`. -/
@[simp]
theorem endAlgEquivOfSimple_tensorUnit_apply (f : 𝟙_ (Center C) ⟶ 𝟙_ (Center C)) :
    endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of f) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of f.f) := by
  rw [endAlgEquivOfSimple_apply_eq_iff]
  ext
  simp only [smul_f, id_f]
  exact (endAlgEquivOfSimple_smul_id (k := k) (X := 𝟙_ C) (End.of f.f)).symm

omit [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C] in
private theorem endAlgEquivOfSimple_sum {ι : Type*} (s : Finset ι) (f : ι → (𝟙_ C ⟶ 𝟙_ C)) :
    endAlgEquivOfSimple k (𝟙_ C) (End.of (∑ i ∈ s, f i)) =
      ∑ i ∈ s, endAlgEquivOfSimple k (𝟙_ C) (End.of (f i)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih => rw [Finset.sum_cons, Finset.sum_cons, End.of_add, map_add, ih]

end UnitScalar

section SemisimpleCenter

variable (k : Type w) [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

include k in
/-- Whenever `Center C` is finite semisimple, it has finitely many isomorphism classes of simple
objects, transferred along the faithful left adjoint `forget C` of `forgetInductionAdjunction`. -/
theorem finite_simpleClasses_of_isFiniteSemisimpleCategory [Finite (SimpleClasses C)]
    [IsFiniteSemisimpleCategory (Center C)] : Finite (SimpleClasses (Center C)) := by
  let := Fintype.ofFinite (SimpleClasses C)
  exact (forget C).finite_simpleClasses_of_faithful_leftAdjoint (forgetInductionAdjunction k C)

variable {C} in
/-- **Frobenius reciprocity for multiplicities in the Drinfeld centre**: the multiplicity of a
simple class `Z` of `Center C` in `(induction k C).obj S.repr` equals the multiplicity of `S` in
the underlying object `Z.repr.1`. -/
theorem simpleMultiplicities_induction_obj [Fintype (SimpleClasses C)]
    [IsFiniteSemisimpleCategory (Center C)]
    (S : SimpleClasses C) (Z : SimpleClasses (Center C)) :
    simpleMultiplicities ((induction k C).obj S.repr) Z =
      simpleMultiplicities Z.repr.1 S := by
  calc simpleMultiplicities ((induction k C).obj S.repr) Z
      = Module.finrank k (Z.repr ⟶ (induction k C).obj S.repr) := by
          rw [finrank_hom_simple_eq_simpleMultiplicities k Z.repr ((induction k C).obj S.repr),
            SimpleClasses.classOf_repr]
    _ = Module.finrank k ((forget C).obj Z.repr ⟶ S.repr) :=
          ((forgetInductionAdjunction k C).homLinearEquiv k Z.repr S.repr).finrank_eq.symm
    _ = simpleMultiplicities Z.repr.1 S := by
          rw [finrank_homTo_simple_eq_simpleMultiplicities k ((forget C).obj Z.repr) S.repr,
            SimpleClasses.classOf_repr]
          rfl

end SemisimpleCenter

section Pivotal

variable (k : Type w) [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C] [PivotalCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

section FintypeSimple

variable [Fintype (SimpleClasses C)]

/-- Underlying morphism form of the averaging identity on `Center C`: composing the unit of
`forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` multiplies `𝟙 Z.1` by
`globalDim C`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit_f (Z : Center C) :
    ((forgetInductionAdjunction k C).unit.app Z).f ≫
        ((inductionForgetAdjunction k C).counit.app Z).f =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) • 𝟙 Z.1 := by
  have hterm (S : SimpleClasses C) :
      (((forgetInductionAdjunction k C).unit.app Z).f ≫ biproduct.π (inductionSummand Z.1) S) ≫
        (biproduct.ι (inductionSummand Z.1) S ≫
          ((inductionForgetAdjunction k C).counit.app Z).f) =
      (ρ_ Z.1).inv ≫ Z.1 ◁ (leftDim S.repr ≫ rightDim S.repr) ≫ (ρ_ Z.1).hom := by
    rw [forgetInductionAdjunction_unit_app_f_comp_π, ι_comp_inductionForgetAdjunction_counit_app_f]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp,
      Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
      coevaluation_comp_simpleSwapExactPairing_evaluation k]
  let u : Z.1 ⟶ inductionObj Z.1 := ((forgetInductionAdjunction k C).unit.app Z).f
  let v : inductionObj Z.1 ⟶ Z.1 := ((inductionForgetAdjunction k C).counit.app Z).f
  set d := endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C))
  change u ≫ v = d • 𝟙 Z.1
  rw [← Category.id_comp v, ← biproduct.total]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  have hsum :
      (∑ S : SimpleClasses C,
        u ≫ biproduct.π (inductionSummand Z.1) S ≫
          biproduct.ι (inductionSummand Z.1) S ≫ v) =
      ∑ S : SimpleClasses C,
        (ρ_ Z.1).inv ≫ Z.1 ◁ (leftDim S.repr ≫ rightDim S.repr) ≫ (ρ_ Z.1).hom := by
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [← Category.assoc u]
    exact hterm S
  have hgd : globalDim C = d • 𝟙 (𝟙_ C) :=
    (endAlgEquivOfSimple_smul_id (k := k) (End.of (globalDim C))).symm
  rw [hsum, ← Preadditive.comp_sum, ← Preadditive.sum_comp, ← whiskerLeft_sum,
    ← globalDim_eq_sum_leftDim_comp_rightDim, hgd, MonoidalLinear.whiskerLeft_smul,
    whiskerLeft_id, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]

/-- **Averaging identity for the Drinfeld centre**: composing the unit of
`forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` at `Z : Center C`
acts as scalar multiplication by `globalDim C`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit (Z : Center C) :
    (forgetInductionAdjunction k C).unit.app Z ≫
        (inductionForgetAdjunction k C).counit.app Z =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) • 𝟙 Z :=
  Hom.ext (forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit_f k C Z)

/-- When `globalDim C ≠ 0`, each component of the unit of `forgetInductionAdjunction` is a split
monomorphism in `Center C`, retracted by `(dim C)⁻¹ • (inductionForgetAdjunction k C).counit`. -/
theorem isSplitMono_forgetInductionAdjunction_unit_of_globalDim_ne_zero
    (hdim : globalDim C ≠ 0) (Z : Center C) :
    IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) := by
  set d := endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C))
  have hd : d ≠ 0 := fun h ↦
    hdim (by simpa using (endAlgEquivOfSimple_apply_eq_iff (End.of (globalDim C)) 0).mp h)
  refine IsSplitMono.mk' ⟨d⁻¹ • (inductionForgetAdjunction k C).counit.app Z, ?_⟩
  rw [Linear.comp_smul, forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit,
    smul_smul, inv_mul_cancel₀ hd, one_smul]
  rfl

include k in
/-- **Semisimplicity of the Drinfeld centre (nondegenerate global dimension)**: if
`globalDim C ≠ 0`, then `Center C` is a split finite semisimple category. -/
theorem isFiniteSemisimpleCategory_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) := by
  have := isSplitMono_forgetInductionAdjunction_unit_of_globalDim_ne_zero k C hdim
  exact IsFiniteSemisimpleCategory.of_natTrans (forget C) (induction k C)
    (forgetInductionAdjunction k C).unit

include k in
/-- **Finiteness of simple classes in the Drinfeld centre (nondegenerate global dimension)**: if
`globalDim C ≠ 0`, then `Center C` has finitely many simple isomorphism classes. -/
theorem finite_simpleClasses_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    Finite (SimpleClasses (Center C)) := by
  have := isFiniteSemisimpleCategory_of_globalDim_ne_zero k C hdim
  exact finite_simpleClasses_of_isFiniteSemisimpleCategory k C

include k in
/-- **Müger's ribbon theorem (nondegenerate global dimension)**: if `C` is a spherical fusion
category with `globalDim C ≠ 0`, then `Center C` is a ribbon category for its canonical twist. -/
theorem ribbonCategory_of_sphericalCategory_of_globalDim_ne_zero [SphericalCategory C]
    (hdim : globalDim C ≠ 0) :
    letI := balancedOfBraidedPivotal (Center C)
    RibbonCategory (Center C) := by
  have := isFiniteSemisimpleCategory_of_globalDim_ne_zero k C hdim
  exact ribbonCategory_of_sphericalCategory k

end FintypeSimple

section CharZero

variable [CharZero k] [Finite (SimpleClasses C)]

include k in
/-- **The Drinfeld centre of a pivotal fusion category in characteristic zero is finite
semisimple** (Etingof–Nikshych–Ostrik, Müger). -/
theorem isFiniteSemisimpleCategory : IsFiniteSemisimpleCategory (Center C) := by
  let := Fintype.ofFinite (SimpleClasses C)
  exact isFiniteSemisimpleCategory_of_globalDim_ne_zero k C (globalDim_ne_zero k C)

include k in
/-- **The Drinfeld centre of a pivotal fusion category in characteristic zero has finitely many
simple isomorphism classes**, completing the fusion category properties of `Center C` alongside
`Abelian (Center C)`, `instFiniteDimensionalHom`, and `instSimpleUnit`. -/
theorem finite_simpleClasses : Finite (SimpleClasses (Center C)) := by
  let := Fintype.ofFinite (SimpleClasses C)
  exact finite_simpleClasses_of_globalDim_ne_zero k C (globalDim_ne_zero k C)

include k in
/-- **Müger's ribbon theorem in characteristic zero**: the Drinfeld centre of a spherical fusion
category over an algebraically closed field of characteristic zero is a ribbon category for its
canonical twist. -/
theorem ribbonCategory_of_sphericalCategory_of_charZero [SphericalCategory C] :
    letI := balancedOfBraidedPivotal (Center C)
    RibbonCategory (Center C) := by
  let := Fintype.ofFinite (SimpleClasses C)
  exact ribbonCategory_of_sphericalCategory_of_globalDim_ne_zero k C (globalDim_ne_zero k C)

end CharZero

/-! ### Categorical and global dimensions of the Drinfeld centre -/

section GlobalDim

variable {C} [Fintype (SimpleClasses C)]

omit [IsFiniteSemisimpleCategory C] in
include k in
/-- The left pivotal dimension of `inductionObj X` is `leftDim X` composed with `globalDim C`. -/
theorem leftDim_inductionObj (X : C) :
    leftDim (inductionObj X) = leftDim X ≫ globalDim C := by
  suffices End.of (leftDim (inductionObj X)) = End.of (leftDim X ≫ globalDim C) from
    congrArg End.asHom this
  apply (endAlgEquivOfSimple k (𝟙_ C)).injective
  rw [inductionObj, leftDim_biproduct, globalDim_def, End.of_comp, map_mul,
    endAlgEquivOfSimple_sum, endAlgEquivOfSimple_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  dsimp only [inductionSummand]
  rw [leftDim_tensor_eq_comp_of_simple k, leftDim_tensor_eq_comp_of_simple k, End.of_comp,
    End.of_comp, End.of_comp, map_mul, map_mul, map_mul]
  ring

omit [IsFiniteSemisimpleCategory C] in
include k in
/-- The right pivotal dimension of `inductionObj X` is `rightDim X` composed with `globalDim C`. -/
theorem rightDim_inductionObj (X : C) :
    rightDim (inductionObj X) = rightDim X ≫ globalDim C := by
  suffices End.of (rightDim (inductionObj X)) = End.of (rightDim X ≫ globalDim C) from
    congrArg End.asHom this
  apply (endAlgEquivOfSimple k (𝟙_ C)).injective
  rw [inductionObj, rightDim_biproduct, globalDim_eq_sum_leftDim_comp_rightDim, End.of_comp,
    map_mul, endAlgEquivOfSimple_sum, endAlgEquivOfSimple_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  dsimp only [inductionSummand]
  rw [rightDim_tensor_eq_comp_of_simple k, rightDim_tensor_eq_comp_of_simple k, rightDim_rightDual,
    End.of_comp, End.of_comp, End.of_comp, map_mul, map_mul, map_mul]
  ring

private theorem endAlgEquivOfSimple_rightDim_eq_sum (X : C) :
    endAlgEquivOfSimple k (𝟙_ C) (End.of (rightDim X)) =
      ∑ S : SimpleClasses C,
        (simpleMultiplicities X S : k) *
          endAlgEquivOfSimple k (𝟙_ C) (End.of (rightDim S.repr)) := by
  have : EssentiallySmall.{max u v} C := essentiallySmall_of_small_of_locallySmall C
  rw [← SplitK0.rightDimChar_of, SplitK0.of_eq_sum, map_finsuppSum,
    Finsupp.sum_fintype _ _ (by simp)]
  simp [SplitK0.rightDimChar_of, nsmul_eq_mul]

private theorem endAlgEquivOfSimple_leftDim_mul_globalDim
    [IsFiniteSemisimpleCategory (Center C)] [Fintype (SimpleClasses (Center C))]
    (S : SimpleClasses C) :
    endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim S.repr)) *
        endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) =
      ∑ Z : SimpleClasses (Center C),
        (simpleMultiplicities Z.repr.1 S : k) *
          endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim Z.repr.1)) := by
  have : EssentiallySmall.{max u v} (Center C) :=
    essentiallySmall_of_small_of_locallySmall (Center C)
  have hK : SplitK0.leftDimChar k (Center C) (SplitK0.of ((induction k C).obj S.repr)) =
      ∑ Z : SimpleClasses (Center C),
        (simpleMultiplicities Z.repr.1 S : k) *
          endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim Z.repr.1)) := by
    rw [SplitK0.of_eq_sum, map_finsuppSum, Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun Z _ ↦ ?_
    rw [map_nsmul, SplitK0.leftDimChar_of, endAlgEquivOfSimple_tensorUnit_apply, leftDim_f,
      simpleMultiplicities_induction_obj k, nsmul_eq_mul]
  rw [SplitK0.leftDimChar_of, endAlgEquivOfSimple_tensorUnit_apply, leftDim_f, induction_obj,
    inductionCenterObj_fst, leftDim_inductionObj k, End.of_comp, map_mul] at hK
  simpa only [mul_comm (endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)))] using hK

variable (C)

/-- **Global dimension of the Drinfeld centre (scalar form)**: whenever `Center C` is finite
semisimple with finitely many simple classes, its global dimension read in `k` is the square of the
global dimension of `C`. -/
theorem endAlgEquivOfSimple_globalDim_of_isFiniteSemisimpleCategory
    [IsFiniteSemisimpleCategory (Center C)] [Fintype (SimpleClasses (Center C))] :
    endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (globalDim (Center C))) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 := by
  have : EssentiallySmall.{max u v} C := essentiallySmall_of_small_of_locallySmall C
  have : EssentiallySmall.{max u v} (Center C) :=
    essentiallySmall_of_small_of_locallySmall (Center C)
  let e := endAlgEquivOfSimple k (𝟙_ C)
  have hglobalC :
      e (End.of (globalDim C)) =
        ∑ S : SimpleClasses C, e (End.of (leftDim S.repr)) * e (End.of (rightDim S.repr)) := by
    rw [globalDim_eq_sum_leftDimChar_smul k, End.of_smul, End.of_id, map_smul, map_one,
      smul_eq_mul, mul_one]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [← SplitK0.dual_of, SplitK0.leftDimChar_dual, SplitK0.leftDimChar_of,
      SplitK0.rightDimChar_of]
  rw [globalDim_eq_sum_leftDimChar_smul k, End.of_smul, End.of_id, map_smul, map_one, smul_eq_mul,
    mul_one]
  calc (∑ Z : SimpleClasses (Center C),
          SplitK0.leftDimChar k (Center C) (SplitK0.of Z.repr) *
            SplitK0.leftDimChar k (Center C) (SplitK0.of (Z.repr)ᘁ))
      = ∑ Z : SimpleClasses (Center C),
          e (End.of (leftDim Z.repr.1)) *
            (∑ S : SimpleClasses C,
              (simpleMultiplicities Z.repr.1 S : k) * e (End.of (rightDim S.repr))) := by
          refine Finset.sum_congr rfl fun Z _ ↦ ?_
          rw [← SplitK0.dual_of, SplitK0.leftDimChar_dual, SplitK0.leftDimChar_of,
            SplitK0.rightDimChar_of, endAlgEquivOfSimple_tensorUnit_apply,
            endAlgEquivOfSimple_tensorUnit_apply, leftDim_f, rightDim_f,
            endAlgEquivOfSimple_rightDim_eq_sum k Z.repr.1]
    _ = ∑ S : SimpleClasses C,
          (∑ Z : SimpleClasses (Center C),
            (simpleMultiplicities Z.repr.1 S : k) * e (End.of (leftDim Z.repr.1))) *
            e (End.of (rightDim S.repr)) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun Z _ ↦ ?_
          ring
    _ = ∑ S : SimpleClasses C,
          (e (End.of (leftDim S.repr)) * e (End.of (globalDim C))) *
            e (End.of (rightDim S.repr)) := by
          refine Finset.sum_congr rfl fun S _ ↦ ?_
          rw [endAlgEquivOfSimple_leftDim_mul_globalDim k S]
    _ = (∑ S : SimpleClasses C, e (End.of (leftDim S.repr)) * e (End.of (rightDim S.repr))) *
          e (End.of (globalDim C)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun S _ ↦ ?_
          ring
    _ = e (End.of (globalDim C)) ^ 2 := by
          rw [← hglobalC, sq]

/-- **Global dimension of the Drinfeld centre (scalar multiplication form)**: whenever `Center C`
is finite semisimple with finitely many simple classes, `globalDim (Center C)` acts on
`𝟙_ (Center C)` as scalar multiplication by `(dim C)²`. -/
theorem globalDim_eq_smul_id_of_isFiniteSemisimpleCategory
    [IsFiniteSemisimpleCategory (Center C)] [Fintype (SimpleClasses (Center C))] :
    globalDim (Center C) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 • 𝟙 (𝟙_ (Center C)) :=
  (endAlgEquivOfSimple_apply_eq_iff (End.of (globalDim (Center C))) _).mp
    (endAlgEquivOfSimple_globalDim_of_isFiniteSemisimpleCategory k C)

include k in
/-- **Global dimension of the Drinfeld centre (morphism form)**: whenever `Center C` is finite
semisimple with finitely many simple classes,
`(globalDim (Center C)).f = globalDim C ≫ globalDim C`. -/
theorem globalDim_f_of_isFiniteSemisimpleCategory
    [IsFiniteSemisimpleCategory (Center C)] [Fintype (SimpleClasses (Center C))] :
    (globalDim (Center C)).f = globalDim C ≫ globalDim C := by
  have h := endAlgEquivOfSimple_globalDim_of_isFiniteSemisimpleCategory k C
  rw [endAlgEquivOfSimple_tensorUnit_apply, sq, ← map_mul, ← End.of_comp] at h
  exact congrArg End.asHom ((endAlgEquivOfSimple k (𝟙_ C)).injective h)

/-- If `globalDim C ≠ 0`, the global dimension of `Center C` read as a scalar in `k` equals the
square of the global dimension of `C`. -/
theorem endAlgEquivOfSimple_globalDim_of_globalDim_ne_zero (hdim : globalDim C ≠ 0)
    [Fintype (SimpleClasses (Center C))] :
    endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (globalDim (Center C))) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 := by
  have := isFiniteSemisimpleCategory_of_globalDim_ne_zero k C hdim
  exact endAlgEquivOfSimple_globalDim_of_isFiniteSemisimpleCategory k C

/-- If `globalDim C ≠ 0`, `globalDim (Center C)` equals `(dim C)² • 𝟙 (𝟙_ (Center C))`. -/
theorem globalDim_eq_smul_id_of_globalDim_ne_zero (hdim : globalDim C ≠ 0)
    [Fintype (SimpleClasses (Center C))] :
    globalDim (Center C) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 • 𝟙 (𝟙_ (Center C)) := by
  have := isFiniteSemisimpleCategory_of_globalDim_ne_zero k C hdim
  exact globalDim_eq_smul_id_of_isFiniteSemisimpleCategory k C

include k in
/-- If `globalDim C ≠ 0`, the underlying endomorphism of `globalDim (Center C)` in `C` is
`globalDim C ≫ globalDim C`. -/
theorem globalDim_f_of_globalDim_ne_zero (hdim : globalDim C ≠ 0)
    [Fintype (SimpleClasses (Center C))] :
    (globalDim (Center C)).f = globalDim C ≫ globalDim C := by
  have := isFiniteSemisimpleCategory_of_globalDim_ne_zero k C hdim
  exact globalDim_f_of_isFiniteSemisimpleCategory k C

/-- **Global dimension of the Drinfeld centre in characteristic zero (scalar form)**:
`dim(Center C) = dim(C)²`. -/
theorem endAlgEquivOfSimple_globalDim [CharZero k] [Fintype (SimpleClasses (Center C))] :
    endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (globalDim (Center C))) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 :=
  endAlgEquivOfSimple_globalDim_of_globalDim_ne_zero k C (globalDim_ne_zero k C)

/-- **Global dimension of the Drinfeld centre in characteristic zero (scalar multiplication form)**:
`globalDim (Center C) = dim(C)² • 𝟙 (𝟙_ (Center C))`. -/
theorem globalDim_eq_smul_id [CharZero k] [Fintype (SimpleClasses (Center C))] :
    globalDim (Center C) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 • 𝟙 (𝟙_ (Center C)) :=
  globalDim_eq_smul_id_of_globalDim_ne_zero k C (globalDim_ne_zero k C)

include k in
/-- **Global dimension of the Drinfeld centre in characteristic zero (morphism form)**:
`(globalDim (Center C)).f = globalDim C ≫ globalDim C`. -/
theorem globalDim_f [CharZero k] [Fintype (SimpleClasses (Center C))] :
    (globalDim (Center C)).f = globalDim C ≫ globalDim C :=
  globalDim_f_of_globalDim_ne_zero k C (globalDim_ne_zero k C)

end GlobalDim

end Pivotal

end CategoryTheory.Center
