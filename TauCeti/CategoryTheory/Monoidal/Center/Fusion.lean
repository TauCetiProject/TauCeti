/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.Adjunction
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.LeftAdjunction
public import TauCeti.CategoryTheory.Monoidal.Center.Ribbon
public import TauCeti.CategoryTheory.Monoidal.Center.Simple
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Biproduct
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Character
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Semisimple
public import TauCeti.CategoryTheory.Semisimple.Finite
public import TauCeti.CategoryTheory.Semisimple.Finrank
public import TauCeti.CategoryTheory.Semisimple.Split

/-!
# The Drinfeld centre of a pivotal fusion category is a fusion category

This file establishes the fusion structure, ribbon structure, and global dimension of the Drinfeld
centre `Center C` of a pivotal fusion category `C` over an algebraically closed field `k`
(Müger; Etingof–Nikshych–Ostrik), along with the pivot-free `averagingScalar` criterion:

* **Averaging identity**: the composite
  `(forgetInductionAdjunction k C).unit.app Z ≫ (inductionForgetAdjunction k C).counit.app Z` of
  the unit of the right adjunction `forget C ⊣ induction k C` with the counit of the left
  adjunction `induction k C ⊣ forget C` acts on every `Z : Center C` as scalar multiplication by
  `averagingScalar k C` (which equals `globalDim C`, read in `k` via `endAlgEquivOfSimple k (𝟙_ C)`,
  when `C` is pivotal), making each component of the unit of `forgetInductionAdjunction` a split
  monomorphism whenever `averagingScalar k C ≠ 0` (in particular whenever `globalDim C ≠ 0` for
  pivotal `C`).
* **Fusion and ribbon structure on `Center C`**: when `averagingScalar k C ≠ 0` (and, for pivotal
  `C`, when `globalDim C ≠ 0`, hence unconditionally when `CharZero k`), `Center C` is finite
  semisimple with finitely many simple isomorphism classes (supplementing the existing
  `Abelian (Center C)`, `instFiniteDimensionalHom`, and `instSimpleUnit` instances). If `C` is
  moreover spherical, `Center C` is a ribbon category for its canonical twist.
* **Multiplicities and dimensions**: when `C` has finitely many simple classes and `Center C` is
  finite semisimple, `Center C` also has finitely many simple classes and Frobenius reciprocity
  identifies the multiplicity of a simple class `Z` of `Center C` in `(induction k C).obj S.repr`
  with the multiplicity of `S` in `Z.repr.1` (without assuming a pivotal structure or simple tensor
  unit). For pivotal `C`, the left and right dimensions of `inductionObj X` multiply those of `X`
  by `globalDim C`, and whenever `Center C` is finite semisimple with finitely many simple classes
  (in particular under `globalDim C ≠ 0` or `CharZero k`), `globalDim (Center C) = (globalDim C)²`.

## Main declarations

* `CategoryTheory.Center.endAlgEquivOfSimple_tensorUnit_apply`: reading an endomorphism of
  `𝟙_ (Center C)` in `k` agrees with reading its underlying endomorphism of `𝟙_ C`;
* `CategoryTheory.Center.finite_simpleClasses_of_isFiniteSemisimpleCategory`: if `C` has finitely
  many simple isomorphism classes and `Center C` is finite semisimple, then `Center C` has finitely
  many simple isomorphism classes;
* `CategoryTheory.Center.simpleMultiplicities_induction_obj`: Frobenius reciprocity for simple
  multiplicities between `C` and `Center C`;
* `CategoryTheory.Center.averagingScalar` and the `averagingScalar` identity
  (`forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit_eq_averagingScalar_smul`
  and `forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit`):
  the pivot-free averaging scalar and averaging identity, and its pivotal form
  `η_Z ≫ ε'_Z = dim(C) • 𝟙 Z`;
* `CategoryTheory.Center.isSplitMono_forgetInductionAdjunction_unit_of_averagingScalar_ne_zero`,
  `CategoryTheory.Center.isFiniteSemisimpleCategory_of_averagingScalar_ne_zero`, and
  `CategoryTheory.Center.finite_simpleClasses_of_averagingScalar_ne_zero`: pivot-free splitting,
  semisimplicity, and finiteness of `Center C` whenever `averagingScalar k C ≠ 0`;
* `CategoryTheory.Center.isFiniteSemisimpleCategory_of_globalDim_ne_zero` and
  `CategoryTheory.Center.finite_simpleClasses_of_globalDim_ne_zero`: for pivotal `C`, `Center C`
  is a fusion category whenever `globalDim C ≠ 0`;
* `CategoryTheory.Center.isFiniteSemisimpleCategory` and
  `CategoryTheory.Center.finite_simpleClasses`: for pivotal `C`, `Center C` is a fusion category in
  characteristic zero;
* `CategoryTheory.Center.ribbonCategory_of_sphericalCategory_of_globalDim_ne_zero` and
  `CategoryTheory.Center.ribbonCategory_of_sphericalCategory_of_charZero`: Müger's ribbon theorem
  on `Center C` under `globalDim C ≠ 0` and unconditionally in characteristic zero;
* `CategoryTheory.Center.leftDim_inductionObj`, `CategoryTheory.Center.rightDim_inductionObj`,
  `CategoryTheory.Center.endAlgEquivOfSimple_globalDim_of_isFiniteSemisimpleCategory`,
  `CategoryTheory.Center.globalDim_eq_smul_id_of_isFiniteSemisimpleCategory`,
  `CategoryTheory.Center.globalDim_f_of_isFiniteSemisimpleCategory`,
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

end UnitScalar

section SemisimpleCenter

variable (k : Type w) [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

include k in
/-- If `C` has finitely many isomorphism classes of simple objects and `Center C` is finite
semisimple, then `Center C` also has finitely many isomorphism classes of simple objects. -/
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

section Averaging

variable (k : Type w) [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
  [Fintype (SimpleClasses C)]

/-- The pivot-free averaging scalar in `k`, obtained by reading the sum of the normalized
pairing closures
`η_ S.repr S.reprᘁ ≫ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleSwapExactPairing S.repr)`
in `k` via `endAlgEquivOfSimple k (𝟙_ C)`. -/
noncomputable def averagingScalar : k :=
  endAlgEquivOfSimple k (𝟙_ C)
    (End.of (∑ S : SimpleClasses C,
      η_ S.repr S.reprᘁ ≫
        @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleSwapExactPairing S.repr)))

omit [MonoidalPreadditive C] [MonoidalLinear k C] in
/-- The defining formula for `averagingScalar k C`. -/
theorem averagingScalar_def :
    averagingScalar k C =
      endAlgEquivOfSimple k (𝟙_ C)
        (End.of (∑ S : SimpleClasses C,
          η_ S.repr S.reprᘁ ≫
            @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleSwapExactPairing S.repr))) := by
  rfl

/-- Underlying morphism form of the pivot-free averaging identity on `Center C`: composing the
unit of `forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` multiplies
`𝟙 Z.1` by `averagingScalar k C`. -/
@[reassoc]
theorem
    forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit_f_eq_averagingScalar_smul
    (Z : Center C) :
    ((forgetInductionAdjunction k C).unit.app Z).f ≫
        ((inductionForgetAdjunction k C).counit.app Z).f =
      averagingScalar k C • 𝟙 Z.1 := by
  have hterm (S : SimpleClasses C) :
      (((forgetInductionAdjunction k C).unit.app Z).f ≫ biproduct.π (inductionSummand Z.1) S) ≫
        (biproduct.ι (inductionSummand Z.1) S ≫
          ((inductionForgetAdjunction k C).counit.app Z).f) =
      (ρ_ Z.1).inv ≫
        Z.1 ◁ (η_ S.repr S.reprᘁ ≫
          @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleSwapExactPairing S.repr)) ≫
        (ρ_ Z.1).hom := by
    rw [forgetInductionAdjunction_unit_app_f_comp_π, ι_comp_inductionForgetAdjunction_counit_app_f]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp,
      Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc]
  let u : Z.1 ⟶ inductionObj Z.1 := ((forgetInductionAdjunction k C).unit.app Z).f
  let v : inductionObj Z.1 ⟶ Z.1 := ((inductionForgetAdjunction k C).counit.app Z).f
  -- `unit.app Z` and `counit.app Z` have dependent endpoints `(𝟭 (Center C)).obj Z` and
  -- `(forget C ⋙ induction k C).obj Z` in the semireducible `Center C`, so `dsimp` and `rw`
  -- cannot reduce the implicit middle object `((forget C ⋙ induction k C).obj Z).1` of `_ ≫ _` to
  -- `inductionObj Z.1`; convert through the typed aliases `u` and `v` so `Category.id_comp` and
  -- `biproduct.total` apply.
  change u ≫ v = _
  rw [← Category.id_comp v, ← biproduct.total]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  have hsum :
      (∑ S : SimpleClasses C,
        u ≫ biproduct.π (inductionSummand Z.1) S ≫
          biproduct.ι (inductionSummand Z.1) S ≫ v) =
      ∑ S : SimpleClasses C,
        (ρ_ Z.1).inv ≫
          Z.1 ◁ (η_ S.repr S.reprᘁ ≫
            @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleSwapExactPairing S.repr)) ≫
          (ρ_ Z.1).hom := by
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [← Category.assoc u]
    exact hterm S
  have hs :
      (∑ S : SimpleClasses C,
        η_ S.repr S.reprᘁ ≫
          @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleSwapExactPairing S.repr)) =
      averagingScalar k C • 𝟙 (𝟙_ C) := by
    rw [averagingScalar_def]
    exact (endAlgEquivOfSimple_smul_id (k := k) _).symm
  rw [hsum, ← Preadditive.comp_sum, ← Preadditive.sum_comp, ← whiskerLeft_sum, hs,
    MonoidalLinear.whiskerLeft_smul, whiskerLeft_id, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Iso.inv_hom_id]

/-- **Pivot-free averaging identity for the Drinfeld centre**: composing the unit of
`forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` at `Z : Center C`
acts as scalar multiplication by `averagingScalar k C`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit_eq_averagingScalar_smul
    (Z : Center C) :
    (forgetInductionAdjunction k C).unit.app Z ≫
        (inductionForgetAdjunction k C).counit.app Z =
      averagingScalar k C • 𝟙 Z :=
  Hom.ext
    (forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit_f_eq_averagingScalar_smul
      k C Z)

/-- When `averagingScalar k C ≠ 0`, each component of the unit of `forgetInductionAdjunction` is
a split monomorphism in `Center C`, retracted by
`(averagingScalar k C)⁻¹ • (inductionForgetAdjunction k C).counit`. -/
theorem isSplitMono_forgetInductionAdjunction_unit_of_averagingScalar_ne_zero
    (h : averagingScalar k C ≠ 0) (Z : Center C) :
    IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) := by
  refine IsSplitMono.mk'
    ⟨(averagingScalar k C)⁻¹ • (inductionForgetAdjunction k C).counit.app Z, ?_⟩
  rw [Linear.comp_smul,
    forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit_eq_averagingScalar_smul,
    smul_smul, inv_mul_cancel₀ h, one_smul]
  simp only [Functor.id_obj]

/-- **Semisimplicity of the Drinfeld centre (pivot-free criterion)**: if `averagingScalar k C ≠ 0`,
then `Center C` is a split finite semisimple category. -/
theorem isFiniteSemisimpleCategory_of_averagingScalar_ne_zero
    (h : averagingScalar k C ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) := by
  have := isSplitMono_forgetInductionAdjunction_unit_of_averagingScalar_ne_zero k C h
  exact IsFiniteSemisimpleCategory.of_natTrans (forget C) (induction k C)
    (forgetInductionAdjunction k C).unit

/-- **Finiteness of simple classes in the Drinfeld centre (pivot-free criterion)**: if
`averagingScalar k C ≠ 0`, then `Center C` has finitely many simple isomorphism classes. -/
theorem finite_simpleClasses_of_averagingScalar_ne_zero
    (h : averagingScalar k C ≠ 0) :
    Finite (SimpleClasses (Center C)) := by
  have := isFiniteSemisimpleCategory_of_averagingScalar_ne_zero k C h
  exact finite_simpleClasses_of_isFiniteSemisimpleCategory k C

end Averaging

section Pivotal

variable (k : Type w) [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C] [PivotalCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

section FintypeSimple

variable [Fintype (SimpleClasses C)]

/-- In a pivotal category, the pivot-free averaging scalar `averagingScalar k C` agrees with
`globalDim C` read in `k`. -/
theorem averagingScalar_eq_endAlgEquivOfSimple_globalDim :
    averagingScalar k C = endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) := by
  rw [averagingScalar_def]
  simp_rw [coevaluation_comp_simpleSwapExactPairing_evaluation k]
  rw [← globalDim_eq_sum_leftDim_comp_rightDim]

/-- **Averaging identity for the Drinfeld centre**: composing the unit of
`forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` at `Z : Center C`
acts as scalar multiplication by `globalDim C`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit (Z : Center C) :
    (forgetInductionAdjunction k C).unit.app Z ≫
        (inductionForgetAdjunction k C).counit.app Z =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) • 𝟙 Z := by
  rw [forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit_eq_averagingScalar_smul,
    averagingScalar_eq_endAlgEquivOfSimple_globalDim]

/-- Underlying morphism form of the averaging identity on `Center C`: composing the unit of
`forgetInductionAdjunction` with the counit of `inductionForgetAdjunction` multiplies `𝟙 Z.1` by
`globalDim C`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit_f (Z : Center C) :
    ((forgetInductionAdjunction k C).unit.app Z).f ≫
        ((inductionForgetAdjunction k C).counit.app Z).f =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) • 𝟙 Z.1 := by
  have h := congrArg (fun x ↦ x.f)
    (forgetInductionAdjunction_unit_comp_inductionForgetAdjunction_counit k C Z)
  rw [comp_f, smul_f, id_f] at h
  exact h

private theorem averagingScalar_ne_zero_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    averagingScalar k C ≠ 0 := by
  rw [averagingScalar_eq_endAlgEquivOfSimple_globalDim]
  intro h
  exact hdim (by simpa using (endAlgEquivOfSimple_apply_eq_iff (End.of (globalDim C)) 0).mp h)

/-- When `globalDim C ≠ 0`, each component of the unit of `forgetInductionAdjunction` is a split
monomorphism in `Center C`, retracted by `(dim C)⁻¹ • (inductionForgetAdjunction k C).counit`. -/
theorem isSplitMono_forgetInductionAdjunction_unit_of_globalDim_ne_zero
    (hdim : globalDim C ≠ 0) (Z : Center C) :
    IsSplitMono ((forgetInductionAdjunction k C).unit.app Z) :=
  isSplitMono_forgetInductionAdjunction_unit_of_averagingScalar_ne_zero k C
    (averagingScalar_ne_zero_of_globalDim_ne_zero k C hdim) Z

include k in
/-- **Semisimplicity of the Drinfeld centre (nondegenerate global dimension)**: if
`globalDim C ≠ 0`, then `Center C` is a split finite semisimple category. -/
theorem isFiniteSemisimpleCategory_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    IsFiniteSemisimpleCategory (Center C) :=
  isFiniteSemisimpleCategory_of_averagingScalar_ne_zero k C
    (averagingScalar_ne_zero_of_globalDim_ne_zero k C hdim)

include k in
/-- **Finiteness of simple classes in the Drinfeld centre (nondegenerate global dimension)**: if
`globalDim C ≠ 0`, then `Center C` has finitely many simple isomorphism classes. -/
theorem finite_simpleClasses_of_globalDim_ne_zero (hdim : globalDim C ≠ 0) :
    Finite (SimpleClasses (Center C)) :=
  finite_simpleClasses_of_averagingScalar_ne_zero k C
    (averagingScalar_ne_zero_of_globalDim_ne_zero k C hdim)

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

omit [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
include k in
/-- The left pivotal dimension of `inductionObj X` is `leftDim X` composed with `globalDim C`. -/
theorem leftDim_inductionObj [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)] (X : C) :
    leftDim (inductionObj X) = leftDim X ≫ globalDim C := by
  rw [inductionObj, leftDim_biproduct, globalDim_def, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  dsimp only [inductionSummand]
  rw [leftDim_tensor_eq_comp_of_simple k, leftDim_tensor_eq_comp_of_simple k,
    ← Category.assoc, scalar_comm (leftDim S.repr), Category.assoc]

omit [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
include k in
/-- The right pivotal dimension of `inductionObj X` is `rightDim X` composed with `globalDim C`. -/
theorem rightDim_inductionObj [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)] (X : C) :
    rightDim (inductionObj X) = rightDim X ≫ globalDim C := by
  rw [inductionObj, rightDim_biproduct, globalDim_eq_sum_leftDim_comp_rightDim,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  dsimp only [inductionSummand]
  rw [rightDim_tensor_eq_comp_of_simple k, rightDim_tensor_eq_comp_of_simple k, rightDim_rightDual,
    scalar_comm (rightDim S.repr), Category.assoc]

private theorem endAlgEquivOfSimple_leftDim_mul_globalDim
    [IsFiniteSemisimpleCategory (Center C)] [Fintype (SimpleClasses (Center C))]
    (S : SimpleClasses C) :
    endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim S.repr)) *
        endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) =
      ∑ Z : SimpleClasses (Center C),
        (simpleMultiplicities Z.repr.1 S : k) *
          endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim Z.repr.1)) := by
  have h := endAlgEquivOfSimple_leftDim_eq_sum k ((induction k C).obj S.repr)
  simp only [simpleMultiplicities_induction_obj k] at h
  rw [endAlgEquivOfSimple_tensorUnit_apply, leftDim_f, induction_obj, inductionCenterObj_fst,
    leftDim_inductionObj k, End.of_comp, map_mul, mul_comm] at h
  refine h.trans (Finset.sum_congr rfl fun Z _ ↦ ?_)
  rw [endAlgEquivOfSimple_tensorUnit_apply, leftDim_f]

variable (C)

/-- **Global dimension of the Drinfeld centre (scalar form)**: whenever `Center C` is finite
semisimple with finitely many simple classes, its global dimension read in `k` is the square of the
global dimension of `C`. -/
theorem endAlgEquivOfSimple_globalDim_of_isFiniteSemisimpleCategory
    [IsFiniteSemisimpleCategory (Center C)] [Fintype (SimpleClasses (Center C))] :
    endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (globalDim (Center C))) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 := by
  let e := endAlgEquivOfSimple k (𝟙_ C)
  rw [TauCeti.endAlgEquivOfSimple_globalDim_eq_sum k (Center C)]
  calc (∑ Z : SimpleClasses (Center C),
          endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (leftDim Z.repr)) *
            endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (rightDim Z.repr)))
      = ∑ Z : SimpleClasses (Center C),
          e (End.of (leftDim Z.repr.1)) *
            (∑ S : SimpleClasses C,
              (simpleMultiplicities Z.repr.1 S : k) * e (End.of (rightDim S.repr))) := by
          refine Finset.sum_congr rfl fun Z _ ↦ ?_
          rw [endAlgEquivOfSimple_tensorUnit_apply, endAlgEquivOfSimple_tensorUnit_apply,
            leftDim_f, rightDim_f, endAlgEquivOfSimple_rightDim_eq_sum k Z.repr.1]
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
          rw [← TauCeti.endAlgEquivOfSimple_globalDim_eq_sum k C, sq]

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

/-- **Global dimension of the Drinfeld centre in characteristic zero (scalar form)**:
`dim(Center C) = dim(C)²`. -/
theorem endAlgEquivOfSimple_globalDim [CharZero k] [Fintype (SimpleClasses (Center C))] :
    endAlgEquivOfSimple k (𝟙_ (Center C)) (End.of (globalDim (Center C))) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 := by
  have := isFiniteSemisimpleCategory k C
  exact endAlgEquivOfSimple_globalDim_of_isFiniteSemisimpleCategory k C

/-- **Global dimension of the Drinfeld centre in characteristic zero (scalar multiplication
form)**: `globalDim (Center C) = (dim C)² • 𝟙 (𝟙_ (Center C))`. -/
theorem globalDim_eq_smul_id [CharZero k] [Fintype (SimpleClasses (Center C))] :
    globalDim (Center C) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (globalDim C)) ^ 2 • 𝟙 (𝟙_ (Center C)) := by
  have := isFiniteSemisimpleCategory k C
  exact globalDim_eq_smul_id_of_isFiniteSemisimpleCategory k C

include k in
/-- **Global dimension of the Drinfeld centre in characteristic zero (morphism form)**:
`(globalDim (Center C)).f = globalDim C ≫ globalDim C`. -/
theorem globalDim_f [CharZero k] [Fintype (SimpleClasses (Center C))] :
    (globalDim (Center C)).f = globalDim C ≫ globalDim C := by
  have := isFiniteSemisimpleCategory k C
  exact globalDim_f_of_isFiniteSemisimpleCategory k C

end GlobalDim

end Pivotal

end CategoryTheory.Center
