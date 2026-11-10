/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GradedObject.MonObj

/-!
# Veronese subalgebras of graded monoid objects

Let `A = ⨁ₙ Aₙ` be a monoid object in `ℕ`-graded objects of a monoidal category `C`, such as a
graded algebra of modules on a scheme. For `d : ℕ`, its *`d`-th Veronese subalgebra*
`A^{(d)} = ⨁ₖ A_{dk}` is the graded monoid object whose degree-`k` component is `A_{dk}`, with the
unit of `A` and the homogeneous multiplications `A_{di} ⊗ A_{dj} ⟶ A_{d(i+j)}` of `A`. Its
degree-zero part is that of `A`. When `A` is commutative, so is `A^{(d)}`.

This is the sheaf-level Veronese subalgebra behind the comparison of the relative `Proj` of
`A^{(d)}` with that of `A` (Stacks Project, Lemma 0B5J).

## Main definitions

* `CategoryTheory.Mon.veronese A d`: the `d`-th Veronese subalgebra of a graded monoid object;
* `CategoryTheory.CommMon.veronese A d`: the same for a commutative graded monoid object.

## Main results

* `CategoryTheory.Mon.veronese_mul` and `CategoryTheory.Mon.veronese_one`: the homogeneous
  multiplications and unit of `A^{(d)}` are those of `A`, up to the identifications of degrees
  (`CategoryTheory.Mon.veroneseMul_eq` and `CategoryTheory.Mon.veroneseOne_eq`).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Mon

section Veronese

variable {C : Type*} [Category* C] [MonoidalCategory C]
  [∀ (X₁ X₂ : GradedObject ℕ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℕ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℕ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℕ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  (A : Mon (GradedObject ℕ C)) (d : ℕ)

/-- The unit of the `d`-th Veronese subalgebra: the unit of `A`, landing in `A_{d·0} = A₀`. -/
def veroneseOne : 𝟙_ C ⟶ A.X (d * 0) :=
  A.one ≫ eqToHom (congrArg A.X (mul_zero d).symm)

/-- The unit of the `d`-th Veronese subalgebra is the unit of `A`, transported along `0 = d · 0`. -/
theorem veroneseOne_eq : A.veroneseOne d = A.one ≫ eqToHom (congrArg A.X (mul_zero d).symm) :=
  (rfl)

/-- The homogeneous multiplications of the `d`-th Veronese subalgebra: the multiplication
`A_{di} ⊗ A_{dj} ⟶ A_{di + dj} = A_{d(i+j)}` of `A`. -/
def veroneseMul (i j : ℕ) : A.X (d * i) ⊗ A.X (d * j) ⟶ A.X (d * (i + j)) :=
  A.mul (d * i) (d * j) ≫ eqToHom (congrArg A.X (mul_add d i j).symm)

/-- The homogeneous multiplication `A_{di} ⊗ A_{dj} ⟶ A_{d(i+j)}` of the `d`-th Veronese
subalgebra is that of `A`, transported along `d i + d j = d (i + j)`. -/
theorem veroneseMul_eq (i j : ℕ) :
    A.veroneseMul d i j = A.mul (d * i) (d * j) ≫ eqToHom (congrArg A.X (mul_add d i j).symm) :=
  (rfl)

/-- The unit of the `d`-th Veronese subalgebra is a left identity. -/
theorem veroneseOne_whiskerRight_veroneseMul (n : ℕ) :
    (A.veroneseOne d ▷ A.X (d * n)) ≫ A.veroneseMul d 0 n =
      (λ_ (A.X (d * n))).hom ≫ eqToHom (congrArg (fun k ↦ A.X (d * k)) (zero_add n).symm) := by
  simp [veroneseOne_eq, veroneseMul_eq]

/-- The unit of the `d`-th Veronese subalgebra is a right identity. -/
theorem whiskerLeft_veroneseOne_veroneseMul (n : ℕ) :
    (A.X (d * n) ◁ A.veroneseOne d) ≫ A.veroneseMul d n 0 =
      (ρ_ (A.X (d * n))).hom ≫ eqToHom (congrArg (fun k ↦ A.X (d * k)) (add_zero n).symm) := by
  simp [veroneseOne_eq, veroneseMul_eq]

/-- The homogeneous multiplications of the `d`-th Veronese subalgebra are associative. -/
theorem veroneseMul_assoc (i j k : ℕ) :
    (A.veroneseMul d i j ▷ A.X (d * k)) ≫ A.veroneseMul d (i + j) k =
      (α_ _ _ _).hom ≫ (A.X (d * i) ◁ A.veroneseMul d j k) ≫ A.veroneseMul d i (j + k) ≫
        eqToHom (congrArg (fun m ↦ A.X (d * m)) (add_assoc i j k).symm) := by
  simp only [veroneseMul_eq, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [eqToHom_whiskerRight_mul_assoc _ (mul_add d i j).symm,
    whiskerLeft_eqToHom_mul_assoc _ _ (mul_add d j k).symm, mul_assoc_assoc]
  simp

/-- The `d`-th Veronese subalgebra `A^{(d)} = ⨁ₖ A_{dk}` of a graded monoid object `A`, with the
unit and homogeneous multiplications of `A`. -/
@[expose] def veronese : Mon (GradedObject ℕ C) :=
  letI := GradedObject.monObjOfHomogeneous (fun k ↦ A.X (d * k)) (A.veroneseOne d)
    (A.veroneseMul d) (A.veroneseOne_whiskerRight_veroneseMul d)
    (A.whiskerLeft_veroneseOne_veroneseMul d) (A.veroneseMul_assoc d)
  Mon.mk fun k ↦ A.X (d * k)

/-- The degree-`k` component of the `d`-th Veronese subalgebra is the degree-`d k` component. -/
@[simp]
theorem veronese_X (k : ℕ) : (A.veronese d).X k = A.X (d * k) :=
  rfl

/-- The homogeneous multiplications of the `d`-th Veronese subalgebra are those of `A`. -/
@[simp]
theorem veronese_mul (i j : ℕ) : (A.veronese d).mul i j = A.veroneseMul d i j :=
  Mon.mul_eq _ _ _ |>.trans
    ((GradedObject.Monoidal.ιTensorObj_mulOfHomogeneous _ (A.veroneseMul d) i j (i + j)
      rfl).trans (Category.comp_id _))

/-- The unit of the `d`-th Veronese subalgebra is that of `A`. -/
@[simp]
theorem veronese_one : (A.veronese d).one = A.veroneseOne d :=
  Mon.one_eq _ |>.trans <| (congrArg (_ ≫ ·)
    (GradedObject.Monoidal.oneOfDegreeZero_zero (fun k ↦ A.X (d * k)) (A.veroneseOne d))).trans
      (Iso.inv_hom_id_assoc _ _)

end Veronese

end CategoryTheory.Mon

namespace CategoryTheory.CommMon

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
  [∀ (X₁ X₂ : GradedObject ℕ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℕ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℕ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℕ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  (A : CommMon (GradedObject ℕ C)) (d : ℕ)

/-- The homogeneous multiplications of the `d`-th Veronese subalgebra of a commutative graded
monoid object are commutative. -/
theorem veroneseMul_comm (i j : ℕ) :
    (β_ (A.toMon.X (d * i)) (A.toMon.X (d * j))).hom ≫ A.toMon.veroneseMul d j i =
      A.toMon.veroneseMul d i j ≫
        eqToHom (congrArg (fun k ↦ A.toMon.X (d * k)) (add_comm i j)) := by
  rw [Mon.veroneseMul_eq, Mon.veroneseMul_eq, mul_comm_assoc]
  simp

/-- The `d`-th Veronese subalgebra `A^{(d)} = ⨁ₖ A_{dk}` of a commutative graded monoid object
`A`. -/
@[expose] def veronese : CommMon (GradedObject ℕ C) :=
  letI := GradedObject.monObjOfHomogeneous (fun k ↦ A.toMon.X (d * k)) (A.toMon.veroneseOne d)
    (A.toMon.veroneseMul d) (A.toMon.veroneseOne_whiskerRight_veroneseMul d)
    (A.toMon.whiskerLeft_veroneseOne_veroneseMul d) (A.toMon.veroneseMul_assoc d)
  haveI := GradedObject.isCommMonObj_monObjOfHomogeneous (fun k ↦ A.toMon.X (d * k))
    (A.toMon.veroneseOne d) (A.toMon.veroneseMul d)
    (A.toMon.veroneseOne_whiskerRight_veroneseMul d)
    (A.toMon.whiskerLeft_veroneseOne_veroneseMul d) (A.toMon.veroneseMul_assoc d)
    (veroneseMul_comm A d)
  CommMon.mk fun k ↦ A.toMon.X (d * k)

/-- The underlying graded monoid object of the `d`-th Veronese subalgebra of a commutative graded
monoid object is the `d`-th Veronese subalgebra of its underlying graded monoid object. -/
@[simp]
theorem veronese_toMon : (A.veronese d).toMon = A.toMon.veronese d :=
  rfl

/-- The degree-`k` component of the `d`-th Veronese subalgebra is the degree-`d k` component. -/
@[simp]
theorem veronese_X (k : ℕ) : (A.veronese d).X k = A.X (d * k) :=
  rfl

end CategoryTheory.CommMon
