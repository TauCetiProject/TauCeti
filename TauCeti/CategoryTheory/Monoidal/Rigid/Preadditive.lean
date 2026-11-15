/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Duals in a monoidal preadditive category

In a monoidal preadditive category the right and left adjoint mates `f ↦ fᘁ` and `f ↦ ᘁf` are
additive, and `k`-linear in a monoidal `k`-linear category, because they are built from whiskering
and composition. Taking right or left adjoint mates therefore defines `k`-linear equivalences
`(X ⟶ Y) ≃ₗ[k] (Yᘁ ⟶ Xᘁ)` and `(X ⟶ Y) ≃ₗ[k] (ᘁY ⟶ ᘁX)` mutually inverse to each other
(`TauCeti.rightAdjointMateLinearEquiv`, `TauCeti.leftAdjointMateLinearEquiv`).

In a monoidal `k`-linear category the Frobenius reciprocity bijections `tensorLeftHomEquiv` and
`tensorRightHomEquiv` are `k`-linear, so they compare dimensions of morphism spaces, for instance
of the multiplicity spaces of a fusion category. Specializing to `tensorPow V 2` identifies
`𝟙_ C ⟶ tensorPow V 2` `k`-linearly with `Vᘁ ⟶ V` (`TauCeti.homTensorPowTwoLinearEquiv`).

## Main declarations

* `TauCeti.rightAdjointMate_zero`, `TauCeti.rightAdjointMate_add`, `TauCeti.rightAdjointMate_sum`,
  `TauCeti.rightAdjointMate_neg`, `TauCeti.rightAdjointMate_sub` and
  `TauCeti.rightAdjointMate_smul`, together with their left-mate counterparts: the right and left
  adjoint mates are additive and `k`-linear;
* `TauCeti.rightAdjointMateLinearEquiv` and `TauCeti.leftAdjointMateLinearEquiv`: taking right and
  left adjoint mates as `k`-linear equivalences;
* `TauCeti.tensorLeftHomLinearEquiv` and `TauCeti.tensorRightHomLinearEquiv`: Frobenius
  reciprocity as `k`-linear equivalences, and `TauCeti.homTensorPowTwoLinearEquiv` (with
  `TauCeti.homTensorPowTwoLinearEquiv_apply` and `TauCeti.homTensorPowTwoLinearEquiv_symm_apply`):
  its specialization `(𝟙_ C ⟶ tensorPow V 2) ≃ₗ[k] (Vᘁ ⟶ V)`.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

section RightMate

variable {X Y : C} [HasRightDual X] [HasRightDual Y]

/-- The right adjoint mate of the zero morphism is zero. -/
@[simp]
theorem rightAdjointMate_zero : (0 : X ⟶ Y)ᘁ = 0 := by
  simp [rightAdjointMate]

/-- The right adjoint mate is additive. -/
@[simp]
theorem rightAdjointMate_add (f g : X ⟶ Y) : (f + g)ᘁ = fᘁ + gᘁ := by
  simp [rightAdjointMate]

/-- Taking right adjoint mates commutes with finite sums. -/
@[simp]
theorem rightAdjointMate_sum {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (∑ i ∈ s, f i)ᘁ = ∑ i ∈ s, (f i)ᘁ := by
  simp [rightAdjointMate, sum_whiskerRight, whiskerLeft_sum, Preadditive.comp_sum,
    Preadditive.sum_comp]

/-- Taking right adjoint mates commutes with negation. -/
@[simp]
theorem rightAdjointMate_neg (f : X ⟶ Y) : (-f)ᘁ = -fᘁ :=
  eq_neg_of_add_eq_zero_left (by rw [← rightAdjointMate_add, neg_add_cancel, rightAdjointMate_zero])

/-- Taking right adjoint mates commutes with subtraction. -/
@[simp]
theorem rightAdjointMate_sub (f g : X ⟶ Y) : (f - g)ᘁ = fᘁ - gᘁ := by
  rw [sub_eq_add_neg, rightAdjointMate_add, rightAdjointMate_neg, sub_eq_add_neg]

/-- Taking right adjoint mates commutes with scalar multiplication in a monoidal linear category. -/
@[simp]
theorem rightAdjointMate_smul {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]
    (r : R) (f : X ⟶ Y) : (r • f)ᘁ = r • fᘁ := by
  simp [rightAdjointMate]

end RightMate

section LeftMate

variable {X Y : C} [HasLeftDual X] [HasLeftDual Y]

/-- The left adjoint mate of the zero morphism is zero. -/
@[simp]
theorem leftAdjointMate_zero : leftAdjointMate (0 : X ⟶ Y) = 0 := by
  simp [leftAdjointMate]

/-- The left adjoint mate is additive. -/
@[simp]
theorem leftAdjointMate_add (f g : X ⟶ Y) :
    leftAdjointMate (f + g) = leftAdjointMate f + leftAdjointMate g := by
  simp [leftAdjointMate]

/-- Taking left adjoint mates commutes with finite sums. -/
@[simp]
theorem leftAdjointMate_sum {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    leftAdjointMate (∑ i ∈ s, f i) = ∑ i ∈ s, leftAdjointMate (f i) := by
  simp [leftAdjointMate, sum_whiskerRight, whiskerLeft_sum, Preadditive.comp_sum,
    Preadditive.sum_comp]

/-- Taking left adjoint mates commutes with negation. -/
@[simp]
theorem leftAdjointMate_neg (f : X ⟶ Y) : leftAdjointMate (-f) = -leftAdjointMate f :=
  eq_neg_of_add_eq_zero_left (by rw [← leftAdjointMate_add, neg_add_cancel, leftAdjointMate_zero])

/-- Taking left adjoint mates commutes with subtraction. -/
@[simp]
theorem leftAdjointMate_sub (f g : X ⟶ Y) :
    leftAdjointMate (f - g) = leftAdjointMate f - leftAdjointMate g := by
  rw [sub_eq_add_neg, leftAdjointMate_add, leftAdjointMate_neg, sub_eq_add_neg]

/-- Taking left adjoint mates commutes with scalar multiplication in a monoidal linear category. -/
@[simp]
theorem leftAdjointMate_smul {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]
    (r : R) (f : X ⟶ Y) : leftAdjointMate (r • f) = r • leftAdjointMate f := by
  simp [leftAdjointMate]

end LeftMate

section Linear

variable (k : Type w) [Semiring k] [Linear k C] [MonoidalLinear k C]

/-- Taking right adjoint mates identifies `X ⟶ Y` `k`-linearly with `Yᘁ ⟶ Xᘁ`, with inverse
`CategoryTheory.leftAdjointMate`. -/
noncomputable def rightAdjointMateLinearEquiv (X Y : C) [HasRightDual X] [HasRightDual Y] :
    (X ⟶ Y) ≃ₗ[k] (Yᘁ ⟶ Xᘁ) where
  toFun := rightAdjointMate
  invFun := leftAdjointMate
  left_inv := leftAdjointMate_rightAdjointMate
  right_inv := rightAdjointMate_leftAdjointMate
  map_add' := rightAdjointMate_add
  map_smul' := rightAdjointMate_smul

/-- `TauCeti.rightAdjointMateLinearEquiv` acts as `CategoryTheory.rightAdjointMate`. -/
@[simp]
theorem rightAdjointMateLinearEquiv_apply (X Y : C) [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : rightAdjointMateLinearEquiv k X Y f = fᘁ :=
  (rfl)

/-- The inverse of `TauCeti.rightAdjointMateLinearEquiv` acts as
`CategoryTheory.leftAdjointMate`. -/
@[simp]
theorem rightAdjointMateLinearEquiv_symm_apply (X Y : C) [HasRightDual X] [HasRightDual Y]
    (f : Yᘁ ⟶ Xᘁ) : (rightAdjointMateLinearEquiv k X Y).symm f = leftAdjointMate f :=
  (rfl)

/-- Taking left adjoint mates identifies `X ⟶ Y` `k`-linearly with `(ᘁY) ⟶ (ᘁX)`, with inverse
`CategoryTheory.rightAdjointMate`. -/
noncomputable def leftAdjointMateLinearEquiv (X Y : C) [HasLeftDual X] [HasLeftDual Y] :
    (X ⟶ Y) ≃ₗ[k] ((ᘁY) ⟶ (ᘁX)) where
  toFun := leftAdjointMate
  invFun := rightAdjointMate
  left_inv := rightAdjointMate_leftAdjointMate
  right_inv := leftAdjointMate_rightAdjointMate
  map_add' := leftAdjointMate_add
  map_smul' := leftAdjointMate_smul

/-- `TauCeti.leftAdjointMateLinearEquiv` acts as `CategoryTheory.leftAdjointMate`. -/
@[simp]
theorem leftAdjointMateLinearEquiv_apply (X Y : C) [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) : leftAdjointMateLinearEquiv k X Y f = leftAdjointMate f :=
  (rfl)

/-- The inverse of `TauCeti.leftAdjointMateLinearEquiv` acts as
`CategoryTheory.rightAdjointMate`. -/
@[simp]
theorem leftAdjointMateLinearEquiv_symm_apply (X Y : C) [HasLeftDual X] [HasLeftDual Y]
    (f : (ᘁY) ⟶ (ᘁX)) : (leftAdjointMateLinearEquiv k X Y).symm f = fᘁ :=
  (rfl)

/-- Frobenius reciprocity `(Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)` for an exact pairing of `Y` and `Y'`
(`CategoryTheory.tensorLeftHomEquiv`) is `k`-linear. -/
noncomputable def tensorLeftHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (Y' ⊗ X ⟶ Z) ≃ₗ[k] (X ⟶ Y ⊗ Z) :=
  { tensorLeftHomEquiv X Y Y' Z with
    map_add' f g := by simp [tensorLeftHomEquiv]
    map_smul' r f := by simp [tensorLeftHomEquiv] }

/-- `TauCeti.tensorLeftHomLinearEquiv` acts as `CategoryTheory.tensorLeftHomEquiv`. -/
@[simp]
theorem tensorLeftHomLinearEquiv_apply (X Y Y' Z : C) [ExactPairing Y Y'] (f : Y' ⊗ X ⟶ Z) :
    tensorLeftHomLinearEquiv k X Y Y' Z f = tensorLeftHomEquiv X Y Y' Z f :=
  (rfl)

/-- The inverse of `TauCeti.tensorLeftHomLinearEquiv` acts as that of
`CategoryTheory.tensorLeftHomEquiv`. -/
@[simp]
theorem tensorLeftHomLinearEquiv_symm_apply (X Y Y' Z : C) [ExactPairing Y Y']
    (f : X ⟶ Y ⊗ Z) :
    (tensorLeftHomLinearEquiv k X Y Y' Z).symm f = (tensorLeftHomEquiv X Y Y' Z).symm f :=
  (rfl)

/-- Frobenius reciprocity `(X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y')` for an exact pairing of `Y` and `Y'`
(`CategoryTheory.tensorRightHomEquiv`) is `k`-linear. -/
noncomputable def tensorRightHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ₗ[k] (X ⟶ Z ⊗ Y') :=
  { tensorRightHomEquiv X Y Y' Z with
    map_add' f g := by simp [tensorRightHomEquiv]
    map_smul' r f := by simp [tensorRightHomEquiv] }

/-- `TauCeti.tensorRightHomLinearEquiv` acts as `CategoryTheory.tensorRightHomEquiv`. -/
@[simp]
theorem tensorRightHomLinearEquiv_apply (X Y Y' Z : C) [ExactPairing Y Y'] (f : X ⊗ Y ⟶ Z) :
    tensorRightHomLinearEquiv k X Y Y' Z f = tensorRightHomEquiv X Y Y' Z f :=
  (rfl)

/-- The inverse of `TauCeti.tensorRightHomLinearEquiv` acts as that of
`CategoryTheory.tensorRightHomEquiv`. -/
@[simp]
theorem tensorRightHomLinearEquiv_symm_apply (X Y Y' Z : C) [ExactPairing Y Y']
    (f : X ⟶ Z ⊗ Y') :
    (tensorRightHomLinearEquiv k X Y Y' Z).symm f = (tensorRightHomEquiv X Y Y' Z).symm f :=
  (rfl)

/-- Frobenius reciprocity identifies `𝟙_ C ⟶ tensorPow V 2` `k`-linearly with `Vᘁ ⟶ V`. -/
noncomputable def homTensorPowTwoLinearEquiv (V : C) [HasRightDual V] :
    (𝟙_ C ⟶ tensorPow V 2) ≃ₗ[k] (Vᘁ ⟶ V) :=
  (Linear.homCongr k (Iso.refl (𝟙_ C)) (whiskerLeftIso V (ρ_ V))).trans
    ((tensorLeftHomLinearEquiv k (𝟙_ C) V Vᘁ V).symm.trans
      (Linear.homCongr k (ρ_ Vᘁ) (Iso.refl V)))

-- Not `@[simp]`: `tensorPow` is `@[reducible]`, so `DiscrTree.getMatch` reduces `tensorPow V 2`
-- inside `DFunLike.coe` while `SimpTheorems` indexes it unreduced (`noIndexAtArgs := true`),
-- causing `simpNF` to reject `@[simp]`.
/-- Evaluating `homTensorPowTwoLinearEquiv` closes up the first factor of `tensorPow V 2` against
`Vᘁ` with `ε_ V Vᘁ`. -/
theorem homTensorPowTwoLinearEquiv_apply (V : C) [HasRightDual V] (f : 𝟙_ C ⟶ tensorPow V 2) :
    homTensorPowTwoLinearEquiv k V f =
      (ρ_ Vᘁ).inv ≫ Vᘁ ◁ (f ≫ V ◁ (ρ_ V).hom) ≫ (α_ Vᘁ V V).inv ≫ ε_ V Vᘁ ▷ V ≫ (λ_ V).hom := by
  simp only [homTensorPowTwoLinearEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, whiskerLeftIso_hom, Category.id_comp, Category.comp_id,
    tensorLeftHomLinearEquiv_symm_apply, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]

-- Not `@[simp]` for the same `simpNF` reason as `homTensorPowTwoLinearEquiv_apply`.
/-- The inverse of `homTensorPowTwoLinearEquiv` sends `g : Vᘁ ⟶ V` to `η_ V Vᘁ` composed with `g`
on the second factor, up to the right unitor of `V`. -/
theorem homTensorPowTwoLinearEquiv_symm_apply (V : C) [HasRightDual V] (g : Vᘁ ⟶ V) :
    (homTensorPowTwoLinearEquiv k V).symm g = η_ V Vᘁ ≫ V ◁ (g ≫ (ρ_ V).inv) := by
  simp only [homTensorPowTwoLinearEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Linear.homCongr_symm_apply, Iso.refl_inv, Iso.refl_hom, whiskerLeftIso_inv,
    Category.id_comp, Category.comp_id, LinearEquiv.symm_symm,
    tensorLeftHomLinearEquiv_apply, tensorLeftHomEquiv, Equiv.coe_fn_mk]
  monoidal

end Linear

end TauCeti
