/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Duals in a monoidal preadditive category

In a monoidal preadditive category the right adjoint mate `f ↦ fᘁ` is additive, because it is
built from whiskering and composition.

In a monoidal `k`-linear category the Frobenius reciprocity bijections `tensorLeftHomEquiv` and
`tensorRightHomEquiv` are `k`-linear, so they compare dimensions of morphism spaces, for instance
of the multiplicity spaces of a fusion category. Specializing to `tensorPow V 2` identifies
`𝟙_ C ⟶ tensorPow V 2` `k`-linearly with `W ⟶ V` for an exact pairing of `V` and `W`, such as
`Vᘁ ⟶ V` (`TauCeti.homTensorPowTwoLinearEquiv`).

## Main declarations

* `TauCeti.rightAdjointMate_zero`, `TauCeti.rightAdjointMate_add`,
  `TauCeti.rightAdjointMate_sum`, and `TauCeti.rightAdjointMate_smul`: the right adjoint mate is
  additive, and `R`-linear in an `R`-linear monoidal category;
* `TauCeti.tensorLeftHomLinearEquiv` and `TauCeti.tensorRightHomLinearEquiv`: Frobenius
  reciprocity as `k`-linear equivalences, and `TauCeti.homTensorPowTwoLinearEquiv` (with
  `TauCeti.homTensorPowTwoLinearEquiv_apply` and `TauCeti.homTensorPowTwoLinearEquiv_symm_apply`):
  its specialization `(𝟙_ C ⟶ tensorPow V 2) ≃ₗ[k] (W ⟶ V)` for an exact pairing of `V` and `W`.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

section Mate

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

/-- The right adjoint mate is `R`-linear in an `R`-linear monoidal category. -/
@[simp]
theorem rightAdjointMate_smul {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C] (r : R)
    (f : X ⟶ Y) : (r • f)ᘁ = r • fᘁ := by
  simp [rightAdjointMate]

end Mate

section Linear

variable (k : Type w) [Semiring k] [Linear k C] [MonoidalLinear k C]

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

/-- Frobenius reciprocity identifies `𝟙_ C ⟶ tensorPow V 2` `k`-linearly with `W ⟶ V` for an
exact pairing of `V` and `W`, for instance with `Vᘁ ⟶ V` for the right dual `Vᘁ`. -/
noncomputable def homTensorPowTwoLinearEquiv (V W : C) [ExactPairing V W] :
    (𝟙_ C ⟶ tensorPow V 2) ≃ₗ[k] (W ⟶ V) :=
  (Linear.homCongr k (Iso.refl (𝟙_ C)) (whiskerLeftIso V (ρ_ V))).trans
    ((tensorLeftHomLinearEquiv k (𝟙_ C) V W V).symm.trans
      (Linear.homCongr k (ρ_ W) (Iso.refl V)))

-- Not `@[simp]`: `tensorPow` is `@[reducible]`, so `DiscrTree.getMatch` reduces `tensorPow V 2`
-- inside `DFunLike.coe` while `SimpTheorems` indexes it unreduced (`noIndexAtArgs := true`),
-- causing `simpNF` to reject `@[simp]`.
/-- Evaluating `homTensorPowTwoLinearEquiv` closes up the first factor of `tensorPow V 2` against
`W` with `ε_ V W`. -/
theorem homTensorPowTwoLinearEquiv_apply (V W : C) [ExactPairing V W]
    (f : 𝟙_ C ⟶ tensorPow V 2) :
    homTensorPowTwoLinearEquiv k V W f =
      (ρ_ W).inv ≫ W ◁ (f ≫ V ◁ (ρ_ V).hom) ≫ (α_ W V V).inv ≫ ε_ V W ▷ V ≫ (λ_ V).hom := by
  simp only [homTensorPowTwoLinearEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, whiskerLeftIso_hom, Category.id_comp, Category.comp_id,
    tensorLeftHomLinearEquiv_symm_apply, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]

-- Not `@[simp]` for the same `simpNF` reason as `homTensorPowTwoLinearEquiv_apply`.
/-- The inverse of `homTensorPowTwoLinearEquiv` sends `g : W ⟶ V` to `η_ V W` composed with `g`
on the second factor, up to the right unitor of `V`. -/
theorem homTensorPowTwoLinearEquiv_symm_apply (V W : C) [ExactPairing V W] (g : W ⟶ V) :
    (homTensorPowTwoLinearEquiv k V W).symm g = η_ V W ≫ V ◁ (g ≫ (ρ_ V).inv) := by
  simp only [homTensorPowTwoLinearEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Linear.homCongr_symm_apply, Iso.refl_inv, Iso.refl_hom, whiskerLeftIso_inv,
    Category.id_comp, Category.comp_id, LinearEquiv.symm_symm,
    tensorLeftHomLinearEquiv_apply, tensorLeftHomEquiv, Equiv.coe_fn_mk]
  monoidal

end Linear

end TauCeti
