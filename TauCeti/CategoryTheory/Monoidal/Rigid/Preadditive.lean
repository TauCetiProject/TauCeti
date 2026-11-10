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
built from whiskering and composition, and the coevaluation of an exact pairing out of a nonzero
object is nonzero, by the zigzag identity.

In a monoidal `k`-linear category the Frobenius reciprocity bijections `tensorLeftHomEquiv` and
`tensorRightHomEquiv` are `k`-linear, so they compare dimensions of morphism spaces, for instance
of the multiplicity spaces of a fusion category. Specializing to `tensorPow V 2` identifies
`𝟙_ C ⟶ tensorPow V 2` `k`-linearly with `Vᘁ ⟶ V` (`TauCeti.homTensorPowTwoLinearEquiv`).

## Main declarations

* `TauCeti.rightAdjointMate_zero` and `TauCeti.rightAdjointMate_add`: the right adjoint mate is
  additive;
* `TauCeti.coevaluation_ne_zero`: the coevaluation `η_ X Y` is nonzero when `X` is;
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

end Mate

omit [MonoidalPreadditive C] in
/-- The coevaluation of an exact pairing of `X` with `Y` is nonzero when `X` is nonzero: otherwise
the zigzag identity would make the identity of `X` zero. -/
theorem coevaluation_ne_zero {X Y : C} [ExactPairing X Y] (hX : ¬IsZero X) : η_ X Y ≠ 0 := by
  intro h
  have hz := ExactPairing.evaluation_coevaluation X Y
  have := (tensorRightAdjunction X Y).isLeftAdjoint
  have h0 : (0 : 𝟙_ C ⟶ X ⊗ Y) ▷ X = 0 := (tensorRight X).map_zero _ _
  rw [h, h0, zero_comp] at hz
  exact hX ((IsZero.iff_id_eq_zero X).2 (by simpa using (λ_ X).inv ≫= hz.symm =≫ (ρ_ X).hom))

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
