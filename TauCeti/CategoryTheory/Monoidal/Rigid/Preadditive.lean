/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Duals in a monoidal preadditive category

In a monoidal preadditive category the right adjoint mate `f ↦ fᘁ` is additive (hence commutes
with negation, subtraction, and finite sums), and in a monoidal `R`-linear category it is
`R`-linear. Consequently, in a rigid monoidal `R`-linear category over a commutative semiring `R`,
having scalar endomorphisms is preserved by passing to the right dual.

In a monoidal `k`-linear category the Frobenius reciprocity bijections `tensorLeftHomEquiv` and
`tensorRightHomEquiv` are `k`-linear, so they compare dimensions of morphism spaces, for instance
of the multiplicity spaces of a fusion category. Specializing to `tensorPow V 2` identifies
`𝟙_ C ⟶ tensorPow V 2` `k`-linearly with `Vᘁ ⟶ V` (`TauCeti.homTensorPowTwoLinearEquiv`). When
either member of an exact pairing has scalar endomorphisms over a commutative semiring, Frobenius
reciprocity shows that every morphism from the paired tensor product to the unit is a scalar
multiple of the evaluation.

## Main declarations

* `TauCeti.rightAdjointMate_zero`, `TauCeti.rightAdjointMate_add`, `TauCeti.rightAdjointMate_neg`,
  `TauCeti.rightAdjointMate_sub`, `TauCeti.rightAdjointMate_sum`, and
  `TauCeti.rightAdjointMate_smul`: additivity and linearity of the right adjoint mate;
* `TauCeti.surjective_algebraMap_end_rightDual` and `TauCeti.bijective_algebraMap_end_rightDual`:
  scalar endomorphisms are preserved by right duality;
* `TauCeti.tensorLeftHomLinearEquiv` and `TauCeti.tensorRightHomLinearEquiv`: Frobenius
  reciprocity as `k`-linear equivalences, and `TauCeti.homTensorPowTwoLinearEquiv` (with
  `TauCeti.homTensorPowTwoLinearEquiv_apply` and `TauCeti.homTensorPowTwoLinearEquiv_symm_apply`):
  its specialization `(𝟙_ C ⟶ tensorPow V 2) ≃ₗ[k] (Vᘁ ⟶ V)`;
* `TauCeti.hom_tensorUnit_eq_smul_evaluation_of_surjective_right` and
  `TauCeti.hom_tensorUnit_eq_smul_evaluation_of_surjective_left`: every morphism from a paired
  tensor product to the unit is a scalar multiple of the evaluation when one paired object has
  scalar endomorphisms.
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

/-- The right adjoint mate commutes with negation. -/
@[simp]
theorem rightAdjointMate_neg (f : X ⟶ Y) : (-f)ᘁ = -fᘁ :=
  eq_neg_of_add_eq_zero_left (by rw [← rightAdjointMate_add, neg_add_cancel, rightAdjointMate_zero])

/-- The right adjoint mate commutes with subtraction. -/
@[simp]
theorem rightAdjointMate_sub (f g : X ⟶ Y) : (f - g)ᘁ = fᘁ - gᘁ := by
  rw [sub_eq_add_neg, rightAdjointMate_add, rightAdjointMate_neg, sub_eq_add_neg]

/-- Taking right adjoint mates commutes with finite sums. -/
@[simp]
theorem rightAdjointMate_sum {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (∑ i ∈ s, f i)ᘁ = ∑ i ∈ s, (f i)ᘁ := by
  simp [rightAdjointMate, sum_whiskerRight, whiskerLeft_sum, Preadditive.comp_sum,
    Preadditive.sum_comp]

/-- The right adjoint mate is `R`-linear in an `R`-linear monoidal category. -/
@[simp]
theorem rightAdjointMate_smul {R : Type w} [Semiring R] [Linear R C] [MonoidalLinear R C]
    (r : R) (f : X ⟶ Y) : (r • f)ᘁ = r • fᘁ := by
  simp [rightAdjointMate]

end Mate

section ScalarEnd

variable {R : Type w} [CommSemiring R] [Linear R C] [MonoidalLinear R C] {X : C} [HasRightDual X]

/-- If every endomorphism of `X` is a scalar multiple of `𝟙 X`, then the same holds for its right
dual `Xᘁ`. -/
theorem surjective_algebraMap_end_rightDual
    (hX : Function.Surjective (algebraMap R (End X))) :
    Function.Surjective (algebraMap R (End Xᘁ)) := by
  intro g
  let p : ExactPairing X Xᘁ := HasRightDual.exact
  obtain ⟨r, hr⟩ := hX (End.of (ExactPairing.leftMate p p g.asHom))
  refine ⟨r, End.ext ?_⟩
  have hg : ExactPairing.leftMate p p g.asHom = r • 𝟙 X := by
    simpa [End.algebraMap_asHom] using (congrArg End.asHom hr).symm
  have hmate : (ExactPairing.leftMate p p g.asHom)ᘁ = g.asHom :=
    ExactPairing.rightHom_ext (X := X) (by
      rw [rightAdjointMate_comp_evaluation, ExactPairing.leftMate_comp_evaluation])
  rw [End.algebraMap_asHom, ← hmate, hg, rightAdjointMate_smul, rightAdjointMate_id]

/-- If `X` has scalar endomorphisms over `R`, then so does its right dual `Xᘁ`. -/
theorem bijective_algebraMap_end_rightDual
    (hX : Function.Bijective (algebraMap R (End X))) :
    Function.Bijective (algebraMap R (End Xᘁ)) := by
  refine ⟨fun r s hrs ↦ hX.injective <| End.ext ?_,
    surjective_algebraMap_end_rightDual hX.surjective⟩
  have h := congrArg End.asHom hrs
  simp only [End.algebraMap_asHom] at h ⊢
  exact rightAdjointMate_injective
    (by simpa only [rightAdjointMate_smul, rightAdjointMate_id] using h)

end ScalarEnd

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

section Evaluation

variable {R : Type w} [CommSemiring R] [Linear R C] [MonoidalLinear R C]

/-- If every endomorphism of the right member `Y` of an exact pairing is a scalar multiple of
`𝟙 Y`, then every morphism `Y ⊗ X ⟶ 𝟙_ C` is a scalar multiple of the evaluation `ε_ X Y`. -/
theorem hom_tensorUnit_eq_smul_evaluation_of_surjective_right {X Y : C} [ExactPairing X Y]
    (hY : Function.Surjective (algebraMap R (End Y))) (f : Y ⊗ X ⟶ 𝟙_ C) :
    ∃ r : R, f = r • ε_ X Y := by
  let e := (tensorRightHomLinearEquiv R Y X Y (𝟙_ C)).trans
    (Linear.homCongr R (Iso.refl Y) (λ_ Y))
  obtain ⟨r, hr⟩ := hY (End.of (e f))
  have hef : e f = r • 𝟙 Y := by
    simpa [End.algebraMap_asHom] using (congrArg End.asHom hr).symm
  refine ⟨r, e.injective ?_⟩
  rw [map_smul, hef]
  congr 1
  -- Frobenius reciprocity carries evaluation to the identity, with the unitors removed.
  simp only [e, LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_inv,
    Category.id_comp, tensorRightHomLinearEquiv_apply]
  simp [tensorRightHomEquiv, ExactPairing.coevaluation_evaluation]

/-- If every endomorphism of the left member `X` of an exact pairing is a scalar multiple of
`𝟙 X`, then every morphism `Y ⊗ X ⟶ 𝟙_ C` is a scalar multiple of the evaluation `ε_ X Y`. -/
theorem hom_tensorUnit_eq_smul_evaluation_of_surjective_left {X Y : C} [ExactPairing X Y]
    (hX : Function.Surjective (algebraMap R (End X))) (f : Y ⊗ X ⟶ 𝟙_ C) :
    ∃ r : R, f = r • ε_ X Y := by
  let e := (tensorLeftHomLinearEquiv R X X Y (𝟙_ C)).trans
    (Linear.homCongr R (Iso.refl X) (ρ_ X))
  obtain ⟨r, hr⟩ := hX (End.of (e f))
  have hef : e f = r • 𝟙 X := by
    simpa [End.algebraMap_asHom] using (congrArg End.asHom hr).symm
  refine ⟨r, e.injective ?_⟩
  rw [map_smul, hef]
  congr 1
  -- The other Frobenius reciprocity bijection carries evaluation to the identity of `X`.
  simp only [e, LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_inv,
    Category.id_comp, tensorLeftHomLinearEquiv_apply]
  simp [tensorLeftHomEquiv, ExactPairing.evaluation_coevaluation]

end Evaluation

end TauCeti
