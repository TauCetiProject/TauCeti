/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Frobenius reciprocity for tensor squares

In a monoidal `k`-linear category, specializing the `k`-linear Frobenius reciprocity
`TauCeti.tensorLeftHomLinearEquiv` to `tensorPow V 2` identifies `𝟙_ C ⟶ tensorPow V 2`
`k`-linearly with `W ⟶ V` for an exact pairing of `V` and `W`
(`TauCeti.homTensorPowTwoLinearEquiv`). Taking `W = Vᘁ` when `V` has a right dual gives the hom
space `Vᘁ ⟶ V`. In a category with kernels, Schur's lemma controls this hom space when `V` and
`Vᘁ` are simple; the equivalence itself needs no kernels.

## Main declarations

* `TauCeti.homTensorPowTwoLinearEquiv`: the `k`-linear equivalence
  `(𝟙_ C ⟶ tensorPow V 2) ≃ₗ[k] (W ⟶ V)` for an exact pairing of `V` and `W`;
* `TauCeti.homTensorPowTwoLinearEquiv_apply` and `TauCeti.homTensorPowTwoLinearEquiv_symm_apply`:
  its values, by the evaluation `ε_ V W` and the coevaluation `η_ V W`.
-/

public section

open CategoryTheory MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

variable (k : Type w) [Semiring k] [Linear k C] [MonoidalLinear k C]

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
  -- Mathlib states no evaluation lemma for `tensorLeftHomEquiv` in general, so this unfolds it:
  -- the right side is its inverse map, which is defined by this formula.
  simp only [homTensorPowTwoLinearEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, whiskerLeftIso_hom, Category.id_comp, Category.comp_id,
    tensorLeftHomLinearEquiv_symm_apply, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]

-- Not `@[simp]` for the same `simpNF` reason as `homTensorPowTwoLinearEquiv_apply`.
/-- The inverse of `homTensorPowTwoLinearEquiv` sends `g : W ⟶ V` to `η_ V W` composed with `g`
on the second factor, up to the right unitor of `V`. -/
theorem homTensorPowTwoLinearEquiv_symm_apply (V W : C) [ExactPairing V W] (g : W ⟶ V) :
    (homTensorPowTwoLinearEquiv k V W).symm g = η_ V W ≫ V ◁ (g ≫ (ρ_ V).inv) := by
  rw [LinearEquiv.symm_apply_eq]
  simp only [homTensorPowTwoLinearEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, whiskerLeftIso_hom, Category.id_comp, Category.comp_id,
    tensorLeftHomLinearEquiv_symm_apply, Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id,
    tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft, Iso.inv_hom_id_assoc]

end TauCeti
