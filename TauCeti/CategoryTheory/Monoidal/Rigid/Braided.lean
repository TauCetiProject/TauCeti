/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# Mates for braided exact pairings

The braiding turns an exact pairing `(X, X')` into an exact pairing `(X', X)`.
Taking a right mate with respect to the original pairings and then with respect to these
swapped pairings recovers the original morphism. This makes double duality natural even
when the chosen dual of `X'` is not `X`.

The swapped pairing is Mathlib's `CategoryTheory.BraidedCategory.exactPairing_swap`.
The explicit-pairing statement `rightMate_swap_rightMate` follows the API proposed in
J. McKoen's Mathlib pull request #42145; its proof uses the evaluation characterization
of mates and naturality of the braiding.

In a symmetric monoidal category, swapping is compatible with tensor products of pairings:
the braided evaluation of the tensor product pairing of `(X, X')` and `(Y, Y')` is the
evaluation of the tensor product of the swapped pairings of `(Y, Y')` and `(X, X')`, in which
the braided loop of `Y` is nested inside the braided loop of `X`
(`TauCeti.braiding_comp_tensor_evaluation`). This is the identity that makes the Drinfeld
isomorphism `X ≅ Xᘁᘁ` of a symmetric rigid category monoidal. Its proof uses the symmetry of
the braiding.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.9
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The evaluation of the swapped pairing is braided evaluation. -/
@[simp, reassoc]
theorem exactPairing_swap_evaluation (X Y : C) [ExactPairing X Y] :
    @ExactPairing.evaluation C _ _ Y X (exactPairing_swap X Y) =
      (β_ X Y).hom ≫ ε_ X Y :=
  (rfl)

/-- The coevaluation of the swapped pairing uses the inverse braiding. -/
@[simp, reassoc]
theorem exactPairing_swap_coevaluation (X Y : C) [ExactPairing X Y] :
    @ExactPairing.coevaluation C _ _ Y X (exactPairing_swap X Y) =
      η_ X Y ≫ (β_ Y X).inv :=
  (rfl)

end TauCeti

namespace CategoryTheory.ExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Taking a right mate and then a right mate with respect to the braided swapped pairings
recovers the original morphism. No symmetry of the braiding is needed. -/
@[simp]
theorem rightMate_swap_rightMate {X X' Y Y' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    rightMate (exactPairing_swap Y Y') (exactPairing_swap X X') (rightMate pX pY f) = f := by
  let := exactPairing_swap Y Y'
  apply rightHom_ext (X := Y')
  rw [rightMate_comp_evaluation, TauCeti.exactPairing_swap_evaluation,
    TauCeti.exactPairing_swap_evaluation, braiding_naturality_right_assoc,
    braiding_naturality_left_assoc, rightMate_comp_evaluation]

end CategoryTheory.ExactPairing

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- In a symmetric monoidal category, the braided evaluation of the tensor product pairing
`(X ⊗ Y, Y' ⊗ X')` nests the braided evaluation of `(Y, Y')` inside that of `(X, X')`. The right
side is the evaluation of the tensor product of the swapped pairings of `(Y, Y')` and `(X, X')`,
so the swapped pairing of a tensor product is the tensor product of the swapped pairings. -/
theorem braiding_comp_tensor_evaluation (X X' Y Y' : C) [ExactPairing X X']
    [ExactPairing Y Y'] :
    (β_ (X ⊗ Y) (Y' ⊗ X')).hom ≫ ε_ (X ⊗ Y) (Y' ⊗ X') =
      𝟙 _ ⊗≫ X ◁ (((β_ Y Y').hom ≫ ε_ Y Y') ▷ X') ⊗≫ (β_ X X').hom ≫ ε_ X X' := by
  rw [ExactPairing.tensor_evaluation]
  -- Braiding `X` past `Y'` and then closing the loop of `X` agrees with braiding `Y'` past `X'`
  -- and then closing the loop of `X`. This is where the symmetry of the braiding is used.
  have hX : (α_ X Y' X').inv ≫ (β_ X Y').hom ▷ X' ⊗≫ Y' ◁ ((β_ X X').hom ≫ ε_ X X') ⊗≫ 𝟙 Y' =
      X ◁ (β_ Y' X').hom ⊗≫ ((β_ X X').hom ≫ ε_ X X') ▷ Y' ⊗≫ 𝟙 Y' := by
    have h := braiding_naturality_left ((β_ X X').hom ≫ ε_ X X') Y'
    rw [braiding_tensorUnit_left, braiding_tensor_left_hom] at h
    simp only [Category.assoc] at h
    calc
      _ = X ◁ ((β_ Y' X').hom ≫ (β_ X' Y').hom) ⊗≫ (β_ X Y').hom ▷ X' ⊗≫
            Y' ◁ ((β_ X X').hom ≫ ε_ X X') ⊗≫ 𝟙 Y' := by
        rw [SymmetricCategory.symmetry]; monoidal
      _ = X ◁ (β_ Y' X').hom ⊗≫ ((α_ X X' Y').hom ≫ X ◁ (β_ X' Y').hom ≫ (α_ X Y' X').inv ≫
            (β_ X Y').hom ▷ X' ≫ (α_ Y' X X').hom ≫ Y' ◁ ((β_ X X').hom ≫ ε_ X X')) ⊗≫
              𝟙 Y' := by
        monoidal
      _ = _ := by rw [← h]; monoidal
  have hY := braiding_naturality_left (ε_ Y Y') X'
  rw [braiding_tensorUnit_left, braiding_tensor_left_hom] at hY
  simp only [Category.assoc] at hY
  -- Expand the braiding of `X ⊗ Y` past `Y' ⊗ X'` into four elementary crossings. By `hX`, the
  -- crossing of `X` past `Y'` is traded for one of `Y'` past `X'`, after which the loop of `X`
  -- closes; the remaining crossings of `Y` past `Y'` and of `Y' ⊗ Y` past `X'` then close the
  -- loop of `Y`.
  calc
    _ = (α_ X Y (Y' ⊗ X')).hom ≫ X ◁ (β_ Y (Y' ⊗ X')).hom ⊗≫
          ((α_ X Y' X').inv ≫ (β_ X Y').hom ▷ X' ⊗≫ Y' ◁ ((β_ X X').hom ≫ ε_ X X') ⊗≫
            𝟙 Y') ▷ Y ⊗≫ ε_ Y Y' := by
      rw [braiding_tensor_left_hom, braiding_tensor_right_hom X Y' X']; monoidal
    _ = (α_ X Y (Y' ⊗ X')).hom ≫ X ◁ (β_ Y (Y' ⊗ X')).hom ⊗≫
          (X ◁ (β_ Y' X').hom ⊗≫ ((β_ X X').hom ≫ ε_ X X') ▷ Y' ⊗≫ 𝟙 Y') ▷ Y ⊗≫ ε_ Y Y' := by
      rw [hX]
    _ = (α_ X Y (Y' ⊗ X')).hom ≫ X ◁ ((β_ Y (Y' ⊗ X')).hom ⊗≫ (β_ Y' X').hom ▷ Y) ⊗≫
          (((β_ X X').hom ≫ ε_ X X') ▷ (Y' ⊗ Y) ≫ 𝟙_ C ◁ ε_ Y Y') ⊗≫ 𝟙 (𝟙_ C) := by
      monoidal
    _ = (α_ X Y (Y' ⊗ X')).hom ≫ X ◁ ((β_ Y (Y' ⊗ X')).hom ⊗≫ (β_ Y' X').hom ▷ Y) ⊗≫
          ((X ⊗ X') ◁ ε_ Y Y' ≫ ((β_ X X').hom ≫ ε_ X X') ▷ 𝟙_ C) ⊗≫ 𝟙 (𝟙_ C) := by
      rw [whisker_exchange]
    _ = (α_ X Y (Y' ⊗ X')).hom ⊗≫ X ◁ ((β_ Y Y').hom ▷ X' ⊗≫ ((α_ Y' Y X').hom ≫
          Y' ◁ (β_ Y X').hom ≫ (α_ Y' X' Y).inv ≫ (β_ Y' X').hom ▷ Y ≫ (α_ X' Y' Y).hom ≫
            X' ◁ ε_ Y Y')) ⊗≫ ((β_ X X').hom ≫ ε_ X X') := by
      rw [braiding_tensor_right_hom Y Y' X']; monoidal
    _ = _ := by rw [← hY]; monoidal

end TauCeti
