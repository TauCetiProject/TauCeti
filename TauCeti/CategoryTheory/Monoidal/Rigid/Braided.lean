/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.CategoryTheory.Monoidal.Braided.Basic
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

Swapping is compatible with tensor products of pairings up to a double braiding. After the
double braiding `β_{X,Y} ≫ β_{Y,X}` of `X ⊗ Y`, the braided evaluation of the tensor product
pairing of `(X, X')` and `(Y, Y')` is the evaluation of the tensor product of the swapped
pairings of `(Y, Y')` and `(X, X')`, in which the braided loop of `Y` is nested inside the
braided loop of `X`
(`TauCeti.braiding_comp_braiding_whiskerRight_comp_braiding_comp_tensor_evaluation`).
Equivalently, the double braiding can be replaced by the inverse double braiding of `Y'` and `X'`
(`TauCeti.braiding_comp_tensor_evaluation`); the two forms are related by the fact that a
braiding is its own mate with respect to tensor product pairings
(`TauCeti.whiskerLeft_braiding_comp_tensor_evaluation`). In a symmetric category the double
braidings are identities. This is the identity that computes the Drinfeld isomorphism
`X ≅ Xᘁᘁ` of a tensor product.

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

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- A braiding is its own mate with respect to tensor product pairings: precomposing the
evaluation of the tensor product pairing `(X ⊗ Y, Y' ⊗ X')` with the braiding of `Y` past `X`
is precomposing the evaluation of `(Y ⊗ X, X' ⊗ Y')` with the braiding of `Y'` past `X'`. -/
theorem whiskerLeft_braiding_comp_tensor_evaluation (X X' Y Y' : C) [ExactPairing X X']
    [ExactPairing Y Y'] :
    (Y' ⊗ X') ◁ (β_ Y X).hom ≫ ε_ (X ⊗ Y) (Y' ⊗ X') =
      (β_ Y' X').hom ▷ (Y ⊗ X) ≫ ε_ (Y ⊗ X) (X' ⊗ Y') := by
  rw [ExactPairing.tensor_evaluation, ExactPairing.tensor_evaluation]
  -- Both sides close the loop of `X` after braiding `Y` back under `X'`, by naturality of the
  -- braiding with respect to the evaluations of `(X, X')` and `(Y, Y')`.
  calc
    _ = 𝟙 _ ⊗≫ Y' ◁ (X' ◁ (β_ Y X).hom ≫ (α_ X' X Y).inv ≫ ε_ X X' ▷ Y) ⊗≫ ε_ Y Y' := by
      monoidal
    _ = 𝟙 _ ⊗≫ Y' ◁ (β_ Y X').inv ▷ X ⊗≫ ((Y' ⊗ Y) ◁ ε_ X X' ≫ ε_ Y Y' ▷ 𝟙_ C) ⊗≫
          𝟙 (𝟙_ C) := by
      rw [whiskerLeft_braiding_comp_whiskerRight]; monoidal
    _ = 𝟙 _ ⊗≫ (Y' ◁ (β_ Y X').inv ≫ (α_ Y' Y X').inv ≫ ε_ Y Y' ▷ X') ▷ X ⊗≫ ε_ X X' := by
      rw [whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ ((β_ Y' X').hom ▷ Y ≫ (α_ X' Y' Y).hom ≫ X' ◁ ε_ Y Y') ▷ X ⊗≫ ε_ X X' := by
      rw [braiding_whiskerRight_comp_whiskerLeft]; monoidal
    _ = _ := by monoidal

/-- The double braiding is its own mate with respect to tensor product pairings: precomposing
the evaluation of `(A ⊗ B, B' ⊗ A')` with the double braiding `β_{A,B} ≫ β_{B,A}` of `A ⊗ B` is
precomposing it with the double braiding `β_{B',A'} ≫ β_{A',B'}` of `B' ⊗ A'`. -/
theorem whiskerLeft_braiding_comp_braiding_comp_tensor_evaluation (A A' B B' : C)
    [ExactPairing A A'] [ExactPairing B B'] :
    (B' ⊗ A') ◁ ((β_ A B).hom ≫ (β_ B A).hom) ≫ ε_ (A ⊗ B) (B' ⊗ A') =
      ((β_ B' A').hom ≫ (β_ A' B').hom) ▷ (A ⊗ B) ≫ ε_ (A ⊗ B) (B' ⊗ A') := by
  rw [whiskerLeft_comp, Category.assoc, whiskerLeft_braiding_comp_tensor_evaluation,
    whisker_exchange_assoc, whiskerLeft_braiding_comp_tensor_evaluation, comp_whiskerRight,
    Category.assoc]

/-- The braided evaluation of the tensor product pairing `(X ⊗ Y, Y' ⊗ X')` is the inverse of the
double braiding `β_{Y',X'} ≫ β_{X',Y'}` of `Y' ⊗ X'`, followed by the braided evaluation of
`(Y, Y')` nested inside the braided evaluation of `(X, X')`. In a symmetric category the double
braiding is the identity, so the swapped pairing of a tensor product is the tensor product of
the swapped pairings. -/
theorem braiding_comp_tensor_evaluation (X X' Y Y' : C) [ExactPairing X X']
    [ExactPairing Y Y'] :
    (β_ (X ⊗ Y) (Y' ⊗ X')).hom ≫ ε_ (X ⊗ Y) (Y' ⊗ X') =
      (X ⊗ Y) ◁ ((β_ X' Y').inv ≫ (β_ Y' X').inv) ⊗≫
        X ◁ (((β_ Y Y').hom ≫ ε_ Y Y') ▷ X') ⊗≫ (β_ X X').hom ≫ ε_ X X' := by
  rw [ExactPairing.tensor_evaluation]
  -- Expand the braiding of `X ⊗ Y` past `Y' ⊗ X'` into four elementary crossings. By
  -- `braiding_whiskerRight_comp_whiskerLeft`, the crossing of `X` past `Y'` is traded for one of
  -- `X'` under `Y'`, after which the loop of `X` closes. The crossings of `Y` past `Y' ⊗ X'` and of
  -- `X'` under `Y'` are then rearranged, by naturality of the braiding, into a crossing of `Y'`
  -- under `X'` followed by those of `Y` past `X' ⊗ Y'`, and the loop of `Y` closes in the same way.
  calc
    _ = 𝟙 _ ⊗≫ X ◁ (β_ Y Y').hom ▷ X' ⊗≫ (X ⊗ Y') ◁ (β_ Y X').hom ⊗≫
          ((β_ X Y').hom ▷ X' ≫ (α_ Y' X X').hom ≫ Y' ◁ ((β_ X X').hom ≫ ε_ X X')) ▷ Y ⊗≫
            ε_ Y Y' := by
      calc
        _ = 𝟙 _ ⊗≫ X ◁ (β_ Y Y').hom ▷ X' ⊗≫
              ((β_ X Y').hom ▷ (Y ⊗ X') ≫ (Y' ⊗ X) ◁ (β_ Y X').hom) ⊗≫
                Y' ◁ ((β_ X X').hom ≫ ε_ X X') ▷ Y ⊗≫ ε_ Y Y' := by
          rw [braiding_tensor_right_hom (X ⊗ Y) Y' X', braiding_tensor_left_hom X Y Y',
            braiding_tensor_left_hom X Y X']
          monoidal
        _ = _ := by rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ ((β_ Y Y').hom ▷ X' ⊗≫ Y' ◁ (β_ Y X').hom ⊗≫ (β_ X' Y').inv ▷ Y) ⊗≫
          (((β_ X X').hom ≫ ε_ X X') ▷ (Y' ⊗ Y) ≫ 𝟙_ C ◁ ε_ Y Y') ⊗≫ 𝟙 (𝟙_ C) := by
      rw [braiding_whiskerRight_comp_whiskerLeft]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ ((β_ Y (Y' ⊗ X')).hom ≫ (β_ X' Y').inv ▷ Y) ⊗≫
          ((X ⊗ X') ◁ ε_ Y Y' ≫ ((β_ X X').hom ≫ ε_ X X') ▷ 𝟙_ C) ⊗≫ 𝟙 (𝟙_ C) := by
      rw [← whisker_exchange, braiding_tensor_right_hom Y Y' X']; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ (β_ X' Y').inv ⊗≫
          ((β_ Y X').hom ▷ Y' ≫ (α_ X' Y Y').hom ≫ X' ◁ ((β_ Y Y').hom ≫ ε_ Y Y'))) ⊗≫
            ((β_ X X').hom ≫ ε_ X X') := by
      rw [← braiding_naturality_right, braiding_tensor_right_hom Y X' Y']; monoidal
    _ = _ := by rw [braiding_whiskerRight_comp_whiskerLeft]; monoidal

/-- After the double braiding `β_{X,Y} ≫ β_{Y,X}` of `X ⊗ Y`, the braided evaluation of the tensor
product pairing `(X ⊗ Y, Y' ⊗ X')` nests the braided evaluation of `(Y, Y')` inside that of
`(X, X')`. The right side is the evaluation of the tensor product of the swapped pairings of
`(Y, Y')` and `(X, X')`. -/
theorem braiding_comp_braiding_whiskerRight_comp_braiding_comp_tensor_evaluation (X X' Y Y' : C)
    [ExactPairing X X'] [ExactPairing Y Y'] :
    ((β_ X Y).hom ≫ (β_ Y X).hom) ▷ (Y' ⊗ X') ≫ (β_ (X ⊗ Y) (Y' ⊗ X')).hom ≫
        ε_ (X ⊗ Y) (Y' ⊗ X') =
      𝟙 _ ⊗≫ X ◁ (((β_ Y Y').hom ≫ ε_ Y Y') ▷ X') ⊗≫ (β_ X X').hom ≫ ε_ X X' := by
  -- The double braiding of `X ⊗ Y` is the mate of that of `Y' ⊗ X'` with respect to the tensor
  -- product of the swapped pairings, whose evaluation is the right side.
  have h := @whiskerLeft_braiding_comp_braiding_comp_tensor_evaluation C _ _ _ Y' Y X' X
    (exactPairing_swap Y Y') (exactPairing_swap X X')
  rw [@ExactPairing.tensor_evaluation C _ _ Y' X' Y X (exactPairing_swap Y Y')
    (exactPairing_swap X X'), exactPairing_swap_evaluation, exactPairing_swap_evaluation] at h
  calc
    _ = (X ⊗ Y) ◁ ((β_ X' Y').inv ≫ (β_ Y' X').inv) ≫
          ((β_ X Y).hom ≫ (β_ Y X).hom) ▷ (Y' ⊗ X') ≫
            (𝟙 _ ⊗≫ X ◁ (((β_ Y Y').hom ≫ ε_ Y Y') ▷ X') ⊗≫ (β_ X X').hom ≫ ε_ X X') := by
      rw [braiding_comp_tensor_evaluation, whisker_exchange_assoc]; monoidal
    _ = _ := by
      rw [← h, ← whiskerLeft_comp_assoc]
      simp

end TauCeti
