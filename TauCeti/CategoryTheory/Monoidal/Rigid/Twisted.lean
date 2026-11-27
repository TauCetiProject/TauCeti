/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import TauCeti.CategoryTheory.Monoidal.Braided.Basic

/-!
# Pairings twisted by an object

Let `V` be an object of a braided monoidal category. A **pairing of `X` and `Y` twisted by `V`**
(`TauCeti.TwistedPairing X Y V`) is a coevaluation `η : V ⟶ X ⊗ Y` and an evaluation
`ε : Y ⊗ X ⟶ V` whose two zigzags are braidings with `V`:

`Y ⊗ V ⟶ Y ⊗ X ⊗ Y ⟶ V ⊗ Y` is `β_{Y,V}` and `V ⊗ X ⟶ X ⊗ Y ⊗ X ⟶ X ⊗ V` is `β_{V,X}`.

For `V = 𝟙` the braidings are unitors and this is an exact pairing in the sense of Mathlib's
`CategoryTheory.ExactPairing` (`TauCeti.TwistedPairing.ofExactPairing`). Pairings with values in
a line other than the unit arise for orientation lines of Fredholm operators: two determinant
lines are paired into the orientation line of a tangent space rather than into the ground ring,
and the corresponding sewing map starts from that line.

* **Swap.** The braiding turns a pairing of `X` and `Y` twisted by `V` into a pairing of `Y` and
  `X` twisted by `V` (`TauCeti.TwistedPairing.swap`), with coevaluation `η ≫ β_{Y,X}⁻¹` and
  evaluation `β_{X,Y} ≫ ε`, exactly as Mathlib's `CategoryTheory.BraidedCategory.exactPairing_swap`
  does for `V = 𝟙` (`TauCeti.TwistedPairing.ofExactPairing_swap`). Where Mathlib's proof of
  `exactPairing_swap` in `Mathlib/CategoryTheory/Monoidal/Rigid/Braided.lean` uses the
  Yang–Baxter equation, the zigzags here follow from the braid identities
  `TauCeti.whiskerLeft_braiding_inv_comp_braiding_whiskerRight` and
  `TauCeti.braiding_inv_whiskerRight_comp_whiskerLeft_braiding` and naturality of the braiding.
* **Tensor product with an exact pairing.** In a symmetric monoidal category, an exact pairing of
  `X₁` and `Y₁` and a pairing of `X₂` and `Y₂` twisted by `V` give a pairing of `X₁ ⊗ X₂` and
  `Y₂ ⊗ Y₁` twisted by `V` (`TauCeti.TwistedPairing.tensor`). The evaluation contracts `Y₁ ⊗ X₁`
  inside `Y₂ ⊗ X₂`, as in Mathlib's `CategoryTheory.ExactPairing.tensor`; the coevaluation
  braids `Y₁` past `V` before expanding `V` into `X₂ ⊗ Y₂`. For `V = 𝟙` this is Mathlib's tensor
  product of exact pairings (`TauCeti.TwistedPairing.tensor_ofExactPairing`), and the zigzags are
  proved by sliding the inner evaluation past the outer coevaluation, as in Mathlib's proof for
  `ExactPairing.tensor`, with one use of the symmetry of the braiding.

## Main definitions

* `TauCeti.TwistedPairing`: a pairing of `X` and `Y` twisted by `V`.
* `TauCeti.TwistedPairing.ofExactPairing`: an exact pairing as a pairing twisted by the unit.
* `TauCeti.TwistedPairing.swap`: the braided swap of a twisted pairing.
* `TauCeti.TwistedPairing.tensor`: the tensor product of an exact pairing and a twisted pairing.

## References

* P. Etingof, S. Gelaki, D. Nikshych and V. Ostrik, *Tensor categories*, Mathematical Surveys and
  Monographs 205, AMS, 2015, Section 2.10, on exact pairings and the zigzag identities.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- A **pairing of `X` and `Y` twisted by `V`**: a coevaluation `V ⟶ X ⊗ Y` and an evaluation
`Y ⊗ X ⟶ V` whose zigzags `Y ⊗ V ⟶ V ⊗ Y` and `V ⊗ X ⟶ X ⊗ V` are the braidings with `V`. For
`V = 𝟙` this is an exact pairing (`TauCeti.TwistedPairing.ofExactPairing`). -/
@[ext]
structure TwistedPairing (X Y V : C) where
  /-- The coevaluation `V ⟶ X ⊗ Y`. -/
  coevaluation : V ⟶ X ⊗ Y
  /-- The evaluation `Y ⊗ X ⟶ V`. -/
  evaluation : Y ⊗ X ⟶ V
  /-- The zigzag through `Y` is the braiding of `Y` past `V`. -/
  coevaluation_evaluation :
    Y ◁ coevaluation ≫ (α_ Y X Y).inv ≫ evaluation ▷ Y = (β_ Y V).hom
  /-- The zigzag through `X` is the braiding of `V` past `X`. -/
  evaluation_coevaluation :
    coevaluation ▷ X ≫ (α_ X Y X).hom ≫ X ◁ evaluation = (β_ V X).hom

namespace TwistedPairing

/-- An exact pairing of `X` and `Y` is a pairing of `X` and `Y` twisted by the unit: the braidings
of an object with the unit are the unitors. -/
def ofExactPairing (X Y : C) [ExactPairing X Y] : TwistedPairing X Y (𝟙_ C) where
  coevaluation := η_ X Y
  evaluation := ε_ X Y
  coevaluation_evaluation := by
    rw [ExactPairing.coevaluation_evaluation, braiding_tensorUnit_right]
  evaluation_coevaluation := by
    rw [ExactPairing.evaluation_coevaluation, braiding_tensorUnit_left]

/-- The coevaluation of an exact pairing as a twisted pairing. -/
@[simp]
theorem ofExactPairing_coevaluation (X Y : C) [ExactPairing X Y] :
    (ofExactPairing X Y).coevaluation = η_ X Y :=
  (rfl)

/-- The evaluation of an exact pairing as a twisted pairing. -/
@[simp]
theorem ofExactPairing_evaluation (X Y : C) [ExactPairing X Y] :
    (ofExactPairing X Y).evaluation = ε_ X Y :=
  (rfl)

variable {X Y V : C}

/-- The zigzag of the swap through `X`. -/
private theorem swap_coevaluation_evaluation_aux (P : TwistedPairing X Y V) :
    X ◁ (P.coevaluation ≫ (β_ Y X).inv) ≫ (α_ X Y X).inv ≫ ((β_ X Y).hom ≫ P.evaluation) ▷ X =
      (β_ X V).hom := by
  -- Trade the two crossings for braidings with `X ⊗ Y` and `Y ⊗ X`, which naturality turns into
  -- braidings with `V` around the other zigzag of `P`.
  rw [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc,
    whiskerLeft_braiding_inv_comp_braiding_whiskerRight_assoc, braiding_naturality_right_assoc,
    ← braiding_inv_naturality_right, reassoc_of% P.evaluation_coevaluation, Iso.hom_inv_id,
    Category.comp_id]

/-- The zigzag of the swap through `Y`. -/
private theorem swap_evaluation_coevaluation_aux (P : TwistedPairing X Y V) :
    (P.coevaluation ≫ (β_ Y X).inv) ▷ Y ≫ (α_ Y X Y).hom ≫ Y ◁ ((β_ X Y).hom ≫ P.evaluation) =
      (β_ V Y).hom := by
  rw [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    braiding_inv_whiskerRight_comp_whiskerLeft_braiding_assoc, braiding_naturality_left_assoc,
    ← braiding_inv_naturality_left, reassoc_of% P.coevaluation_evaluation, Iso.hom_inv_id,
    Category.comp_id]

/-- The **swap** of a pairing of `X` and `Y` twisted by `V`: the pairing of `Y` and `X` twisted by
`V` with coevaluation `η ≫ β_{Y,X}⁻¹` and evaluation `β_{X,Y} ≫ ε`. For an exact pairing this is
Mathlib's `CategoryTheory.BraidedCategory.exactPairing_swap`
(`TauCeti.TwistedPairing.ofExactPairing_swap`). -/
def swap (P : TwistedPairing X Y V) : TwistedPairing Y X V where
  coevaluation := P.coevaluation ≫ (β_ Y X).inv
  evaluation := (β_ X Y).hom ≫ P.evaluation
  coevaluation_evaluation := swap_coevaluation_evaluation_aux P
  evaluation_coevaluation := swap_evaluation_coevaluation_aux P

/-- The coevaluation of the swap is the coevaluation followed by the inverse braiding. -/
@[simp]
theorem swap_coevaluation (P : TwistedPairing X Y V) :
    P.swap.coevaluation = P.coevaluation ≫ (β_ Y X).inv :=
  (rfl)

/-- The evaluation of the swap is the braiding followed by the evaluation. -/
@[simp]
theorem swap_evaluation (P : TwistedPairing X Y V) :
    P.swap.evaluation = (β_ X Y).hom ≫ P.evaluation :=
  (rfl)

/-- For an exact pairing, the swap of the twisted pairing is the twisted pairing of Mathlib's
swapped exact pairing `CategoryTheory.BraidedCategory.exactPairing_swap`. -/
theorem ofExactPairing_swap (X Y : C) [ExactPairing X Y] :
    (ofExactPairing X Y).swap = @ofExactPairing C _ _ _ Y X (exactPairing_swap X Y) :=
  (rfl)

end TwistedPairing

end Braided

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

namespace TwistedPairing

/-- In a symmetric monoidal category, swapping a twisted pairing twice gives it back. -/
@[simp]
theorem swap_swap {X Y V : C} (P : TwistedPairing X Y V) : P.swap.swap = P := by
  ext
  · rw [swap_coevaluation, swap_coevaluation, Category.assoc,
      ← SymmetricCategory.braiding_swap_eq_inv_braiding Y X, Iso.hom_inv_id, Category.comp_id]
  · simp

/-- The zigzag of the tensor product through `Y₂ ⊗ Y₁`. -/
private theorem tensor_coevaluation_evaluation_aux {X₁ Y₁ X₂ Y₂ V : C} [ExactPairing X₁ Y₁]
    (P : TwistedPairing X₂ Y₂ V) :
    (Y₂ ⊗ Y₁) ◁ ((λ_ V).inv ≫ η_ X₁ Y₁ ▷ V ⊗≫ X₁ ◁ ((β_ Y₁ V).hom ≫ P.coevaluation ▷ Y₁) ⊗≫
        𝟙 ((X₁ ⊗ X₂) ⊗ Y₂ ⊗ Y₁)) ≫ (α_ (Y₂ ⊗ Y₁) (X₁ ⊗ X₂) (Y₂ ⊗ Y₁)).inv ≫
      (𝟙 ((Y₂ ⊗ Y₁) ⊗ X₁ ⊗ X₂) ⊗≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ P.evaluation) ▷ (Y₂ ⊗ Y₁) =
      (β_ (Y₂ ⊗ Y₁) V).hom := by
  -- Slide the evaluation of `Y₁ ⊗ X₁` before the coevaluation of `P`: the zigzag of `Y₁` closes,
  -- leaving the braiding of `Y₁` past `V` and the twisted zigzag of `Y₂`.
  calc
    _ = 𝟙 _ ⊗≫ (Y₂ ⊗ Y₁) ◁ η_ X₁ Y₁ ▷ V ⊗≫
          Y₂ ◁ ((Y₁ ⊗ X₁) ◁ ((β_ Y₁ V).hom ≫ P.coevaluation ▷ Y₁) ≫
            ε_ X₁ Y₁ ▷ ((X₂ ⊗ Y₂) ⊗ Y₁)) ⊗≫ P.evaluation ▷ (Y₂ ⊗ Y₁) := by
      monoidal
    _ = 𝟙 _ ⊗≫ (Y₂ ⊗ Y₁) ◁ η_ X₁ Y₁ ▷ V ⊗≫
          Y₂ ◁ (ε_ X₁ Y₁ ▷ (Y₁ ⊗ V) ≫ 𝟙_ C ◁ ((β_ Y₁ V).hom ≫ P.coevaluation ▷ Y₁)) ⊗≫
            P.evaluation ▷ (Y₂ ⊗ Y₁) := by
      rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ Y₂ ◁ ((Y₁ ◁ η_ X₁ Y₁ ⊗≫ ε_ X₁ Y₁ ▷ Y₁) ▷ V) ⊗≫ Y₂ ◁ (β_ Y₁ V).hom ⊗≫
          (Y₂ ◁ P.coevaluation ≫ (α_ Y₂ X₂ Y₂).inv ≫ P.evaluation ▷ Y₂) ▷ Y₁ ⊗≫ 𝟙 _ := by
      monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation'', P.coevaluation_evaluation,
        braiding_tensor_left_hom]
      monoidal

/-- The zigzag of the tensor product through `X₁ ⊗ X₂`. -/
private theorem tensor_evaluation_coevaluation_aux {X₁ Y₁ X₂ Y₂ V : C} [ExactPairing X₁ Y₁]
    (P : TwistedPairing X₂ Y₂ V) :
    ((λ_ V).inv ≫ η_ X₁ Y₁ ▷ V ⊗≫ X₁ ◁ ((β_ Y₁ V).hom ≫ P.coevaluation ▷ Y₁) ⊗≫
        𝟙 ((X₁ ⊗ X₂) ⊗ Y₂ ⊗ Y₁)) ▷ (X₁ ⊗ X₂) ≫ (α_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) (X₁ ⊗ X₂)).hom ≫
      (X₁ ⊗ X₂) ◁ (𝟙 ((Y₂ ⊗ Y₁) ⊗ X₁ ⊗ X₂) ⊗≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ P.evaluation) =
      (β_ V (X₁ ⊗ X₂)).hom := by
  -- Slide the evaluation of `Y₁ ⊗ X₁` before the coevaluation of `P` and past the braiding of
  -- `Y₁` and `V`, which becomes the braiding of `V` past `X₁` by symmetry; then the zigzag of
  -- `X₁` closes, leaving the twisted zigzag of `X₂`.
  calc
    _ = 𝟙 _ ⊗≫ η_ X₁ Y₁ ▷ (V ⊗ X₁ ⊗ X₂) ⊗≫ X₁ ◁ ((β_ Y₁ V).hom ▷ (X₁ ⊗ X₂)) ⊗≫
          X₁ ◁ ((P.coevaluation ▷ (Y₁ ⊗ X₁) ≫ (X₂ ⊗ Y₂) ◁ ε_ X₁ Y₁) ▷ X₂) ⊗≫
            (X₁ ⊗ X₂) ◁ P.evaluation := by
      monoidal
    _ = 𝟙 _ ⊗≫ η_ X₁ Y₁ ▷ (V ⊗ X₁ ⊗ X₂) ⊗≫ X₁ ◁ ((β_ Y₁ V).hom ▷ (X₁ ⊗ X₂)) ⊗≫
          X₁ ◁ ((V ◁ ε_ X₁ Y₁ ≫ P.coevaluation ▷ 𝟙_ C) ▷ X₂) ⊗≫
            (X₁ ⊗ X₂) ◁ P.evaluation := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ η_ X₁ Y₁ ▷ (V ⊗ X₁ ⊗ X₂) ⊗≫
          X₁ ◁ (((β_ Y₁ V).hom ▷ X₁ ≫ (α_ V Y₁ X₁).hom ≫ V ◁ ε_ X₁ Y₁) ▷ X₂) ⊗≫
            X₁ ◁ (P.coevaluation ▷ X₂ ≫ (α_ X₂ Y₂ X₂).hom ≫ X₂ ◁ P.evaluation) ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ (η_ X₁ Y₁ ▷ (V ⊗ X₁) ≫ (X₁ ⊗ Y₁) ◁ (β_ X₁ V).inv) ▷ X₂ ⊗≫
          X₁ ◁ ε_ X₁ Y₁ ▷ V ▷ X₂ ⊗≫ X₁ ◁ (β_ V X₂).hom ⊗≫ 𝟙 _ := by
      rw [braiding_whiskerRight_comp_whiskerLeft, P.evaluation_coevaluation,
        braiding_tensorUnit_left]
      monoidal
    _ = 𝟙 _ ⊗≫ (β_ X₁ V).inv ▷ X₂ ⊗≫ ((η_ X₁ Y₁ ▷ X₁ ⊗≫ X₁ ◁ ε_ X₁ Y₁) ▷ V) ▷ X₂ ⊗≫
          X₁ ◁ (β_ V X₂).hom ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      monoidal
    _ = _ := by
      rw [ExactPairing.evaluation_coevaluation'',
        ← SymmetricCategory.braiding_swap_eq_inv_braiding, braiding_tensor_right_hom]
      monoidal

/-- The **tensor product** of an exact pairing of `X₁` and `Y₁` with a pairing of `X₂` and `Y₂`
twisted by `V`: the pairing of `X₁ ⊗ X₂` and `Y₂ ⊗ Y₁` twisted by `V` whose evaluation contracts
`Y₁ ⊗ X₁` and then evaluates `Y₂ ⊗ X₂ ⟶ V`, and whose coevaluation expands `𝟙 ⟶ X₁ ⊗ Y₁`, braids
`Y₁` past `V` and then expands `V ⟶ X₂ ⊗ Y₂`. For `V = 𝟙` this is Mathlib's
`CategoryTheory.ExactPairing.tensor` (`TauCeti.TwistedPairing.tensor_ofExactPairing`). -/
def tensor {X₁ Y₁ X₂ Y₂ V : C} [ExactPairing X₁ Y₁] (P : TwistedPairing X₂ Y₂ V) :
    TwistedPairing (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) V where
  coevaluation :=
    (λ_ V).inv ≫ η_ X₁ Y₁ ▷ V ⊗≫ X₁ ◁ ((β_ Y₁ V).hom ≫ P.coevaluation ▷ Y₁) ⊗≫ 𝟙 _
  evaluation := 𝟙 _ ⊗≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ P.evaluation
  coevaluation_evaluation := tensor_coevaluation_evaluation_aux P
  evaluation_coevaluation := tensor_evaluation_coevaluation_aux P

/-- The coevaluation of the tensor product expands `𝟙 ⟶ X₁ ⊗ Y₁`, braids `Y₁` past `V` and
expands `V ⟶ X₂ ⊗ Y₂`. -/
@[simp]
theorem tensor_coevaluation {X₁ Y₁ X₂ Y₂ V : C} [ExactPairing X₁ Y₁] (P : TwistedPairing X₂ Y₂ V) :
    (P.tensor (X₁ := X₁) (Y₁ := Y₁)).coevaluation =
      (λ_ V).inv ≫ η_ X₁ Y₁ ▷ V ⊗≫ X₁ ◁ ((β_ Y₁ V).hom ≫ P.coevaluation ▷ Y₁) ⊗≫ 𝟙 _ :=
  (rfl)

/-- The evaluation of the tensor product contracts `Y₁ ⊗ X₁` and then evaluates
`Y₂ ⊗ X₂ ⟶ V`. -/
@[simp]
theorem tensor_evaluation {X₁ Y₁ X₂ Y₂ V : C} [ExactPairing X₁ Y₁] (P : TwistedPairing X₂ Y₂ V) :
    (P.tensor (X₁ := X₁) (Y₁ := Y₁)).evaluation =
      𝟙 _ ⊗≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ P.evaluation :=
  (rfl)

/-- For two exact pairings, the tensor product of twisted pairings is the twisted pairing of
Mathlib's tensor product of exact pairings `CategoryTheory.ExactPairing.tensor`. -/
theorem tensor_ofExactPairing (X₁ Y₁ X₂ Y₂ : C) [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    (ofExactPairing X₂ Y₂).tensor (X₁ := X₁) (Y₁ := Y₁) = ofExactPairing (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) := by
  ext
  · simp only [tensor_coevaluation, ofExactPairing_coevaluation,
      ExactPairing.tensor_coevaluation, braiding_tensorUnit_right]
    monoidal
  · simp [ExactPairing.tensor_evaluation]

end TwistedPairing

end Symmetric

end TauCeti
