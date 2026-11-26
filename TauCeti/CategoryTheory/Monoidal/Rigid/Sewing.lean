/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Sewing of functionals along an exact pairing

Let `(Y, X)` be an exact pairing in a monoidal category, with coevaluation `η : 𝟙 ⟶ Y ⊗ X` and
evaluation `ε : X ⊗ Y ⟶ 𝟙`. The **sewing** of functionals `F : A ⊗ Y ⟶ 𝟙` and
`G : X ⊗ Z ⟶ 𝟙` along the pairing (`TauCeti.ExactPairing.sewing`) inserts the coevaluation
between `A` and `Z` and applies `F ⊗ G`:

`A ⊗ Z ⟶ A ⊗ (Y ⊗ X) ⊗ Z ≅ (A ⊗ Y) ⊗ (X ⊗ Z) ⟶ 𝟙`.

A morphism `T : A ⟶ X` gives the functional `T ▷ Y ≫ ε` on `A ⊗ Y`, and sewing it with `G` is
`T ▷ Z ≫ G` (`TauCeti.ExactPairing.sewing_whiskerRight_comp_evaluation`). Dually, sewing `F` with
the functional `X ◁ U ≫ ε` of a morphism `U : Z ⟶ Y` is `A ◁ U ≫ F`
(`TauCeti.ExactPairing.sewing_whiskerLeft_comp_evaluation`). Both are the snake identities of the
pairing; in particular the evaluation is a unit for sewing on either side. Sewing along two
pairings is associative by the interchange law alone (`TauCeti.ExactPairing.sewing_assoc`).

## Main definitions

* `TauCeti.ExactPairing.sewing`: the sewing of functionals on `A ⊗ Y` and `X ⊗ Z` along an exact
  pairing `(Y, X)` into a functional on `A ⊗ Z`.

## Main results

* `TauCeti.ExactPairing.sewing_whiskerRight_comp_evaluation` and
  `TauCeti.ExactPairing.sewing_whiskerLeft_comp_evaluation`: sewing with the functional of a
  morphism composes with that morphism.
* `TauCeti.ExactPairing.sewing_evaluation_left` and `TauCeti.ExactPairing.sewing_evaluation_right`:
  the evaluation is a unit for sewing.
* `TauCeti.ExactPairing.sewing_assoc`: sewing is associative.

## References

* P. Etingof, S. Gelaki, D. Nikshych and V. Ostrik, *Tensor categories*, Mathematical Surveys and
  Monographs 205, AMS, 2015, Section 2.10, on exact pairings and the snake identities.
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

namespace ExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The **sewing** of a functional `F` on `A ⊗ Y` and a functional `G` on `X ⊗ Z` along an exact
pairing `(Y, X)`: the functional on `A ⊗ Z` that inserts the coevaluation `𝟙 ⟶ Y ⊗ X` between `A`
and `Z` and applies `F ⊗ G`: `A ⊗ Z ⟶ A ⊗ (Y ⊗ X) ⊗ Z ≅ (A ⊗ Y) ⊗ (X ⊗ Z) ⟶ 𝟙`. -/
def sewing {A Y X Z : C} [ExactPairing Y X] (F : A ⊗ Y ⟶ 𝟙_ C) (G : X ⊗ Z ⟶ 𝟙_ C) :
    A ⊗ Z ⟶ 𝟙_ C :=
  (ρ_ A).inv ▷ Z ⊗≫ (A ◁ η_ Y X) ▷ Z ⊗≫ (F ⊗ₘ G) ≫ (λ_ _).hom

variable {A Y X Z : C} [ExactPairing Y X]

/-- The sewing inserts the coevaluation of the pairing and applies `F ⊗ G`. -/
lemma sewing_def (F : A ⊗ Y ⟶ 𝟙_ C) (G : X ⊗ Z ⟶ 𝟙_ C) :
    sewing F G = (ρ_ A).inv ▷ Z ⊗≫ (A ◁ η_ Y X) ▷ Z ⊗≫ (F ⊗ₘ G) ≫ (λ_ _).hom :=
  (rfl)

/-- **Sewing with the functional of a morphism on the left.** Sewing the functional
`T ▷ Y ≫ ε` of `T : A ⟶ X` with a functional `G` on `X ⊗ Z` is `T ▷ Z ≫ G`. -/
@[simp]
theorem sewing_whiskerRight_comp_evaluation (T : A ⟶ X) (G : X ⊗ Z ⟶ 𝟙_ C) :
    sewing (T ▷ Y ≫ ε_ Y X) G = T ▷ Z ≫ G := by
  rw [sewing_def]
  -- Pull `T` below the coevaluation; the remaining zigzag of `(Y, X)` is the identity of `X`.
  calc
    _ = 𝟙 _ ⊗≫ (A ◁ η_ Y X ≫ T ▷ (Y ⊗ X)) ▷ Z ⊗≫ ε_ Y X ▷ X ▷ Z ⊗≫ G := by
      rw [tensorHom_def]
      monoidal
    _ = 𝟙 _ ⊗≫ (T ▷ 𝟙_ _ ≫ X ◁ η_ Y X) ▷ Z ⊗≫ ε_ Y X ▷ X ▷ Z ⊗≫ G := by
      rw [whisker_exchange]
    _ = T ▷ Z ⊗≫ (X ◁ η_ Y X ⊗≫ ε_ Y X ▷ X) ▷ Z ⊗≫ G := by
      monoidal
    _ = T ▷ Z ≫ G := by
      rw [CategoryTheory.ExactPairing.coevaluation_evaluation'']
      monoidal

/-- **Sewing with the functional of a morphism on the right.** Sewing a functional `F` on `A ⊗ Y`
with the functional `X ◁ U ≫ ε` of `U : Z ⟶ Y` is `A ◁ U ≫ F`. -/
@[simp]
theorem sewing_whiskerLeft_comp_evaluation (F : A ⊗ Y ⟶ 𝟙_ C) (U : Z ⟶ Y) :
    sewing F (X ◁ U ≫ ε_ Y X) = A ◁ U ≫ F := by
  rw [sewing_def]
  -- Pull `U` above the coevaluation; the remaining zigzag of `(Y, X)` is the identity of `Y`.
  calc
    _ = 𝟙 _ ⊗≫ A ◁ (η_ Y X ▷ Z ≫ (Y ⊗ X) ◁ U) ⊗≫ A ◁ Y ◁ ε_ Y X ⊗≫ F := by
      rw [tensorHom_def']
      monoidal
    _ = 𝟙 _ ⊗≫ A ◁ (𝟙_ _ ◁ U ≫ η_ Y X ▷ Y) ⊗≫ A ◁ Y ◁ ε_ Y X ⊗≫ F := by
      rw [← whisker_exchange]
    _ = A ◁ U ⊗≫ A ◁ (η_ Y X ▷ Y ⊗≫ Y ◁ ε_ Y X) ⊗≫ F := by
      monoidal
    _ = A ◁ U ≫ F := by
      rw [CategoryTheory.ExactPairing.evaluation_coevaluation'']
      monoidal

/-- **The evaluation is a left unit for sewing.** Sewing the evaluation `X ⊗ Y ⟶ 𝟙` of the pairing
with a functional `G` on `X ⊗ Z` gives `G`. -/
@[simp]
theorem sewing_evaluation_left (G : X ⊗ Z ⟶ 𝟙_ C) : sewing (ε_ Y X) G = G := by
  simpa using sewing_whiskerRight_comp_evaluation (Y := Y) (𝟙 X) G

/-- **The evaluation is a right unit for sewing.** Sewing a functional `F` on `A ⊗ Y` with the
evaluation `X ⊗ Y ⟶ 𝟙` of the pairing gives `F`. -/
@[simp]
theorem sewing_evaluation_right (F : A ⊗ Y ⟶ 𝟙_ C) : sewing F (ε_ Y X) = F := by
  simpa using sewing_whiskerLeft_comp_evaluation (X := X) F (𝟙 Y)

/-- **Sewing is associative.** For exact pairings `(Y, X)` and `(Y', X')` and functionals on
`A ⊗ Y`, `X ⊗ Y'` and `X' ⊗ W`, sewing along `(Y, X)` and then along `(Y', X')` gives the same
functional on `A ⊗ W` as sewing along `(Y', X')` and then along `(Y, X)`. -/
theorem sewing_assoc {Y' X' W : C} [ExactPairing Y' X'] (F : A ⊗ Y ⟶ 𝟙_ C)
    (G : X ⊗ Y' ⟶ 𝟙_ C) (H : X' ⊗ W ⟶ 𝟙_ C) :
    sewing (sewing F G) H = sewing F (sewing G H) := by
  -- Both sides insert the two coevaluations and then apply `F`, `G` and `H`; they differ only in
  -- the order of independent steps, which the interchange law exchanges.
  calc
    _ = 𝟙 _ ⊗≫ A ◁ (𝟙_ _ ◁ η_ Y' X' ≫ η_ Y X ▷ (Y' ⊗ X')) ▷ W ⊗≫
          F ▷ (X ⊗ Y' ⊗ X' ⊗ W) ⊗≫ G ▷ (X' ⊗ W) ⊗≫ H := by
      simp only [sewing_def, tensorHom_def]
      monoidal
    _ = 𝟙 _ ⊗≫ A ◁ (η_ Y X ▷ 𝟙_ _ ≫ (Y ⊗ X) ◁ η_ Y' X') ▷ W ⊗≫
          F ▷ (X ⊗ Y' ⊗ X' ⊗ W) ⊗≫ G ▷ (X' ⊗ W) ⊗≫ H := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ A ◁ η_ Y X ▷ W ⊗≫
          ((A ⊗ Y) ◁ (X ◁ η_ Y' X' ▷ W) ≫ F ▷ (X ⊗ (Y' ⊗ X') ⊗ W)) ⊗≫
            G ▷ (X' ⊗ W) ⊗≫ H := by
      monoidal
    _ = 𝟙 _ ⊗≫ A ◁ η_ Y X ▷ W ⊗≫ (F ▷ (X ⊗ 𝟙_ _ ⊗ W) ≫ 𝟙_ _ ◁ (X ◁ η_ Y' X' ▷ W)) ⊗≫
          G ▷ (X' ⊗ W) ⊗≫ H := by
      rw [whisker_exchange]
    _ = _ := by
      simp only [sewing_def, tensorHom_def]
      monoidal

end ExactPairing

end TauCeti
