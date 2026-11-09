/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Cyclic shifts of tensor powers in braided monoidal categories

In a braided monoidal category `C`, the first factor of `tensorPow X (n + 1) = X ⊗ tensorPow X n`
can be braided past `tensorPow X n` and re-bracketed onto the right using `tensorPowSuccIso X n`.
This gives the cyclic shift automorphism `TauCeti.tensorPowShiftIso X n` of `tensorPow X (n + 1)`.

For `n = 0` the shift is the identity (`TauCeti.tensorPowShiftIso_zero`), and for `n + 1` it
factors into a single braiding of the first two factors followed by the shift on the remaining
`n + 1` factors (`TauCeti.tensorPowShiftIso_succ_hom`). In a symmetric rigid category with its
canonical pivotal structure (`TauCeti.symmetricPivotalCategory`), composing with
`tensorPowShiftIso X n` computes the Ng–Schauenburg Frobenius–Schur rotation operator.

## Main declarations

* `TauCeti.tensorPowShiftIso`: the cyclic shift automorphism of `tensorPow X (n + 1)` in a braided
  monoidal category;
* `TauCeti.tensorPowShiftIso_zero` and `TauCeti.tensorPowShiftIso_succ_hom`: base case and
  recursive decomposition of the cyclic shift;
* `TauCeti.tensorPowShiftIso_hom_naturality`: naturality with respect to `tensorPowMap`.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The cyclic shift automorphism of `tensorPow X (n + 1)` in a braided monoidal category: braid
the first factor `X` past `tensorPow X n` and re-bracket on the right. -/
def tensorPowShiftIso (X : C) (n : ℕ) : tensorPow X (n + 1) ≅ tensorPow X (n + 1) :=
  β_ X (tensorPow X n) ≪≫ tensorPowSuccIso X n

/-- The forward morphism of `tensorPowShiftIso`. -/
theorem tensorPowShiftIso_hom (X : C) (n : ℕ) :
    (tensorPowShiftIso X n).hom = (β_ X (tensorPow X n)).hom ≫ (tensorPowSuccIso X n).hom :=
  (rfl)

/-- The inverse morphism of `tensorPowShiftIso`. -/
theorem tensorPowShiftIso_inv (X : C) (n : ℕ) :
    (tensorPowShiftIso X n).inv = (tensorPowSuccIso X n).inv ≫ (β_ X (tensorPow X n)).inv :=
  (rfl)

/-- On the first tensor power `X ⊗ 𝟙_ C`, the cyclic shift is the identity. -/
@[simp]
theorem tensorPowShiftIso_zero (X : C) :
    tensorPowShiftIso X 0 = Iso.refl (tensorPow X 1) := by
  ext
  simp [tensorPowShiftIso_hom, braiding_tensorUnit_right]

/-- Recursive decomposition of the cyclic shift on `tensorPow X (n + 2)`: swap the first two
factors with the braiding, then apply the cyclic shift on the remaining `n + 1` factors. -/
theorem tensorPowShiftIso_succ_hom (X : C) (n : ℕ) :
    (tensorPowShiftIso X (n + 1)).hom =
      (α_ X X (tensorPow X n)).inv ≫ (β_ X X).hom ▷ tensorPow X n ≫
        (α_ X X (tensorPow X n)).hom ≫ X ◁ (tensorPowShiftIso X n).hom := by
  rw [tensorPowShiftIso_hom, tensorPowShiftIso_hom, braiding_tensor_right_hom,
    tensorPowSuccIso_succ_hom]
  simp [MonoidalCategory.whiskerLeft_comp]

/-- The cyclic shift commutes with the tensor powers of any morphism. -/
@[reassoc]
theorem tensorPowShiftIso_hom_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorPowMap f (n + 1) ≫ (tensorPowShiftIso Y n).hom =
      (tensorPowShiftIso X n).hom ≫ tensorPowMap f (n + 1) := by
  rw [tensorPowShiftIso_hom, tensorPowShiftIso_hom, tensorPowMap_succ,
    braiding_naturality_assoc, tensorPowSuccIso_hom_naturality, tensorPowMap_succ, Category.assoc]

end TauCeti
