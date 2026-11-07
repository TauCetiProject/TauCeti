/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Braided.TensorPow

/-!
# Tensor powers of actions on underlying objects

For a monoidal category `V`, a monoid `H`, and `X : Action V H`, the underlying object
`(tensorPow X n).V` of the `n`-th tensor power in `Action V H` agrees definitionally with
`tensorPow X.V n` at each concrete `n`, but not uniformly in a variable `n : ℕ` because `tensorPow`
recurses in `Action V H` on the left and in `V` on the right.

`Action.tensorPowVIso X n : (tensorPow X n).V ≅ tensorPow X.V n` constructs the canonical comparison
isomorphism by recursion on `n` using `whiskerLeftIso`, avoiding `eqToHom` casts. It intertwines the
action of `g : H` on `tensorPow X n` with `tensorPowMap (X.ρ g).asHom n`, commutes with
`tensorPowSuccIso`, and, when `V` is braided, intertwines the cyclic shift `tensorPowShiftIso X n`
with `tensorPowShiftIso X.V n`.

## Main declarations

* `Action.tensorPowVIso`: the recursive comparison `(tensorPow X n).V ≅ tensorPow X.V n`, with
  `Action.tensorPowVIso_zero`, `Action.tensorPowVIso_succ`, `Action.tensorPowVIso_succ_hom`, and
  `Action.tensorPowVIso_succ_inv`;
* `Action.ρ_comp_tensorPowVIso_hom`: `tensorPowVIso` intertwines `(tensorPow X n).ρ g` with
  `tensorPowMap (X.ρ g).asHom n`;
* `Action.tensorPowSuccIso_hom_comp_tensorPowVIso_hom` and
  `Action.tensorPowShiftIso_hom_comp_tensorPowVIso_hom`: compatibility of `tensorPowVIso` with
  `tensorPowSuccIso` and `tensorPowShiftIso`.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory TauCeti

namespace Action

variable {V : Type*} [Category* V] [MonoidalCategory V] {H : Type*} [Monoid H]

/-- Recursive comparison isomorphism `(tensorPow X n).V ≅ tensorPow X.V n` on underlying objects,
built by whiskering without object casts. -/
def tensorPowVIso (X : Action V H) : ∀ n : ℕ, (tensorPow X n).V ≅ tensorPow X.V n
  | 0 => Iso.refl (𝟙_ V)
  | n + 1 => whiskerLeftIso X.V (tensorPowVIso X n)

/-- At `n = 0`, `tensorPowVIso` is the identity of `𝟙_ V`. -/
@[simp]
theorem tensorPowVIso_zero (X : Action V H) : tensorPowVIso X 0 = Iso.refl (𝟙_ V) :=
  (rfl)

/-- Recursive step of `tensorPowVIso`. -/
theorem tensorPowVIso_succ (X : Action V H) (n : ℕ) :
    tensorPowVIso X (n + 1) = whiskerLeftIso X.V (tensorPowVIso X n) :=
  (rfl)

/-- Forward morphism of `tensorPowVIso` at `n + 1`. -/
@[simp]
theorem tensorPowVIso_succ_hom (X : Action V H) (n : ℕ) :
    (tensorPowVIso X (n + 1)).hom = X.V ◁ (tensorPowVIso X n).hom :=
  (rfl)

/-- Inverse morphism of `tensorPowVIso` at `n + 1`. -/
@[simp]
theorem tensorPowVIso_succ_inv (X : Action V H) (n : ℕ) :
    (tensorPowVIso X (n + 1)).inv = X.V ◁ (tensorPowVIso X n).inv :=
  (rfl)

/-- `tensorPowVIso` intertwines the action of `g` on `tensorPow X n` with `tensorPowMap` of the
action of `g` on `X`. -/
@[reassoc]
theorem ρ_comp_tensorPowVIso_hom (X : Action V H) (g : H) (n : ℕ) :
    ((tensorPow X n).ρ g).asHom ≫ (tensorPowVIso X n).hom =
      (tensorPowVIso X n).hom ≫ tensorPowMap (X.ρ g).asHom n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [tensorPowVIso_succ_hom]
    rw [tensor_ρ, tensorPowMap_succ, tensorHom_def, Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, ih, MonoidalCategory.whiskerLeft_comp,
      ← whisker_exchange_assoc, ← tensorHom_def]

/-- `tensorPowVIso` commutes with appending a tensor factor on the right via `tensorPowSuccIso`. -/
@[reassoc]
theorem tensorPowSuccIso_hom_comp_tensorPowVIso_hom (X : Action V H) (n : ℕ) :
    (tensorPowSuccIso X n).hom.hom ≫ (tensorPowVIso X (n + 1)).hom =
      (tensorPowVIso X n).hom ▷ X.V ≫ (tensorPowSuccIso X.V n).hom := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := congrArg Hom.hom (tensorPowSuccIso_succ_hom X n)
    simp only [comp_hom, associator_hom_hom, whiskerLeft_hom] at h
    rw [h, tensorPowVIso_succ_hom X (n + 1), Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, ih, tensorPowSuccIso_succ_hom X.V n,
      tensorPowVIso_succ_hom]
    monoidal

/-- In a braided monoidal category, `tensorPowVIso` intertwines the cyclic shift on `tensorPow X`
with the cyclic shift on `tensorPow X.V`. -/
@[reassoc]
theorem tensorPowShiftIso_hom_comp_tensorPowVIso_hom [BraidedCategory V] (X : Action V H) (n : ℕ) :
    (tensorPowShiftIso X n).hom.hom ≫ (tensorPowVIso X (n + 1)).hom =
      (tensorPowVIso X (n + 1)).hom ≫ (tensorPowShiftIso X.V n).hom := by
  rw [tensorPowShiftIso_hom, tensorPowShiftIso_hom, comp_hom, β_hom_hom, Category.assoc,
    tensorPowSuccIso_hom_comp_tensorPowVIso_hom, tensorPowVIso_succ_hom,
    ← braiding_naturality_right_assoc]

end Action
