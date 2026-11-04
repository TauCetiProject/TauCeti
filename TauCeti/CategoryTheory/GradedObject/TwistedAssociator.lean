/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Graded objects with a twisted associator

Let `C` be an `R`-linear monoidal category, over a commutative semiring `R`, and let `I` be an
additive monoid. Mathlib makes `GradedObject I C` a monoidal category
(`CategoryTheory.GradedObject.monoidalCategory`): the tensor product of `X₁` and `X₂` is the
coproduct of the objects `X₁ i₁ ⊗ X₂ i₂` with `i₁ + i₂ = j` in degree `j`, and the associator acts
on each summand `(X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃` by the associator of `C`.

Given a function `ω : I → I → I → Rˣ`, this file twists that associator by `ω`: the
*twisted associator* `GradedObject.Monoidal.twistedAssociator ω X₁ X₂ X₃` acts on the summand
`(X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃` by `ω i₁ i₂ i₃` times the associator of `C`. It is natural for every
`ω`. It satisfies the pentagon axiom when `ω` satisfies the `3`-cocycle identity

`ω (i₁ + i₂) i₃ i₄ * ω i₁ i₂ (i₃ + i₄) = ω i₂ i₃ i₄ * ω i₁ (i₂ + i₃) i₄ * ω i₁ i₂ i₃`

(the multiplicative `3`-cocycle condition `TauCeti.groupCohomology.IsMulCocycle₃` for the trivial
action, written additively in the degrees), since the two sides of the pentagon multiply the
summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⊗ X₄ i₄` by the two sides of this identity. It satisfies the
triangle axiom, with the unchanged unitors, when `ω i₁ 0 i₃ = 1`, as for a normalized cocycle.
Under these two conditions `GradedObject.twistedMonoidalCategory ω hω h₀` is a monoidal structure
on `GradedObject I C`.

For a group `G`, a field `k`, and a normalized `3`-cocycle `ω` of `G` with values in `kˣ`, taking
`I = Additive G` and `C` the category of `k`-vector spaces gives the twisted associator of the
pointed categories `Vec^ω_G` of `G`-graded vector spaces.

## Main declarations

* `CategoryTheory.GradedObject.Monoidal.twistedAssociator`: the twisted associator, characterized
  by `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_twistedAssociator_hom` and
  `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_twistedAssociator_inv`, with the untwisted
  associator as the case `ω = 1` (`CategoryTheory.GradedObject.Monoidal.twistedAssociator_one`).
* `CategoryTheory.GradedObject.Monoidal.twistedAssociator_pentagon`: the pentagon axiom for a
  `3`-cocycle.
* `CategoryTheory.GradedObject.Monoidal.twistedAssociator_triangle`: the triangle axiom when
  `ω i₁ 0 i₃ = 1`.
* `CategoryTheory.GradedObject.twistedMonoidalCategory`: the resulting monoidal structure on
  `GradedObject I C`.

## Implementation notes

The twisted associator is the untwisted associator followed by the automorphism of
`tensorObj X₁ (tensorObj X₂ X₃)` acting on the summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃` by `ω i₁ i₂ i₃`.
The proof of the pentagon axiom follows the proof of
`CategoryTheory.GradedObject.Monoidal.pentagon_inv` in
`Mathlib/CategoryTheory/GradedObject/Monoidal.lean` (Joël Riou, Kim Morrison), keeping track of the
scalars, and the monoidal structure is assembled as in
`CategoryTheory.GradedObject.monoidalCategory`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.3 (the
  categories `Vec^ω_G`)
-/

public section

noncomputable section

universe u

namespace CategoryTheory.GradedObject

open Limits MonoidalCategory Category

variable {I : Type u} [AddMonoid I] {C : Type*} [Category* C] [MonoidalCategory C]
  {R : Type*} [CommSemiring R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C]

namespace Monoidal

section Smul

variable (c : I → I → I → R) (X₁ X₂ X₃ : GradedObject I C) [HasTensor X₂ X₃]
  [HasTensor X₁ (tensorObj X₂ X₃)]

/-- The endomorphism of `tensorObj X₁ (tensorObj X₂ X₃)` acting by the scalar `c i₁ i₂ i₃` on
the summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃`. -/
private def tensorObj₃Smul : tensorObj X₁ (tensorObj X₂ X₃) ⟶ tensorObj X₁ (tensorObj X₂ X₃) :=
  fun j ↦ tensorObjDesc fun i₁ i₂₃ h ↦
    X₁ i₁ ◁ tensorObjDesc (fun i₂ i₃ h' ↦ c i₁ i₂ i₃ • ιTensorObj X₂ X₃ i₂ i₃ i₂₃ h') ≫
      ιTensorObj X₁ (tensorObj X₂ X₃) i₁ i₂₃ j h

@[reassoc]
private lemma ιTensorObj₃_tensorObj₃Smul (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorObj₃Smul c X₁ X₂ X₃ j =
      c i₁ i₂ i₃ • ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃, assoc, tensorObj₃Smul, ι_tensorObjDesc, ← whiskerLeft_comp_assoc,
    ι_tensorObjDesc, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]

variable [HasGoodTensorTensor₂₃ X₁ X₂ X₃]

private lemma tensorObj₃Smul_comp (d : I → I → I → R) :
    tensorObj₃Smul c X₁ X₂ X₃ ≫ tensorObj₃Smul d X₁ X₂ X₃ = tensorObj₃Smul (c * d) X₁ X₂ X₃ := by
  ext j i₁ i₂ i₃ h
  simp [ιTensorObj₃_tensorObj₃Smul_assoc, ιTensorObj₃_tensorObj₃Smul, smul_smul]

private lemma tensorObj₃Smul_one : tensorObj₃Smul (1 : I → I → I → R) X₁ X₂ X₃ = 𝟙 _ := by
  ext j i₁ i₂ i₃ h
  simp [ιTensorObj₃_tensorObj₃Smul]

/-- `tensorObj₃Smul` for a family of units, as an automorphism. -/
private def tensorObj₃SmulIso (u : I → I → I → Rˣ) :
    tensorObj X₁ (tensorObj X₂ X₃) ≅ tensorObj X₁ (tensorObj X₂ X₃) where
  hom := tensorObj₃Smul (fun i₁ i₂ i₃ ↦ (u i₁ i₂ i₃ : R)) X₁ X₂ X₃
  inv := tensorObj₃Smul (fun i₁ i₂ i₃ ↦ (((u i₁ i₂ i₃)⁻¹ : Rˣ) : R)) X₁ X₂ X₃
  hom_inv_id := by
    rw [tensorObj₃Smul_comp, ← tensorObj₃Smul_one (R := R)]
    congr
    ext
    simp
  inv_hom_id := by
    rw [tensorObj₃Smul_comp, ← tensorObj₃Smul_one (R := R)]
    congr
    ext
    simp

end Smul

section TwistedAssociator

variable (ω : I → I → I → Rˣ) (X₁ X₂ X₃ : GradedObject I C)
  [HasTensor X₁ X₂] [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₂ X₃]
  [HasTensor X₁ (tensorObj X₂ X₃)]
  [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The associator of graded objects twisted by `ω`: on the summand `(X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃` it
is the associator of `C` multiplied by the scalar `ω i₁ i₂ i₃`. -/
def twistedAssociator :
    tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃) :=
  associator X₁ X₂ X₃ ≪≫ tensorObj₃SmulIso X₁ X₂ X₃ ω

/-- On the summand `(X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃`, the twisted associator is `ω i₁ i₂ i₃` times the
associator of `C`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃'_twistedAssociator_hom (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (twistedAssociator ω X₁ X₂ X₃).hom j =
      (ω i₁ i₂ i₃ : R) • ((α_ _ _ _).hom ≫ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) := by
  simp [twistedAssociator, tensorObj₃SmulIso, ιTensorObj₃_tensorObj₃Smul]

/-- On the summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃`, the inverse of the twisted associator is
`(ω i₁ i₂ i₃)⁻¹` times the inverse associator of `C`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃_twistedAssociator_inv (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (twistedAssociator ω X₁ X₂ X₃).inv j =
      (((ω i₁ i₂ i₃)⁻¹ : Rˣ) : R) • ((α_ _ _ _).inv ≫ ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h) := by
  simp [twistedAssociator, tensorObj₃SmulIso, ιTensorObj₃_tensorObj₃Smul_assoc]

/-- The associator twisted by the constant function `1` is the untwisted associator. -/
@[simp]
lemma twistedAssociator_one :
    twistedAssociator (1 : I → I → I → Rˣ) X₁ X₂ X₃ = associator X₁ X₂ X₃ := by
  ext j i₁ i₂ i₃ h
  simp

variable {X₁ X₂ X₃} {Y₁ Y₂ Y₃ : GradedObject I C}
  [HasTensor Y₁ Y₂] [HasTensor (tensorObj Y₁ Y₂) Y₃] [HasTensor Y₂ Y₃]
  [HasTensor Y₁ (tensorObj Y₂ Y₃)]
  [HasGoodTensor₁₂Tensor Y₁ Y₂ Y₃] [HasGoodTensorTensor₂₃ Y₁ Y₂ Y₃] in
/-- The twisted associator is natural, for any `ω`. -/
lemma twistedAssociator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (twistedAssociator ω Y₁ Y₂ Y₃).hom =
      (twistedAssociator ω X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  ext j i₁ i₂ i₃ h
  simp

end TwistedAssociator

section Pentagon

variable (ω : I → I → I → Rˣ) (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₁ X₂] [HasTensor X₂ X₃] [HasTensor X₃ X₄]
  [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)]
  [HasTensor (tensorObj X₂ X₃) X₄] [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor (tensorObj (tensorObj X₁ X₂) X₃) X₄]
  [HasTensor (tensorObj X₁ (tensorObj X₂ X₃)) X₄]
  [HasTensor X₁ (tensorObj (tensorObj X₂ X₃) X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]
  [HasTensor (tensorObj X₁ X₂) (tensorObj X₃ X₄)]
  [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasGoodTensor₁₂Tensor X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensorTensor₂₃ X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensor₁₂Tensor X₂ X₃ X₄] [HasGoodTensorTensor₂₃ X₂ X₃ X₄]
  [HasGoodTensor₁₂Tensor (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensorTensor₂₃ (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensor₁₂Tensor X₁ X₂ (tensorObj X₃ X₄)]
  [HasGoodTensorTensor₂₃ X₁ X₂ (tensorObj X₃ X₄)]
  [HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- The pentagon axiom for the inverses of the twisted associators, when `ω` satisfies the
`3`-cocycle identity. -/
@[reassoc]
lemma twistedAssociator_pentagon_inv
    (hω : ∀ i₁ i₂ i₃ i₄ : I,
      ω (i₁ + i₂) i₃ i₄ * ω i₁ i₂ (i₃ + i₄) = ω i₂ i₃ i₄ * ω i₁ (i₂ + i₃) i₄ * ω i₁ i₂ i₃) :
    tensorHom (𝟙 X₁) (twistedAssociator ω X₂ X₃ X₄).inv ≫
        (twistedAssociator ω X₁ (tensorObj X₂ X₃) X₄).inv ≫
          tensorHom (twistedAssociator ω X₁ X₂ X₃).inv (𝟙 X₄) =
      (twistedAssociator ω X₁ X₂ (tensorObj X₃ X₄)).inv ≫
        (twistedAssociator ω (tensorObj X₁ X₂) X₃ X₄).inv := by
  -- On the summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⊗ X₄ i₄`, both sides are computed as in the proof of
  -- `GradedObject.Monoidal.pentagon_inv`, pulling out the scalar after each twisted associator.
  -- The remaining morphisms agree by the pentagon axiom of `C`, and the scalars by `hω`.
  ext j i₁ i₂ i₃ i₄ h
  dsimp only [categoryOfGradedObjects_comp]
  conv_lhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h _ rfl, assoc, ι_tensorHom_assoc]
    dsimp only [categoryOfGradedObjects_id, id_eq, eq_mpr_eq_cast, cast_eq]
    rw [id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ιTensorObj₃_twistedAssociator_inv]
    simp only [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, assoc]
    rw [ιTensorObj₃'_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, MonoidalCategory.whiskerLeft_comp_assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) _ rfl, ιTensorObj₃_twistedAssociator_inv_assoc]
    simp only [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, assoc]
    rw [ιTensorObj₃'_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) (i₁ + i₂ + i₃) (by rw [add_assoc]), ι_tensorHom]
    dsimp only [id_eq, eq_mpr_eq_cast, categoryOfGradedObjects_id]
    rw [tensorHom_id, whisker_assoc_symm_assoc, Iso.hom_inv_id_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl, ιTensorObj₃_twistedAssociator_inv]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, assoc]
    rw [MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.pentagon_inv_assoc]
  conv_rhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ _ _ _ rfl,
      ιTensorObj₃_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) (i₂ + i₃ + i₄) (by rw [add_assoc]),
      ιTensorObj₃_twistedAssociator_inv_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    rw [associator_inv_naturality_right_assoc,
      ιTensorObj₃'_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) _ rfl, whisker_exchange_assoc,
      ← ιTensorObj₃_eq_assoc (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ιTensorObj₃_twistedAssociator_inv]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    rw [whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
      ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃'_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]
  rw [smul_smul, smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul,
    ← mul_inv, ← mul_inv, ← mul_inv, ← hω, mul_comm]

/-- The pentagon axiom for the twisted associator, when `ω` satisfies the `3`-cocycle identity. -/
lemma twistedAssociator_pentagon
    (hω : ∀ i₁ i₂ i₃ i₄ : I,
      ω (i₁ + i₂) i₃ i₄ * ω i₁ i₂ (i₃ + i₄) = ω i₂ i₃ i₄ * ω i₁ (i₂ + i₃) i₄ * ω i₁ i₂ i₃) :
    tensorHom (twistedAssociator ω X₁ X₂ X₃).hom (𝟙 X₄) ≫
        (twistedAssociator ω X₁ (tensorObj X₂ X₃) X₄).hom ≫
          tensorHom (𝟙 X₁) (twistedAssociator ω X₂ X₃ X₄).hom =
      (twistedAssociator ω (tensorObj X₁ X₂) X₃ X₄).hom ≫
        (twistedAssociator ω X₁ X₂ (tensorObj X₃ X₄)).hom := by
  rw [← cancel_epi (twistedAssociator ω (tensorObj X₁ X₂) X₃ X₄).inv,
    ← cancel_epi (twistedAssociator ω X₁ X₂ (tensorObj X₃ X₄)).inv, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, ← twistedAssociator_pentagon_inv_assoc ω X₁ X₂ X₃ X₄ hω]
  simp [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]

end Pentagon

section Triangle

variable (ω : I → I → I → Rˣ) [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  (X₁ X₃ : GradedObject I C)
  [HasTensor (tensorObj X₁ tensorUnit) X₃] [HasTensor X₁ (tensorObj tensorUnit X₃)]
  [HasGoodTensor₁₂Tensor X₁ tensorUnit X₃] [HasGoodTensorTensor₂₃ X₁ tensorUnit X₃]

/-- A twist which is trivial whenever the middle degree is `0` does not change the associator
with the tensor unit in the middle. -/
lemma twistedAssociator_tensorUnit (h₀ : ∀ i₁ i₃ : I, ω i₁ 0 i₃ = 1) :
    twistedAssociator ω X₁ tensorUnit X₃ = associator X₁ tensorUnit X₃ := by
  ext j i₁ i₂ i₃ h
  by_cases hi₂ : i₂ = 0
  · subst hi₂
    simp [h₀]
  · exact ((((isInitialTensorUnitApply i₂ hi₂).isInitialObj
      ((curriedTensor C).obj (X₁ i₁))).isInitialObj
        ((curriedTensor C).flip.obj (X₃ i₃)))).hom_ext _ _

/-- The triangle axiom for the twisted associator and the untwisted unitors, when `ω` is trivial
whenever the middle degree is `0`. -/
lemma twistedAssociator_triangle [HasTensor X₁ X₃] (h₀ : ∀ i₁ i₃ : I, ω i₁ 0 i₃ = 1) :
    (twistedAssociator ω X₁ tensorUnit X₃).hom ≫ tensorHom (𝟙 X₁) (leftUnitor X₃).hom =
      tensorHom (rightUnitor X₁).hom (𝟙 X₃) := by
  rw [twistedAssociator_tensorUnit ω X₁ X₃ h₀]
  exact triangle X₁ X₃

end Triangle

end Monoidal

section

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- The monoidal structure on `GradedObject I C` whose tensor product, unit and unitors are those
of `GradedObject.monoidalCategory`, and whose associator is twisted by `ω`. -/
abbrev twistedMonoidalCategory (ω : I → I → I → Rˣ)
    (hω : ∀ i₁ i₂ i₃ i₄ : I,
      ω (i₁ + i₂) i₃ i₄ * ω i₁ i₂ (i₃ + i₄) = ω i₂ i₃ i₄ * ω i₁ (i₂ + i₃) i₄ * ω i₁ i₂ i₃)
    (h₀ : ∀ i₁ i₃ : I, ω i₁ 0 i₃ = 1) : MonoidalCategory (GradedObject I C) where
  tensorObj X Y := Monoidal.tensorObj X Y
  tensorHom f g := Monoidal.tensorHom f g
  tensorHom_def f g := Monoidal.tensorHom_def f g
  whiskerLeft X _ _ φ := Monoidal.whiskerLeft X φ
  whiskerRight {_ _ φ Y} := Monoidal.whiskerRight φ Y
  tensorUnit := Monoidal.tensorUnit
  associator X₁ X₂ X₃ := Monoidal.twistedAssociator ω X₁ X₂ X₃
  associator_naturality f₁ f₂ f₃ := Monoidal.twistedAssociator_naturality ω f₁ f₂ f₃
  leftUnitor X := Monoidal.leftUnitor X
  leftUnitor_naturality := Monoidal.leftUnitor_naturality
  rightUnitor X := Monoidal.rightUnitor X
  rightUnitor_naturality := Monoidal.rightUnitor_naturality
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := Monoidal.tensorHom_comp_tensorHom f₁ g₁ f₂ g₂
  pentagon X₁ X₂ X₃ X₄ := Monoidal.twistedAssociator_pentagon ω X₁ X₂ X₃ X₄ hω
  triangle X₁ X₂ := Monoidal.twistedAssociator_triangle ω X₁ X₂ h₀

end

end CategoryTheory.GradedObject
