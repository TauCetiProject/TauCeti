/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Tensor products of commuting squares in a monoidal category

The interchange law `MonoidalCategory.tensorHom_comp_tensorHom` turns a pair of commuting squares
`f₁ ≫ g₁ = f₁' ≫ g₁'` and `f₂ ≫ g₂ = f₂' ≫ g₂'` in a monoidal category into the commuting square
`(f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁' ⊗ₘ f₂') ≫ (g₁' ⊗ₘ g₂')`. Packaging this—together with
transport across epimorphic quotient maps—avoids repeating `tensorHom_comp_tensorHom` and diagram
chases across intermediate objects that agree up to definitional equality.

## Main results

* `TauCeti.tensorHom_comp_tensorHom_eq`: the tensor product of two commuting squares commutes.
* `TauCeti.tensorHom_comp_eq_of_epi_tensorHom`: transports a commuting square `(a₁ ⊗ₘ a₂) ≫ b' =
  b ≫ a₀` along quotient projections when `p₁ ⊗ₘ p₂` is an epimorphism.
* `TauCeti.comp_tensorHom_eq_of_epi`: transports a commuting square `a₀ ≫ b' = b ≫ (a₁ ⊗ₘ a₂)`
  along quotient projections when `p₀` is an epimorphism.
-/

public section

namespace TauCeti

open CategoryTheory MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- The tensor product of two commuting squares in a monoidal category commutes: if
`f₁ ≫ g₁ = f₁' ≫ g₁'` and `f₂ ≫ g₂ = f₂' ≫ g₂'`, then
`(f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁' ⊗ₘ f₂') ≫ (g₁' ⊗ₘ g₂')`. -/
@[reassoc]
lemma tensorHom_comp_tensorHom_eq {X₁ Y₁ Z₁ W₁ X₂ Y₂ Z₂ W₂ : C}
    {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ W₁} {f₁' : X₁ ⟶ Z₁} {g₁' : Z₁ ⟶ W₁}
    {f₂ : X₂ ⟶ Y₂} {g₂ : Y₂ ⟶ W₂} {f₂' : X₂ ⟶ Z₂} {g₂' : Z₂ ⟶ W₂}
    (h₁ : f₁ ≫ g₁ = f₁' ≫ g₁') (h₂ : f₂ ≫ g₂ = f₂' ≫ g₂') :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁' ⊗ₘ f₂') ≫ (g₁' ⊗ₘ g₂') := by
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, h₁, h₂]

/-- Transporting a commuting square `(a₁ ⊗ₘ a₂) ≫ b' = b ≫ a₀` across quotient projections:
if `p₁ ⊗ₘ p₂` is an epimorphism and `r`, `r'` intertwine `p₁ ⊗ₘ p₂`, `p₁' ⊗ₘ p₂'` with `b`, `b'`
through `q₀`, `q₀'`, then `(q₁ ⊗ₘ q₂) ≫ r' = r ≫ q₃`. -/
lemma tensorHom_comp_eq_of_epi_tensorHom
    {X₁ X₂ Y₁ Y₂ X₁' X₂' Y₁' Y₂' Z Z' W W' : C}
    {p₁ : X₁ ⟶ Y₁} {p₂ : X₂ ⟶ Y₂} [Epi (p₁ ⊗ₘ p₂)]
    {p₁' : X₁' ⟶ Y₁'} {p₂' : X₂' ⟶ Y₂'}
    {q₁ : Y₁ ⟶ Y₁'} {q₂ : Y₂ ⟶ Y₂'} {a₁ : X₁ ⟶ X₁'} {a₂ : X₂ ⟶ X₂'}
    {b : X₁ ⊗ X₂ ⟶ Z} {b' : X₁' ⊗ X₂' ⟶ Z'} {q₀ : Z ⟶ W} {q₀' : Z' ⟶ W'}
    {a₀ : Z ⟶ Z'} {q₃ : W ⟶ W'} {r : Y₁ ⊗ Y₂ ⟶ W} {r' : Y₁' ⊗ Y₂' ⟶ W'}
    (h₁ : p₁ ≫ q₁ = a₁ ≫ p₁') (h₂ : p₂ ≫ q₂ = a₂ ≫ p₂')
    (hr : (p₁ ⊗ₘ p₂) ≫ r = b ≫ q₀) (hr' : (p₁' ⊗ₘ p₂') ≫ r' = b' ≫ q₀')
    (hb : (a₁ ⊗ₘ a₂) ≫ b' = b ≫ a₀) (hq : a₀ ≫ q₀' = q₀ ≫ q₃) :
    (q₁ ⊗ₘ q₂) ≫ r' = r ≫ q₃ := by
  rw [← cancel_epi (p₁ ⊗ₘ p₂)]
  calc (p₁ ⊗ₘ p₂) ≫ (q₁ ⊗ₘ q₂) ≫ r'
      = ((a₁ ⊗ₘ a₂) ≫ (p₁' ⊗ₘ p₂')) ≫ r' := by
        rw [← Category.assoc, tensorHom_comp_tensorHom_eq h₁ h₂]
    _ = (a₁ ⊗ₘ a₂) ≫ b' ≫ q₀' := by rw [Category.assoc, hr']
    _ = b ≫ a₀ ≫ q₀' := by rw [← Category.assoc, hb, Category.assoc]
    _ = (b ≫ q₀) ≫ q₃ := by rw [hq, ← Category.assoc]
    _ = (p₁ ⊗ₘ p₂) ≫ r ≫ q₃ := by rw [← hr, Category.assoc]

/-- Transporting a commuting square `a₀ ≫ b' = b ≫ (a₁ ⊗ₘ a₂)` across quotient projections:
if `p₀` is an epimorphism and `r`, `r'` intertwine `p₀`, `p₀'` with `b`, `b'` through
`p₁ ⊗ₘ p₂`, `p₁' ⊗ₘ p₂'`, then `q₀ ≫ r' = r ≫ (q₁ ⊗ₘ q₂)`. -/
lemma comp_tensorHom_eq_of_epi
    {W W' Z Z' X₁ X₂ Y₁ Y₂ X₁' X₂' Y₁' Y₂' : C}
    {p₀ : Z ⟶ W} [Epi p₀] {p₀' : Z' ⟶ W'} {q₀ : W ⟶ W'} {a₀ : Z ⟶ Z'}
    {p₁ : X₁ ⟶ Y₁} {p₂ : X₂ ⟶ Y₂} {p₁' : X₁' ⟶ Y₁'} {p₂' : X₂' ⟶ Y₂'}
    {q₁ : Y₁ ⟶ Y₁'} {q₂ : Y₂ ⟶ Y₂'} {a₁ : X₁ ⟶ X₁'} {a₂ : X₂ ⟶ X₂'}
    {b : Z ⟶ X₁ ⊗ X₂} {b' : Z' ⟶ X₁' ⊗ X₂'} {r : W ⟶ Y₁ ⊗ Y₂} {r' : W' ⟶ Y₁' ⊗ Y₂'}
    (h₀ : p₀ ≫ q₀ = a₀ ≫ p₀') (h₁ : a₁ ≫ p₁' = p₁ ≫ q₁) (h₂ : a₂ ≫ p₂' = p₂ ≫ q₂)
    (hr : p₀ ≫ r = b ≫ (p₁ ⊗ₘ p₂)) (hr' : p₀' ≫ r' = b' ≫ (p₁' ⊗ₘ p₂'))
    (hb : a₀ ≫ b' = b ≫ (a₁ ⊗ₘ a₂)) :
    q₀ ≫ r' = r ≫ (q₁ ⊗ₘ q₂) := by
  rw [← cancel_epi p₀]
  calc p₀ ≫ q₀ ≫ r'
      = a₀ ≫ p₀' ≫ r' := by rw [← Category.assoc, h₀, Category.assoc]
    _ = (a₀ ≫ b') ≫ (p₁' ⊗ₘ p₂') := by rw [hr', Category.assoc]
    _ = b ≫ (a₁ ⊗ₘ a₂) ≫ (p₁' ⊗ₘ p₂') := by rw [hb, Category.assoc]
    _ = (b ≫ (p₁ ⊗ₘ p₂)) ≫ (q₁ ⊗ₘ q₂) := by
        rw [tensorHom_comp_tensorHom_eq h₁ h₂, Category.assoc]
    _ = p₀ ≫ r ≫ (q₁ ⊗ₘ q₂) := by rw [← hr, Category.assoc]

end TauCeti
