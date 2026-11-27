/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Exchanging the exponent and the source of a map into an internal Hom

In a braided monoidal category `C` with closed objects `A` and `B`, the maps `B ⟶ (A ⟶[C] X)`
and `A ⟶ (B ⟶[C] X)` both correspond to the maps `A ⊗ B ⟶ X`, the second one through the braiding
`B ⊗ A ≅ A ⊗ B`. The resulting bijection `MonoidalClosed.ihomSwapEquiv A B X` exchanges the roles
of the exponent and of the source. It turns precomposition in the source into precomposition with
`pre` in the exponent, and conversely; in a symmetric monoidal category it is an involution
(`MonoidalClosed.ihomSwapEquiv_symm`).

For simplicial sets, a map `B ⟶ Fun(Δ[n], X)` is a family of `n`-simplices of `X` parametrized by
`B`, and the bijection presents it as a single `n`-simplex of the functor complex `Fun(B, X)`.
Horn filling in `Fun(B, X)` thus becomes horn filling for families parametrized by `B`.

## Main declarations

* `MonoidalClosed.ihomSwapEquiv A B X : (B ⟶ (A ⟶[C] X)) ≃ (A ⟶ (B ⟶[C] X))`, an involution
  in a symmetric monoidal category (`MonoidalClosed.ihomSwapEquiv_symm`).
* `MonoidalClosed.ihomSwapEquiv_comp_pre_app`, `MonoidalClosed.ihomSwapEquiv_comp`: its
  naturality in the exponent and in the source.
-/

public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

universe v u

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- In a braided monoidal category, the maps `B ⟶ (A ⟶[C] X)` correspond to the maps
`A ⟶ (B ⟶[C] X)`, for closed objects `A` and `B`: both are curried forms of maps `A ⊗ B ⟶ X`, up
to the braiding.

This packages the transposition `curry ((β_ _ _).hom ≫ uncurry _)` used inline earlier in the
proof of `SSet.Edge.isEquivalence_iff_forall_isEquivalence_map_evalAt`. -/
noncomputable def ihomSwapEquiv (A B X : C) [Closed A] [Closed B] :
    (B ⟶ (ihom A).obj X) ≃ (A ⟶ (ihom B).obj X) :=
  ((ihom.adjunction A).homEquiv B X).symm.trans <|
    ((β_ B A).symm.homCongr (Iso.refl X)).trans ((ihom.adjunction B).homEquiv A X)

variable {A A' B B' X : C}

/-- The exchange of exponent and source curries the braided uncurried map. -/
lemma ihomSwapEquiv_apply [Closed A] [Closed B] (g : B ⟶ (ihom A).obj X) :
    ihomSwapEquiv A B X g = curry ((β_ B A).hom ≫ uncurry g) := by
  simp [ihomSwapEquiv, curry, uncurry]

/-- The inverse exchange curries the uncurried map composed with the inverse braiding. -/
lemma ihomSwapEquiv_symm_apply [Closed A] [Closed B] (g : A ⟶ (ihom B).obj X) :
    (ihomSwapEquiv A B X).symm g = curry ((β_ B A).inv ≫ uncurry g) := by
  simp [ihomSwapEquiv, curry, uncurry]

/-- Exchanging exponent and source turns precomposition with `pre f` into precomposition with
`f`. -/
lemma ihomSwapEquiv_comp_pre_app [Closed A] [Closed A'] [Closed B] (f : A' ⟶ A)
    (g : B ⟶ (ihom A).obj X) :
    ihomSwapEquiv A' B X (g ≫ (pre f).app X) = f ≫ ihomSwapEquiv A B X g := by
  rw [ihomSwapEquiv_apply, ihomSwapEquiv_apply, uncurry_pre_app,
    ← BraidedCategory.braiding_naturality_right_assoc, curry_natural_left]

/-- Exchanging exponent and source turns precomposition with `i` into precomposition with
`pre i`. -/
lemma ihomSwapEquiv_comp [Closed A] [Closed B] [Closed B'] (i : B' ⟶ B)
    (g : B ⟶ (ihom A).obj X) :
    ihomSwapEquiv A B' X (i ≫ g) = ihomSwapEquiv A B X g ≫ (pre i).app X := by
  rw [ihomSwapEquiv_apply, ihomSwapEquiv_apply, uncurry_natural_left,
    ← BraidedCategory.braiding_naturality_left_assoc, curry_pre_app]

end Braided

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- In a symmetric monoidal category, exchanging exponent and source is an involution. -/
@[simp]
lemma ihomSwapEquiv_symm (A B X : C) [Closed A] [Closed B] :
    (ihomSwapEquiv A B X).symm = ihomSwapEquiv B A X := by
  ext g
  rw [ihomSwapEquiv_symm_apply, ihomSwapEquiv_apply,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding]

end Symmetric

end CategoryTheory.MonoidalClosed
