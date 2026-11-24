/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic

/-!
# Finite ordinals in the augmented simplex category

An object of Mathlib's `AugmentedSimplexCategory` is either the empty ordinal or `⦋n⦌`, and a
morphism is a monotone map of the underlying finite ordinals. This file records this view.

## Main definitions

* `AugmentedSimplexCategory.card`, `AugmentedSimplexCategory.toOrderHom`: the number of elements
  of an object and the monotone map underlying a morphism, with `toOrderHom_id`,
  `toOrderHom_comp` and the extensionality lemma `AugmentedSimplexCategory.hom_ext`.
* `TauCeti.AugmentedSimplexCategory.ofCard`, `TauCeti.AugmentedSimplexCategory.homOfOrderHom`:
  the object with `n` elements and the morphism given by a monotone map, with their
  functoriality and the round trips `card_ofCard`, `AugmentedSimplexCategory.ofCard_card`,
  `toOrderHom_homOfOrderHom` and `homOfOrderHom_toOrderHom`.
-/

public section

open CategoryTheory Simplicial

namespace AugmentedSimplexCategory

open SimplexCategory

/-- The number of elements of an object of the augmented simplex category: `0` for the empty
ordinal and `n + 1` for `⦋n⦌`. -/
@[expose]
def card : AugmentedSimplexCategory → ℕ
  | .star => 0
  | .of x => x.len + 1

@[simp]
lemma card_star : card .star = 0 := rfl

@[simp]
lemma card_of (x : SimplexCategory) : card (.of x) = x.len + 1 := rfl

/-- The monotone map of finite ordinals underlying a morphism of the augmented simplex
category. -/
def toOrderHom : {X Y : AugmentedSimplexCategory} → (X ⟶ Y) → (Fin X.card →o Fin Y.card)
  | .of _, .of _, f => (WithInitial.down f).toOrderHom
  | .star, _, _ => ⟨fun a ↦ a.elim0, fun a ↦ a.elim0⟩
  | .of _, .star, f => (f : PEmpty).elim

@[simp]
lemma toOrderHom_of {x y : SimplexCategory} (f : WithInitial.of x ⟶ WithInitial.of y) :
    toOrderHom f = (WithInitial.down f).toOrderHom := (rfl)

lemma toOrderHom_inclusion_map {x y : SimplexCategory} (f : x ⟶ y) :
    toOrderHom (inclusion.map f) = f.toOrderHom := (rfl)

@[simp]
lemma toOrderHom_id (X : AugmentedSimplexCategory) : toOrderHom (𝟙 X) = OrderHom.id := by
  cases X with
  | of x => exact id_toOrderHom x
  | star => ext a; exact a.elim0

@[simp]
lemma toOrderHom_comp {X Y Z : AugmentedSimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toOrderHom (f ≫ g) = (toOrderHom g).comp (toOrderHom f) :=
  match X, Y, Z, f, g with
  | .of _, .of _, .of _, _, _ => rfl
  | .star, _, _, _, _ => by ext a; exact a.elim0
  | .of _, .star, _, f, _ => (f : PEmpty).elim
  | .of _, .of _, .star, _, g => (g : PEmpty).elim

lemma hom_ext {X Y : AugmentedSimplexCategory} {f g : X ⟶ Y}
    (h : toOrderHom f = toOrderHom g) : f = g :=
  match X, Y, f, g with
  | .of _, .of _, _, _ => Hom.ext _ _ h
  | .star, _, _, _ => (WithInitial.starInitial.hom_ext _ _)
  | .of _, .star, f, _ => (f : PEmpty).elim

end AugmentedSimplexCategory

namespace TauCeti.AugmentedSimplexCategory

open _root_.AugmentedSimplexCategory SimplexCategory

/-- The object of the augmented simplex category with `n` elements: the empty ordinal for
`n = 0` and `⦋n - 1⦌` otherwise. -/
@[expose]
def ofCard : ℕ → AugmentedSimplexCategory
  | 0 => .star
  | n + 1 => .of ⦋n⦌

@[simp]
lemma ofCard_zero : ofCard 0 = .star := rfl

@[simp]
lemma ofCard_succ (n : ℕ) : ofCard (n + 1) = .of ⦋n⦌ := rfl

lemma card_ofCard (n : ℕ) : card (ofCard n) = n := by
  cases n <;> rfl

/-- The morphism of the augmented simplex category given by a monotone map of finite
ordinals. -/
def homOfOrderHom : {n m : ℕ} → (Fin n →o Fin m) → (ofCard n ⟶ ofCard m)
  | 0, _, _ => WithInitial.starInitial.to _
  | _ + 1, 0, f => (f 0).elim0
  | _ + 1, _ + 1, f => (mkHom f : ⦋_⦌ ⟶ ⦋_⦌)

@[simp]
lemma down_homOfOrderHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) :
    WithInitial.down (homOfOrderHom f) = mkHom f := (rfl)

@[simp]
lemma toOrderHom_homOfOrderHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) :
    toOrderHom (homOfOrderHom f) = f := (rfl)

lemma homOfOrderHom_toOrderHom {n m : ℕ} (f : WithInitial.of ⦋n⦌ ⟶ WithInitial.of ⦋m⦌) :
    homOfOrderHom (toOrderHom f) = f :=
  hom_ext (toOrderHom_homOfOrderHom _)

@[simp]
lemma homOfOrderHom_id (n : ℕ) : homOfOrderHom (OrderHom.id : Fin n →o Fin n) = 𝟙 _ := by
  cases n with
  | zero => exact WithInitial.starInitial.hom_ext _ _
  | succ n => rfl

@[simp]
lemma homOfOrderHom_comp {n m p : ℕ} (f : Fin n →o Fin m) (g : Fin m →o Fin p) :
    homOfOrderHom (g.comp f) = homOfOrderHom f ≫ homOfOrderHom g :=
  match n, m, p, f, g with
  | 0, _, _, _, _ => WithInitial.starInitial.hom_ext _ _
  | _ + 1, 0, _, f, _ => (f 0).elim0
  | _ + 1, _ + 1, 0, _, g => (g 0).elim0
  | _ + 1, _ + 1, _ + 1, _, _ => rfl

end TauCeti.AugmentedSimplexCategory

namespace AugmentedSimplexCategory

open TauCeti.AugmentedSimplexCategory

lemma ofCard_card (X : AugmentedSimplexCategory) : ofCard (card X) = X := by
  cases X <;> rfl

end AugmentedSimplexCategory
