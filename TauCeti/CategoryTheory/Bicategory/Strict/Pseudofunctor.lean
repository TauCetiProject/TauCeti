/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor

/-!
# Pasting the commutative-square isomorphisms of a pseudofunctor

For a pseudofunctor `F` out of a strict bicategory and a commutative square
`t ≫ r = l ≫ b`, Mathlib's `Pseudofunctor.isoMapOfCommSq` is the isomorphism
`F t ≫ F r ≅ F l ≫ F b`. This file proves that these isomorphisms are compatible with pasting
squares: horizontally, the isomorphism of a composite square is the pasting of the isomorphisms of
its two halves, up to the composition comparisons `F.mapComp'` of the top and bottom edges; and
vertically, the same with the left and right edges. Degenerate squares with identity edges are
handled by `F.mapId'`.

Squares in a locally discrete bicategory are the naturality squares of a natural transformation,
and these four identities are exactly the unit and composition conditions for the naturality
isomorphisms `F (f φ) ≫ F (α y) ≅ F (α x) ≫ F (g φ)` to form a strong transformation, and for
those strong transformations to depend functorially on `α`
(see `CategoryTheory.Pseudofunctor.mapNatTrans`).

## Main results

* `CategoryTheory.Pseudofunctor.isoMapOfCommSq_hom_whiskerLeft_mapId'` and
  `CategoryTheory.Pseudofunctor.isoMapOfCommSq_hom_whiskerLeft_mapComp'`: the square
  isomorphisms are compatible with identity and composite top and bottom edges;
* `CategoryTheory.Pseudofunctor.isoMapOfCommSq_hom_whiskerRight_mapId'` and
  `CategoryTheory.Pseudofunctor.isoMapOfCommSq_hom_whiskerRight_mapComp'`: the square
  isomorphisms are compatible with identity and composite left and right edges.
-/

public section

namespace CategoryTheory.Pseudofunctor

open Bicategory

variable {B₀ : Type*} [Bicategory B₀] [Strict B₀] {C : Type*} [Bicategory C] (F : B₀ ⥤ᵖ C)

/-- For a commutative square whose top and bottom edges are identities, the square isomorphism
`F t ≫ F u ≅ F u ≫ F b` is the composite of the unit comparisons of the top and bottom edges with
the unitors. -/
lemma isoMapOfCommSq_hom_whiskerLeft_mapId' {X Y : B₀} {t : X ⟶ X} {u : X ⟶ Y} {b : Y ⟶ Y}
    (sq : CommSq t u u b) (ht : t = 𝟙 X) (hb : b = 𝟙 Y) :
    (F.isoMapOfCommSq sq).hom ≫ F.map u ◁ (F.mapId' b hb).hom =
      (F.mapId' t ht).hom ▷ F.map u ≫ (λ_ _).hom ≫ (ρ_ _).inv := by
  subst ht hb
  rw [isoMapOfCommSq_horiz_id, mapId'_eq_mapId, mapId'_eq_mapId]
  simp

/-- Horizontal pasting: the square isomorphism of the composite of two horizontally adjacent
commutative squares is the pasting of their square isomorphisms, up to the composition
comparisons of the top edges `t₁ ≫ t₂ = t` and the bottom edges `b₁ ≫ b₂ = b`. -/
lemma isoMapOfCommSq_hom_whiskerLeft_mapComp' {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : B₀}
    {t₁ : X₁ ⟶ Y₁} {t₂ : Y₁ ⟶ Z₁} {t : X₁ ⟶ Z₁} {l : X₁ ⟶ X₂} {m : Y₁ ⟶ Y₂} {r : Z₁ ⟶ Z₂}
    {b₁ : X₂ ⟶ Y₂} {b₂ : Y₂ ⟶ Z₂} {b : X₂ ⟶ Z₂}
    (sq₁ : CommSq t₁ l m b₁) (sq₂ : CommSq t₂ m r b₂) (sq : CommSq t l r b)
    (ht : t₁ ≫ t₂ = t) (hb : b₁ ≫ b₂ = b) :
    (F.isoMapOfCommSq sq).hom ≫ F.map l ◁ (F.mapComp' b₁ b₂ b hb).hom =
      (F.mapComp' t₁ t₂ t ht).hom ▷ F.map r ≫ (α_ _ _ _).hom ≫
        F.map t₁ ◁ (F.isoMapOfCommSq sq₂).hom ≫ (α_ _ _ _).inv ≫
          (F.isoMapOfCommSq sq₁).hom ▷ F.map b₂ ≫ (α_ _ _ _).hom := by
  subst ht hb
  have hd : (t₁ ≫ t₂) ≫ r = l ≫ b₁ ≫ b₂ := by
    rw [Category.assoc, sq₂.w, ← Category.assoc, sq₁.w, Category.assoc]
  have hm : t₁ ≫ m ≫ b₂ = l ≫ b₁ ≫ b₂ := by rw [← Category.assoc, sq₁.w, Category.assoc]
  rw [F.isoMapOfCommSq_eq sq (l ≫ b₁ ≫ b₂) hd, F.isoMapOfCommSq_eq sq₁ (l ≫ b₁) sq₁.w,
    F.isoMapOfCommSq_eq sq₂ (m ≫ b₂) sq₂.w]
  -- Both sides are compared through the factorization `t₁ ≫ (m ≫ b₂)` of the diagonal.
  have h₁ := F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom t₁ t₂ r (t₁ ≫ t₂) (m ≫ b₂)
    (l ≫ b₁ ≫ b₂) rfl sq₂.w hd
  have h₂ := F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom t₁ m b₂ (l ≫ b₁) (m ≫ b₂)
    (l ≫ b₁ ≫ b₂) sq₁.w rfl hm
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom l b₁ b₂ (l ≫ b₁) (b₁ ≫ b₂)
    (l ≫ b₁ ≫ b₂) rfl rfl rfl]
  calc _ = ((F.mapComp' (t₁ ≫ t₂) r (l ≫ b₁ ≫ b₂) hd).inv ≫
          (F.mapComp' t₁ (m ≫ b₂) (l ≫ b₁ ≫ b₂) hm).hom) ≫
        ((F.mapComp' t₁ (m ≫ b₂) (l ≫ b₁ ≫ b₂) hm).inv ≫
          (F.mapComp' (l ≫ b₁) b₂ (l ≫ b₁ ≫ b₂) (Category.assoc _ _ _)).hom) ≫
        (F.mapComp' l b₁ (l ≫ b₁)).hom ▷ F.map b₂ ≫ (α_ _ _ _).hom := by simp
    _ = _ := by rw [h₁, h₂]; simp

/-- For a commutative square whose left and right edges are identities, the square isomorphism
`F t ≫ F r ≅ F l ≫ F t` is the composite of the unit comparisons of the left and right edges
with the unitors. -/
lemma isoMapOfCommSq_hom_whiskerRight_mapId' {X Y : B₀} {t : X ⟶ Y} {l : X ⟶ X} {r : Y ⟶ Y}
    (sq : CommSq t l r t) (hl : l = 𝟙 X) (hr : r = 𝟙 Y) :
    (F.isoMapOfCommSq sq).hom ≫ (F.mapId' l hl).hom ▷ F.map t =
      F.map t ◁ (F.mapId' r hr).hom ≫ (ρ_ _).hom ≫ (λ_ _).inv := by
  subst hl hr
  rw [isoMapOfCommSq_vert_id, mapId'_eq_mapId, mapId'_eq_mapId]
  simp

/-- Vertical pasting: the square isomorphism of the composite of two vertically adjacent
commutative squares is the pasting of their square isomorphisms, up to the composition
comparisons of the left edges `l₁ ≫ l₂ = l` and the right edges `r₁ ≫ r₂ = r`. -/
lemma isoMapOfCommSq_hom_whiskerRight_mapComp' {X₁ Y₁ X₂ Y₂ X₃ Y₃ : B₀}
    {t : X₁ ⟶ Y₁} {l₁ : X₁ ⟶ X₂} {r₁ : Y₁ ⟶ Y₂} {m : X₂ ⟶ Y₂} {l₂ : X₂ ⟶ X₃} {r₂ : Y₂ ⟶ Y₃}
    {b : X₃ ⟶ Y₃} {l : X₁ ⟶ X₃} {r : Y₁ ⟶ Y₃}
    (sq₁ : CommSq t l₁ r₁ m) (sq₂ : CommSq m l₂ r₂ b) (sq : CommSq t l r b)
    (hl : l₁ ≫ l₂ = l) (hr : r₁ ≫ r₂ = r) :
    (F.isoMapOfCommSq sq).hom ≫ (F.mapComp' l₁ l₂ l hl).hom ▷ F.map b =
      F.map t ◁ (F.mapComp' r₁ r₂ r hr).hom ≫ (α_ _ _ _).inv ≫
        (F.isoMapOfCommSq sq₁).hom ▷ F.map r₂ ≫ (α_ _ _ _).hom ≫
          F.map l₁ ◁ (F.isoMapOfCommSq sq₂).hom ≫ (α_ _ _ _).inv := by
  subst hl hr
  have hd : t ≫ r₁ ≫ r₂ = (l₁ ≫ l₂) ≫ b := by
    rw [← Category.assoc, sq₁.w, Category.assoc, sq₂.w, Category.assoc]
  have he : (l₁ ≫ m) ≫ r₂ = (l₁ ≫ l₂) ≫ b := by
    rw [Category.assoc, sq₂.w, Category.assoc]
  rw [F.isoMapOfCommSq_eq sq _ hd, F.isoMapOfCommSq_eq sq₁ (l₁ ≫ m) sq₁.w,
    F.isoMapOfCommSq_eq sq₂ (l₂ ≫ b) sq₂.w]
  -- Both sides are compared after composing with the comparison of `t ≫ (r₁ ≫ r₂)`, through
  -- the factorization `l₁ ≫ (l₂ ≫ b)` of the diagonal.
  rw [← cancel_epi (F.mapComp' t (r₁ ≫ r₂) _ hd).hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    comp_whiskerRight, whiskerLeft_comp]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight l₁ l₂ b (l₁ ≫ l₂) (l₂ ≫ b) _ rfl rfl
      (by rw [Category.assoc]),
    F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_assoc t r₁ r₂ (l₁ ≫ m) (r₁ ≫ r₂) _
      sq₁.w rfl hd]
  simp only [Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_assoc l₁ m r₂ (l₁ ≫ m) (l₂ ≫ b) _ rfl
      sq₂.w he]
  simp

end CategoryTheory.Pseudofunctor
