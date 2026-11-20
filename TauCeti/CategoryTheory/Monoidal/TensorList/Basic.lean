/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic
public import TauCeti.CategoryTheory.Monoidal.Opposite

/-!
# Right-associated tensor products of finite lists

For an indexed family `f : α → C` in a monoidal category `C` and `L : List α`,
`TauCeti.tensorList f L` is the right-associated tensor product of the entries of `L` ending in
`𝟙_ C`: `tensorList f [] = 𝟙_ C` and `tensorList f (a :: L) = f a ⊗ tensorList f L`. On
`List.replicate n a`, it reduces definitionally to `TauCeti.tensorPow (f a) n`.

* `TauCeti.tensorListAppendIso` and `TauCeti.tensorListAppendIso_assoc`: block concatenation
  `tensorList f L ⊗ tensorList f M ≅ tensorList f (L ++ M)` and its pentagon-coherent associativity;
* `TauCeti.tensorListCongrHom`, `TauCeti.tensorListCongrIso`, `TauCeti.tensorListMapIso`, and
  `TauCeti.tensorListFlatMapIso`: functoriality in the indexing family, list mapping, and
  flattening;
* `CategoryTheory.Functor.mapTensorListIso` and `CategoryTheory.Functor.opMopTensorListIso`:
  covariant and contravariant (`C ⥤ (Dᵒᵖ)ᴹᵒᵖ`) strong monoidal comparisons, together with monoidal
  naturality (`CategoryTheory.NatTrans.app_comp_mapTensorListIso_hom` and
  `CategoryTheory.NatTrans.unmop_unop_app_comp_opMopTensorListIso_hom`).
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

universe v₁ v₂ u₁ u₂

namespace TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] {α β : Type*}

-- Reducible so `tensorList f (a :: L)` and `tensorList f []` elaborate as `f a ⊗ _` and `𝟙_ C`.
/-- Right-associated tensor product of a list indexed by `f : α → C`, ending in `𝟙_ C`. -/
@[expose, reducible]
def tensorList (f : α → C) : List α → C
  | [] => 𝟙_ C
  | a :: L => f a ⊗ tensorList f L

theorem tensorList_nil (f : α → C) : tensorList f [] = 𝟙_ C := by rfl
theorem tensorList_cons (f : α → C) (a : α) (L : List α) :
    tensorList f (a :: L) = f a ⊗ tensorList f L := by rfl

/-- On a replicated list, `tensorList` agrees with `tensorPow`. -/
@[simp] theorem tensorList_replicate (f : α → C) (n : ℕ) (a : α) :
    tensorList f (List.replicate n a) = tensorPow (f a) n := by
  induction n with | zero => rfl | succ _ ih => exact congrArg (f a ⊗ ·) ih

/-- Right-unitor identification `tensorList f [a] ≅ f a` on a singleton list. -/
def tensorListSingletonIso (f : α → C) (a : α) : tensorList f [a] ≅ f a := ρ_ (f a)

@[simp] theorem tensorListSingletonIso_hom (f : α → C) (a : α) :
    (tensorListSingletonIso f a).hom = (ρ_ (f a)).hom := by rfl
@[simp] theorem tensorListSingletonIso_inv (f : α → C) (a : α) :
    (tensorListSingletonIso f a).inv = (ρ_ (f a)).inv := by rfl

/-- Block concatenation isomorphism `tensorList f L ⊗ tensorList f M ≅ tensorList f (L ++ M)`. -/
def tensorListAppendIso (f : α → C) :
    (L M : List α) → tensorList f L ⊗ tensorList f M ≅ tensorList f (L ++ M)
  | [], M => λ_ (tensorList f M)
  | a :: L, M => α_ (f a) (tensorList f L) (tensorList f M) ≪≫
      whiskerLeftIso (f a) (tensorListAppendIso f L M)

@[simp] theorem tensorListAppendIso_nil (f : α → C) (M : List α) :
    tensorListAppendIso f [] M = λ_ (tensorList f M) := by rfl
theorem tensorListAppendIso_cons (f : α → C) (a : α) (L M : List α) :
    tensorListAppendIso f (a :: L) M = α_ (f a) (tensorList f L) (tensorList f M) ≪≫
      whiskerLeftIso (f a) (tensorListAppendIso f L M) := by rfl
theorem tensorListAppendIso_cons_hom (f : α → C) (a : α) (L M : List α) :
    (tensorListAppendIso f (a :: L) M).hom = (α_ (f a) (tensorList f L) (tensorList f M)).hom ≫
      f a ◁ (tensorListAppendIso f L M).hom := by rfl
theorem tensorListAppendIso_cons_inv (f : α → C) (a : α) (L M : List α) :
    (tensorListAppendIso f (a :: L) M).inv = f a ◁ (tensorListAppendIso f L M).inv ≫
      (α_ (f a) (tensorList f L) (tensorList f M)).inv := by rfl

/-- Concatenating a singleton left block acts by the right unitor on `f a`. -/
theorem tensorListAppendIso_singleton_hom (f : α → C) (a : α) (M : List α) :
    (tensorListAppendIso f [a] M).hom = (ρ_ (f a)).hom ▷ tensorList f M := by
  rw [tensorListAppendIso_cons_hom, tensorListAppendIso_nil]; monoidal_coherence
theorem tensorListAppendIso_singleton_inv (f : α → C) (a : α) (M : List α) :
    (tensorListAppendIso f [a] M).inv = (ρ_ (f a)).inv ▷ tensorList f M := by
  rw [tensorListAppendIso_cons_inv, tensorListAppendIso_nil]; monoidal_coherence

/-- Concatenating an empty right block agrees with the right unitor up to `List.append_nil`. -/
theorem tensorListAppendIso_nil_right_hom (f : α → C) (L : List α) :
    (tensorListAppendIso f L []).hom =
      (ρ_ (tensorList f L)).hom ≫ eqToHom (congrArg (tensorList f) (List.append_nil L).symm) := by
  induction L with
  | nil => exact unitors_equal.trans (Category.comp_id _).symm
  | cons a L ih =>
    rw [tensorListAppendIso_cons_hom, ih]; simp only [MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.whiskerLeft_eqToHom, MonoidalCategory.whiskerLeft_rightUnitor,
      Category.assoc, Iso.hom_inv_id_assoc]

/-- **Associativity of block concatenation**: splitting `(L ++ M) ++ N` in either order agrees up
to `List.append_assoc`. -/
theorem tensorListAppendIso_assoc (f : α → C) (L M N : List α) :
    (tensorListAppendIso f L M).hom ▷ tensorList f N ≫ (tensorListAppendIso f (L ++ M) N).hom =
      (α_ (tensorList f L) (tensorList f M) (tensorList f N)).hom ≫
        tensorList f L ◁ (tensorListAppendIso f M N).hom ≫
        (tensorListAppendIso f L (M ++ N)).hom ≫
        eqToHom (congrArg (tensorList f) (List.append_assoc L M N).symm) := by
  induction L with
  | nil => simp [tensorListAppendIso_nil, leftUnitor_whiskerRight]
  | cons a L ih =>
    calc _ = (α_ (f a) (tensorList f L) (tensorList f M)).hom ▷ tensorList f N ≫
          (α_ (f a) (tensorList f L ⊗ tensorList f M) (tensorList f N)).hom ≫
          f a ◁ ((tensorListAppendIso f L M).hom ▷ tensorList f N ≫
            (tensorListAppendIso f (L ++ M) N).hom) := by
          dsimp only [List.cons_append]
          rw [tensorListAppendIso_cons_hom, tensorListAppendIso_cons_hom]; monoidal
      _ = _ := by
          rw [ih]; simp only [tensorListAppendIso_cons_hom, MonoidalCategory.whiskerLeft_comp,
            MonoidalCategory.whiskerLeft_eqToHom]
          rw [← cancel_mono (eqToHom (congrArg (tensorList f) (List.append_assoc (a :: L) M N)))]
          simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]; monoidal

/-! ### Functoriality in the indexing family -/

/-- Tensor product of a pointwise family of morphisms `φ a : f₁ a ⟶ f₂ a` along `L : List α`. -/
def tensorListCongrHom {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) :
    (L : List α) → tensorList f₁ L ⟶ tensorList f₂ L
  | [] => 𝟙 (𝟙_ C)
  | a :: L => φ a ⊗ₘ tensorListCongrHom φ L

@[simp] theorem tensorListCongrHom_nil {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) :
    tensorListCongrHom φ [] = 𝟙 (𝟙_ C) := by rfl
@[simp] theorem tensorListCongrHom_cons {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) (a : α)
    (L : List α) : tensorListCongrHom φ (a :: L) = φ a ⊗ₘ tensorListCongrHom φ L := by rfl

/-- Pointwise identities induce the identity morphism on `tensorList f L`. -/
@[simp] theorem tensorListCongrHom_id (f : α → C) (L : List α) :
    tensorListCongrHom (fun a ↦ 𝟙 (f a)) L = 𝟙 (tensorList f L) := by
  induction L with | nil => rfl | cons _ _ ih => rw [tensorListCongrHom_cons, ih, id_tensorHom_id]

/-- Pointwise composites induce the composite morphism on `tensorList`. -/
@[simp, reassoc]
theorem tensorListCongrHom_comp {f₁ f₂ f₃ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a)
    (ψ : ∀ a, f₂ a ⟶ f₃ a) (L : List α) :
    tensorListCongrHom (fun a ↦ φ a ≫ ψ a) L =
      tensorListCongrHom φ L ≫ tensorListCongrHom ψ L := by
  induction L with
  | nil => exact (Category.comp_id _).symm
  | cons _ _ ih => simp [ih, tensorHom_comp_tensorHom]

@[reassoc]
theorem tensorListCongrHom_eqToHom {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) {L M : List α}
    (h : L = M) :
    tensorListCongrHom φ L ≫ eqToHom (congrArg (tensorList f₂) h) =
      eqToHom (congrArg (tensorList f₁) h) ≫ tensorListCongrHom φ M := by subst h; simp

/-- Tensor product of a pointwise family of isomorphisms `e a : f₁ a ≅ f₂ a` along `L : List α`. -/
def tensorListCongrIso {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : List α) :
    tensorList f₁ L ≅ tensorList f₂ L where
  hom := tensorListCongrHom (fun a ↦ (e a).hom) L
  inv := tensorListCongrHom (fun a ↦ (e a).inv) L
  hom_inv_id := by simp [← tensorListCongrHom_comp]
  inv_hom_id := by simp [← tensorListCongrHom_comp]

@[simp] theorem tensorListCongrIso_hom {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : List α) :
    (tensorListCongrIso e L).hom = tensorListCongrHom (fun a ↦ (e a).hom) L := by rfl
@[simp] theorem tensorListCongrIso_inv {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : List α) :
    (tensorListCongrIso e L).inv = tensorListCongrHom (fun a ↦ (e a).inv) L := by rfl

/-- Block concatenation is natural with respect to `tensorListCongrHom`. -/
@[reassoc]
theorem tensorListAppendIso_hom_naturality {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) (L M : List α) :
    (tensorListCongrHom φ L ⊗ₘ tensorListCongrHom φ M) ≫ (tensorListAppendIso f₂ L M).hom =
      (tensorListAppendIso f₁ L M).hom ≫ tensorListCongrHom φ (L ++ M) := by
  induction L with
  | nil => simp [tensorListAppendIso_nil]
  | cons a L ih =>
    dsimp only [List.cons_append]; rw [tensorListAppendIso_cons_hom, tensorListAppendIso_cons_hom,
      tensorListCongrHom_cons, tensorListCongrHom_cons]
    calc _ = (α_ (f₁ a) (tensorList f₁ L) (tensorList f₁ M)).hom ≫
          (φ a ⊗ₘ ((tensorListCongrHom φ L ⊗ₘ tensorListCongrHom φ M) ≫
            (tensorListAppendIso f₂ L M).hom)) := by monoidal
      _ = _ := by rw [ih, tensorHom_def', tensorHom_def' (φ a)]; monoidal

/-! ### Mapping and flattening lists -/

/-- Structural isomorphism `tensorList (fun a ↦ g (h a)) L ≅ tensorList g (L.map h)`. -/
def tensorListMapIso (g : β → C) (h : α → β) :
    (L : List α) → tensorList (fun a ↦ g (h a)) L ≅ tensorList g (L.map h)
  | [] => Iso.refl (𝟙_ C)
  | a :: L => whiskerLeftIso (g (h a)) (tensorListMapIso g h L)

@[simp] theorem tensorListMapIso_nil (g : β → C) (h : α → β) :
    tensorListMapIso g h [] = Iso.refl (𝟙_ C) := by rfl
@[simp] theorem tensorListMapIso_cons_hom (g : β → C) (h : α → β) (a : α) (L : List α) :
    (tensorListMapIso g h (a :: L)).hom = g (h a) ◁ (tensorListMapIso g h L).hom := by rfl
@[simp] theorem tensorListMapIso_cons_inv (g : β → C) (h : α → β) (a : α) (L : List α) :
    (tensorListMapIso g h (a :: L)).inv = g (h a) ◁ (tensorListMapIso g h L).inv := by rfl

/-- Object-level equality `tensorList g (L.map h) = tensorList (fun a ↦ g (h a)) L`. -/
theorem tensorList_map (g : β → C) (h : α → β) (L : List α) :
    tensorList g (L.map h) = tensorList (fun a ↦ g (h a)) L := by
  induction L with | nil => rfl | cons a _ ih => exact congrArg (g (h a) ⊗ ·) ih

/-- `(tensorListMapIso g h L).hom` agrees with `eqToHom (tensorList_map g h L).symm`. -/
theorem tensorListMapIso_hom_eq_eqToHom (g : β → C) (h : α → β) (L : List α) :
    (tensorListMapIso g h L).hom = eqToHom (tensorList_map g h L).symm := by
  induction L with | nil => rfl | cons _ _ ih => simp [ih, MonoidalCategory.whiskerLeft_eqToHom]
theorem tensorListMapIso_inv_eq_eqToHom (g : β → C) (h : α → β) (L : List α) :
    (tensorListMapIso g h L).inv = eqToHom (tensorList_map g h L) := by
  rw [← cancel_epi (tensorListMapIso g h L).hom, Iso.hom_inv_id, tensorListMapIso_hom_eq_eqToHom,
    eqToHom_trans, eqToHom_refl]

/-- `tensorListMapIso` commutes with block concatenation `tensorListAppendIso`. -/
@[reassoc]
theorem tensorListMapIso_append_hom (g : β → C) (h : α → β) (L M : List α) :
    (tensorListAppendIso (fun a ↦ g (h a)) L M).hom ≫ (tensorListMapIso g h (L ++ M)).hom =
      ((tensorListMapIso g h L).hom ⊗ₘ (tensorListMapIso g h M).hom) ≫
        (tensorListAppendIso g (L.map h) (M.map h)).hom ≫
        eqToHom (congrArg (tensorList g) (List.map_append (f := h)).symm) := by
  induction L with
  | nil => simp [List.map, tensorListAppendIso_nil]
  | cons a L ih =>
    dsimp only [List.map, List.cons_append]
    rw [tensorListAppendIso_cons_hom, tensorListAppendIso_cons_hom, tensorListMapIso_cons_hom,
      tensorListMapIso_cons_hom, Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ih,
      ← id_tensorHom (g (h a)) (f := (tensorListMapIso g h L).hom)]
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_eqToHom,
      Category.assoc]
    rw [associator_naturality_assoc, id_tensorHom]

/-- Naturality of `tensorListMapIso` in the target family. -/
@[reassoc]
theorem tensorListMapIso_hom_naturality {g₁ g₂ : β → C} (φ : ∀ b, g₁ b ⟶ g₂ b) (h : α → β)
    (L : List α) :
    tensorListCongrHom (fun a ↦ φ (h a)) L ≫ (tensorListMapIso g₂ h L).hom =
      (tensorListMapIso g₁ h L).hom ≫ tensorListCongrHom φ (L.map h) := by
  induction L with
  | nil => rfl
  | cons _ _ ih =>
    simp only [tensorListCongrHom_cons, tensorListMapIso_cons_hom]
    rw [tensorHom_def, Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ih,
      MonoidalCategory.whiskerLeft_comp, ← whisker_exchange_assoc, ← tensorHom_def]; rfl

/-- Isomorphism `tensorList (fun a ↦ tensorList f (g a)) L ≅ tensorList f (L.flatMap g)`. -/
def tensorListFlatMapIso (f : β → C) (g : α → List β) :
    (L : List α) → tensorList (fun a ↦ tensorList f (g a)) L ≅ tensorList f (L.flatMap g)
  | [] => Iso.refl (𝟙_ C)
  | a :: L => whiskerLeftIso (tensorList f (g a)) (tensorListFlatMapIso f g L) ≪≫
      tensorListAppendIso f (g a) (L.flatMap g)

@[simp] theorem tensorListFlatMapIso_nil (f : β → C) (g : α → List β) :
    tensorListFlatMapIso f g [] = Iso.refl (𝟙_ C) := by rfl
theorem tensorListFlatMapIso_cons_hom (f : β → C) (g : α → List β) (a : α) (L : List α) :
    (tensorListFlatMapIso f g (a :: L)).hom =
      tensorList f (g a) ◁ (tensorListFlatMapIso f g L).hom ≫
        (tensorListAppendIso f (g a) (L.flatMap g)).hom := by rfl
theorem tensorListFlatMapIso_cons_inv (f : β → C) (g : α → List β) (a : α) (L : List α) :
    (tensorListFlatMapIso f g (a :: L)).inv =
      (tensorListAppendIso f (g a) (L.flatMap g)).inv ≫
        tensorList f (g a) ◁ (tensorListFlatMapIso f g L).inv := by rfl

/-- Naturality of `tensorListFlatMapIso` in the target family. -/
@[reassoc]
theorem tensorListFlatMapIso_hom_naturality {f₁ f₂ : β → C} (φ : ∀ b, f₁ b ⟶ f₂ b)
    (g : α → List β) (L : List α) :
    tensorListCongrHom (fun a ↦ tensorListCongrHom φ (g a)) L ≫
        (tensorListFlatMapIso f₂ g L).hom =
      (tensorListFlatMapIso f₁ g L).hom ≫ tensorListCongrHom φ (L.flatMap g) := by
  induction L with
  | nil => rfl
  | cons _ _ ih =>
    simp only [tensorListFlatMapIso_cons_hom, tensorListCongrHom_cons, Category.assoc]
    rw [tensorHom_def'_assoc, ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ih, MonoidalCategory.whiskerLeft_comp_assoc,
      ← tensorHom_def'_assoc, tensorListAppendIso_hom_naturality]; rfl

end TauCeti

/-! ### Covariant and contravariant strong monoidal comparisons -/

namespace CategoryTheory.Functor

open TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] {α β : Type*}

/-- Strong monoidal comparison `F.obj (tensorList f L) ≅ tensorList (fun a ↦ F.obj (f a)) L`. -/
def mapTensorListIso (F : C ⥤ D) [F.Monoidal] (f : α → C) :
    (L : List α) → F.obj (tensorList f L) ≅ tensorList (fun a ↦ F.obj (f a)) L
  | [] => (εIso F).symm
  | a :: L => (μIso F (f a) (tensorList f L)).symm ≪≫
      whiskerLeftIso (F.obj (f a)) (F.mapTensorListIso f L)

@[simp] theorem mapTensorListIso_nil_hom (F : C ⥤ D) [F.Monoidal] (f : α → C) :
    (F.mapTensorListIso f []).hom = η F := by rfl
@[simp] theorem mapTensorListIso_nil_inv (F : C ⥤ D) [F.Monoidal] (f : α → C) :
    (F.mapTensorListIso f []).inv = ε F := by rfl
theorem mapTensorListIso_cons_hom (F : C ⥤ D) [F.Monoidal] (f : α → C) (a : α) (L : List α) :
    (F.mapTensorListIso f (a :: L)).hom =
      δ F (f a) (tensorList f L) ≫ F.obj (f a) ◁ (F.mapTensorListIso f L).hom := by rfl
theorem mapTensorListIso_cons_inv (F : C ⥤ D) [F.Monoidal] (f : α → C) (a : α) (L : List α) :
    (F.mapTensorListIso f (a :: L)).inv =
      F.obj (f a) ◁ (F.mapTensorListIso f L).inv ≫ μ F (f a) (tensorList f L) := by rfl

/-- `F.mapTensorListIso` commutes with block concatenation `tensorListAppendIso`. -/
theorem mapTensorListIso_append_hom (F : C ⥤ D) [F.Monoidal] (f : α → C) (L M : List α) :
    F.map (tensorListAppendIso f L M).hom ≫ (F.mapTensorListIso f (L ++ M)).hom =
      δ F (tensorList f L) (tensorList f M) ≫
        ((F.mapTensorListIso f L).hom ⊗ₘ (F.mapTensorListIso f M).hom) ≫
        (tensorListAppendIso (fun a ↦ F.obj (f a)) L M).hom := by
  induction L with
  | nil =>
    rw [tensorListAppendIso_nil, tensorListAppendIso_nil, mapTensorListIso_nil_hom]
    dsimp only [List.nil_append, tensorList]
    simp only [map_leftUnitor, tensorHom_def, Category.assoc, leftUnitor_naturality]
  | cons a L ih =>
    dsimp only [List.cons_append]
    rw [tensorListAppendIso_cons_hom, tensorListAppendIso_cons_hom, mapTensorListIso_cons_hom,
      mapTensorListIso_cons_hom]
    dsimp only [List.cons_append, tensorList]
    rw [Functor.map_comp, Category.assoc, map_whiskerLeft, Category.assoc, Category.assoc,
      μ_δ_assoc, ← MonoidalCategory.whiskerLeft_comp, ih, MonoidalCategory.whiskerLeft_comp,
      ← cancel_epi (μ F (f a ⊗ tensorList f L) (tensorList f M)),
      ← cancel_epi (μ F (f a) (tensorList f L) ▷ F.obj (tensorList f M))]
    simp only [Category.assoc, μ_δ_assoc, whiskerRight_μ_δ_assoc, map_associator,
      whiskerLeft_μ_δ_assoc, tensorHom_def', MonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
    rw [whisker_exchange_assoc, whiskerRight_μ_δ_assoc]; monoidal

private theorem mapTensorListIso_intertwine {F₁ F₂ : C ⥤ D} [F₁.Monoidal] [F₂.Monoidal]
    {f₁ f₂ : α → C} (u : ∀ L, F₁.obj (tensorList f₁ L) ⟶ F₂.obj (tensorList f₂ L))
    (v : ∀ a, F₁.obj (f₁ a) ⟶ F₂.obj (f₂ a)) (h0 : ε F₁ ≫ u [] = ε F₂)
    (h2 : ∀ a L, μ F₁ (f₁ a) (tensorList f₁ L) ≫ u (a :: L) =
      (v a ⊗ₘ u L) ≫ μ F₂ (f₂ a) (tensorList f₂ L)) (L : List α) :
    u L ≫ (F₂.mapTensorListIso f₂ L).hom =
      (F₁.mapTensorListIso f₁ L).hom ≫ tensorListCongrHom v L := by
  induction L with
  | nil =>
    rw [mapTensorListIso_nil_hom, mapTensorListIso_nil_hom, tensorListCongrHom_nil]
    dsimp only [tensorList]
    rw [Category.comp_id, ← cancel_epi (ε F₁), reassoc_of% h0, ε_η, ε_η]
  | cons a L ih =>
    rw [mapTensorListIso_cons_hom, mapTensorListIso_cons_hom, tensorListCongrHom_cons]
    dsimp only [tensorList]
    rw [← cancel_epi (μ F₁ (f₁ a) (tensorList f₁ L)), reassoc_of% (h2 a L), μ_δ_assoc,
      Category.assoc, μ_δ_assoc, tensorHom_def', Category.assoc, ← whisker_exchange,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ih, MonoidalCategory.whiskerLeft_comp_assoc,
      ← tensorHom_def']

/-- Naturality of `F.mapTensorListIso` in the indexing family. -/
@[reassoc]
theorem mapTensorListIso_hom_naturality (F : C ⥤ D) [F.Monoidal] {f₁ f₂ : α → C}
    (φ : ∀ a, f₁ a ⟶ f₂ a) (L : List α) :
    F.map (tensorListCongrHom φ L) ≫ (F.mapTensorListIso f₂ L).hom =
      (F.mapTensorListIso f₁ L).hom ≫ tensorListCongrHom (fun a ↦ F.map (φ a)) L :=
  Functor.mapTensorListIso_intertwine (fun L ↦ F.map (tensorListCongrHom φ L))
    (fun a ↦ F.map (φ a)) (by simp [tensorListCongrHom_nil])
    (fun a M ↦ (LaxMonoidal.μ_natural F (φ a) (tensorListCongrHom φ M)).symm) L

private abbrev uo (z : (Dᵒᵖ)ᴹᵒᵖ) : D := z.unmop.unop
private abbrev um {X Y : (Dᵒᵖ)ᴹᵒᵖ} (k : X ⟶ Y) : uo Y ⟶ uo X := k.unmop.unop
private def opMopUnitIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] : uo (G.obj (𝟙_ C)) ≅ 𝟙_ D :=
  ⟨um (ε G), um (η G), congrArg um (η_ε G), congrArg um (ε_η G)⟩
private def opMopTensorIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (X Y : C) :
    uo (G.obj (X ⊗ Y)) ≅ uo (G.obj Y) ⊗ uo (G.obj X) :=
  ⟨um (μ G X Y), um (δ G X Y), congrArg um (δ_μ G X Y), congrArg um (μ_δ G X Y)⟩

/-- Accumulator comparison for `opMopTensorListIso` along `List.reverseAux`. -/
def opMopTensorListAuxIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) :
    (L acc : List α) →
      (G.obj (tensorList f L)).unmop.unop ⊗
          tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc ≅
        tensorList (fun a ↦ (G.obj (f a)).unmop.unop) (L.reverseAux acc)
  | [], acc => whiskerRightIso (opMopUnitIso G) _ ≪≫
      λ_ (tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc)
  | a :: L, acc => whiskerRightIso (opMopTensorIso G (f a) (tensorList f L)) _ ≪≫
      α_ (G.obj (tensorList f L)).unmop.unop (G.obj (f a)).unmop.unop
        (tensorList (fun b ↦ (G.obj (f b)).unmop.unop) acc) ≪≫
      G.opMopTensorListAuxIso f L (a :: acc)

theorem opMopTensorListAuxIso_nil_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C)
    (acc : List α) :
    (G.opMopTensorListAuxIso f [] acc).hom =
      (ε G).unmop.unop ▷ tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc ≫
        (λ_ (tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc)).hom := by rfl
theorem opMopTensorListAuxIso_cons_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) (a : α)
    (L acc : List α) :
    (G.opMopTensorListAuxIso f (a :: L) acc).hom =
      (μ G (f a) (tensorList f L)).unmop.unop ▷
          tensorList (fun b ↦ (G.obj (f b)).unmop.unop) acc ≫
        (α_ (G.obj (tensorList f L)).unmop.unop (G.obj (f a)).unmop.unop
          (tensorList (fun b ↦ (G.obj (f b)).unmop.unop) acc)).hom ≫
        (G.opMopTensorListAuxIso f L (a :: acc)).hom := by rfl

/-- Reversed-list comparison for a contravariant strong monoidal functor `G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ`. -/
def opMopTensorListIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) (L : List α) :
    (G.obj (tensorList f L)).unmop.unop ≅
      tensorList (fun a ↦ (G.obj (f a)).unmop.unop) L.reverse :=
  (ρ_ (G.obj (tensorList f L)).unmop.unop).symm ≪≫ G.opMopTensorListAuxIso f L []

theorem opMopTensorListIso_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) (L : List α) :
    (G.opMopTensorListIso f L).hom =
      (ρ_ (G.obj (tensorList f L)).unmop.unop).inv ≫ (G.opMopTensorListAuxIso f L []).hom := by rfl
theorem opMopTensorListIso_nil_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) :
    (G.opMopTensorListIso f []).hom = (ε G).unmop.unop := by
  rw [opMopTensorListIso_hom, opMopTensorListAuxIso_nil_hom]
  dsimp only [List.reverse, List.reverseAux, tensorList]
  rw [unitors_equal, rightUnitor_naturality, Iso.inv_hom_id_assoc]

private theorem opMopTensorListIso_of_aux (G₁ G₂ : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G₁.Monoidal] [G₂.Monoidal]
    {f₁ : α → C} {f₂ : β → C} {M : List β} {L : List α}
    {u : uo (G₂.obj (tensorList f₂ M)) ⟶ uo (G₁.obj (tensorList f₁ L))}
    {w : tensorList (fun b ↦ uo (G₂.obj (f₂ b))) M.reverse ⟶
      tensorList (fun a ↦ uo (G₁.obj (f₁ a))) L.reverse}
    (h : (u ⊗ₘ 𝟙 (𝟙_ D)) ≫ (G₁.opMopTensorListAuxIso f₁ L []).hom =
      (G₂.opMopTensorListAuxIso f₂ M []).hom ≫ w) :
    u ≫ (G₁.opMopTensorListIso f₁ L).hom = (G₂.opMopTensorListIso f₂ M).hom ≫ w :=
  (rightUnitor_inv_naturality_assoc u _).trans <|
    ((ρ_ _).inv ≫= ((tensorHom_id u (𝟙_ D)).symm =≫ _).trans h).trans (Category.assoc _ _ _).symm

private theorem opMopTensorListAuxIso_intertwine {G₁ G₂ : C ⥤ (Dᵒᵖ)ᴹᵒᵖ} [G₁.Monoidal]
    [G₂.Monoidal] {f₁ f₂ : α → C}
    (u : ∀ L, uo (G₂.obj (tensorList f₂ L)) ⟶ uo (G₁.obj (tensorList f₁ L)))
    (v : ∀ a, uo (G₂.obj (f₂ a)) ⟶ uo (G₁.obj (f₁ a))) (h0 : u [] ≫ um (ε G₁) = um (ε G₂))
    (h2 : ∀ a L, u (a :: L) ≫ um (μ G₁ (f₁ a) (tensorList f₁ L)) =
      um (μ G₂ (f₂ a) (tensorList f₂ L)) ≫ (u L ⊗ₘ v a)) (L acc : List α) :
    (u L ⊗ₘ tensorListCongrHom v acc) ≫ (G₁.opMopTensorListAuxIso f₁ L acc).hom =
      (G₂.opMopTensorListAuxIso f₂ L acc).hom ≫ tensorListCongrHom v (L.reverseAux acc) := by
  induction L generalizing acc with
  | nil =>
    rw [opMopTensorListAuxIso_nil_hom, opMopTensorListAuxIso_nil_hom]
    dsimp only [uo, um, tensorList, List.reverseAux, unmop_tensorUnit, unop_tensorUnit]
    rw [tensorHom_def'_assoc, ← comp_whiskerRight_assoc, h0, whisker_exchange_assoc,
      leftUnitor_naturality, Category.assoc]
  | cons a L ih =>
    rw [opMopTensorListAuxIso_cons_hom, opMopTensorListAuxIso_cons_hom]
    dsimp only [uo, um, tensorList, List.reverseAux]; simp only [Category.assoc]
    rw [← ih (a :: acc), tensorListCongrHom_cons, ← associator_naturality_assoc,
      tensorHom_def'_assoc, ← comp_whiskerRight_assoc, h2 a L]
    simp only [comp_whiskerRight, Category.assoc, whisker_exchange_assoc, tensorHom_def']; rfl

/-- Naturality of `opMopTensorListAuxIso` in the indexing family. -/
@[reassoc]
theorem opMopTensorListAuxIso_hom_naturality (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] {f₁ f₂ : α → C}
    (φ : ∀ a, f₁ a ⟶ f₂ a) (L acc : List α) :
    ((G.map (tensorListCongrHom φ L)).unmop.unop ⊗ₘ
        tensorListCongrHom (fun a ↦ (G.map (φ a)).unmop.unop) acc) ≫
      (G.opMopTensorListAuxIso f₁ L acc).hom =
      (G.opMopTensorListAuxIso f₂ L acc).hom ≫
        tensorListCongrHom (fun a ↦ (G.map (φ a)).unmop.unop) (L.reverseAux acc) :=
  Functor.opMopTensorListAuxIso_intertwine (fun M ↦ um (G.map (tensorListCongrHom φ M)))
    (fun a ↦ um (G.map (φ a)))
    (by rw [tensorListCongrHom_nil, G.map_id, um, unmop_id, unop_id, Category.id_comp])
    (fun a M ↦ congrArg um (LaxMonoidal.μ_natural G (φ a) (tensorListCongrHom φ M)).symm) L acc

/-- Naturality of `opMopTensorListIso` in the indexing family. -/
@[reassoc]
theorem opMopTensorListIso_hom_naturality (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] {f₁ f₂ : α → C}
    (φ : ∀ a, f₁ a ⟶ f₂ a) (L : List α) :
    (G.map (tensorListCongrHom φ L)).unmop.unop ≫ (G.opMopTensorListIso f₁ L).hom =
      (G.opMopTensorListIso f₂ L).hom ≫
        tensorListCongrHom (fun a ↦ (G.map (φ a)).unmop.unop) L.reverse :=
  opMopTensorListIso_of_aux G G (G.opMopTensorListAuxIso_hom_naturality φ L [])

private theorem reverseAux_map_eq (h : α → β) (L acc : List α) :
    (L.map h).reverseAux (acc.map h) = (L.reverseAux acc).map h := by
  induction L generalizing acc with | nil => rfl | cons a _ ih => exact ih (a :: acc)

private theorem opMopTensorListAuxIso_map_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (g : β → C)
    (h : α → β) (L acc : List α) :
    (um (G.map (tensorListMapIso g h L).inv) ⊗ₘ
        (tensorListMapIso (fun b ↦ uo (G.obj (g b))) h acc).hom) ≫
      (G.opMopTensorListAuxIso g (L.map h) (acc.map h)).hom =
      (G.opMopTensorListAuxIso (fun a ↦ g (h a)) L acc).hom ≫
        (tensorListMapIso (fun b ↦ uo (G.obj (g b))) h (L.reverseAux acc)).hom ≫
        eqToHom (congrArg (tensorList fun b ↦ uo (G.obj (g b)))
          (reverseAux_map_eq h L acc).symm) := by
  induction L generalizing acc with
  | nil =>
    dsimp only [uo, um, List.map, List.reverseAux, tensorList, unmop_tensorUnit, unop_tensorUnit]
    generalize_proofs; rw [opMopTensorListAuxIso_nil_hom, opMopTensorListAuxIso_nil_hom,
      tensorListMapIso_nil, Iso.refl_inv]
    dsimp only [List.reverseAux, tensorList, unmop_tensorUnit, unop_tensorUnit]
    rw [G.map_id, unmop_id, unop_id, id_tensorHom, whisker_exchange_assoc, leftUnitor_naturality,
      eqToHom_refl, Category.comp_id, Category.assoc]
  | cons a L ih =>
    have ihStep := ih (a :: acc)
    dsimp only [uo, um, List.map, List.reverseAux, tensorList] at ihStep ⊢
    generalize_proofs at ihStep ⊢; rw [opMopTensorListAuxIso_cons_hom,
      opMopTensorListAuxIso_cons_hom, tensorListMapIso_cons_inv, ← id_tensorHom (g (h a))]
    dsimp only [List.reverseAux, tensorList]
    have hμ := congrArg um (LaxMonoidal.μ_natural G (𝟙 (g (h a))) (tensorListMapIso g h L).inv).symm
    dsimp only [um, unmop_comp, unop_comp, unmop_tensorObj, unop_tensorObj, unmop_tensorHom,
      unop_tensorHom] at hμ; rw [G.map_id, unmop_id, unop_id] at hμ; simp only [Category.assoc]
    rw [← ihStep, tensorListMapIso_cons_hom, ← id_tensorHom, ← associator_naturality_assoc,
      tensorHom_def'_assoc, ← comp_whiskerRight_assoc, hμ]
    simp only [comp_whiskerRight, Category.assoc, whisker_exchange_assoc, tensorHom_def',
      MonoidalCategory.whiskerLeft_id, Category.id_comp]; rfl

/-- Compatibility of `G.opMopTensorListIso` with list mapping `L.map h`. -/
@[reassoc]
theorem opMopTensorListIso_map_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (g : β → C) (h : α → β)
    (L : List α) :
    (G.map (tensorListMapIso g h L).inv).unmop.unop ≫ (G.opMopTensorListIso g (L.map h)).hom =
      (G.opMopTensorListIso (fun a ↦ g (h a)) L).hom ≫
        (tensorListMapIso (fun b ↦ (G.obj (g b)).unmop.unop) h L.reverse).hom ≫
        eqToHom (congrArg (tensorList (fun b ↦ (G.obj (g b)).unmop.unop)) List.map_reverse) :=
  opMopTensorListIso_of_aux G G (G.opMopTensorListAuxIso_map_hom g h L [])

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

open TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] {α : Type*}

/-- A monoidal natural transformation `τ : F ⟶ G` between strong monoidal functors intertwines
`mapTensorListIso` with `tensorListCongrHom`. -/
@[reassoc]
theorem app_comp_mapTensorListIso_hom {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    (τ : F ⟶ G) [NatTrans.IsMonoidal τ] (f : α → C) (L : List α) :
    τ.app (tensorList f L) ≫ (G.mapTensorListIso f L).hom =
      (F.mapTensorListIso f L).hom ≫ tensorListCongrHom (fun a ↦ τ.app (f a)) L :=
  Functor.mapTensorListIso_intertwine (fun M ↦ τ.app (tensorList f M)) (fun a ↦ τ.app (f a))
    IsMonoidal.unit (fun a M ↦ IsMonoidal.tensor (f a) (tensorList f M)) L

/-- A monoidal natural transformation `τ : G₁ ⟶ G₂` between contravariant strong monoidal functors
`C ⥤ (Dᵒᵖ)ᴹᵒᵖ` intertwines `opMopTensorListIso` with `tensorListCongrHom` on `L.reverse`. -/
@[reassoc]
theorem unmop_unop_app_comp_opMopTensorListIso_hom
    {G₁ G₂ : C ⥤ (Dᵒᵖ)ᴹᵒᵖ} [G₁.Monoidal] [G₂.Monoidal] (τ : G₁ ⟶ G₂) [NatTrans.IsMonoidal τ]
    (f : α → C) (L : List α) :
    (τ.app (tensorList f L)).unmop.unop ≫ (G₁.opMopTensorListIso f L).hom =
      (G₂.opMopTensorListIso f L).hom ≫
        tensorListCongrHom (fun a ↦ (τ.app (f a)).unmop.unop) L.reverse :=
  Functor.opMopTensorListIso_of_aux G₁ G₂
    (Functor.opMopTensorListAuxIso_intertwine (fun M ↦ Functor.um (τ.app (tensorList f M)))
      (fun a ↦ Functor.um (τ.app (f a))) (congrArg Functor.um (IsMonoidal.unit (τ := τ)))
      (fun a M ↦ congrArg Functor.um (IsMonoidal.tensor (τ := τ) (f a) (tensorList f M))) L [])

end CategoryTheory.NatTrans
