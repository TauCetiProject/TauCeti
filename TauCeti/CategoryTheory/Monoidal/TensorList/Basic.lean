/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.Data.List.Basic
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Right-associated tensor products of finite lists

Interpreting ordered boundary words in a non-strict monoidal category `C` assigns to each finite
list `L : List α` and generator valuation `f : α → C` the right-associated tensor product
`TauCeti.tensorList f L` ending in `𝟙_ C`: `tensorList f [] = 𝟙_ C` and
`tensorList f (a :: L) = f a ⊗ tensorList f L`. Multi-port boundary substitution corresponds to
`List.flatMap`, while order-reversing duals act as contravariant strong monoidal functors
`C ⥤ (Dᵒᵖ)ᴹᵒᵖ` reversing the list factors. On a replicated list `List.replicate n a`,
`tensorList f (List.replicate n a)` agrees propositionally with `TauCeti.tensorPow (f a) n` via
`TauCeti.tensorList_replicate` (reducing definitionally only on closed numerals).

## Main declarations

* `TauCeti.tensorList`: right-associated tensor product of an indexed list, with
  `TauCeti.tensorList_replicate`;
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

-- Exposed and reducible so `tensorList f (a :: L)` and `tensorList f []` elaborate as
-- `f a ⊗ tensorList f L` and `𝟙_ C` without object-level `eqToHom` wrappers.
/-- Right-associated tensor product of a list indexed by `f : α → C`, ending in `𝟙_ C`. -/
@[expose, reducible]
def tensorList (f : α → C) : List α → C
  | [] => 𝟙_ C
  | a :: L => f a ⊗ tensorList f L

theorem tensorList_nil (f : α → C) : tensorList f [] = 𝟙_ C := (rfl)

theorem tensorList_cons (f : α → C) (a : α) (L : List α) :
    tensorList f (a :: L) = f a ⊗ tensorList f L := (rfl)

/-- On a replicated list, `tensorList` agrees propositionally with `tensorPow`. -/
@[simp] theorem tensorList_replicate (f : α → C) (n : ℕ) (a : α) :
    tensorList f (List.replicate n a) = tensorPow (f a) n := by
  induction n with
  | zero => rfl
  | succ _ ih => exact congrArg (f a ⊗ ·) ih

/-- Block concatenation isomorphism `tensorList f L ⊗ tensorList f M ≅ tensorList f (L ++ M)`. -/
def tensorListAppendIso (f : α → C) :
    (L M : List α) → tensorList f L ⊗ tensorList f M ≅ tensorList f (L ++ M)
  | [], M => λ_ (tensorList f M)
  | a :: L, M => α_ (f a) (tensorList f L) (tensorList f M) ≪≫
      whiskerLeftIso (f a) (tensorListAppendIso f L M)

@[simp] theorem tensorListAppendIso_nil (f : α → C) (M : List α) :
    tensorListAppendIso f [] M = λ_ (tensorList f M) := (rfl)

theorem tensorListAppendIso_cons (f : α → C) (a : α) (L M : List α) :
    tensorListAppendIso f (a :: L) M = α_ (f a) (tensorList f L) (tensorList f M) ≪≫
      whiskerLeftIso (f a) (tensorListAppendIso f L M) := (rfl)

theorem tensorListAppendIso_cons_hom (f : α → C) (a : α) (L M : List α) :
    (tensorListAppendIso f (a :: L) M).hom = (α_ (f a) (tensorList f L) (tensorList f M)).hom ≫
      f a ◁ (tensorListAppendIso f L M).hom := (rfl)

theorem tensorListAppendIso_cons_inv (f : α → C) (a : α) (L M : List α) :
    (tensorListAppendIso f (a :: L) M).inv = f a ◁ (tensorListAppendIso f L M).inv ≫
      (α_ (f a) (tensorList f L) (tensorList f M)).inv := (rfl)

/-- Concatenating a singleton left block acts by the right unitor on `f a`. -/
theorem tensorListAppendIso_singleton_hom (f : α → C) (a : α) (M : List α) :
    (tensorListAppendIso f [a] M).hom = (ρ_ (f a)).hom ▷ tensorList f M := by
  rw [tensorListAppendIso_cons_hom, tensorListAppendIso_nil]; monoidal_coherence

theorem tensorListAppendIso_singleton_inv (f : α → C) (a : α) (M : List α) :
    (tensorListAppendIso f [a] M).inv = (ρ_ (f a)).inv ▷ tensorList f M := by
  rw [tensorListAppendIso_cons_inv, tensorListAppendIso_nil]; monoidal_coherence

/-- Concatenating an empty right block agrees with the right unitor up to `List.append_nil`. -/
@[reassoc]
theorem tensorListAppendIso_nil_right_hom (f : α → C) (L : List α) :
    (tensorListAppendIso f L []).hom =
      (ρ_ (tensorList f L)).hom ≫ eqToHom (congrArg (tensorList f) (List.append_nil L).symm) := by
  induction L with
  | nil => exact unitors_equal.trans (Category.comp_id _).symm
  | cons a L ih =>
    rw [tensorListAppendIso_cons_hom, ih]
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_eqToHom,
      MonoidalCategory.whiskerLeft_rightUnitor, Category.assoc, Iso.hom_inv_id_assoc]

/-- Inverse of `tensorListAppendIso_nil_right_hom` on an empty right block. -/
@[reassoc]
theorem tensorListAppendIso_nil_right_inv (f : α → C) (L : List α) :
    (tensorListAppendIso f L []).inv =
      eqToHom (congrArg (tensorList f) (List.append_nil L)) ≫ (ρ_ (tensorList f L)).inv := by
  rw [← cancel_epi (tensorListAppendIso f L []).hom, Iso.hom_inv_id,
    tensorListAppendIso_nil_right_hom]
  simp

/-- **Associativity of block concatenation**: splitting `(L ++ M) ++ N` in either order agrees up
to `List.append_assoc`. -/
@[reassoc]
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
    tensorListCongrHom φ [] = 𝟙 (𝟙_ C) := (rfl)

@[simp] theorem tensorListCongrHom_cons {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) (a : α)
    (L : List α) : tensorListCongrHom φ (a :: L) = φ a ⊗ₘ tensorListCongrHom φ L := (rfl)

/-- Pointwise identities induce the identity morphism on `tensorList f L`. -/
@[simp] theorem tensorListCongrHom_id (f : α → C) (L : List α) :
    tensorListCongrHom (fun a ↦ 𝟙 (f a)) L = 𝟙 (tensorList f L) := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Pointwise composites induce the composite morphism on `tensorList`. -/
@[simp, reassoc]
theorem tensorListCongrHom_comp {f₁ f₂ f₃ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a)
    (ψ : ∀ a, f₂ a ⟶ f₃ a) (L : List α) :
    tensorListCongrHom (fun a ↦ φ a ≫ ψ a) L =
      tensorListCongrHom φ L ≫ tensorListCongrHom ψ L := by
  induction L with
  | nil => simp
  | cons _ _ ih => simp [ih, tensorHom_comp_tensorHom]

@[reassoc]
theorem tensorListCongrHom_eqToHom {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) {L M : List α}
    (h : L = M) :
    tensorListCongrHom φ L ≫ eqToHom (congrArg (tensorList f₂) h) =
      eqToHom (congrArg (tensorList f₁) h) ≫ tensorListCongrHom φ M := by
  subst h; simp

/-- Tensor product of a pointwise family of isomorphisms `e a : f₁ a ≅ f₂ a` along `L : List α`. -/
def tensorListCongrIso {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : List α) :
    tensorList f₁ L ≅ tensorList f₂ L where
  hom := tensorListCongrHom (fun a ↦ (e a).hom) L
  inv := tensorListCongrHom (fun a ↦ (e a).inv) L
  hom_inv_id := by simp [← tensorListCongrHom_comp]
  inv_hom_id := by simp [← tensorListCongrHom_comp]

@[simp] theorem tensorListCongrIso_hom {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : List α) :
    (tensorListCongrIso e L).hom = tensorListCongrHom (fun a ↦ (e a).hom) L := (rfl)

@[simp] theorem tensorListCongrIso_inv {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : List α) :
    (tensorListCongrIso e L).inv = tensorListCongrHom (fun a ↦ (e a).inv) L := (rfl)

/-- Block concatenation is natural with respect to `tensorListCongrHom`. -/
@[reassoc]
theorem tensorListAppendIso_hom_naturality {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) (L M : List α) :
    (tensorListCongrHom φ L ⊗ₘ tensorListCongrHom φ M) ≫ (tensorListAppendIso f₂ L M).hom =
      (tensorListAppendIso f₁ L M).hom ≫ tensorListCongrHom φ (L ++ M) := by
  induction L with
  | nil => simp [tensorListAppendIso_nil]
  | cons a L ih =>
    dsimp only [List.cons_append]
    rw [tensorListAppendIso_cons_hom, tensorListAppendIso_cons_hom,
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
    tensorListMapIso g h [] = Iso.refl (𝟙_ C) := (rfl)

@[simp] theorem tensorListMapIso_cons_hom (g : β → C) (h : α → β) (a : α) (L : List α) :
    (tensorListMapIso g h (a :: L)).hom = g (h a) ◁ (tensorListMapIso g h L).hom := (rfl)

@[simp] theorem tensorListMapIso_cons_inv (g : β → C) (h : α → β) (a : α) (L : List α) :
    (tensorListMapIso g h (a :: L)).inv = g (h a) ◁ (tensorListMapIso g h L).inv := (rfl)

/-- Object-level equality `tensorList g (L.map h) = tensorList (fun a ↦ g (h a)) L`. -/
theorem tensorList_map (g : β → C) (h : α → β) (L : List α) :
    tensorList g (L.map h) = tensorList (fun a ↦ g (h a)) L := by
  induction L with
  | nil => rfl
  | cons a _ ih => exact congrArg (g (h a) ⊗ ·) ih

/-- `(tensorListMapIso g h L).hom` agrees with `eqToHom (tensorList_map g h L).symm`. -/
theorem tensorListMapIso_hom_eq_eqToHom (g : β → C) (h : α → β) (L : List α) :
    (tensorListMapIso g h L).hom = eqToHom (tensorList_map g h L).symm := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ih, MonoidalCategory.whiskerLeft_eqToHom]

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
      MonoidalCategory.whiskerLeft_comp, ← whisker_exchange_assoc, ← tensorHom_def]
    rfl

/-- Isomorphism `tensorList (fun a ↦ tensorList f (g a)) L ≅ tensorList f (L.flatMap g)`. -/
def tensorListFlatMapIso (f : β → C) (g : α → List β) :
    (L : List α) → tensorList (fun a ↦ tensorList f (g a)) L ≅ tensorList f (L.flatMap g)
  | [] => Iso.refl (𝟙_ C)
  | a :: L => whiskerLeftIso (tensorList f (g a)) (tensorListFlatMapIso f g L) ≪≫
      tensorListAppendIso f (g a) (L.flatMap g)

@[simp] theorem tensorListFlatMapIso_nil (f : β → C) (g : α → List β) :
    tensorListFlatMapIso f g [] = Iso.refl (𝟙_ C) := (rfl)

theorem tensorListFlatMapIso_cons_hom (f : β → C) (g : α → List β) (a : α) (L : List α) :
    (tensorListFlatMapIso f g (a :: L)).hom =
      tensorList f (g a) ◁ (tensorListFlatMapIso f g L).hom ≫
        (tensorListAppendIso f (g a) (L.flatMap g)).hom := (rfl)

theorem tensorListFlatMapIso_cons_inv (f : β → C) (g : α → List β) (a : α) (L : List α) :
    (tensorListFlatMapIso f g (a :: L)).inv =
      (tensorListAppendIso f (g a) (L.flatMap g)).inv ≫
        tensorList f (g a) ◁ (tensorListFlatMapIso f g L).inv := (rfl)

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
      ← tensorHom_def'_assoc, tensorListAppendIso_hom_naturality]
    rfl

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
    (F.mapTensorListIso f []).hom = η F := (rfl)

@[simp] theorem mapTensorListIso_nil_inv (F : C ⥤ D) [F.Monoidal] (f : α → C) :
    (F.mapTensorListIso f []).inv = ε F := (rfl)

theorem mapTensorListIso_cons_hom (F : C ⥤ D) [F.Monoidal] (f : α → C) (a : α) (L : List α) :
    (F.mapTensorListIso f (a :: L)).hom =
      δ F (f a) (tensorList f L) ≫ F.obj (f a) ◁ (F.mapTensorListIso f L).hom := (rfl)

theorem mapTensorListIso_cons_inv (F : C ⥤ D) [F.Monoidal] (f : α → C) (a : α) (L : List α) :
    (F.mapTensorListIso f (a :: L)).inv =
      F.obj (f a) ◁ (F.mapTensorListIso f L).inv ≫ μ F (f a) (tensorList f L) := (rfl)

/-- `F.mapTensorListIso` commutes with block concatenation `tensorListAppendIso`. -/
@[reassoc]
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
    simp only [Functor.map_comp, map_whiskerLeft, Category.assoc, μ_δ_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp, ih, MonoidalCategory.whiskerLeft_comp,
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
    rw [← cancel_epi (μ F₁ (f₁ a) (tensorList f₁ L)), reassoc_of% (h2 a L)]
    simp only [Category.assoc, μ_δ_assoc, tensorHom_def']
    rw [← whisker_exchange, ← MonoidalCategory.whiskerLeft_comp_assoc, ih,
      MonoidalCategory.whiskerLeft_comp_assoc]

/-- Naturality of `F.mapTensorListIso` in the indexing family. -/
@[reassoc]
theorem mapTensorListIso_hom_naturality (F : C ⥤ D) [F.Monoidal] {f₁ f₂ : α → C}
    (φ : ∀ a, f₁ a ⟶ f₂ a) (L : List α) :
    F.map (tensorListCongrHom φ L) ≫ (F.mapTensorListIso f₂ L).hom =
      (F.mapTensorListIso f₁ L).hom ≫ tensorListCongrHom (fun a ↦ F.map (φ a)) L :=
  Functor.mapTensorListIso_intertwine (fun L ↦ F.map (tensorListCongrHom φ L))
    (fun a ↦ F.map (φ a)) (by simp [tensorListCongrHom_nil])
    (fun a M ↦ (LaxMonoidal.μ_natural F (φ a) (tensorListCongrHom φ M)).symm) L

/-- Unwrapped unit isomorphism `(G.obj (𝟙_ C)).unmop.unop ≅ 𝟙_ D` for `G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ`. -/
private def opMopUnitIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] :
    (G.obj (𝟙_ C)).unmop.unop ≅ 𝟙_ D :=
  (εIso G).unmop.unop

@[simp]
private theorem opMopUnitIso_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] :
    (opMopUnitIso G).hom = (ε G).unmop.unop := (rfl)

@[simp]
private theorem opMopUnitIso_inv (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] :
    (opMopUnitIso G).inv = (η G).unmop.unop := (rfl)

/-- Unwrapped reversed-tensor isomorphism
`(G.obj (X ⊗ Y)).unmop.unop ≅ (G.obj Y).unmop.unop ⊗ (G.obj X).unmop.unop` for
`G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ`. -/
private def opMopTensorIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (X Y : C) :
    (G.obj (X ⊗ Y)).unmop.unop ≅ (G.obj Y).unmop.unop ⊗ (G.obj X).unmop.unop :=
  (μIso G X Y).unmop.unop

@[simp]
private theorem opMopTensorIso_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (X Y : C) :
    (opMopTensorIso G X Y).hom = (μ G X Y).unmop.unop := (rfl)

@[simp]
private theorem opMopTensorIso_inv (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (X Y : C) :
    (opMopTensorIso G X Y).inv = (δ G X Y).unmop.unop := (rfl)

/-- Reversed-list comparison for a contravariant strong monoidal functor `G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ`:
the tensor factors reverse order and the empty list maps to the monoidal unit. -/
def opMopTensorListIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) :
    (L : List α) →
      (G.obj (tensorList f L)).unmop.unop ≅
        tensorList (fun a ↦ (G.obj (f a)).unmop.unop) L.reverse
  | [] => opMopUnitIso G
  | a :: L =>
    opMopTensorIso G (f a) (tensorList f L) ≪≫
      (G.opMopTensorListIso f L ⊗ᵢ (ρ_ (G.obj (f a)).unmop.unop).symm) ≪≫
      tensorListAppendIso (fun b ↦ (G.obj (f b)).unmop.unop) L.reverse [a] ≪≫
      eqToIso (congrArg (tensorList (fun b ↦ (G.obj (f b)).unmop.unop)) List.reverse_cons.symm)

@[simp] theorem opMopTensorListIso_nil_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) :
    (G.opMopTensorListIso f []).hom = (ε G).unmop.unop := (rfl)

@[simp] theorem opMopTensorListIso_nil_inv (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) :
    (G.opMopTensorListIso f []).inv = (η G).unmop.unop := (rfl)

theorem opMopTensorListIso_cons_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) (a : α)
    (L : List α) :
    (G.opMopTensorListIso f (a :: L)).hom =
      (μ G (f a) (tensorList f L)).unmop.unop ≫
        ((G.opMopTensorListIso f L).hom ⊗ₘ (ρ_ (G.obj (f a)).unmop.unop).inv) ≫
        (tensorListAppendIso (fun b ↦ (G.obj (f b)).unmop.unop) L.reverse [a]).hom ≫
        eqToHom (congrArg (tensorList (fun b ↦ (G.obj (f b)).unmop.unop))
          List.reverse_cons.symm) := (rfl)

theorem opMopTensorListIso_cons_inv (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) (a : α)
    (L : List α) :
    (G.opMopTensorListIso f (a :: L)).inv =
      eqToHom (congrArg (tensorList (fun b ↦ (G.obj (f b)).unmop.unop)) List.reverse_cons) ≫
        (tensorListAppendIso (fun b ↦ (G.obj (f b)).unmop.unop) L.reverse [a]).inv ≫
        ((G.opMopTensorListIso f L).inv ⊗ₘ (ρ_ (G.obj (f a)).unmop.unop).hom) ≫
        (δ G (f a) (tensorList f L)).unmop.unop := by
  simp [opMopTensorListIso]

/-- On a singleton list `[a]`, `opMopTensorListIso` unpacks the unit factor on the right. -/
theorem opMopTensorListIso_singleton_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C) (a : α) :
    (G.opMopTensorListIso f [a]).hom =
      (μ G (f a) (𝟙_ C)).unmop.unop ≫
        ((ε G).unmop.unop ⊗ₘ (ρ_ (G.obj (f a)).unmop.unop).inv) ≫
        (λ_ ((G.obj (f a)).unmop.unop ⊗ 𝟙_ D)).hom := by
  rw [opMopTensorListIso_cons_hom, opMopTensorListIso_nil_hom]
  -- Unfold `tensorList f []` and `[].reverse ++ [a]` so `eqToHom` simplifies to `eqToHom rfl`.
  change (μ G (f a) (𝟙_ C)).unmop.unop ≫
      ((ε G).unmop.unop ⊗ₘ (ρ_ (G.obj (f a)).unmop.unop).inv) ≫
      (tensorListAppendIso (fun b ↦ (G.obj (f b)).unmop.unop) [] [a]).hom ≫
      eqToHom rfl = _
  rw [tensorListAppendIso_nil, eqToHom_refl, Category.comp_id]

private theorem opMop_left_unitality_inv (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (X : C) :
    (G.map (λ_ X).inv).unmop.unop =
      (μ G (𝟙_ C) X).unmop.unop ≫
        ((G.obj X).unmop.unop ◁ (ε G).unmop.unop) ≫ (ρ_ (G.obj X).unmop.unop).hom := by
  have h := congrArg (fun k ↦ k.unmop.unop) (LaxMonoidal.left_unitality G X)
  simp only [unmop_comp, unop_comp, unmop_whiskerRight, unop_whiskerLeft] at h
  have hu : (λ_ (G.obj X)).hom.unmop.unop = (ρ_ (G.obj X).unmop.unop).inv := rfl
  rw [hu] at h
  rw [← cancel_mono (ρ_ (G.obj X).unmop.unop).inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id,
    ← cancel_epi (G.map (λ_ X).hom).unmop.unop, ← Category.assoc,
    ← unop_comp, ← unmop_comp, ← G.map_comp, Iso.inv_hom_id, G.map_id, unmop_id, unop_id,
    Category.id_comp, h]
  simp only [Category.assoc]

private theorem opMop_associativity_inv (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (X Y Z : C) :
    (G.map (α_ X Y Z).inv).unmop.unop ≫ (μ G X (Y ⊗ Z)).unmop.unop ≫
        ((μ G Y Z).unmop.unop ▷ (G.obj X).unmop.unop) =
      (μ G (X ⊗ Y) Z).unmop.unop ≫
        ((G.obj Z).unmop.unop ◁ (μ G X Y).unmop.unop) ≫
        (α_ (G.obj Z).unmop.unop (G.obj Y).unmop.unop (G.obj X).unmop.unop).inv := by
  have h := congrArg (fun k ↦ k.unmop.unop) (LaxMonoidal.associativity G X Y Z)
  simp only [unmop_comp, unop_comp, unmop_whiskerRight, unop_whiskerLeft,
    unmop_whiskerLeft, unop_whiskerRight, Category.assoc] at h
  have ha : (α_ (G.obj X) (G.obj Y) (G.obj Z)).hom.unmop.unop =
      (α_ (G.obj Z).unmop.unop (G.obj Y).unmop.unop (G.obj X).unmop.unop).hom := rfl
  rw [ha] at h
  rw [← cancel_epi (G.map (α_ X Y Z).hom).unmop.unop, ← Category.assoc,
    ← unop_comp, ← unmop_comp, ← G.map_comp, Iso.inv_hom_id, G.map_id, unmop_id, unop_id,
    Category.id_comp, reassoc_of% h]
  simp

/-- `G.opMopTensorListIso` reverses block concatenation `tensorListAppendIso`. -/
@[reassoc]
theorem opMopTensorListIso_append_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (f : α → C)
    (L M : List α) :
    (G.map (tensorListAppendIso f L M).inv).unmop.unop ≫ (G.opMopTensorListIso f (L ++ M)).hom =
      (μ G (tensorList f L) (tensorList f M)).unmop.unop ≫
        ((G.opMopTensorListIso f M).hom ⊗ₘ (G.opMopTensorListIso f L).hom) ≫
        (tensorListAppendIso (fun a ↦ (G.obj (f a)).unmop.unop) M.reverse L.reverse).hom ≫
        eqToHom (congrArg (tensorList (fun a ↦ (G.obj (f a)).unmop.unop))
          (List.reverse_append).symm) := by
  let g : α → D := fun a ↦ (G.obj (f a)).unmop.unop
  induction L with
  | nil =>
    rw [tensorListAppendIso_nil, opMopTensorListIso_nil_hom]
    -- Unfold `tensorList f [] = 𝟙_ C` and `[].reverse = []` so `eqToHom` sits on `M.reverse ++ []`.
    change (G.map (λ_ (tensorList f M)).inv).unmop.unop ≫ (G.opMopTensorListIso f M).hom =
      (μ G (𝟙_ C) (tensorList f M)).unmop.unop ≫
        ((G.opMopTensorListIso f M).hom ⊗ₘ ((ε G).unmop.unop : _ ⟶ 𝟙_ D)) ≫
        (tensorListAppendIso g M.reverse []).hom ≫
        eqToHom (congrArg (tensorList g) (List.append_nil M.reverse))
    rw [tensorListAppendIso_nil_right_hom, opMop_left_unitality_inv]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, tensorHom_def]
    rw [← whisker_exchange_assoc]
    dsimp only [unmop_tensorUnit, unop_tensorUnit]
    rw [rightUnitor_naturality]
  | cons a L ih =>
    dsimp only [List.cons_append]
    rw [tensorListAppendIso_cons_inv, G.map_comp, unmop_comp, unop_comp,
      opMopTensorListIso_cons_hom, opMopTensorListIso_cons_hom]
    have hmap : (G.map (f a ◁ (tensorListAppendIso f L M).inv)).unmop.unop ≫
        (μ G (f a) (tensorList f (L ++ M))).unmop.unop =
        (μ G (f a) (tensorList f L ⊗ tensorList f M)).unmop.unop ≫
          ((G.map (tensorListAppendIso f L M).inv).unmop.unop ⊗ₘ 𝟙 (g a)) := by
      have hm := congrArg (fun k ↦ k.unmop.unop)
        (LaxMonoidal.μ_natural_right G (f a) (tensorListAppendIso f L M).inv)
      simp only [unmop_comp, unop_comp] at hm
      exact hm.symm.trans (congrArg (_ ≫ ·) (tensorHom_id _ (g a)).symm)
    have hsplitL : ∀ {A₁ A₂ A₃ B₁ B₂ : D} (p : A₁ ⟶ A₂) (q : A₂ ⟶ A₃) (r : B₁ ⟶ B₂),
        (p ≫ q) ⊗ₘ r = p ▷ B₁ ≫ (q ⊗ₘ r) := by
      intros; simp [tensorHom_def]
    rw [Category.assoc, reassoc_of% hmap, tensorHom_comp_tensorHom_assoc, ih, Category.id_comp,
      hsplitL (μ G (tensorList f L) (tensorList f M)).unmop.unop, Category.assoc,
      reassoc_of% (opMop_associativity_inv G (f a) (tensorList f L) (tensorList f M))]
    have hnat : ∀ {R₁ R₂ : List α} (hr : R₁ = R₂),
        (eqToHom (congrArg (tensorList g) hr) ▷ (g a ⊗ 𝟙_ D)) ≫
          (tensorListAppendIso g R₂ [a]).hom =
        (tensorListAppendIso g R₁ [a]).hom ≫
          eqToHom (congrArg (tensorList g) (congrArg (· ++ [a]) hr)) := by
      intro R₁ R₂ hr; subst hr; simp
    have hR : ∀ {W₁ W₂ : List α} (h₁ : W₁ = W₂)
        (h₂ : M.reverse ++ W₂ = M.reverse ++ W₁),
        (tensorList g M.reverse ◁ eqToHom (congrArg (tensorList g) h₁)) ≫
          (tensorListAppendIso g M.reverse W₂).hom ≫
          eqToHom (congrArg (tensorList g) h₂) =
        (tensorListAppendIso g M.reverse W₁).hom := by
      intro W₁ W₂ h₁ h₂; subst h₁; simp
    simp only [Category.assoc, tensorHom_def', comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp]
    rw [reassoc_of% (hnat List.reverse_append.symm)]
    have hassocApp := tensorListAppendIso_assoc g M.reverse L.reverse [a]
    dsimp only [tensorList] at hassocApp
    rw [reassoc_of% hassocApp]
    -- Slide `eqToHom` past `(G.opMopTensorListIso f M).hom` on the right-hand side.
    rw [whisker_exchange_assoc (G.opMopTensorListIso f M).hom
      (eqToHom (congrArg (tensorList g) List.reverse_cons.symm))]
    rw [← cancel_mono (eqToHom (congrArg (tensorList g)
      (by simp [List.reverse_cons, List.append_assoc] :
        ((a :: L) ++ M).reverse = M.reverse ++ (L.reverse ++ [a]))))]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    congr 1
    rw [hR List.reverse_cons.symm (congrArg (M.reverse ++ ·) List.reverse_cons),
      whisker_exchange_assoc (G.opMopTensorListIso f M).hom
        (tensorListAppendIso g L.reverse [a]).hom]
    dsimp only [tensorList, g]
    monoidal

private theorem opMopTensorListIso_intertwine {G₁ G₂ : C ⥤ (Dᵒᵖ)ᴹᵒᵖ} [G₁.Monoidal]
    [G₂.Monoidal] {f₁ f₂ : α → C}
    (u : ∀ L, (G₂.obj (tensorList f₂ L)).unmop.unop ⟶ (G₁.obj (tensorList f₁ L)).unmop.unop)
    (v : ∀ a, (G₂.obj (f₂ a)).unmop.unop ⟶ (G₁.obj (f₁ a)).unmop.unop)
    (h0 : u [] ≫ (ε G₁).unmop.unop = (ε G₂).unmop.unop)
    (h2 : ∀ a L, u (a :: L) ≫ (μ G₁ (f₁ a) (tensorList f₁ L)).unmop.unop =
      (μ G₂ (f₂ a) (tensorList f₂ L)).unmop.unop ≫ (u L ⊗ₘ v a)) (L : List α) :
    u L ≫ (G₁.opMopTensorListIso f₁ L).hom =
      (G₂.opMopTensorListIso f₂ L).hom ≫ tensorListCongrHom v L.reverse := by
  induction L with
  | nil =>
    rw [opMopTensorListIso_nil_hom, opMopTensorListIso_nil_hom]
    dsimp only [List.reverse_nil]
    rw [tensorListCongrHom_nil, Category.comp_id, h0]
  | cons a L ih =>
    rw [opMopTensorListIso_cons_hom, opMopTensorListIso_cons_hom, reassoc_of% (h2 a L),
      tensorHom_comp_tensorHom_assoc, ih, rightUnitor_inv_naturality]
    have hv : v a ▷ 𝟙_ D = tensorListCongrHom v [a] := (tensorHom_id (v a) (𝟙_ D)).symm
    rw [hv, ← tensorHom_comp_tensorHom_assoc, tensorListAppendIso_hom_naturality_assoc,
      tensorListCongrHom_eqToHom v List.reverse_cons.symm]
    simp only [Category.assoc]

/-- Naturality of `opMopTensorListIso` in the indexing family. -/
@[reassoc]
theorem opMopTensorListIso_hom_naturality (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] {f₁ f₂ : α → C}
    (φ : ∀ a, f₁ a ⟶ f₂ a) (L : List α) :
    (G.map (tensorListCongrHom φ L)).unmop.unop ≫ (G.opMopTensorListIso f₁ L).hom =
      (G.opMopTensorListIso f₂ L).hom ≫
        tensorListCongrHom (fun a ↦ (G.map (φ a)).unmop.unop) L.reverse :=
  Functor.opMopTensorListIso_intertwine (fun M ↦ (G.map (tensorListCongrHom φ M)).unmop.unop)
    (fun a ↦ (G.map (φ a)).unmop.unop)
    (by rw [tensorListCongrHom_nil, G.map_id, unmop_id, unop_id, Category.id_comp])
    (fun a M ↦ congrArg (fun k ↦ k.unmop.unop)
      (LaxMonoidal.μ_natural G (φ a) (tensorListCongrHom φ M)).symm) L

/-- Compatibility of `G.opMopTensorListIso` with list mapping `L.map h`. -/
@[reassoc]
theorem opMopTensorListIso_map_hom (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (g : β → C) (h : α → β)
    (L : List α) :
    (G.map (tensorListMapIso g h L).inv).unmop.unop ≫ (G.opMopTensorListIso g (L.map h)).hom =
      (G.opMopTensorListIso (fun a ↦ g (h a)) L).hom ≫
        (tensorListMapIso (fun b ↦ (G.obj (g b)).unmop.unop) h L.reverse).hom ≫
        eqToHom (congrArg (tensorList (fun b ↦ (G.obj (g b)).unmop.unop)) List.map_reverse) := by
  let g' : β → D := fun b ↦ (G.obj (g b)).unmop.unop
  induction L with
  | nil =>
    dsimp only [List.map, List.reverse_nil, tensorList]
    rw [tensorListMapIso_nil, Iso.refl_inv, G.map_id, unmop_id, unop_id, Category.id_comp,
      opMopTensorListIso_nil_hom, opMopTensorListIso_nil_hom, tensorListMapIso_nil]
    simp
  | cons a L ih =>
    dsimp only [List.map]
    rw [tensorListMapIso_cons_inv, opMopTensorListIso_cons_hom, opMopTensorListIso_cons_hom]
    have hμ : (G.map (g (h a) ◁ (tensorListMapIso g h L).inv)).unmop.unop ≫
        (μ G (g (h a)) (tensorList g (L.map h))).unmop.unop =
        (μ G (g (h a)) (tensorList (fun x ↦ g (h x)) L)).unmop.unop ≫
          ((G.map (tensorListMapIso g h L).inv).unmop.unop ⊗ₘ 𝟙 (g' (h a))) := by
      have hm := congrArg (fun k ↦ k.unmop.unop)
        (LaxMonoidal.μ_natural_right G (g (h a)) (tensorListMapIso g h L).inv)
      simp only [unmop_comp, unop_comp] at hm
      exact hm.symm.trans (congrArg (_ ≫ ·) (tensorHom_id _ (g' (h a))).symm)
    rw [reassoc_of% hμ, tensorHom_comp_tensorHom_assoc, ih, Category.id_comp]
    have hAppEq : ∀ {R₁ R₂ : List β} (hr : R₁ = R₂),
        (eqToHom (congrArg (tensorList g') hr) ▷ (g' (h a) ⊗ 𝟙_ D)) ≫
          (tensorListAppendIso g' R₂ [h a]).hom =
        (tensorListAppendIso g' R₁ [h a]).hom ≫
          eqToHom (congrArg (tensorList g') (congrArg (· ++ [h a]) hr)) := by
      intro R₁ R₂ hr; subst hr; simp
    have hMapSing : (tensorListMapIso g' h [a]).hom = 𝟙 (g' (h a) ⊗ 𝟙_ D) := by
      rw [tensorListMapIso_cons_hom, tensorListMapIso_nil, Iso.refl_hom,
        MonoidalCategory.whiskerLeft_id]
    have hsplit3 : ∀ {A₁ A₂ A₃ A₄ B₁ B₂ : D} (p : A₁ ⟶ A₂) (q : A₂ ⟶ A₃) (r : A₃ ⟶ A₄)
        (s : B₁ ⟶ B₂),
        (p ≫ q ≫ r) ⊗ₘ s = (p ⊗ₘ s) ≫ (q ▷ B₂) ≫ (r ▷ B₂) := by
      intros; simp [tensorHom_def']
    rw [hsplit3]
    simp only [Category.assoc]
    have hMid : (tensorListMapIso g' h L.reverse).hom ▷ (g' (h a) ⊗ 𝟙_ D) =
        (tensorListMapIso g' h L.reverse).hom ⊗ₘ (tensorListMapIso g' h [a]).hom := by
      rw [hMapSing, tensorHom_id]
    have hMapApp : ((tensorListMapIso g' h L.reverse).hom ⊗ₘ (tensorListMapIso g' h [a]).hom) ≫
        (tensorListAppendIso g' (L.reverse.map h) ([a].map h)).hom =
        (tensorListAppendIso (fun x ↦ g' (h x)) L.reverse [a]).hom ≫
          (tensorListMapIso g' h (L.reverse ++ [a])).hom ≫
          eqToHom (congrArg (tensorList g') (List.map_append (f := h))) := by
      rw [← cancel_mono (eqToHom (congrArg (tensorList g') (List.map_append (f := h)).symm))]
      simpa [Category.assoc] using (tensorListMapIso_append_hom g' h L.reverse [a]).symm
    rw [reassoc_of% (hAppEq List.map_reverse), reassoc_of% hMid]
    dsimp only [List.map] at hMapApp ⊢
    rw [reassoc_of% hMapApp]
    simp only [eqToHom_trans]
    have hNatEq : ∀ {W₁ W₂ : List α} (hw : W₁ = W₂),
        eqToHom (congrArg (tensorList fun x ↦ g' (h x)) hw) ≫ (tensorListMapIso g' h W₂).hom =
          (tensorListMapIso g' h W₁).hom ≫
            eqToHom (congrArg (tensorList g') (congrArg (List.map h) hw)) := by
      intro W₁ W₂ hw; subst hw; simp
    rw [reassoc_of% (hNatEq List.reverse_cons.symm)]
    simp only [eqToHom_trans]
    rfl

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
  Functor.opMopTensorListIso_intertwine
    (fun M ↦ (τ.app (tensorList f M)).unmop.unop)
    (fun a ↦ (τ.app (f a)).unmop.unop)
    (congrArg (fun k ↦ k.unmop.unop) (IsMonoidal.unit (τ := τ)))
    (fun a M ↦ congrArg (fun k ↦ k.unmop.unop)
      (IsMonoidal.tensor (τ := τ) (f a) (tensorList f M))) L

end CategoryTheory.NatTrans
