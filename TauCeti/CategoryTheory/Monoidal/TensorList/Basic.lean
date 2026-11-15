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

For an indexed family `f : α → C` in a monoidal category `C` and a list `L : List α`,
`TauCeti.tensorList f L` is the right-associated tensor product of the entries of `L`, ending in
the tensor unit: `tensorList f [] = 𝟙_ C` and `tensorList f (a :: L) = f a ⊗ tensorList f L`.
On a constant list `List.replicate n a`, it reduces definitionally to `TauCeti.tensorPow (f a) n`.

Splitting a list into two blocks gives the isomorphism
`TauCeti.tensorListAppendIso f L M : tensorList f L ⊗ tensorList f M ≅ tensorList f (L ++ M)`,
built by recursion on `L` from associators and the left unitor without `eqToHom`. Reindexing along
`List.append_assoc` expresses the associativity of three-block splittings
(`TauCeti.tensorListAppendIso_assoc`), and `TauCeti.tensorListFlatMapIso` iterates block
concatenation along `List.flatMap`.

For a strong monoidal functor `F : C ⥤ D`, `CategoryTheory.Functor.mapTensorListIso` compares
`F.obj (tensorList f L)` with `tensorList (F.obj ∘ f) L`, compatibly with monoidal natural
transformations (`CategoryTheory.NatTrans.app_comp_mapTensorListIso_hom`) and block concatenation.
For a contravariant strong monoidal functor `G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ` such as the left or right dual
functor of a rigid category, `CategoryTheory.Functor.opMopTensorListIso` reverses the list order
via `List.reverseAux` with no `eqToHom`, again compatibly with monoidal natural transformations
(`CategoryTheory.NatTrans.unmop_unop_app_comp_opMopTensorListIso_hom`).

## Main declarations

* `TauCeti.tensorList`: right-associated tensor product of a list of indexed objects;
* `TauCeti.tensorListAppendIso` and `TauCeti.tensorListAppendIso_assoc`: block concatenation and
  its associativity;
* `TauCeti.tensorListCongrHom`, `TauCeti.tensorListCongrIso`, `TauCeti.tensorListMapIso`, and
  `TauCeti.tensorListFlatMapIso`: functoriality in the indexing family, list mapping, and
  flattening;
* `CategoryTheory.Functor.mapTensorListIso` and `CategoryTheory.Functor.opMopTensorListIso`:
  covariant and contravariant strong monoidal comparisons for `tensorList`.
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

universe v₁ v₂ u₁ u₂

namespace TauCeti

section Basic

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

-- Exposed and reducible so morphisms into `tensorList f (a :: L)` and `tensorList f []` elaborate
-- directly against `f a ⊗ tensorList f L` and `𝟙_ C`, matching `TauCeti.tensorPow`.
/-- Right-associated tensor product of a list of objects indexed by `f : α → C`, ending in the
tensor unit: `tensorList f [] = 𝟙_ C` and `tensorList f (a :: L) = f a ⊗ tensorList f L`. -/
@[expose, reducible]
def tensorList {α : Type*} (f : α → C) : List α → C
  | [] => 𝟙_ C
  | a :: L => f a ⊗ tensorList f L

/-- The tensor product of the empty list is the tensor unit. -/
theorem tensorList_nil {α : Type*} (f : α → C) : tensorList f [] = 𝟙_ C :=
  (rfl)

/-- The tensor product of `a :: L` is `f a ⊗ tensorList f L`. -/
theorem tensorList_cons {α : Type*} (f : α → C) (a : α) (L : List α) :
    tensorList f (a :: L) = f a ⊗ tensorList f L :=
  (rfl)

/-- On a replicated list, `tensorList` agrees with `tensorPow`. -/
@[simp]
theorem tensorList_replicate {α : Type*} (f : α → C) (n : ℕ) (a : α) :
    tensorList f (List.replicate n a) = tensorPow (f a) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (f a ⊗ ·) ih

/-- A singleton list tensors `f a` on the right with `𝟙_ C`, identified with `f a` by the right
unitor. -/
def tensorListSingletonIso {α : Type*} (f : α → C) (a : α) : tensorList f [a] ≅ f a :=
  ρ_ (f a)

/-- The forward morphism of `tensorListSingletonIso` is the right unitor. -/
@[simp]
theorem tensorListSingletonIso_hom {α : Type*} (f : α → C) (a : α) :
    (tensorListSingletonIso f a).hom = (ρ_ (f a)).hom :=
  (rfl)

/-- The inverse morphism of `tensorListSingletonIso` is the inverse right unitor. -/
@[simp]
theorem tensorListSingletonIso_inv {α : Type*} (f : α → C) (a : α) :
    (tensorListSingletonIso f a).inv = (ρ_ (f a)).inv :=
  (rfl)

/-- Block concatenation `tensorList f L ⊗ tensorList f M ≅ tensorList f (L ++ M)`, built from
associators and the left unitor by recursion on `L`. -/
def tensorListAppendIso {α : Type*} (f : α → C) :
    (L M : List α) → tensorList f L ⊗ tensorList f M ≅ tensorList f (L ++ M)
  | [], M => λ_ (tensorList f M)
  | a :: L, M =>
      α_ (f a) (tensorList f L) (tensorList f M) ≪≫
        whiskerLeftIso (f a) (tensorListAppendIso f L M)

/-- Concatenating an empty left block is the left unitor. -/
@[simp]
theorem tensorListAppendIso_nil {α : Type*} (f : α → C) (M : List α) :
    tensorListAppendIso f [] M = λ_ (tensorList f M) :=
  (rfl)

/-- Recursive step of `tensorListAppendIso` on `a :: L`. -/
theorem tensorListAppendIso_cons {α : Type*} (f : α → C) (a : α) (L M : List α) :
    tensorListAppendIso f (a :: L) M =
      α_ (f a) (tensorList f L) (tensorList f M) ≪≫
        whiskerLeftIso (f a) (tensorListAppendIso f L M) :=
  (rfl)

/-- Recursive step of `tensorListAppendIso`, on forward morphisms. -/
theorem tensorListAppendIso_cons_hom {α : Type*} (f : α → C) (a : α) (L M : List α) :
    (tensorListAppendIso f (a :: L) M).hom =
      (α_ (f a) (tensorList f L) (tensorList f M)).hom ≫
        f a ◁ (tensorListAppendIso f L M).hom :=
  (rfl)

/-- Recursive step of `tensorListAppendIso`, on inverse morphisms. -/
theorem tensorListAppendIso_cons_inv {α : Type*} (f : α → C) (a : α) (L M : List α) :
    (tensorListAppendIso f (a :: L) M).inv =
      f a ◁ (tensorListAppendIso f L M).inv ≫
        (α_ (f a) (tensorList f L) (tensorList f M)).inv :=
  (rfl)

/-- Concatenating a singleton left block removes its trailing tensor unit. -/
theorem tensorListAppendIso_singleton_hom {α : Type*} (f : α → C) (a : α) (M : List α) :
    (tensorListAppendIso f [a] M).hom = (ρ_ (f a)).hom ▷ tensorList f M := by
  rw [tensorListAppendIso_cons_hom, tensorListAppendIso_nil]
  monoidal_coherence

/-- Inverse of `tensorListAppendIso` on a singleton left block. -/
theorem tensorListAppendIso_singleton_inv {α : Type*} (f : α → C) (a : α) (M : List α) :
    (tensorListAppendIso f [a] M).inv = (ρ_ (f a)).inv ▷ tensorList f M := by
  rw [tensorListAppendIso_cons_inv, tensorListAppendIso_nil]
  monoidal_coherence

/-- Concatenating an empty right block is the right unitor, up to `List.append_nil`. -/
theorem tensorListAppendIso_nil_right_hom {α : Type*} (f : α → C) (L : List α) :
    (tensorListAppendIso f L []).hom =
      (ρ_ (tensorList f L)).hom ≫ eqToHom (congrArg (tensorList f) (List.append_nil L).symm) := by
  induction L with
  | nil => exact unitors_equal.trans (Category.comp_id _).symm
  | cons a L ih =>
    rw [tensorListAppendIso_cons_hom, ih]
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_eqToHom,
      MonoidalCategory.whiskerLeft_rightUnitor, Category.assoc, Iso.hom_inv_id_assoc]

/-- **Associativity of block concatenation**: splitting a three-block list `(L ++ M) ++ N` in
either order agrees up to `List.append_assoc`. -/
theorem tensorListAppendIso_assoc {α : Type*} (f : α → C) (L M N : List α) :
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
          rw [show (tensorListAppendIso f ((a :: L) ++ M) N).hom = _ from
            tensorListAppendIso_cons_hom f a (L ++ M) N, tensorListAppendIso_cons_hom]
          monoidal
      _ = _ := by
          rw [ih]
          simp only [tensorListAppendIso_cons_hom, MonoidalCategory.whiskerLeft_comp,
            MonoidalCategory.whiskerLeft_eqToHom]
          rw [← cancel_mono (eqToHom (congrArg (tensorList f) (List.append_assoc (a :: L) M N)))]
          simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
          monoidal

/-! ### Functoriality in the indexing family -/

/-- Tensor product of a pointwise family of morphisms `φ a : f₁ a ⟶ f₂ a` along `L : List α`. -/
def tensorListCongrHom {α : Type*} {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) :
    (L : List α) → tensorList f₁ L ⟶ tensorList f₂ L
  | [] => 𝟙 (𝟙_ C)
  | a :: L => φ a ⊗ₘ tensorListCongrHom φ L

/-- On the empty list, `tensorListCongrHom` is the identity on the tensor unit. -/
@[simp]
theorem tensorListCongrHom_nil {α : Type*} {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a) :
    tensorListCongrHom φ [] = 𝟙 (𝟙_ C) :=
  (rfl)

/-- Recursive step of `tensorListCongrHom` on `a :: L`. -/
@[simp]
theorem tensorListCongrHom_cons {α : Type*} {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a)
    (a : α) (L : List α) :
    tensorListCongrHom φ (a :: L) = φ a ⊗ₘ tensorListCongrHom φ L :=
  (rfl)

/-- Pointwise identities induce the identity morphism on `tensorList f L`. -/
@[simp]
theorem tensorListCongrHom_id {α : Type*} (f : α → C) (L : List α) :
    tensorListCongrHom (fun a ↦ 𝟙 (f a)) L = 𝟙 (tensorList f L) := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [tensorListCongrHom_cons, ih, id_tensorHom_id]

/-- Pointwise composites induce the composite morphism on `tensorList`. -/
@[simp, reassoc]
theorem tensorListCongrHom_comp {α : Type*} {f₁ f₂ f₃ : α → C}
    (φ : ∀ a, f₁ a ⟶ f₂ a) (ψ : ∀ a, f₂ a ⟶ f₃ a) (L : List α) :
    tensorListCongrHom (fun a ↦ φ a ≫ ψ a) L =
      tensorListCongrHom φ L ≫ tensorListCongrHom ψ L := by
  induction L with
  | nil => exact (Category.comp_id _).symm
  | cons a L ih => rw [tensorListCongrHom_cons, tensorListCongrHom_cons,
      tensorListCongrHom_cons, ih, tensorHom_comp_tensorHom]

/-- Transporting along a list equality commutes with `tensorListCongrHom`. -/
@[reassoc]
theorem tensorListCongrHom_eqToHom {α : Type*} {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a)
    {L M : List α} (h : L = M) :
    tensorListCongrHom φ L ≫ eqToHom (congrArg (tensorList f₂) h) =
      eqToHom (congrArg (tensorList f₁) h) ≫ tensorListCongrHom φ M := by
  subst h; simp

/-- Tensor product of a pointwise family of isomorphisms `e a : f₁ a ≅ f₂ a` along `L : List α`. -/
def tensorListCongrIso {α : Type*} {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : List α) :
    tensorList f₁ L ≅ tensorList f₂ L where
  hom := tensorListCongrHom (fun a ↦ (e a).hom) L
  inv := tensorListCongrHom (fun a ↦ (e a).inv) L
  hom_inv_id := by simp [← tensorListCongrHom_comp]
  inv_hom_id := by simp [← tensorListCongrHom_comp]

/-- Forward morphism of `tensorListCongrIso`. -/
@[simp]
theorem tensorListCongrIso_hom {α : Type*} {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : List α) :
    (tensorListCongrIso e L).hom = tensorListCongrHom (fun a ↦ (e a).hom) L :=
  (rfl)

/-- Inverse morphism of `tensorListCongrIso`. -/
@[simp]
theorem tensorListCongrIso_inv {α : Type*} {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : List α) :
    (tensorListCongrIso e L).inv = tensorListCongrHom (fun a ↦ (e a).inv) L :=
  (rfl)

/-- Block concatenation is natural with respect to `tensorListCongrHom`. -/
@[reassoc]
theorem tensorListAppendIso_hom_naturality {α : Type*} {f₁ f₂ : α → C}
    (φ : ∀ a, f₁ a ⟶ f₂ a) (L M : List α) :
    (tensorListCongrHom φ L ⊗ₘ tensorListCongrHom φ M) ≫ (tensorListAppendIso f₂ L M).hom =
      (tensorListAppendIso f₁ L M).hom ≫ tensorListCongrHom φ (L ++ M) := by
  induction L with
  | nil => simp [tensorListAppendIso_nil]
  | cons a L ih =>
    rw [tensorListAppendIso_cons_hom, tensorListAppendIso_cons_hom, tensorListCongrHom_cons,
      show tensorListCongrHom φ ((a :: L) ++ M) = φ a ⊗ₘ tensorListCongrHom φ (L ++ M) from rfl]
    calc _ = (α_ (f₁ a) (tensorList f₁ L) (tensorList f₁ M)).hom ≫
          (φ a ⊗ₘ ((tensorListCongrHom φ L ⊗ₘ tensorListCongrHom φ M) ≫
            (tensorListAppendIso f₂ L M).hom)) := by
          monoidal
      _ = _ := by
          rw [ih, tensorHom_def', tensorHom_def' (φ a)]
          monoidal

/-! ### Mapping and flattening lists -/

/-- Structural isomorphism `tensorList (fun a ↦ g (h a)) L ≅ tensorList g (L.map h)` built by
recursion on `L` without `eqToHom`. -/
def tensorListMapIso {α β : Type*} (g : β → C) (h : α → β) :
    (L : List α) → tensorList (fun a ↦ g (h a)) L ≅ tensorList g (L.map h)
  | [] => Iso.refl (𝟙_ C)
  | a :: L => whiskerLeftIso (g (h a)) (tensorListMapIso g h L)

/-- On the empty list, `tensorListMapIso` is the identity. -/
@[simp]
theorem tensorListMapIso_nil {α β : Type*} (g : β → C) (h : α → β) :
    tensorListMapIso g h [] = Iso.refl (𝟙_ C) :=
  (rfl)

/-- Recursive step of `tensorListMapIso` on forward morphisms. -/
@[simp]
theorem tensorListMapIso_cons_hom {α β : Type*} (g : β → C) (h : α → β) (a : α) (L : List α) :
    (tensorListMapIso g h (a :: L)).hom = g (h a) ◁ (tensorListMapIso g h L).hom :=
  (rfl)

/-- Recursive step of `tensorListMapIso` on inverse morphisms. -/
@[simp]
theorem tensorListMapIso_cons_inv {α β : Type*} (g : β → C) (h : α → β) (a : α) (L : List α) :
    (tensorListMapIso g h (a :: L)).inv = g (h a) ◁ (tensorListMapIso g h L).inv :=
  (rfl)

/-- Object-level equality underlying `tensorListMapIso`. -/
theorem tensorList_map {α β : Type*} (g : β → C) (h : α → β) (L : List α) :
    tensorList g (L.map h) = tensorList (fun a ↦ g (h a)) L := by
  induction L with
  | nil => rfl
  | cons a L ih => exact congrArg (g (h a) ⊗ ·) ih

/-- Although constructed from `whiskerLeftIso` without `eqToHom`, `(tensorListMapIso g h L).hom`
agrees with `eqToHom (tensorList_map g h L).symm`. -/
theorem tensorListMapIso_hom_eq_eqToHom {α β : Type*} (g : β → C) (h : α → β) (L : List α) :
    (tensorListMapIso g h L).hom = eqToHom (tensorList_map g h L).symm := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [tensorListMapIso_cons_hom, ih, MonoidalCategory.whiskerLeft_eqToHom]

/-- Inverse form of `tensorListMapIso_hom_eq_eqToHom`. -/
theorem tensorListMapIso_inv_eq_eqToHom {α β : Type*} (g : β → C) (h : α → β) (L : List α) :
    (tensorListMapIso g h L).inv = eqToHom (tensorList_map g h L) := by
  rw [← cancel_epi (tensorListMapIso g h L).hom, Iso.hom_inv_id, tensorListMapIso_hom_eq_eqToHom,
    eqToHom_trans, eqToHom_refl]

/-- Naturality of `tensorListMapIso` in the target family. -/
@[reassoc]
theorem tensorListMapIso_hom_naturality {α β : Type*} {g₁ g₂ : β → C} (φ : ∀ b, g₁ b ⟶ g₂ b)
    (h : α → β) (L : List α) :
    tensorListCongrHom (fun a ↦ φ (h a)) L ≫ (tensorListMapIso g₂ h L).hom =
      (tensorListMapIso g₁ h L).hom ≫ tensorListCongrHom φ (L.map h) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [tensorListCongrHom_cons, tensorListMapIso_cons_hom, tensorListMapIso_cons_hom,
      show tensorListCongrHom φ ((a :: L).map h) = φ (h a) ⊗ₘ tensorListCongrHom φ (L.map h) from
        rfl]
    rw [tensorHom_def, Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ih,
      MonoidalCategory.whiskerLeft_comp, ← whisker_exchange_assoc, ← tensorHom_def]

/-- Structural isomorphism `tensorList (fun a ↦ tensorList f (g a)) L ≅ tensorList f (L.flatMap g)`
iterating `tensorListAppendIso` along `L` without `eqToHom`. -/
def tensorListFlatMapIso {α β : Type*} (f : β → C) (g : α → List β) :
    (L : List α) → tensorList (fun a ↦ tensorList f (g a)) L ≅ tensorList f (L.flatMap g)
  | [] => Iso.refl (𝟙_ C)
  | a :: L =>
      whiskerLeftIso (tensorList f (g a)) (tensorListFlatMapIso f g L) ≪≫
        tensorListAppendIso f (g a) (L.flatMap g)

/-- On the empty list, `tensorListFlatMapIso` is the identity. -/
@[simp]
theorem tensorListFlatMapIso_nil {α β : Type*} (f : β → C) (g : α → List β) :
    tensorListFlatMapIso f g [] = Iso.refl (𝟙_ C) :=
  (rfl)

/-- Recursive step of `tensorListFlatMapIso` on forward morphisms. -/
theorem tensorListFlatMapIso_cons_hom {α β : Type*} (f : β → C) (g : α → List β)
    (a : α) (L : List α) :
    (tensorListFlatMapIso f g (a :: L)).hom =
      tensorList f (g a) ◁ (tensorListFlatMapIso f g L).hom ≫
        (tensorListAppendIso f (g a) (L.flatMap g)).hom :=
  (rfl)

/-- Recursive step of `tensorListFlatMapIso` on inverse morphisms. -/
theorem tensorListFlatMapIso_cons_inv {α β : Type*} (f : β → C) (g : α → List β)
    (a : α) (L : List α) :
    (tensorListFlatMapIso f g (a :: L)).inv =
      (tensorListAppendIso f (g a) (L.flatMap g)).inv ≫
        tensorList f (g a) ◁ (tensorListFlatMapIso f g L).inv :=
  (rfl)

/-- Naturality of `tensorListFlatMapIso` in the target family. -/
@[reassoc]
theorem tensorListFlatMapIso_hom_naturality {α β : Type*} {f₁ f₂ : β → C}
    (φ : ∀ b, f₁ b ⟶ f₂ b) (g : α → List β) (L : List α) :
    tensorListCongrHom (fun a ↦ tensorListCongrHom φ (g a)) L ≫
        (tensorListFlatMapIso f₂ g L).hom =
      (tensorListFlatMapIso f₁ g L).hom ≫ tensorListCongrHom φ (L.flatMap g) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [tensorListFlatMapIso_cons_hom, tensorListCongrHom_cons, Category.assoc]
    rw [tensorHom_def'_assoc, ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ih, MonoidalCategory.whiskerLeft_comp_assoc,
      ← tensorHom_def'_assoc, tensorListAppendIso_hom_naturality]
    rfl

end Basic

end TauCeti

/-! ### Covariant and contravariant strong monoidal comparisons -/

namespace CategoryTheory.Functor

open TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

section Covariant

/-- Comparison `F.obj (tensorList f L) ≅ tensorList (fun a ↦ F.obj (f a)) L` for a strong
monoidal functor `F`, built from `εIso` and `μIso` by recursion on `L`. -/
def mapTensorListIso (F : C ⥤ D) [F.Monoidal] {α : Type*} (f : α → C) :
    (L : List α) → F.obj (tensorList f L) ≅ tensorList (fun a ↦ F.obj (f a)) L
  | [] => (εIso F).symm
  | a :: L =>
      (μIso F (f a) (tensorList f L)).symm ≪≫
        whiskerLeftIso (F.obj (f a)) (F.mapTensorListIso f L)

variable (F : C ⥤ D) [F.Monoidal]

/-- On the empty list, `F.mapTensorListIso` is `(εIso F).symm`. -/
@[simp]
theorem mapTensorListIso_nil_hom {α : Type*} (f : α → C) :
    (F.mapTensorListIso f []).hom = η F :=
  (rfl)

/-- On the empty list, the inverse of `F.mapTensorListIso` is `ε F`. -/
@[simp]
theorem mapTensorListIso_nil_inv {α : Type*} (f : α → C) :
    (F.mapTensorListIso f []).inv = ε F :=
  (rfl)

/-- Recursive step of `F.mapTensorListIso` on forward morphisms. -/
theorem mapTensorListIso_cons_hom {α : Type*} (f : α → C) (a : α) (L : List α) :
    (F.mapTensorListIso f (a :: L)).hom =
      δ F (f a) (tensorList f L) ≫ F.obj (f a) ◁ (F.mapTensorListIso f L).hom :=
  (rfl)

/-- Recursive step of `F.mapTensorListIso` on inverse morphisms. -/
theorem mapTensorListIso_cons_inv {α : Type*} (f : α → C) (a : α) (L : List α) :
    (F.mapTensorListIso f (a :: L)).inv =
      F.obj (f a) ◁ (F.mapTensorListIso f L).inv ≫ μ F (f a) (tensorList f L) :=
  (rfl)

/-- `F.mapTensorListIso` commutes with block concatenation `tensorListAppendIso`. -/
theorem mapTensorListIso_append_hom {α : Type*} (f : α → C) (L M : List α) :
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
    rw [tensorListAppendIso_cons_hom, tensorListAppendIso_cons_hom,
      show (F.mapTensorListIso f ((a :: L) ++ M)).hom = _ from
        F.mapTensorListIso_cons_hom f a (L ++ M),
      F.mapTensorListIso_cons_hom]
    dsimp only [List.cons_append, tensorList]
    rw [Functor.map_comp, Category.assoc, map_whiskerLeft, Category.assoc, Category.assoc,
      μ_δ_assoc, ← MonoidalCategory.whiskerLeft_comp, ih]
    simp only [MonoidalCategory.whiskerLeft_comp]
    rw [← cancel_epi (μ F (f a ⊗ tensorList f L) (tensorList f M)),
      ← cancel_epi (μ F (f a) (tensorList f L) ▷ F.obj (tensorList f M))]
    simp only [Category.assoc, μ_δ_assoc, whiskerRight_μ_δ_assoc, map_associator,
      whiskerLeft_μ_δ_assoc, tensorHom_def', MonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
    rw [whisker_exchange_assoc, whiskerRight_μ_δ_assoc]
    monoidal

/-- Naturality of `F.mapTensorListIso` in the indexing family. -/
@[reassoc]
theorem mapTensorListIso_hom_naturality {α : Type*} {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a)
    (L : List α) :
    F.map (tensorListCongrHom φ L) ≫ (F.mapTensorListIso f₂ L).hom =
      (F.mapTensorListIso f₁ L).hom ≫ tensorListCongrHom (fun a ↦ F.map (φ a)) L := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [tensorListCongrHom_cons, mapTensorListIso_cons_hom, mapTensorListIso_cons_hom,
      tensorListCongrHom_cons]
    dsimp only [tensorList]
    rw [← cancel_epi (μ F (f₁ a) (tensorList f₁ L)), ← LaxMonoidal.μ_natural_assoc, μ_δ_assoc,
      Category.assoc, μ_δ_assoc, tensorHom_def', Category.assoc, ← whisker_exchange,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ih, MonoidalCategory.whiskerLeft_comp_assoc,
      ← tensorHom_def']

end Covariant

section Contravariant

private def opMopUnitIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] :
    (G.obj (𝟙_ C)).unmop.unop ≅ 𝟙_ D where
  hom := (ε G).unmop.unop
  inv := (η G).unmop.unop
  hom_inv_id := congrArg (fun k ↦ k.unmop.unop) (η_ε G)
  inv_hom_id := congrArg (fun k ↦ k.unmop.unop) (ε_η G)

private def opMopTensorIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] (X Y : C) :
    (G.obj (X ⊗ Y)).unmop.unop ≅ (G.obj Y).unmop.unop ⊗ (G.obj X).unmop.unop where
  hom := (μ G X Y).unmop.unop
  inv := (δ G X Y).unmop.unop
  hom_inv_id := congrArg (fun k ↦ k.unmop.unop) (δ_μ G X Y)
  inv_hom_id := congrArg (fun k ↦ k.unmop.unop) (μ_δ G X Y)

/-- Auxiliary accumulator isomorphism for `opMopTensorListIso`, using `List.reverseAux` so every
step is definitional on list indices without `eqToHom`. -/
def opMopTensorListAuxIso (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal] {α : Type*} (f : α → C) :
    (L acc : List α) →
      (G.obj (tensorList f L)).unmop.unop ⊗
          tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc ≅
        tensorList (fun a ↦ (G.obj (f a)).unmop.unop) (L.reverseAux acc)
  | [], acc =>
      whiskerRightIso (opMopUnitIso G) _ ≪≫
        λ_ (tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc)
  | a :: L, acc =>
      whiskerRightIso (opMopTensorIso G (f a) (tensorList f L)) _ ≪≫
        α_ (G.obj (tensorList f L)).unmop.unop (G.obj (f a)).unmop.unop
          (tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc) ≪≫
        G.opMopTensorListAuxIso f L (a :: acc)

variable (G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ) [G.Monoidal]

/-- Base step of `opMopTensorListAuxIso` on forward morphisms. -/
theorem opMopTensorListAuxIso_nil_hom {α : Type*} (f : α → C) (acc : List α) :
    (G.opMopTensorListAuxIso f [] acc).hom =
      (ε G).unmop.unop ▷ tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc ≫
        (λ_ (tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc)).hom :=
  (rfl)

/-- Recursive step of `opMopTensorListAuxIso` on forward morphisms. -/
theorem opMopTensorListAuxIso_cons_hom {α : Type*} (f : α → C) (a : α) (L acc : List α) :
    (G.opMopTensorListAuxIso f (a :: L) acc).hom =
      (μ G (f a) (tensorList f L)).unmop.unop ▷
          tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc ≫
        (α_ (G.obj (tensorList f L)).unmop.unop (G.obj (f a)).unmop.unop
          (tensorList (fun a ↦ (G.obj (f a)).unmop.unop) acc)).hom ≫
        (G.opMopTensorListAuxIso f L (a :: acc)).hom :=
  (rfl)

/-- Reversed-list comparison `(G.obj (tensorList f L)).unmop.unop ≅ tensorList _ L.reverse` for a
contravariant strong monoidal functor `G : C ⥤ (Dᵒᵖ)ᴹᵒᵖ`, constructed without `eqToHom`. -/
def opMopTensorListIso {α : Type*} (f : α → C) (L : List α) :
    (G.obj (tensorList f L)).unmop.unop ≅
      tensorList (fun a ↦ (G.obj (f a)).unmop.unop) L.reverse :=
  (ρ_ (G.obj (tensorList f L)).unmop.unop).symm ≪≫ G.opMopTensorListAuxIso f L []

/-- Forward morphism of `opMopTensorListIso`. -/
theorem opMopTensorListIso_hom {α : Type*} (f : α → C) (L : List α) :
    (G.opMopTensorListIso f L).hom =
      (ρ_ (G.obj (tensorList f L)).unmop.unop).inv ≫ (G.opMopTensorListAuxIso f L []).hom :=
  (rfl)

/-- On the empty list, `opMopTensorListIso` is `(ε G).unmop.unop`. -/
theorem opMopTensorListIso_nil_hom {α : Type*} (f : α → C) :
    (G.opMopTensorListIso f []).hom = (ε G).unmop.unop := by
  rw [opMopTensorListIso_hom, opMopTensorListAuxIso_nil_hom]
  dsimp only [List.reverse, List.reverseAux, tensorList]
  rw [unitors_equal, rightUnitor_naturality, Iso.inv_hom_id_assoc]

/-- Naturality of `opMopTensorListAuxIso` in the indexing family. -/
@[reassoc]
theorem opMopTensorListAuxIso_hom_naturality {α : Type*} {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a)
    (L acc : List α) :
    ((G.map (tensorListCongrHom φ L)).unmop.unop ⊗ₘ
        tensorListCongrHom (fun a ↦ (G.map (φ a)).unmop.unop) acc) ≫
      (G.opMopTensorListAuxIso f₁ L acc).hom =
      (G.opMopTensorListAuxIso f₂ L acc).hom ≫
        tensorListCongrHom (fun a ↦ (G.map (φ a)).unmop.unop) (L.reverseAux acc) := by
  induction L generalizing acc with
  | nil =>
    rw [opMopTensorListAuxIso_nil_hom, opMopTensorListAuxIso_nil_hom, tensorListCongrHom_nil]
    dsimp only [List.reverseAux, tensorList, unmop_tensorUnit, unop_tensorUnit]
    rw [G.map_id, unmop_id, unop_id, id_tensorHom,
      whisker_exchange_assoc, leftUnitor_naturality, Category.assoc]
  | cons a L ih =>
    rw [opMopTensorListAuxIso_cons_hom, opMopTensorListAuxIso_cons_hom, tensorListCongrHom_cons]
    dsimp only [List.reverseAux, tensorList]
    have hμ : (G.map (φ a ⊗ₘ tensorListCongrHom φ L)).unmop.unop ≫
        (μ G (f₁ a) (tensorList f₁ L)).unmop.unop =
        (μ G (f₂ a) (tensorList f₂ L)).unmop.unop ≫
          ((G.map (tensorListCongrHom φ L)).unmop.unop ⊗ₘ (G.map (φ a)).unmop.unop) :=
      congrArg (fun k ↦ k.unmop.unop)
        (LaxMonoidal.μ_natural G (φ a) (tensorListCongrHom φ L)).symm
    simp only [Category.assoc]
    rw [← ih (a :: acc), tensorListCongrHom_cons]
    rw [← associator_naturality_assoc, tensorHom_def'_assoc, ← comp_whiskerRight_assoc, hμ]
    simp only [comp_whiskerRight, Category.assoc, whisker_exchange_assoc, tensorHom_def']
    rfl

/-- Naturality of `opMopTensorListIso` in the indexing family. -/
@[reassoc]
theorem opMopTensorListIso_hom_naturality {α : Type*} {f₁ f₂ : α → C} (φ : ∀ a, f₁ a ⟶ f₂ a)
    (L : List α) :
    (G.map (tensorListCongrHom φ L)).unmop.unop ≫ (G.opMopTensorListIso f₁ L).hom =
      (G.opMopTensorListIso f₂ L).hom ≫
        tensorListCongrHom (fun a ↦ (G.map (φ a)).unmop.unop) L.reverse := by
  rw [opMopTensorListIso_hom, opMopTensorListIso_hom]
  dsimp only [List.reverse, tensorList]
  rw [Category.assoc, rightUnitor_inv_naturality_assoc]
  have h0 := G.opMopTensorListAuxIso_hom_naturality φ L []
  rw [tensorListCongrHom_nil] at h0
  dsimp only [tensorList] at h0
  rw [tensorHom_id] at h0
  exact _ ≫= h0

private theorem reverseAux_map_eq {α β : Type*} (h : α → β) (L acc : List α) :
    (L.map h).reverseAux (acc.map h) = (L.reverseAux acc).map h := by
  induction L generalizing acc with
  | nil => rfl
  | cons a _ ih => exact ih (a :: acc)

private theorem opMopTensorListAuxIso_map_hom {α β : Type*} (g : β → C) (h : α → β)
    (L acc : List α) :
    ((G.map (tensorListMapIso g h L).inv).unmop.unop ⊗ₘ
        (tensorListMapIso (fun b ↦ (G.obj (g b)).unmop.unop) h acc).hom) ≫
      (G.opMopTensorListAuxIso g (L.map h) (acc.map h)).hom =
      (G.opMopTensorListAuxIso (fun a ↦ g (h a)) L acc).hom ≫
        (tensorListMapIso (fun b ↦ (G.obj (g b)).unmop.unop) h (L.reverseAux acc)).hom ≫
        eqToHom (congrArg (tensorList (fun b ↦ (G.obj (g b)).unmop.unop))
          (reverseAux_map_eq h L acc).symm) := by
  induction L generalizing acc with
  | nil =>
    dsimp only [List.map, List.reverseAux, tensorList, unmop_tensorUnit, unop_tensorUnit]
    generalize_proofs
    rw [opMopTensorListAuxIso_nil_hom, opMopTensorListAuxIso_nil_hom,
      show (tensorListMapIso g h []).inv = 𝟙 (𝟙_ C) from rfl]
    dsimp only [List.reverseAux, tensorList, unmop_tensorUnit, unop_tensorUnit]
    rw [G.map_id, unmop_id, unop_id, id_tensorHom, whisker_exchange_assoc, leftUnitor_naturality,
      eqToHom_refl, Category.comp_id, Category.assoc]
  | cons a L ih =>
    have ihStep := ih (a :: acc)
    dsimp only [List.map, List.reverseAux, tensorList] at ihStep ⊢
    generalize_proofs at ihStep ⊢
    rw [opMopTensorListAuxIso_cons_hom, opMopTensorListAuxIso_cons_hom, tensorListMapIso_cons_inv,
      ← id_tensorHom (g (h a))]
    dsimp only [List.reverseAux, tensorList]
    have hμ : (G.map (𝟙 (g (h a)) ⊗ₘ (tensorListMapIso g h L).inv)).unmop.unop ≫
        (μ G (g (h a)) (tensorList g (L.map h))).unmop.unop =
        (μ G (g (h a)) (tensorList (fun x ↦ g (h x)) L)).unmop.unop ≫
          ((G.map (tensorListMapIso g h L).inv).unmop.unop ⊗ₘ
            𝟙 (G.obj (g (h a))).unmop.unop) := by
      have hnat := congrArg (fun k ↦ k.unmop.unop)
        (LaxMonoidal.μ_natural G (𝟙 (g (h a))) (tensorListMapIso g h L).inv).symm
      dsimp only [unmop_comp, unop_comp, unmop_tensorObj, unop_tensorObj,
        unmop_tensorHom, unop_tensorHom] at hnat
      rwa [G.map_id, unmop_id, unop_id] at hnat
    simp only [Category.assoc]
    rw [← ihStep, tensorListMapIso_cons_hom, ← id_tensorHom]
    rw [← associator_naturality_assoc, tensorHom_def'_assoc, ← comp_whiskerRight_assoc, hμ]
    simp only [comp_whiskerRight, Category.assoc, whisker_exchange_assoc, tensorHom_def',
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rfl

/-- Compatibility of `G.opMopTensorListIso` with list mapping `L.map h`. -/
@[reassoc]
theorem opMopTensorListIso_map_hom {α β : Type*} (g : β → C) (h : α → β) (L : List α) :
    (G.map (tensorListMapIso g h L).inv).unmop.unop ≫ (G.opMopTensorListIso g (L.map h)).hom =
      (G.opMopTensorListIso (fun a ↦ g (h a)) L).hom ≫
        (tensorListMapIso (fun b ↦ (G.obj (g b)).unmop.unop) h L.reverse).hom ≫
        eqToHom (congrArg (tensorList (fun b ↦ (G.obj (g b)).unmop.unop))
          List.map_reverse) := by
  rw [opMopTensorListIso_hom, opMopTensorListIso_hom]
  dsimp only [List.reverse, tensorList]
  rw [Category.assoc, rightUnitor_inv_naturality_assoc]
  have h0 := G.opMopTensorListAuxIso_map_hom g h L []
  rw [show (tensorListMapIso (fun b ↦ (G.obj (g b)).unmop.unop) h []).hom = 𝟙 (𝟙_ D) from rfl] at h0
  dsimp only [List.map, tensorList] at h0
  rw [tensorHom_id] at h0
  exact _ ≫= h0

end Contravariant

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

open TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- A monoidal natural transformation `τ : F ⟶ G` between strong monoidal functors intertwines
`mapTensorListIso` with `tensorListCongrHom`. -/
@[reassoc]
theorem app_comp_mapTensorListIso_hom {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    (τ : F ⟶ G) [NatTrans.IsMonoidal τ] {α : Type*} (f : α → C) (L : List α) :
    τ.app (tensorList f L) ≫ (G.mapTensorListIso f L).hom =
      (F.mapTensorListIso f L).hom ≫ tensorListCongrHom (fun a ↦ τ.app (f a)) L := by
  induction L with
  | nil =>
    rw [Functor.mapTensorListIso_nil_hom, Functor.mapTensorListIso_nil_hom, tensorListCongrHom_nil]
    dsimp only [tensorList]
    rw [Category.comp_id, ← cancel_epi (ε F), IsMonoidal.unit_assoc, ε_η, ε_η]
  | cons a L ih =>
    rw [Functor.mapTensorListIso_cons_hom, Functor.mapTensorListIso_cons_hom,
      tensorListCongrHom_cons]
    dsimp only [tensorList]
    rw [← cancel_epi (μ F (f a) (tensorList f L)), IsMonoidal.tensor_assoc, μ_δ_assoc,
      Category.assoc, μ_δ_assoc, tensorHom_def', Category.assoc, ← whisker_exchange,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ih, MonoidalCategory.whiskerLeft_comp_assoc,
      ← tensorHom_def']

private theorem unmop_unop_app_comp_opMopTensorListAuxIso_hom
    {G₁ G₂ : C ⥤ (Dᵒᵖ)ᴹᵒᵖ} [G₁.Monoidal] [G₂.Monoidal] (τ : G₁ ⟶ G₂) [NatTrans.IsMonoidal τ]
    {α : Type*} (f : α → C) (L acc : List α) :
    ((τ.app (tensorList f L)).unmop.unop ⊗ₘ
        tensorListCongrHom (fun a ↦ (τ.app (f a)).unmop.unop) acc) ≫
      (G₁.opMopTensorListAuxIso f L acc).hom =
      (G₂.opMopTensorListAuxIso f L acc).hom ≫
        tensorListCongrHom (fun a ↦ (τ.app (f a)).unmop.unop) (L.reverseAux acc) := by
  induction L generalizing acc with
  | nil =>
    rw [Functor.opMopTensorListAuxIso_nil_hom, Functor.opMopTensorListAuxIso_nil_hom]
    dsimp only [tensorList, List.reverseAux, unmop_tensorUnit, unop_tensorUnit]
    have hε : (τ.app (𝟙_ C)).unmop.unop ≫ (ε G₁).unmop.unop = (ε G₂).unmop.unop :=
      congrArg (fun k ↦ k.unmop.unop) (IsMonoidal.unit (τ := τ))
    rw [tensorHom_def'_assoc, ← comp_whiskerRight_assoc, hε, whisker_exchange_assoc,
      leftUnitor_naturality, Category.assoc]
  | cons a L ih =>
    rw [Functor.opMopTensorListAuxIso_cons_hom, Functor.opMopTensorListAuxIso_cons_hom]
    dsimp only [tensorList, List.reverseAux]
    have hμ : (τ.app (f a ⊗ tensorList f L)).unmop.unop ≫
        (μ G₁ (f a) (tensorList f L)).unmop.unop =
        (μ G₂ (f a) (tensorList f L)).unmop.unop ≫
          ((τ.app (tensorList f L)).unmop.unop ⊗ₘ (τ.app (f a)).unmop.unop) :=
      congrArg (fun k ↦ k.unmop.unop) (IsMonoidal.tensor (τ := τ) (f a) (tensorList f L))
    simp only [Category.assoc]
    rw [← ih (a :: acc), tensorListCongrHom_cons]
    rw [← associator_naturality_assoc, tensorHom_def'_assoc, ← comp_whiskerRight_assoc, hμ]
    simp only [comp_whiskerRight, Category.assoc, whisker_exchange_assoc, tensorHom_def']
    rfl

/-- A monoidal natural transformation `τ : G₁ ⟶ G₂` between contravariant strong monoidal functors
`C ⥤ (Dᵒᵖ)ᴹᵒᵖ` intertwines `opMopTensorListIso` with `tensorListCongrHom` on `L.reverse`. -/
@[reassoc]
theorem unmop_unop_app_comp_opMopTensorListIso_hom
    {G₁ G₂ : C ⥤ (Dᵒᵖ)ᴹᵒᵖ} [G₁.Monoidal] [G₂.Monoidal] (τ : G₁ ⟶ G₂) [NatTrans.IsMonoidal τ]
    {α : Type*} (f : α → C) (L : List α) :
    (τ.app (tensorList f L)).unmop.unop ≫ (G₁.opMopTensorListIso f L).hom =
      (G₂.opMopTensorListIso f L).hom ≫
        tensorListCongrHom (fun a ↦ (τ.app (f a)).unmop.unop) L.reverse := by
  rw [Functor.opMopTensorListIso_hom, Functor.opMopTensorListIso_hom]
  dsimp only [List.reverse, tensorList]
  rw [Category.assoc, rightUnitor_inv_naturality_assoc]
  have h0 := unmop_unop_app_comp_opMopTensorListAuxIso_hom τ f L []
  rw [tensorListCongrHom_nil] at h0
  dsimp only [tensorList] at h0
  rw [tensorHom_id] at h0
  exact _ ≫= h0

end CategoryTheory.NatTrans
