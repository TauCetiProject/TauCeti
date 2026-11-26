/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Ordered tensor products of families over lists

For a family `X : ι → C` of objects of a monoidal category and a list `l` of indices,
`TauCeti.listTensor X l` is the ordered tensor product of the `X i` for `i` in `l`, nested to the
right: `X l₀ ⊗ (X l₁ ⊗ (⋯ ⊗ (X lₖ ⊗ 𝟙_ C)))`, with `listTensor X [] = 𝟙_ C`. Unlike
`CategoryTheory.Functor.tensorPow`, which tensors a tuple indexed by `Fin n`, the factors are
labelled by the entries of the list, so that sublists, concatenations and reorderings of the
labels give tensor products of the same family. This is the form in which tensor products over
the fibers of a map of finite sets appear in the category of operators of a symmetric monoidal
category.

The structural isomorphisms are built from the unitors and associators:

* `TauCeti.listTensorAppendIso X l₁ l₂`, from `listTensor X (l₁ ++ l₂)` to
  `listTensor X l₁ ⊗ listTensor X l₂`, splits a concatenation;
* `TauCeti.listTensorFlatMapIso X L M : listTensor X (M.flatMap L) ≅ listTensor Y M`, where
  `Y j = listTensor X (L j)`, groups the factors of a concatenation of the lists `L j` for `j` in
  `M`.

They are natural in the family (`listTensorAppendIso_hom_naturality`,
`listTensorFlatMapIso_hom_naturality`), associative (`listTensorAppendIso_hom_assoc`,
`listTensorFlatMapIso_hom_listTensorAppendIso_hom`, `listTensorFlatMapIso_hom_flatMap`) and unital
(`listTensorAppendIso_nil_right_hom`, `listTensorFlatMapIso_hom_listTensorMap_rightUnitor`,
`listTensorFlatMapIso_singleton_hom_rightUnitor_hom`): grouping factors in two stages agrees with
grouping them at once, and groups of one factor can be removed. Reordering the factors, which
needs a symmetric monoidal structure, is in `TauCeti.CategoryTheory.Monoidal.Braided.ListTensor`.

## References

* J. Lurie, *Higher Algebra*, Construction 2.0.0.1.
-/

public section

open CategoryTheory MonoidalCategory

universe v u w w' w''

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {ι : Type w} {κ : Type w'}
  {ν : Type w''}

/-- The ordered tensor product `X l₀ ⊗ (X l₁ ⊗ (⋯ ⊗ (X lₖ ⊗ 𝟙_ C)))` of the members of the family
`X` labelled by the entries of the list `l`. The body is exposed so that morphisms out of
`listTensor X (a :: l)` can be used as morphisms out of `X a ⊗ listTensor X l`. -/
@[expose, implicit_reducible]
def listTensor (X : ι → C) : List ι → C
  | [] => 𝟙_ C
  | a :: l => X a ⊗ listTensor X l

@[simp]
lemma listTensor_nil (X : ι → C) : listTensor X [] = 𝟙_ C :=
  rfl

@[simp]
lemma listTensor_cons (X : ι → C) (a : ι) (l : List ι) :
    listTensor X (a :: l) = X a ⊗ listTensor X l :=
  rfl

/-- The tensor product over a list of a family of morphisms `f i : X i ⟶ Y i`. -/
def listTensorMap {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) :
    (l : List ι) → (listTensor X l ⟶ listTensor Y l)
  | [] => 𝟙 _
  | a :: l => f a ⊗ₘ listTensorMap f l

@[simp]
lemma listTensorMap_nil {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) : listTensorMap f [] = 𝟙 (𝟙_ C) :=
  (rfl)

@[simp]
lemma listTensorMap_cons {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) (a : ι) (l : List ι) :
    listTensorMap f (a :: l) = f a ⊗ₘ listTensorMap f l :=
  (rfl)

@[simp]
lemma listTensorMap_id (X : ι → C) (l : List ι) :
    listTensorMap (fun i ↦ 𝟙 (X i)) l = 𝟙 (listTensor X l) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

@[reassoc (attr := simp)]
lemma listTensorMap_comp {X Y Z : ι → C} (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i)
    (l : List ι) :
    listTensorMap f l ≫ listTensorMap g l = listTensorMap (fun i ↦ f i ≫ g i) l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [tensorHom_comp_tensorHom, ih]

/-- The ordered tensor product over a concatenation `l₁ ++ l₂` is the tensor product of the
ordered tensor products over `l₁` and over `l₂`. -/
def listTensorAppendIso (X : ι → C) :
    (l₁ l₂ : List ι) → (listTensor X (l₁ ++ l₂) ≅ listTensor X l₁ ⊗ listTensor X l₂)
  | [], _ => (λ_ _).symm
  | a :: l₁, l₂ => whiskerLeftIso (X a) (listTensorAppendIso X l₁ l₂) ≪≫ (α_ _ _ _).symm

@[simp]
lemma listTensorAppendIso_nil (X : ι → C) (l : List ι) :
    listTensorAppendIso X [] l = (λ_ _).symm :=
  (rfl)

@[simp]
lemma listTensorAppendIso_cons (X : ι → C) (a : ι) (l₁ l₂ : List ι) :
    listTensorAppendIso X (a :: l₁) l₂ =
      whiskerLeftIso (X a) (listTensorAppendIso X l₁ l₂) ≪≫ (α_ _ _ _).symm :=
  (rfl)

/-- Splitting a concatenation is natural in the family. -/
@[reassoc]
lemma listTensorAppendIso_hom_naturality {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) (l₁ l₂ : List ι) :
    listTensorMap f (l₁ ++ l₂) ≫ (listTensorAppendIso Y l₁ l₂).hom =
      (listTensorAppendIso X l₁ l₂).hom ≫ (listTensorMap f l₁ ⊗ₘ listTensorMap f l₂) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    dsimp only [List.cons_append]
    simp only [listTensorMap_cons, listTensorAppendIso_cons, Iso.trans_hom, whiskerLeftIso_hom,
      Iso.symm_hom]
    rw [tensorHom_def_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ih]
    simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← whisker_exchange_assoc]
    monoidal

/-- Splitting a concatenation of three lists is associative. -/
lemma listTensorAppendIso_hom_assoc (X : ι → C) (l₁ l₂ l₃ : List ι) :
    (listTensorAppendIso X (l₁ ++ l₂) l₃).hom ≫ (listTensorAppendIso X l₁ l₂).hom ▷ _ ≫
        (α_ _ _ _).hom =
      eqToHom (by rw [List.append_assoc]) ≫ (listTensorAppendIso X l₁ (l₂ ++ l₃)).hom ≫
        _ ◁ (listTensorAppendIso X l₂ l₃).hom := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    dsimp only [List.cons_append]
    simp only [listTensorAppendIso_cons, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom]
    have h := congrArg (X a ◁ ·) ih
    simp only [MonoidalCategory.whiskerLeft_comp, whiskerLeft_eqToHom] at h
    calc _ = (X a ◁ (listTensorAppendIso X (l₁ ++ l₂) l₃).hom ≫
            X a ◁ (listTensorAppendIso X l₁ l₂).hom ▷ listTensor X l₃ ≫
            X a ◁ (α_ (listTensor X l₁) (listTensor X l₂) (listTensor X l₃)).hom) ≫
          (α_ _ _ _).inv := by monoidal
      _ = _ := by rw [h]; simp

/-- Splitting off the empty list on the right is the right unitor. -/
lemma listTensorAppendIso_nil_right_hom (X : ι → C) (l : List ι) :
    (listTensorAppendIso X l []).hom ≫ (ρ_ _).hom = eqToHom (by rw [List.append_nil]) := by
  induction l with
  | nil => simp only [listTensorAppendIso_nil, Iso.symm_hom, eqToHom_refl]; monoidal
  | cons a l ih =>
    dsimp only [List.cons_append]
    have h := congrArg (X a ◁ ·) ih
    simp only [MonoidalCategory.whiskerLeft_comp, whiskerLeft_eqToHom] at h
    simp only [listTensorAppendIso_cons, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
      Category.assoc]
    calc _ = X a ◁ (listTensorAppendIso X l []).hom ≫ X a ◁ (ρ_ (listTensor X l)).hom := by
          monoidal
      _ = _ := by rw [h]

/-- Transporting the second list of a splitting along an equality of lists. -/
@[reassoc]
lemma eqToHom_comp_listTensorAppendIso_hom (X : ι → C) (l₁ : List ι) {l₂ l₂' : List ι}
    (h : l₂ = l₂') :
    eqToHom (by rw [h]) ≫ (listTensorAppendIso X l₁ l₂').hom =
      (listTensorAppendIso X l₁ l₂).hom ≫ _ ◁ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The ordered tensor product over a concatenation `M.flatMap L` of lists `L j` is the ordered
tensor product, over `M`, of the ordered tensor products over the lists `L j`. -/
def listTensorFlatMapIso (X : ι → C) (L : κ → List ι) :
    (M : List κ) → (listTensor X (M.flatMap L) ≅ listTensor (fun j ↦ listTensor X (L j)) M)
  | [] => Iso.refl _
  | j :: M => listTensorAppendIso X (L j) (M.flatMap L) ≪≫
      whiskerLeftIso _ (listTensorFlatMapIso X L M)

@[simp]
lemma listTensorFlatMapIso_nil (X : ι → C) (L : κ → List ι) :
    listTensorFlatMapIso X L [] = Iso.refl _ :=
  (rfl)

@[simp]
lemma listTensorFlatMapIso_cons (X : ι → C) (L : κ → List ι) (j : κ) (M : List κ) :
    listTensorFlatMapIso X L (j :: M) = listTensorAppendIso X (L j) (M.flatMap L) ≪≫
      whiskerLeftIso _ (listTensorFlatMapIso X L M) :=
  (rfl)

/-- Grouping factors is natural in the family. -/
@[reassoc]
lemma listTensorFlatMapIso_hom_naturality {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) (L : κ → List ι)
    (M : List κ) :
    listTensorMap f (M.flatMap L) ≫ (listTensorFlatMapIso Y L M).hom =
      (listTensorFlatMapIso X L M).hom ≫ listTensorMap (fun j ↦ listTensorMap f (L j)) M := by
  induction M with
  | nil =>
    simp only [listTensorFlatMapIso_nil, Iso.refl_hom, Category.comp_id, Category.id_comp]
    -- `List.flatMap L []` is `[]` by definition.
    exact listTensorMap_nil f
  | cons j M ih =>
    -- `List.flatMap_cons` is not a definitional lemma, so `dsimp` cannot use it to rewrite the
    -- lists in the types of the morphisms; unfolding `List.flatMap` and folding it back can.
    dsimp only [List.flatMap_def, List.map, List.flatten_cons]
    dsimp only [← List.flatMap_def]
    simp only [listTensorFlatMapIso_cons, Iso.trans_hom, whiskerLeftIso_hom, listTensorMap_cons]
    rw [listTensorAppendIso_hom_naturality_assoc]
    rw [tensorHom_def_assoc, ← MonoidalCategory.whiskerLeft_comp, ih, tensorHom_def,
      MonoidalCategory.whiskerLeft_comp, ← whisker_exchange_assoc]
    simp

/-- Grouping the factors over a concatenation `M₁ ++ M₂` of index lists is grouping them over
`M₁` and over `M₂`. -/
@[reassoc]
lemma listTensorFlatMapIso_hom_listTensorAppendIso_hom (X : ι → C) (L : κ → List ι)
    (M₁ M₂ : List κ) :
    (listTensorFlatMapIso X L (M₁ ++ M₂)).hom ≫ (listTensorAppendIso _ M₁ M₂).hom =
      eqToHom (by rw [List.flatMap_append]) ≫
        (listTensorAppendIso X (M₁.flatMap L) (M₂.flatMap L)).hom ≫
        ((listTensorFlatMapIso X L M₁).hom ⊗ₘ (listTensorFlatMapIso X L M₂).hom) := by
  induction M₁ with
  | nil =>
    simp only [List.nil_append, listTensorAppendIso_nil, Iso.symm_hom, eqToHom_refl,
      Category.id_comp, listTensorFlatMapIso_nil, Iso.refl_hom, id_tensorHom]
    exact leftUnitor_inv_naturality (listTensorFlatMapIso X L M₂).hom
  | cons j M₁ ih =>
    dsimp only [List.cons_append, List.flatMap_def, List.map, List.flatten_cons]
    dsimp only [← List.flatMap_def]
    have h := congrArg (listTensor X (L j) ◁ ·) ih
    simp only [MonoidalCategory.whiskerLeft_comp] at h
    have hassoc : (listTensorAppendIso X (L j) (M₁.flatMap L ++ M₂.flatMap L)).hom ≫
        listTensor X (L j) ◁ (listTensorAppendIso X (M₁.flatMap L) (M₂.flatMap L)).hom =
          eqToHom (by rw [List.append_assoc]) ≫
            (listTensorAppendIso X (L j ++ M₁.flatMap L) (M₂.flatMap L)).hom ≫
            (listTensorAppendIso X (L j) (M₁.flatMap L)).hom ▷ _ ≫ (α_ _ _ _).hom := by
      rw [listTensorAppendIso_hom_assoc]
      simp
    simp only [listTensorFlatMapIso_cons, listTensorAppendIso_cons, Iso.trans_hom,
      whiskerLeftIso_hom, Iso.symm_hom, Category.assoc]
    rw [reassoc_of% h, ← eqToHom_comp_listTensorAppendIso_hom_assoc (h := List.flatMap_append),
      reassoc_of% hassoc]
    simp only [eqToHom_trans_assoc, tensorHom_def, MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    congr 1
    monoidal

/-- Grouping factors in two stages, first along `L` and then along `M`, is grouping them along the
composite `fun k ↦ (M k).flatMap L` and then grouping each `M k`. -/
lemma listTensorFlatMapIso_hom_flatMap (X : ι → C) (L : κ → List ι) (M : ν → List κ)
    (N : List ν) :
    (listTensorFlatMapIso X L (N.flatMap M)).hom ≫
        (listTensorFlatMapIso (fun j ↦ listTensor X (L j)) M N).hom =
      eqToHom (by rw [List.flatMap_assoc]) ≫
        (listTensorFlatMapIso X (fun k ↦ (M k).flatMap L) N).hom ≫
        listTensorMap (fun k ↦ (listTensorFlatMapIso X L (M k)).hom) N := by
  induction N with
  | nil =>
    simp only [listTensorFlatMapIso_nil, Iso.refl_hom, listTensorMap_nil, eqToHom_refl,
      Category.comp_id, Category.id_comp]
    -- `List.flatMap M []` is `[]` by definition.
    exact congrArg Iso.hom (listTensorFlatMapIso_nil X L)
  | cons k N ih =>
    dsimp only [List.flatMap_def, List.map, List.flatten_cons]
    dsimp only [← List.flatMap_def]
    simp only [listTensorFlatMapIso_cons, Iso.trans_hom, whiskerLeftIso_hom, listTensorMap_cons,
      Category.assoc]
    rw [listTensorFlatMapIso_hom_listTensorAppendIso_hom_assoc, tensorHom_def_assoc,
      ← MonoidalCategory.whiskerLeft_comp, ih, MonoidalCategory.whiskerLeft_comp,
      ← whisker_exchange_assoc,
      ← eqToHom_comp_listTensorAppendIso_hom_assoc (h := List.flatMap_assoc),
      eqToHom_trans_assoc, tensorHom_def, MonoidalCategory.whiskerLeft_comp,
      ← whisker_exchange_assoc]

/-- Grouping the factors over `M` into one-element groups and removing the units of these groups
is the identity. -/
lemma listTensorFlatMapIso_hom_listTensorMap_rightUnitor (X : ι → C) (M : List ι) :
    (listTensorFlatMapIso X (fun i ↦ [i]) M).hom ≫ listTensorMap (fun i ↦ (ρ_ (X i)).hom) M =
      eqToHom (by rw [List.flatMap_singleton']) := by
  induction M with
  | nil => simp
  | cons i M ih =>
    dsimp only [List.flatMap_def, List.map, List.flatten_cons]
    dsimp only [← List.flatMap_def]
    simp only [listTensorFlatMapIso_cons, Iso.trans_hom, whiskerLeftIso_hom, listTensorMap_cons,
      Category.assoc, listTensorAppendIso_cons, listTensorAppendIso_nil, Iso.symm_hom]
    calc
      _ = X i ◁ ((listTensorFlatMapIso X (fun i ↦ [i]) M).hom ≫
          listTensorMap (fun i ↦ (ρ_ (X i)).hom) M) := by
        rw [tensorHom_def']
        monoidal
      _ = _ := by rw [ih, whiskerLeft_eqToHom]

/-- Grouping all factors into a single group and removing the unit is the identity. -/
lemma listTensorFlatMapIso_singleton_hom_rightUnitor_hom (X : ι → C) (L : κ → List ι) (j : κ) :
    (listTensorFlatMapIso X L [j]).hom ≫ (ρ_ (listTensor X (L j))).hom =
      eqToHom (by rw [List.flatMap_singleton]) := by
  rw [listTensorFlatMapIso_cons, Iso.trans_hom, whiskerLeftIso_hom, listTensorFlatMapIso_nil,
    Iso.refl_hom, whiskerLeft_id, Category.assoc, Category.id_comp]
  exact listTensorAppendIso_nil_right_hom X (L j)

end TauCeti
