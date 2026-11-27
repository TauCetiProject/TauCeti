/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Perm.Basic
public import TauCeti.CategoryTheory.Monoidal.Braided.Basic
public import TauCeti.CategoryTheory.Monoidal.ListTensor
public import TauCeti.Data.List.Sort
import Mathlib.Order.Extension.Linear

/-!
# Reordering ordered tensor products in a symmetric monoidal category

Let `X : ι → C` be a family of objects of a symmetric monoidal category. For a permutation
`h : l ~ l'` of lists of indices, `TauCeti.listTensorPermIso X h` is the canonical isomorphism
`listTensor X l ≅ listTensor X l'` between the ordered tensor products over the two lists. It
depends only on the two lists, it is functorial in the permutation (`listTensorPermIso_self`,
`listTensorPermIso_trans`, `listTensorPermIso_symm`), it acts on the tail of a list by whiskering
(`listTensorPermIso_cons`), and on two distinct neighbouring factors it is their braiding
(`listTensorPermIso_swap`). These properties characterize it: any assignment of maps to the
permutations of lists with them agrees with it (`eq_listTensorPermIso_hom`). This is uniqueness of
the canonical reordering. Since a `List.Perm` records only the two lists, not which occurrences of
a repeated label are exchanged, it does not express coherence for structural maps indexed by
permutations of positions; that form of the coherence theorem is not formalized here.

The isomorphism is constructed by sorting: for an auxiliary linear order on `ι`, which by the
uniqueness theorem does not affect the result and does not appear in the statements, the tensor
product over `l` is identified with the tensor product over the sorted list
`l.insertionSort (· ≤ ·)` by inserting the factors one at a time into the sorted tail, braiding
each past the smaller ones. Two lists
which are permutations of each other have the same sorted list. Sorting is invariant under
exchanging two neighbouring distinct factors; this uses the hexagon identities, through the
Yang–Baxter equation, and the symmetry `β_ Y X ≫ β_ X Y = 𝟙`.

The reorderings are compatible with the splitting and grouping isomorphisms of
`TauCeti.CategoryTheory.Monoidal.ListTensor`: with concatenation (`listTensorPermIso_append_hom`),
moving a factor or a block of factors past a block of factors distinct from it, which is the
braiding with that block (`listTensorPermIso_perm_middle_hom`,
`listTensorPermIso_perm_append_comm_assoc_hom`), and reordering the groups or the factors inside
each group of a `flatMap` (`listTensorPermIso_flatMap_right_hom`,
`listTensorPermIso_flatMap_left_hom`). These are the identities needed to compose maps in the
category of operators of a symmetric monoidal category, whose maps over a map of finite pointed
sets are maps out of the ordered tensor products over its fibers.

The distinctness hypotheses of `listTensorPermIso_swap` and of the lemmas identifying reorderings
with braidings of factors or blocks (`listTensorPermIso_perm_middle_hom`,
`listTensorPermIso_perm_append_comm_assoc_hom`, `listTensorPermIso_flatMap_right_hom`) cannot be
dropped: two equal neighbouring labels `a :: a :: l` are a permutation of the list onto itself,
whose reordering is the identity, while the braiding `β_ (X a) (X a)` of their factors need not
be.

## References

* S. Mac Lane, *Natural associativity and commutativity*, Rice Univ. Studies 49 (1963), §5.
* J. Lurie, *Higher Algebra*, Construction 2.0.0.1.
-/

public section

open CategoryTheory MonoidalCategory

universe v u w w'

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {ι : Type w} {κ : Type w'}

section Braided

variable [BraidedCategory C] (X : ι → C)

/-- The braiding of the first two factors of the ordered tensor product over `a :: b :: l`. -/
def listTensorSwapIso (a b : ι) (l : List ι) :
    listTensor X (a :: b :: l) ≅ listTensor X (b :: a :: l) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso (β_ (X a) (X b)) _ ≪≫ α_ _ _ _

/-- The exchange of the first two factors is the braiding `β_ (X a) (X b)`, reassociated. -/
lemma listTensorSwapIso_hom (a b : ι) (l : List ι) :
    (listTensorSwapIso X a b l).hom =
      (α_ _ _ _).inv ≫ (β_ (X a) (X b)).hom ▷ listTensor X l ≫ (α_ _ _ _).hom :=
  (rfl)

/-- Exchanging the first two factors commutes with maps of the remaining factors. -/
@[reassoc]
lemma listTensorSwapIso_hom_naturality (a b : ι) {l l' : List ι}
    (g : listTensor X l ⟶ listTensor X l') :
    X a ◁ X b ◁ g ≫ (listTensorSwapIso X a b l').hom =
      (listTensorSwapIso X a b l).hom ≫ X b ◁ X a ◁ g := by
  simpa only [listTensorSwapIso_hom, Category.assoc] using
    whiskerLeft_whiskerLeft_comp_associator_inv_braiding_associator_hom (X a) (X b) g

/-- Exchanging the first two factors is natural in the family. -/
@[reassoc]
lemma listTensorMap_listTensorSwapIso_hom {Y : ι → C} (f : ∀ i, X i ⟶ Y i) (a b : ι)
    (l : List ι) :
    listTensorMap f (a :: b :: l) ≫ (listTensorSwapIso Y a b l).hom =
      (listTensorSwapIso X a b l).hom ≫ listTensorMap f (b :: a :: l) := by
  simp only [listTensorSwapIso_hom, listTensorMap_cons, Category.assoc,
    associator_inv_naturality_assoc, ← associator_naturality, tensorHom_comp_tensorHom_assoc,
    ← tensorHom_id, BraidedCategory.braiding_naturality, Category.comp_id, Category.id_comp]

/-- The Yang–Baxter equation for the exchanges of the first three factors. -/
@[reassoc]
lemma listTensorSwapIso_hom_yang_baxter (a b c : ι) (l : List ι) :
    (listTensorSwapIso X a b (c :: l)).hom ≫ X b ◁ (listTensorSwapIso X a c l).hom ≫
        (listTensorSwapIso X b c (a :: l)).hom =
      X a ◁ (listTensorSwapIso X b c l).hom ≫ (listTensorSwapIso X a c (b :: l)).hom ≫
        X c ◁ (listTensorSwapIso X a b l).hom := by
  simp only [listTensorSwapIso_hom, MonoidalCategory.whiskerLeft_comp]
  calc _ = 𝟙 (X a ⊗ X b ⊗ X c ⊗ listTensor X l) ⊗≫ (((β_ (X a) (X b)).hom ▷ X c ⊗≫
          X b ◁ (β_ (X a) (X c)).hom ⊗≫ (β_ (X b) (X c)).hom ▷ X a) ▷ listTensor X l) ⊗≫
          𝟙 (X c ⊗ X b ⊗ X a ⊗ listTensor X l) := by monoidal
    _ = 𝟙 (X a ⊗ X b ⊗ X c ⊗ listTensor X l) ⊗≫ ((X a ◁ (β_ (X b) (X c)).hom ⊗≫
          (β_ (X a) (X c)).hom ▷ X b ⊗≫ X c ◁ (β_ (X a) (X b)).hom) ▷ listTensor X l) ⊗≫
          𝟙 (X c ⊗ X b ⊗ X a ⊗ listTensor X l) := by
        rw [BraidedCategory.yang_baxter']; monoidal
    _ = _ := by monoidal

end Braided

section Symmetric

variable [SymmetricCategory C] (X : ι → C)

/-- Exchanging the first two factors twice is the identity. -/
@[reassoc (attr := simp)]
lemma listTensorSwapIso_hom_listTensorSwapIso_hom (a b : ι) (l : List ι) :
    (listTensorSwapIso X a b l).hom ≫ (listTensorSwapIso X b a l).hom = 𝟙 _ := by
  simp [listTensorSwapIso_hom, ← comp_whiskerRight_assoc]

/-! ### Sorting the factors -/

section Sorting

variable [LinearOrder ι]

/-- Inserting the first factor of `a :: s` into its place in `s.orderedInsert (· ≤ ·) a`, by
braiding it past the factors smaller than it. -/
private def insertIso (a : ι) :
    (s : List ι) → (listTensor X (a :: s) ≅ listTensor X (s.orderedInsert (· ≤ ·) a))
  | [] => eqToIso (by rw [List.orderedInsert_nil])
  | c :: s =>
    if h : a ≤ c then eqToIso (by rw [List.orderedInsert_cons_of_le _ _ h])
    else listTensorSwapIso X a c s ≪≫ whiskerLeftIso (X c) (insertIso a s) ≪≫
      eqToIso (by rw [List.orderedInsert_of_not_le _ _ h]; rfl)

/-- Sorting the factors of an ordered tensor product, by insertion sort. -/
private def sortIso : (l : List ι) → (listTensor X l ≅ listTensor X (l.insertionSort (· ≤ ·)))
  | [] => eqToIso (by rw [List.insertionSort_nil])
  | a :: l => whiskerLeftIso (X a) (sortIso l) ≪≫ insertIso X a (l.insertionSort (· ≤ ·)) ≪≫
      eqToIso (by rw [List.insertionSort_cons])

private lemma insertIso_nil_hom (a : ι) :
    (insertIso X a []).hom = eqToHom (by rw [List.orderedInsert_nil]) := by
  rw [insertIso]; rfl

private lemma insertIso_cons_hom_of_le {a c : ι} (s : List ι) (h : a ≤ c) :
    (insertIso X a (c :: s)).hom = eqToHom (by rw [List.orderedInsert_cons_of_le _ _ h]) := by
  simp [insertIso, h]

private lemma insertIso_cons_hom_of_not_le {a c : ι} (s : List ι) (h : ¬ a ≤ c) :
    (insertIso X a (c :: s)).hom = (listTensorSwapIso X a c s).hom ≫
      X c ◁ (insertIso X a s).hom ≫ eqToHom (by rw [List.orderedInsert_of_not_le _ _ h]; rfl) := by
  simp [insertIso, h]

/-- Transporting an insertion along an equality of lists. -/
private lemma insertIso_hom_of_eq (a : ι) {s s' : List ι} (h : s = s') :
    (insertIso X a s).hom =
      X a ◁ eqToHom (congrArg (listTensor X) h) ≫ (insertIso X a s').hom ≫
        eqToHom (by rw [h]) := by
  subst h
  simp

/-- **Inserting two distinct factors in either order agrees**, after exchanging them. This is
the step of the coherence theorem that uses the Yang–Baxter equation and the symmetry. -/
@[reassoc]
private lemma insertIso_insertIso {a b : ι} (hab : a ≠ b) (s : List ι) :
    (listTensorSwapIso X a b s).hom ≫ X b ◁ (insertIso X a s).hom ≫
        (insertIso X b (s.orderedInsert (· ≤ ·) a)).hom =
      X a ◁ (insertIso X b s).hom ≫ (insertIso X a (s.orderedInsert (· ≤ ·) b)).hom ≫
        eqToHom (congrArg (listTensor X) (List.orderedInsert_comm a b s)) := by
  induction s with
  | nil =>
    rw [insertIso_hom_of_eq X b (List.orderedInsert_nil _ a),
      insertIso_hom_of_eq X a (List.orderedInsert_nil _ b)]
    rcases lt_or_gt_of_ne hab with h | h <;>
      simp [insertIso_nil_hom, insertIso_cons_hom_of_le, insertIso_cons_hom_of_not_le, h.le,
        not_le.2 h]
  | cons c s ih =>
    by_cases ha : a ≤ c <;> by_cases hb : b ≤ c
    · rw [insertIso_hom_of_eq X b (List.orderedInsert_cons_of_le _ _ ha),
        insertIso_hom_of_eq X a (List.orderedInsert_cons_of_le _ _ hb)]
      rcases lt_or_gt_of_ne hab with h | h <;>
        simp [insertIso_cons_hom_of_le, insertIso_cons_hom_of_not_le, ha, hb, h.le, not_le.2 h]
    · rw [insertIso_hom_of_eq X b (List.orderedInsert_cons_of_le _ _ ha),
        insertIso_hom_of_eq X a (List.orderedInsert_of_not_le _ _ hb)]
      have hba : ¬ b ≤ a := fun h ↦ hb (h.trans ha)
      simp [insertIso_cons_hom_of_le, insertIso_cons_hom_of_not_le, ha, hb, hba]
    · rw [insertIso_hom_of_eq X b (List.orderedInsert_of_not_le _ _ ha),
        insertIso_hom_of_eq X a (List.orderedInsert_cons_of_le _ _ hb)]
      have hab' : ¬ a ≤ b := fun h ↦ ha (h.trans hb)
      simp [insertIso_cons_hom_of_le, insertIso_cons_hom_of_not_le, ha, hb, hab']
    · rw [insertIso_hom_of_eq X b (List.orderedInsert_of_not_le _ _ ha),
        insertIso_hom_of_eq X a (List.orderedInsert_of_not_le _ _ hb)]
      have ih' := congrArg (X c ◁ ·) ih
      simp only [MonoidalCategory.whiskerLeft_comp] at ih'
      simp only [insertIso_cons_hom_of_not_le, ha, hb, not_false_eq_true,
        MonoidalCategory.whiskerLeft_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, whiskerLeft_eqToHom]
      rw [listTensorSwapIso_hom_naturality_assoc X b c (insertIso X a s).hom,
        listTensorSwapIso_hom_naturality_assoc X a c (insertIso X b s).hom,
        listTensorSwapIso_hom_yang_baxter_assoc, reassoc_of% ih']
      simp

private lemma sortIso_cons_hom (a : ι) (l : List ι) :
    (sortIso X (a :: l)).hom = X a ◁ (sortIso X l).hom ≫
      (insertIso X a (l.insertionSort (· ≤ ·))).hom ≫
      eqToHom (by rw [List.insertionSort_cons]) := by
  simp [sortIso]

/-- Sorting is invariant under exchanging the first two factors, when they are distinct. -/
private lemma listTensorSwapIso_hom_sortIso_hom {a b : ι} (hab : a ≠ b) (l : List ι) :
    (listTensorSwapIso X a b l).hom ≫ (sortIso X (b :: a :: l)).hom =
      (sortIso X (a :: b :: l)).hom ≫
        eqToHom (congrArg (listTensor X) (List.Perm.swap b a l).insertionSort_eq) := by
  rw [sortIso_cons_hom, sortIso_cons_hom, sortIso_cons_hom, sortIso_cons_hom,
    insertIso_hom_of_eq X b (List.insertionSort_cons _ a l),
    insertIso_hom_of_eq X a (List.insertionSort_cons _ b l)]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← listTensorSwapIso_hom_naturality_assoc X a b (sortIso X l).hom,
    insertIso_insertIso_assoc X hab]
  simp

/-- Reordering the factors by sorting both lists, for the linear order of `ι`. -/
private def sortPermIso {l l' : List ι} (h : l.Perm l') : listTensor X l ≅ listTensor X l' :=
  sortIso X l ≪≫ eqToIso (congrArg (listTensor X) h.insertionSort_eq) ≪≫ (sortIso X l').symm

@[reassoc]
private lemma sortPermIso_hom_sortIso_hom {l l' : List ι} (h : l.Perm l') :
    (sortPermIso X h).hom ≫ (sortIso X l').hom =
      (sortIso X l).hom ≫ eqToHom (congrArg (listTensor X) h.insertionSort_eq) := by
  simp [sortPermIso]

private lemma sortPermIso_self {l : List ι} (h : l.Perm l) : sortPermIso X h = Iso.refl _ := by
  ext
  simp [sortPermIso]

private lemma sortPermIso_hom_sortPermIso_hom {l₁ l₂ l₃ : List ι} (h₁ : l₁.Perm l₂)
    (h₂ : l₂.Perm l₃) :
    (sortPermIso X h₁).hom ≫ (sortPermIso X h₂).hom = (sortPermIso X (h₁.trans h₂)).hom := by
  simp [sortPermIso]

private lemma sortPermIso_symm {l l' : List ι} (h : l.Perm l') :
    (sortPermIso X h).symm = sortPermIso X h.symm := by
  ext
  simp [sortPermIso]

private lemma sortPermIso_cons (a : ι) {l l' : List ι} (h : l.Perm l') :
    sortPermIso X (h.cons a) = whiskerLeftIso (X a) (sortPermIso X h) := by
  ext
  rw [← cancel_mono (sortIso X (a :: l')).hom, sortPermIso_hom_sortIso_hom,
    sortIso_cons_hom, sortIso_cons_hom, whiskerLeftIso_hom,
    ← MonoidalCategory.whiskerLeft_comp_assoc, sortPermIso_hom_sortIso_hom,
    insertIso_hom_of_eq X a h.insertionSort_eq]
  simp

private lemma sortPermIso_swap {a b : ι} (hab : a ≠ b) (l : List ι) :
    sortPermIso X (List.Perm.swap b a l) = listTensorSwapIso X a b l := by
  ext
  rw [← cancel_mono (sortIso X (b :: a :: l)).hom, sortPermIso_hom_sortIso_hom,
    listTensorSwapIso_hom_sortIso_hom X hab]

end Sorting

/-! ### The reordering isomorphisms -/

variable (ι) in
/-- An auxiliary linear order on `ι`, used only to construct `TauCeti.listTensorPermIso`: a linear
extension of the discrete order. By `TauCeti.eq_listTensorPermIso_hom`, the choice is
immaterial. -/
@[instance_reducible]
private noncomputable def auxLinearOrder : LinearOrder ι :=
  letI : PartialOrder ι := PartialOrder.lift (fun i : ι ↦ ({i} : Set ι)) Set.singleton_injective
  inferInstanceAs (LinearOrder (LinearExtension ι))

/-- **The canonical reordering of ordered tensor products.** The isomorphism between the ordered
tensor products over two lists which are permutations of each other: both are sorted, for an
auxiliary linear order of `ι`, by braiding factors past each other. It is characterized by its
basic properties (`TauCeti.eq_listTensorPermIso_hom`), so the order used is immaterial. -/
noncomputable def listTensorPermIso {l l' : List ι} (h : l.Perm l') :
    listTensor X l ≅ listTensor X l' :=
  letI := auxLinearOrder ι
  sortPermIso X h

/-- Reordering a list into itself is the identity. -/
@[simp]
lemma listTensorPermIso_self {l : List ι} (h : l.Perm l) :
    listTensorPermIso X h = Iso.refl _ :=
  letI := auxLinearOrder ι
  sortPermIso_self X h

/-- Reorderings compose. -/
@[reassoc (attr := simp)]
lemma listTensorPermIso_hom_listTensorPermIso_hom {l₁ l₂ l₃ : List ι} (h₁ : l₁.Perm l₂)
    (h₂ : l₂.Perm l₃) :
    (listTensorPermIso X h₁).hom ≫ (listTensorPermIso X h₂).hom =
      (listTensorPermIso X (h₁.trans h₂)).hom :=
  letI := auxLinearOrder ι
  sortPermIso_hom_sortPermIso_hom X h₁ h₂

/-- Reorderings compose. -/
@[simp]
lemma listTensorPermIso_trans {l₁ l₂ l₃ : List ι} (h₁ : l₁.Perm l₂) (h₂ : l₂.Perm l₃) :
    listTensorPermIso X h₁ ≪≫ listTensorPermIso X h₂ = listTensorPermIso X (h₁.trans h₂) := by
  ext
  simp

/-- The inverse of a reordering is the reverse reordering. -/
@[simp]
lemma listTensorPermIso_symm {l l' : List ι} (h : l.Perm l') :
    (listTensorPermIso X h).symm = listTensorPermIso X h.symm :=
  letI := auxLinearOrder ι
  sortPermIso_symm X h

/-- The inverse of a reordering is the reverse reordering, as a morphism. -/
@[simp]
lemma listTensorPermIso_inv {l l' : List ι} (h : l.Perm l') :
    (listTensorPermIso X h).inv = (listTensorPermIso X h.symm).hom :=
  congrArg Iso.hom (listTensorPermIso_symm X h)

/-- Reordering along an equality of lists is the transport along it. -/
lemma listTensorPermIso_of_eq {l l' : List ι} (h : l = l') (h' : l.Perm l') :
    listTensorPermIso X h' = eqToIso (congrArg (listTensor X) h) := by
  subst h
  simp

/-- A reordering followed by the transport along an equality of lists is a reordering. -/
@[reassoc]
lemma listTensorPermIso_hom_eqToHom {l₁ l₂ l₃ : List ι} (h : l₁.Perm l₂) (e : l₂ = l₃) :
    (listTensorPermIso X h).hom ≫ eqToHom (congrArg (listTensor X) e) =
      (listTensorPermIso X (h.trans (.of_eq e))).hom := by
  subst e
  simp

/-- Reordering the tail of a list. -/
@[simp]
lemma listTensorPermIso_cons (a : ι) {l l' : List ι} (h : l.Perm l') :
    listTensorPermIso X (h.cons a) = whiskerLeftIso (X a) (listTensorPermIso X h) :=
  letI := auxLinearOrder ι
  sortPermIso_cons X a h

/-- On two distinct neighbouring factors, reordering is their braiding. -/
lemma listTensorPermIso_swap {a b : ι} (hab : a ≠ b) (l : List ι) :
    listTensorPermIso X (List.Perm.swap b a l) = listTensorSwapIso X a b l :=
  letI := auxLinearOrder ι
  sortPermIso_swap X hab l

/-- Reordering is natural in the family. -/
@[reassoc]
lemma listTensorPermIso_hom_naturality {Y : ι → C} (f : ∀ i, X i ⟶ Y i) {l l' : List ι}
    (h : l.Perm l') :
    listTensorMap f l ≫ (listTensorPermIso Y h).hom =
      (listTensorPermIso X h).hom ≫ listTensorMap f l' := by
  induction h with
  | nil => simp
  | cons a h ih =>
    rw [listTensorPermIso_cons Y a h, listTensorPermIso_cons X a h]
    simp only [whiskerLeftIso_hom, listTensorMap_cons]
    rw [tensorHom_def_assoc, ← MonoidalCategory.whiskerLeft_comp, ih, tensorHom_def',
      MonoidalCategory.whiskerLeft_comp, ← whisker_exchange_assoc, ← whisker_exchange]
  | swap x y l =>
    by_cases hxy : y = x
    · subst hxy
      simp
    · rw [listTensorPermIso_swap X hxy, listTensorPermIso_swap Y hxy]
      exact listTensorMap_listTensorSwapIso_hom X f y x l
  | trans h₁ h₂ ih₁ ih₂ =>
    rw [← listTensorPermIso_hom_listTensorPermIso_hom Y h₁ h₂, reassoc_of% ih₁, ih₂,
      listTensorPermIso_hom_listTensorPermIso_hom_assoc]

/-- Reordering the second part of a concatenation. -/
@[reassoc]
lemma listTensorPermIso_append_left_hom (l₁ : List ι) {l₂ l₂' : List ι} (h : l₂.Perm l₂') :
    (listTensorPermIso X (h.append_left l₁)).hom ≫ (listTensorAppendIso X l₁ l₂').hom =
      (listTensorAppendIso X l₁ l₂).hom ≫ _ ◁ (listTensorPermIso X h).hom := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    dsimp only [List.cons_append]
    rw [listTensorPermIso_cons X a (h.append_left l₁)]
    simp only [whiskerLeftIso_hom, listTensorAppendIso_cons, Iso.trans_hom, Iso.symm_hom]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ih, MonoidalCategory.whiskerLeft_comp_assoc,
      associator_inv_naturality_right]
    simp only [Category.assoc, listTensor_cons]

/-- Reordering the first part of a concatenation. -/
@[reassoc]
lemma listTensorPermIso_append_right_hom {l₁ l₁' : List ι} (h : l₁.Perm l₁') (l₂ : List ι) :
    (listTensorPermIso X (h.append_right l₂)).hom ≫ (listTensorAppendIso X l₁' l₂).hom =
      (listTensorAppendIso X l₁ l₂).hom ≫ (listTensorPermIso X h).hom ▷ _ := by
  induction h with
  | nil => simp
  | cons a h ih =>
    dsimp only [List.cons_append]
    rw [listTensorPermIso_cons X a (h.append_right l₂), listTensorPermIso_cons X a h]
    simp only [whiskerLeftIso_hom, listTensorAppendIso_cons, Iso.trans_hom, Iso.symm_hom]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ih,
      MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_middle]
    simp only [Category.assoc]
  | swap x y l =>
    by_cases hxy : y = x
    · subst hxy
      simp
    dsimp only [List.cons_append]
    rw [listTensorPermIso_swap X hxy, listTensorPermIso_swap X hxy]
    simp only [listTensorAppendIso_cons, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, listTensorSwapIso_hom]
    rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
      ← associator_inv_naturality_right_assoc]
    monoidal
  | trans h₁ h₂ ih₁ ih₂ =>
    rw [← listTensorPermIso_hom_listTensorPermIso_hom X (h₁.append_right l₂)
      (h₂.append_right l₂), Category.assoc, ih₂, reassoc_of% ih₁,
      ← comp_whiskerRight, listTensorPermIso_hom_listTensorPermIso_hom]

/-- Reordering both parts of a concatenation. -/
@[reassoc]
lemma listTensorPermIso_append_hom {l₁ l₁' l₂ l₂' : List ι} (h₁ : l₁.Perm l₁')
    (h₂ : l₂.Perm l₂') :
    (listTensorPermIso X (h₁.append h₂)).hom ≫ (listTensorAppendIso X l₁' l₂').hom =
      (listTensorAppendIso X l₁ l₂).hom ≫
        ((listTensorPermIso X h₁).hom ⊗ₘ (listTensorPermIso X h₂).hom) := by
  rw [← listTensorPermIso_hom_listTensorPermIso_hom X (h₁.append_right l₂) (h₂.append_left l₁'),
    Category.assoc, listTensorPermIso_append_left_hom,
    listTensorPermIso_append_right_hom_assoc X h₁ l₂, tensorHom_def]

/-- Moving a factor past a block of factors distinct from it is the braiding with that block. -/
@[reassoc]
lemma listTensorPermIso_perm_middle_hom {a : ι} {l₁ : List ι} (ha : a ∉ l₁) (l₂ : List ι) :
    (listTensorPermIso X (List.perm_middle.symm : (a :: (l₁ ++ l₂)).Perm (l₁ ++ a :: l₂))).hom ≫
        (listTensorAppendIso X l₁ (a :: l₂)).hom =
      X a ◁ (listTensorAppendIso X l₁ l₂).hom ≫ (α_ _ _ _).inv ≫
        (β_ (X a) (listTensor X l₁)).hom ▷ _ ≫ (α_ _ _ _).hom := by
  induction l₁ with
  | nil =>
    dsimp only [List.nil_append]
    rw [listTensorPermIso_self]
    simp only [Iso.refl_hom, Category.id_comp, listTensorAppendIso_nil, Iso.symm_hom]
    calc _ = 𝟙 (X a ⊗ listTensor X l₂) ⊗≫
          ((ρ_ (X a)).inv ≫ (β_ (X a) (𝟙_ C)).hom) ▷ listTensor X l₂ ⊗≫
            𝟙 (𝟙_ C ⊗ X a ⊗ listTensor X l₂) := by
          rw [rightUnitor_inv_braiding]; monoidal
      _ = _ := by monoidal
  | cons c l₁ ih =>
    have hac : a ≠ c := fun h ↦ ha (h ▸ List.mem_cons_self)
    dsimp only [List.cons_append]
    rw [← listTensorPermIso_hom_listTensorPermIso_hom X (List.Perm.swap c a (l₁ ++ l₂))
      ((List.perm_middle.symm : (a :: (l₁ ++ l₂)).Perm (l₁ ++ a :: l₂)).cons c),
      listTensorPermIso_swap X hac, listTensorPermIso_cons X c
        (List.perm_middle.symm : (a :: (l₁ ++ l₂)).Perm (l₁ ++ a :: l₂))]
    simp only [whiskerLeftIso_hom, listTensorAppendIso_cons, Iso.trans_hom, Iso.symm_hom,
      Category.assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ih (fun h ↦ ha (List.mem_cons_of_mem _ h)),
      listTensorSwapIso_hom]
    dsimp only [listTensor_cons]
    rw [BraidedCategory.braiding_tensor_right_hom]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← whiskerLeft_whiskerLeft_comp_associator_inv_braiding_associator_hom_assoc]
    monoidal

/-- Exchanging two disjoint blocks of factors at the front is the braiding of the blocks. -/
@[reassoc]
lemma listTensorPermIso_perm_append_comm_assoc_hom {l₁ l₂ : List ι} (h : l₁.Disjoint l₂)
    (l₃ : List ι) :
    (listTensorPermIso X (List.perm_append_comm_assoc l₁ l₂ l₃)).hom ≫
        (listTensorAppendIso X l₂ (l₁ ++ l₃)).hom ≫ _ ◁ (listTensorAppendIso X l₁ l₃).hom =
      (listTensorAppendIso X l₁ (l₂ ++ l₃)).hom ≫ _ ◁ (listTensorAppendIso X l₂ l₃).hom ≫
        (α_ _ _ _).inv ≫ (β_ (listTensor X l₁) (listTensor X l₂)).hom ▷ _ ≫ (α_ _ _ _).hom := by
  induction l₁ with
  | nil =>
    dsimp only [List.nil_append]
    rw [listTensorPermIso_self]
    simp only [Iso.refl_hom, Category.id_comp, listTensorAppendIso_nil, Iso.symm_hom]
    dsimp only [List.nil_append, listTensor_nil]
    rw [← leftUnitor_inv_naturality_assoc]
    congr 1
    calc _ = 𝟙 (listTensor X l₂ ⊗ listTensor X l₃) ⊗≫
          ((λ_ (listTensor X l₂)).inv ≫ (β_ (𝟙_ C) (listTensor X l₂)).hom) ▷ listTensor X l₃ ⊗≫
            𝟙 (listTensor X l₂ ⊗ 𝟙_ C ⊗ listTensor X l₃) := by
          rw [leftUnitor_inv_braiding]; monoidal
      _ = _ := by monoidal
  | cons a l₁ ih =>
    obtain ⟨ha, h⟩ := List.disjoint_cons_left.1 h
    have ih' := congrArg (X a ◁ ·) (ih h)
    simp only [MonoidalCategory.whiskerLeft_comp] at ih'
    dsimp only [List.cons_append]
    rw [← listTensorPermIso_hom_listTensorPermIso_hom X
      ((List.perm_append_comm_assoc l₁ l₂ l₃).cons a)
      (List.perm_middle.symm : (a :: (l₂ ++ (l₁ ++ l₃))).Perm (l₂ ++ a :: (l₁ ++ l₃))),
      listTensorPermIso_cons X a (List.perm_append_comm_assoc l₁ l₂ l₃)]
    simp only [whiskerLeftIso_hom, Category.assoc]
    rw [listTensorPermIso_perm_middle_hom_assoc X ha]
    simp only [listTensorAppendIso_cons, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← whiskerLeft_whiskerLeft_comp_associator_inv_braiding_associator_hom_assoc,
      reassoc_of% ih']
    dsimp only [listTensor_cons]
    rw [BraidedCategory.braiding_tensor_left_hom]
    monoidal

/-- Reordering the groups of a grouped ordered tensor product, when the groups with distinct
labels share no factor. -/
@[reassoc]
lemma listTensorPermIso_flatMap_right_hom (L : κ → List ι) {M M' : List κ}
    (h : M.Perm M') (hL : ∀ j ∈ M, ∀ k ∈ M, j ≠ k → (L j).Disjoint (L k)) :
    (listTensorPermIso X (h.flatMap_right L)).hom ≫ (listTensorFlatMapIso X L M').hom =
      (listTensorFlatMapIso X L M).hom ≫
        (listTensorPermIso (fun j ↦ listTensor X (L j)) h).hom := by
  induction h with
  | nil => simp
  | cons j h ih =>
    -- `List.flatMap_cons` is not a definitional lemma, so `dsimp` cannot use it to rewrite the
    -- lists in the types of the morphisms; unfolding `List.flatMap` and folding it back can.
    dsimp only [List.flatMap_def, List.map, List.flatten_cons]
    dsimp only [← List.flatMap_def]
    rw [listTensorPermIso_cons (fun j ↦ listTensor X (L j)) j h, listTensorFlatMapIso_cons,
      listTensorFlatMapIso_cons]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
    rw [listTensorPermIso_append_left_hom_assoc X (L j) (h.flatMap_right L),
      ← MonoidalCategory.whiskerLeft_comp,
      ih fun a ha b hb ↦ hL a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb),
      MonoidalCategory.whiskerLeft_comp]
  | swap x y M =>
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hdisj : (L y).Disjoint (L x) :=
        hL y List.mem_cons_self x (List.mem_cons_of_mem _ List.mem_cons_self) (Ne.symm hxy)
      dsimp only [List.flatMap_def, List.map, List.flatten_cons]
      dsimp only [← List.flatMap_def]
      rw [listTensorPermIso_swap _ (Ne.symm hxy), listTensorFlatMapIso_cons,
        listTensorFlatMapIso_cons, listTensorFlatMapIso_cons, listTensorFlatMapIso_cons]
      dsimp only [List.flatMap_def, List.map, List.flatten_cons]
      dsimp only [← List.flatMap_def]
      simp only [Iso.trans_hom, whiskerLeftIso_hom, MonoidalCategory.whiskerLeft_comp,
        Category.assoc]
      rw [listTensorPermIso_perm_append_comm_assoc_hom_assoc X hdisj, listTensorSwapIso_hom,
        whiskerLeft_whiskerLeft_comp_associator_inv_braiding_associator_hom]
  | trans h₁ h₂ ih₁ ih₂ =>
    rw [← listTensorPermIso_hom_listTensorPermIso_hom X (h₁.flatMap_right L)
      (h₂.flatMap_right L), Category.assoc,
      ih₂ fun a ha b hb ↦ hL a (h₁.mem_iff.2 ha) b (h₁.mem_iff.2 hb), reassoc_of% (ih₁ hL),
      listTensorPermIso_hom_listTensorPermIso_hom]

/-- Reordering the factors inside each group of a grouped ordered tensor product. -/
@[reassoc]
lemma listTensorPermIso_flatMap_left_hom {A B : κ → List ι} (h : ∀ j, (A j).Perm (B j))
    (M : List κ) :
    (listTensorPermIso X (List.Perm.flatMap_left M fun j _ ↦ h j)).hom ≫
        (listTensorFlatMapIso X B M).hom =
      (listTensorFlatMapIso X A M).hom ≫
        listTensorMap (fun j ↦ (listTensorPermIso X (h j)).hom) M := by
  induction M with
  | nil => simp
  | cons j M ih =>
    dsimp only [List.flatMap_def, List.map, List.flatten_cons]
    dsimp only [← List.flatMap_def]
    rw [listTensorFlatMapIso_cons, listTensorFlatMapIso_cons]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, listTensorMap_cons]
    rw [listTensorPermIso_append_hom_assoc X (h j) (List.Perm.flatMap_left M fun j _ ↦ h j),
      tensorHom_def_assoc, ← MonoidalCategory.whiskerLeft_comp, ih,
      MonoidalCategory.whiskerLeft_comp, ← whisker_exchange_assoc, ← whisker_exchange]
    simp [tensorHom_def']

/-- **Uniqueness of the reorderings.** An assignment of maps to the permutations of lists that is
the identity on the empty list, acts on the tail of a list by whiskering, is the braiding on two
distinct neighbouring factors, and is compatible with composition of permutations, agrees with
`listTensorPermIso`. In particular the reorderings do not depend on the auxiliary linear order of
`ι` used to construct them. -/
theorem eq_listTensorPermIso_hom
    (F : ∀ {l l' : List ι}, l.Perm l' → (listTensor X l ⟶ listTensor X l'))
    (nil : F List.Perm.nil = 𝟙 _)
    (cons : ∀ (a : ι) {l l' : List ι} (h : l.Perm l'), F (h.cons a) = X a ◁ F h)
    (swap : ∀ {a b : ι} (l : List ι), a ≠ b →
      F (List.Perm.swap b a l) = (listTensorSwapIso X a b l).hom)
    (trans : ∀ {l₁ l₂ l₃ : List ι} (h₁ : l₁.Perm l₂) (h₂ : l₂.Perm l₃),
      F (h₁.trans h₂) = F h₁ ≫ F h₂)
    {l l' : List ι} (h : l.Perm l') : F h = (listTensorPermIso X h).hom := by
  -- `F` depends only on the two lists, so it is the identity on permutations of a list onto
  -- itself; this covers the exchange of two equal neighbouring factors.
  have refl (m : List ι) : F (List.Perm.refl m) = 𝟙 _ := by
    induction m with
    | nil => exact nil
    | cons a m ih =>
      rw [cons a (List.Perm.refl m), ih]
      exact MonoidalCategory.whiskerLeft_id (X a) (listTensor X m)
  induction h with
  | nil => simp [nil]
  | cons a h ih => rw [cons a h, ih, listTensorPermIso_cons X a h, whiskerLeftIso_hom]
  | swap x y l =>
    by_cases hxy : y = x
    · subst hxy
      rw [refl, listTensorPermIso_self, Iso.refl_hom]
    · rw [swap l hxy, listTensorPermIso_swap X hxy]
  | trans h₁ h₂ ih₁ ih₂ =>
    rw [trans h₁ h₂, ih₁, ih₂, listTensorPermIso_hom_listTensorPermIso_hom]

end Symmetric

end TauCeti
