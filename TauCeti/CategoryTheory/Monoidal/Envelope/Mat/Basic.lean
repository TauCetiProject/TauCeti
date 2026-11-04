/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Mat
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The monoidal structure on the matrix category

For a monoidal preadditive category `C`, the additive envelope `Mat_ C` is again monoidal. The
tensor product of two finite families `M.X : M.ι → C` and `N.X : N.ι → C` is the family
`(i, j) ↦ M.X i ⊗ N.X j` indexed by `M.ι × N.ι`, the tensor unit is the one-term family `𝟙_ C`,
and the tensor product of two matrices is their Kronecker product,
`(f ⊗ₘ g) (i, j) (k, l) = f i k ⊗ₘ g j l`. The associator and unitors are the monomial
isomorphisms (`CategoryTheory.Mat_.isoOfEquiv`) over `Equiv.prodAssoc`, `Equiv.punitProd` and
`Equiv.prodPUnit` whose entries are the associators and unitors of `C`. The Kronecker product is
compatible with matrix multiplication exactly because the tensor product of `C` is biadditive,
which is why `MonoidalPreadditive C` is assumed.

With this structure the embedding `Mat_.embedding C : C ⥤ Mat_ C` of one-term families is strong
monoidal, and `Mat_ C` is again monoidal preadditive. Since `Mat_ C` is the additive envelope of
`C` (`Mat_.lift`), this equips the additive envelope with the tensor product of `C`; together with
the monoidal structure on the idempotent completion
(`CategoryTheory.Idempotents.Karoubi.instMonoidalCategory`) it makes `Karoubi (Mat_ C)` monoidal,
the setting in which diagrammatic categories such as the Temperley–Lieb category acquire direct
sums and images of idempotents.

## Main declarations

* `CategoryTheory.Mat_.instMonoidalCategory`: the monoidal structure on `Mat_ C`, characterized
  by the `simp` lemmas `Mat_.tensorObj_X`, `Mat_.tensorHom_apply`, `Mat_.whiskerLeft_apply` and
  `Mat_.whiskerRight_apply`, by `Mat_.associator_eq`, `Mat_.leftUnitor_eq` and
  `Mat_.rightUnitor_eq` for the structure isomorphisms, and by entry lemmas such as
  `Mat_.associator_hom_comp_apply` computing composites with them without `eqToHom`.
* `CategoryTheory.Mat_.instMonoidalPreadditive`: `Mat_ C` is monoidal preadditive.
* `CategoryTheory.Mat_.embeddingMonoidal`: the strong monoidal structure on `Mat_.embedding C`,
  with unit `Mat_.embeddingUnitIso` and tensorator `Mat_.embeddingTensorIso`, all of whose entries
  are identities.
-/

-- The data are exposed so that the projection lemmas below are `rfl` lemmas, usable by `dsimp`
-- to rewrite objects of `Mat_ C` occurring inside the types of morphisms.
@[expose] public section

namespace CategoryTheory.Mat_

open MonoidalCategory Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The tensor product, unit, whiskerings, associator and unitors of `Mat_ C`: the tensor product
of families is indexed by the product of the index types, the tensor product of matrices is their
Kronecker product, and the structure isomorphisms are monomial with entries those of `C`. -/
noncomputable instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Mat_ C) where
  tensorObj M N := ⟨M.ι × N.ι, fun p ↦ M.X p.1 ⊗ N.X p.2⟩
  tensorUnit := ⟨PUnit, fun _ ↦ 𝟙_ C⟩
  tensorHom f g p q := f p.1 q.1 ⊗ₘ g p.2 q.2
  whiskerLeft M _ _ g p q := (𝟙 M : M ⟶ M) p.1 q.1 ⊗ₘ g p.2 q.2
  whiskerRight f N p q := f p.1 q.1 ⊗ₘ (𝟙 N : N ⟶ N) p.2 q.2
  associator M N P :=
    isoOfEquiv (Equiv.prodAssoc M.ι N.ι P.ι) fun p ↦ α_ (M.X p.1.1) (N.X p.1.2) (P.X p.2)
  leftUnitor M := isoOfEquiv (Equiv.punitProd M.ι) fun p ↦ λ_ (M.X p.2)
  rightUnitor M := isoOfEquiv (Equiv.prodPUnit M.ι) fun p ↦ ρ_ (M.X p.1)

@[simp]
theorem tensorObj_ι (M N : Mat_ C) : (M ⊗ N).ι = (M.ι × N.ι) := rfl

@[simp]
theorem tensorObj_X (M N : Mat_ C) (p : M.ι × N.ι) : (M ⊗ N).X p = M.X p.1 ⊗ N.X p.2 := rfl

@[simp]
theorem tensorUnit_ι : (𝟙_ (Mat_ C)).ι = PUnit := rfl

@[simp]
theorem tensorUnit_X (u : PUnit) : (𝟙_ (Mat_ C)).X u = 𝟙_ C := rfl

/-- The tensor unit of `Mat_ C` is indexed by a singleton. -/
instance : Unique (𝟙_ (Mat_ C)).ι := inferInstanceAs (Unique PUnit)

/-- The tensor unit of `Mat_ C` is the one-term family on the tensor unit of `C`. -/
theorem tensorUnit_eq : 𝟙_ (Mat_ C) = (embedding C).obj (𝟙_ C) := rfl

@[simp]
theorem tensorHom_apply {M₁ N₁ M₂ N₂ : Mat_ C} (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂) (p : M₁.ι × M₂.ι)
    (q : N₁.ι × N₂.ι) : (f ⊗ₘ g) p q = f p.1 q.1 ⊗ₘ g p.2 q.2 := rfl

@[simp]
theorem whiskerLeft_apply (M : Mat_ C) {N₁ N₂ : Mat_ C} (g : N₁ ⟶ N₂) (p : M.ι × N₁.ι)
    (q : M.ι × N₂.ι) : (M ◁ g) p q = (𝟙 M : M ⟶ M) p.1 q.1 ⊗ₘ g p.2 q.2 := rfl

@[simp]
theorem whiskerRight_apply {M₁ M₂ : Mat_ C} (f : M₁ ⟶ M₂) (N : Mat_ C) (p : M₁.ι × N.ι)
    (q : M₂.ι × N.ι) : (f ▷ N) p q = f p.1 q.1 ⊗ₘ (𝟙 N : N ⟶ N) p.2 q.2 := rfl

theorem associator_eq (M N P : Mat_ C) :
    α_ M N P = isoOfEquiv (M := (M ⊗ N) ⊗ P) (N := M ⊗ N ⊗ P) (Equiv.prodAssoc M.ι N.ι P.ι)
      fun p ↦ α_ (M.X p.1.1) (N.X p.1.2) (P.X p.2) :=
  rfl

theorem leftUnitor_eq (M : Mat_ C) :
    λ_ M = isoOfEquiv (M := 𝟙_ _ ⊗ M) (N := M) (Equiv.punitProd M.ι) fun p ↦ λ_ (M.X p.2) :=
  rfl

theorem rightUnitor_eq (M : Mat_ C) :
    ρ_ M = isoOfEquiv (M := M ⊗ 𝟙_ _) (N := M) (Equiv.prodPUnit M.ι) fun p ↦ ρ_ (M.X p.1) :=
  rfl

theorem associator_hom_comp_apply (M N P : Mat_ C) {Q : Mat_ C} (g : M ⊗ N ⊗ P ⟶ Q)
    (p : ((M ⊗ N) ⊗ P).ι) (k : Q.ι) :
    ((α_ M N P).hom ≫ g) p k =
      (α_ (M.X p.1.1) (N.X p.1.2) (P.X p.2)).hom ≫ g (p.1.1, p.1.2, p.2) k :=
  isoOfEquiv_hom_comp_apply _ _ g p k

theorem comp_associator_inv_apply (M N P : Mat_ C) {Q : Mat_ C} (f : Q ⟶ M ⊗ N ⊗ P) (k : Q.ι)
    (p : ((M ⊗ N) ⊗ P).ι) :
    (f ≫ (α_ M N P).inv) k p =
      f k (p.1.1, p.1.2, p.2) ≫ (α_ (M.X p.1.1) (N.X p.1.2) (P.X p.2)).inv :=
  comp_isoOfEquiv_inv_apply _ _ f k p

theorem leftUnitor_hom_comp_apply (M : Mat_ C) {Q : Mat_ C} (g : M ⟶ Q) (p : (𝟙_ _ ⊗ M).ι)
    (k : Q.ι) : ((λ_ M).hom ≫ g) p k = (λ_ (M.X p.2)).hom ≫ g p.2 k :=
  isoOfEquiv_hom_comp_apply _ _ g p k

theorem comp_leftUnitor_inv_apply (M : Mat_ C) {Q : Mat_ C} (f : Q ⟶ M) (k : Q.ι)
    (p : (𝟙_ _ ⊗ M).ι) : (f ≫ (λ_ M).inv) k p = f k p.2 ≫ (λ_ (M.X p.2)).inv :=
  comp_isoOfEquiv_inv_apply _ _ f k p

theorem rightUnitor_hom_comp_apply (M : Mat_ C) {Q : Mat_ C} (g : M ⟶ Q) (p : (M ⊗ 𝟙_ _).ι)
    (k : Q.ι) : ((ρ_ M).hom ≫ g) p k = (ρ_ (M.X p.1)).hom ≫ g p.1 k :=
  isoOfEquiv_hom_comp_apply _ _ g p k

theorem comp_rightUnitor_inv_apply (M : Mat_ C) {Q : Mat_ C} (f : Q ⟶ M) (k : Q.ι)
    (p : (M ⊗ 𝟙_ _).ι) : (f ≫ (ρ_ M).inv) k p = f k p.1 ≫ (ρ_ (M.X p.1)).inv :=
  comp_isoOfEquiv_inv_apply _ _ f k p

variable [MonoidalPreadditive C]

/-- Whiskering a monomial isomorphism on the right and then composing moves the rows along the
equivalence, multiplying them by the whiskered entries. -/
theorem isoOfEquiv_hom_whiskerRight_comp_apply {M₁ M₂ : Mat_ C} (e : M₁.ι ≃ M₂.ι)
    (φ : ∀ i, M₁.X i ≅ M₂.X (e i)) (N : Mat_ C) {Q : Mat_ C} (g : M₂ ⊗ N ⟶ Q) (p : M₁.ι × N.ι)
    (k : Q.ι) :
    ((isoOfEquiv e φ).hom ▷ N ≫ g) p k = ((φ p.1).hom ▷ N.X p.2) ≫ g (e p.1, p.2) k := by
  rw [comp_apply]
  refine (Fintype.sum_eq_single (e p.1, p.2) fun ⟨i, j⟩ h ↦ ?_).trans (by simp)
  by_cases hi : e p.1 = i
  · subst hi
    simp [show p.2 ≠ j by rintro rfl; exact h rfl]
  · simp [isoOfEquiv_hom_apply, hi]

/-- Whiskering a monomial isomorphism on the left and then composing moves the rows along the
equivalence, multiplying them by the whiskered entries. -/
theorem whiskerLeft_isoOfEquiv_hom_comp_apply (M : Mat_ C) {N₁ N₂ : Mat_ C} (e : N₁.ι ≃ N₂.ι)
    (φ : ∀ j, N₁.X j ≅ N₂.X (e j)) {Q : Mat_ C} (g : M ⊗ N₂ ⟶ Q) (p : M.ι × N₁.ι) (k : Q.ι) :
    ((M ◁ (isoOfEquiv e φ).hom) ≫ g) p k = (M.X p.1 ◁ (φ p.2).hom) ≫ g (p.1, e p.2) k := by
  rw [comp_apply]
  refine (Fintype.sum_eq_single (p.1, e p.2) fun ⟨i, j⟩ h ↦ ?_).trans (by simp)
  by_cases hi : p.1 = i
  · subst hi
    simp [isoOfEquiv_hom_apply, show e p.2 ≠ j by rintro rfl; exact h rfl]
  · simp [hi]

theorem associator_hom_whiskerRight_comp_apply (M N P R : Mat_ C) {Q : Mat_ C}
    (g : (M ⊗ N ⊗ P) ⊗ R ⟶ Q) (p : (((M ⊗ N) ⊗ P) ⊗ R).ι) (k : Q.ι) :
    ((α_ M N P).hom ▷ R ≫ g) p k =
      ((α_ (M.X p.1.1.1) (N.X p.1.1.2) (P.X p.1.2)).hom ▷ R.X p.2) ≫
        g ((p.1.1.1, p.1.1.2, p.1.2), p.2) k :=
  isoOfEquiv_hom_whiskerRight_comp_apply _ _ R g p k

theorem whiskerLeft_associator_hom_comp_apply (M N P R : Mat_ C) {Q : Mat_ C}
    (g : M ⊗ N ⊗ P ⊗ R ⟶ Q) (p : (M ⊗ (N ⊗ P) ⊗ R).ι) (k : Q.ι) :
    ((M ◁ (α_ N P R).hom) ≫ g) p k =
      (M.X p.1 ◁ (α_ (N.X p.2.1.1) (P.X p.2.1.2) (R.X p.2.2)).hom) ≫
        g (p.1, p.2.1.1, p.2.1.2, p.2.2) k :=
  whiskerLeft_isoOfEquiv_hom_comp_apply M _ _ g p k

theorem whiskerLeft_leftUnitor_hom_comp_apply (M N : Mat_ C) {Q : Mat_ C} (g : M ⊗ N ⟶ Q)
    (p : (M ⊗ 𝟙_ _ ⊗ N).ι) (k : Q.ι) :
    ((M ◁ (λ_ N).hom) ≫ g) p k = (M.X p.1 ◁ (λ_ (N.X p.2.2)).hom) ≫ g (p.1, p.2.2) k :=
  whiskerLeft_isoOfEquiv_hom_comp_apply M _ _ g p k

theorem rightUnitor_hom_whiskerRight_comp_apply (M N : Mat_ C) {Q : Mat_ C} (g : M ⊗ N ⟶ Q)
    (p : ((M ⊗ 𝟙_ _) ⊗ N).ι) (k : Q.ι) :
    ((ρ_ M).hom ▷ N ≫ g) p k = ((ρ_ (M.X p.1.1)).hom ▷ N.X p.2) ≫ g (p.1.1, p.2) k :=
  isoOfEquiv_hom_whiskerRight_comp_apply _ _ N g p k

/-- The matrix category of a monoidal preadditive category is monoidal, with the Kronecker product
of matrices as tensor product. -/
noncomputable instance instMonoidalCategory : MonoidalCategory (Mat_ C) :=
  .ofTensorHom
    (id_tensorHom_id := fun M N ↦ by
      ext ⟨i, j⟩ ⟨k, l⟩
      by_cases h₁ : i = k
      · by_cases h₂ : j = l
        · subst h₁ h₂
          simp
        · simp [h₂]
      · simp [h₁])
    (id_tensorHom := fun _ _ _ _ ↦ rfl)
    (tensorHom_id := fun _ _ ↦ rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ ↦ by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [tensorObj_ι, tensorObj_X, comp_apply, tensorHom_apply, tensorHom_comp_tensorHom,
        Fintype.sum_prod_type, tensor_sum, sum_tensor]
      rw [Finset.sum_comm])
    (associator_naturality := fun f₁ f₂ f₃ ↦ by
      rw [← Iso.eq_comp_inv, Category.assoc]
      ext p q
      simp only [associator_hom_comp_apply, comp_associator_inv_apply]
      simp)
    (leftUnitor_naturality := fun f ↦ by
      rw [← Iso.eq_comp_inv, Category.assoc]
      ext ⟨⟨⟩, i⟩ ⟨⟨⟩, k⟩
      simp only [leftUnitor_hom_comp_apply, comp_leftUnitor_inv_apply]
      simp)
    (rightUnitor_naturality := fun f ↦ by
      rw [← Iso.eq_comp_inv, Category.assoc]
      ext ⟨i, ⟨⟩⟩ ⟨k, ⟨⟩⟩
      simp only [rightUnitor_hom_comp_apply, comp_rightUnitor_inv_apply]
      simp)
    (pentagon := fun W X Y Z ↦ by
      -- The whiskerings of `Mat_ C` are by definition tensor products with identity matrices.
      change (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom = _
      refine (Category.comp_id _).symm.trans (Eq.trans ?_ (Category.comp_id _))
      ext p q
      simp only [Category.assoc, associator_hom_whiskerRight_comp_apply,
        associator_hom_comp_apply, whiskerLeft_associator_hom_comp_apply]
      simp)
    (triangle := fun X Y ↦ by
      -- The whiskerings of `Mat_ C` are by definition tensor products with identity matrices.
      change (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y
      refine (Category.comp_id _).symm.trans (Eq.trans ?_ (Category.comp_id _))
      ext p q
      simp only [Category.assoc, associator_hom_comp_apply, whiskerLeft_leftUnitor_hom_comp_apply,
        rightUnitor_hom_whiskerRight_comp_apply]
      simp)

/-- If `C` is monoidal preadditive, then so is its matrix category. -/
instance instMonoidalPreadditive : MonoidalPreadditive (Mat_ C) where
  whiskerLeft_zero := by intros; ext; simp
  zero_whiskerRight := by intros; ext; simp
  whiskerLeft_add := by intros; ext; simp [MonoidalPreadditive.tensor_add]
  add_whiskerRight := by intros; ext; simp [MonoidalPreadditive.add_tensor]

end CategoryTheory.Mat_

end

-- The strong monoidal structure on `Mat_.embedding C` stays unexposed: its unit and tensorator
-- are characterized by the entry lemmas below.
public section

namespace CategoryTheory.Mat_

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The tensor unit of `Mat_ C` is the one-term family on `𝟙_ C`; this identity isomorphism, typed
as an isomorphism with `(embedding C).obj (𝟙_ C)`, is the unit of `Mat_.embedding C`. -/
noncomputable def embeddingUnitIso : 𝟙_ (Mat_ C) ≅ (embedding C).obj (𝟙_ C) :=
  Iso.refl _

@[simp]
theorem embeddingUnitIso_hom_apply (u : (𝟙_ (Mat_ C)).ι) (v : ((embedding C).obj (𝟙_ C)).ι) :
    (embeddingUnitIso (C := C)).hom u v = 𝟙 (𝟙_ C) := by
  rcases u with ⟨⟩
  rcases v with ⟨⟩
  exact id_apply_self _ _

@[simp]
theorem embeddingUnitIso_inv_apply (v : ((embedding C).obj (𝟙_ C)).ι) (u : (𝟙_ (Mat_ C)).ι) :
    (embeddingUnitIso (C := C)).inv v u = 𝟙 (𝟙_ C) := by
  rcases u with ⟨⟩
  rcases v with ⟨⟩
  exact id_apply_self _ _

/-- The one-term family on `X ⊗ Y` is isomorphic to the tensor product of the one-term families on
`X` and `Y`, by the monomial isomorphism with entry `𝟙 (X ⊗ Y)`; this is the tensorator of
`Mat_.embedding C`. -/
noncomputable def embeddingTensorIso (X Y : C) :
    (embedding C).obj X ⊗ (embedding C).obj Y ≅ (embedding C).obj (X ⊗ Y) :=
  isoOfEquiv (Equiv.prodPUnit PUnit) fun _ ↦ Iso.refl _

@[simp]
theorem embeddingTensorIso_hom_apply (X Y : C) (p : ((embedding C).obj X ⊗ (embedding C).obj Y).ι)
    (u : ((embedding C).obj (X ⊗ Y)).ι) : (embeddingTensorIso X Y).hom p u = 𝟙 (X ⊗ Y) := by
  rcases p with ⟨⟨⟩, ⟨⟩⟩
  rcases u with ⟨⟩
  exact isoOfEquiv_hom_apply_self _ _ _

@[simp]
theorem embeddingTensorIso_inv_apply (X Y : C) (u : ((embedding C).obj (X ⊗ Y)).ι)
    (p : ((embedding C).obj X ⊗ (embedding C).obj Y).ι) :
    (embeddingTensorIso X Y).inv u p = 𝟙 (X ⊗ Y) := by
  rcases p with ⟨⟨⟩, ⟨⟩⟩
  rcases u with ⟨⟩
  exact isoOfEquiv_inv_apply_self _ _ _

variable [MonoidalPreadditive C]

/-- The embedding of a monoidal preadditive category into its matrix category is strong monoidal,
with unit and tensorator whose entries are identities. -/
noncomputable instance embeddingMonoidal : (embedding C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := embeddingUnitIso
      μIso := embeddingTensorIso
      -- In each axiom both sides are one-by-one matrices: after splitting the indices into their
      -- (unique) components, each side collapses to a single composite in `C`. The terms of the
      -- one-term families `(embedding C).obj X` are the objects `X` only up to unfolding
      -- `Mat_.embedding`, which the `change` steps perform.
      μIso_hom_natural_left := fun {X Y} f X' ↦ by
        ext ⟨a, b⟩ u
        obtain rfl := Subsingleton.elim a default
        obtain rfl := Subsingleton.elim b default
        obtain rfl := Subsingleton.elim u default
        simp only [comp_apply, tensorObj_ι, Fintype.sum_prod_type]
        simp only [Fintype.sum_unique, whiskerRight_apply, embedding_map_apply, id_apply_self,
          embeddingTensorIso_hom_apply]
        change (f ⊗ₘ 𝟙 X') ≫ 𝟙 (Y ⊗ X') = 𝟙 (X ⊗ X') ≫ f ▷ X'
        simp
      μIso_hom_natural_right := fun {X Y} X' f ↦ by
        ext ⟨a, b⟩ u
        obtain rfl := Subsingleton.elim a default
        obtain rfl := Subsingleton.elim b default
        obtain rfl := Subsingleton.elim u default
        simp only [comp_apply, tensorObj_ι, Fintype.sum_prod_type]
        simp only [Fintype.sum_unique, whiskerLeft_apply, embedding_map_apply, id_apply_self,
          embeddingTensorIso_hom_apply]
        change (𝟙 X' ⊗ₘ f) ≫ 𝟙 (X' ⊗ Y) = 𝟙 (X' ⊗ X) ≫ X' ◁ f
        simp
      associativity := fun X Y Z ↦ by
        ext ⟨⟨a, b⟩, c⟩ u
        obtain rfl := Subsingleton.elim a default
        obtain rfl := Subsingleton.elim b default
        obtain rfl := Subsingleton.elim c default
        obtain rfl := Subsingleton.elim u default
        simp only [associator_hom_comp_apply]
        simp only [comp_apply, tensorObj_ι, Fintype.sum_prod_type]
        simp only [Fintype.sum_unique, whiskerLeft_apply, whiskerRight_apply, embedding_map_apply,
          id_apply_self, embeddingTensorIso_hom_apply]
        change (𝟙 (X ⊗ Y) ⊗ₘ 𝟙 Z) ≫ 𝟙 ((X ⊗ Y) ⊗ Z) ≫ (α_ X Y Z).hom =
          (α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ 𝟙 (Y ⊗ Z)) ≫ 𝟙 (X ⊗ Y ⊗ Z)
        simp
      left_unitality := fun X ↦ by
        refine (Category.comp_id _).symm.trans ?_
        ext ⟨a, b⟩ u
        obtain rfl := Subsingleton.elim a default
        obtain rfl := Subsingleton.elim b default
        obtain rfl := Subsingleton.elim u default
        simp only [leftUnitor_hom_comp_apply]
        simp only [comp_apply, tensorObj_ι, Fintype.sum_prod_type]
        simp only [Fintype.sum_unique, whiskerRight_apply, embedding_map_apply, id_apply_self,
          embeddingUnitIso_hom_apply, embeddingTensorIso_hom_apply]
        change (λ_ X).hom ≫ 𝟙 X = (𝟙 (𝟙_ C) ⊗ₘ 𝟙 X) ≫ 𝟙 (𝟙_ C ⊗ X) ≫ (λ_ X).hom
        simp
      right_unitality := fun X ↦ by
        refine (Category.comp_id _).symm.trans ?_
        ext ⟨a, b⟩ u
        obtain rfl := Subsingleton.elim a default
        obtain rfl := Subsingleton.elim b default
        obtain rfl := Subsingleton.elim u default
        simp only [rightUnitor_hom_comp_apply]
        simp only [comp_apply, tensorObj_ι, Fintype.sum_prod_type]
        simp only [Fintype.sum_unique, whiskerLeft_apply, embedding_map_apply, id_apply_self,
          embeddingUnitIso_hom_apply, embeddingTensorIso_hom_apply]
        change (ρ_ X).hom ≫ 𝟙 X = (𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ≫ 𝟙 (X ⊗ 𝟙_ C) ≫ (ρ_ X).hom
        simp }

@[simp]
theorem embedding_ε : Functor.LaxMonoidal.ε (embedding C) = (embeddingUnitIso (C := C)).hom :=
  (rfl)

@[simp]
theorem embedding_η : Functor.OplaxMonoidal.η (embedding C) = (embeddingUnitIso (C := C)).inv :=
  (rfl)

@[simp]
theorem embedding_μ (X Y : C) :
    Functor.LaxMonoidal.μ (embedding C) X Y = (embeddingTensorIso X Y).hom :=
  (rfl)

@[simp]
theorem embedding_δ (X Y : C) :
    Functor.OplaxMonoidal.δ (embedding C) X Y = (embeddingTensorIso X Y).inv :=
  (rfl)

end CategoryTheory.Mat_

end
