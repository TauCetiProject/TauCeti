/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Splitting one summand off a biproduct

In a preadditive category, a biproduct `⨁ f` is the binary biproduct of one summand `f j` and the
biproduct of the remaining summands `f j'`, `j' ≠ j`. The underlying identity
`π j ≫ ι j + toSubtype ≫ fromSubtype = 𝟙` decomposes the identity of `⨁ f`. This is the inductive
step of arguments that peel off one summand at a time, such as the exchange argument for the
uniqueness of decompositions. A biproduct over an empty index type is zero.

## Main results

* `TauCeti.biproduct_π_ι_add_toSubtype_fromSubtype`: the decomposition of the identity.
* `TauCeti.biproductSubtypeNeIso`: `⨁ f ≅ f j ⊞ ⨁_{j' ≠ j} f j'`.
* `TauCeti.isZero_biproduct_of_isEmpty`: a biproduct over an empty index type is zero.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v w u

section IsEmpty

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A biproduct over an empty index type is zero. -/
theorem isZero_biproduct_of_isEmpty {J : Type w} [IsEmpty J] (f : J → C) [HasBiproduct f] :
    IsZero (⨁ f) :=
  (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun j ↦ isEmptyElim j)

end IsEmpty

section SubtypeNe

variable {C : Type u} [Category.{v} C] [Preadditive C] {J : Type w} (f : J → C) (j : J)
  [HasBiproduct f] [HasBiproduct (Subtype.restrict (· ≠ j) f)]

/-- The decomposition `⨁ f = f j ⊕ ⨁_{j' ≠ j} f j'` of the identity: the projection onto the
summand `f j` followed by its inclusion, plus the projection onto the remaining summands followed
by their inclusion. -/
theorem biproduct_π_ι_add_toSubtype_fromSubtype :
    biproduct.π f j ≫ biproduct.ι f j +
      biproduct.toSubtype f (· ≠ j) ≫ biproduct.fromSubtype f (· ≠ j) = 𝟙 (⨁ f) := by
  classical
  ext a b
  by_cases hab : b = a
  · subst hab
    by_cases hb : b = j
    · subst hb
      simp
    · simp [biproduct.ι_π_ne_assoc _ hb, hb]
  · by_cases hb : b = j
    · subst hb
      simp [biproduct.ι_π_ne _ hab, biproduct.ι_π_ne_assoc _ hab]
    · simp [biproduct.ι_π_ne_assoc _ hb, biproduct.ι_π_ne_assoc _ hab, biproduct.ι_π_ne _ hab]

variable [HasBinaryBiproduct (f j) (⨁ Subtype.restrict (· ≠ j) f)]

/-- A biproduct is the binary biproduct of one summand `f j` and the biproduct of the remaining
summands. -/
noncomputable def biproductSubtypeNeIso : ⨁ f ≅ f j ⊞ ⨁ Subtype.restrict (· ≠ j) f where
  hom := biprod.lift (biproduct.π f j) (biproduct.toSubtype f (· ≠ j))
  inv := biprod.desc (biproduct.ι f j) (biproduct.fromSubtype f (· ≠ j))
  hom_inv_id := by
    rw [biprod.lift_desc, biproduct_π_ι_add_toSubtype_fromSubtype]
  inv_hom_id := by
    classical
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · simp
    · ext k
      simp
    · ext k
      simp [biproduct.fromSubtype_π]
    · simp

@[simp]
theorem biproductSubtypeNeIso_hom :
    (biproductSubtypeNeIso f j).hom =
      biprod.lift (biproduct.π f j) (biproduct.toSubtype f (· ≠ j)) :=
  (rfl)

@[simp]
theorem biproductSubtypeNeIso_inv :
    (biproductSubtypeNeIso f j).inv =
      biprod.desc (biproduct.ι f j) (biproduct.fromSubtype f (· ≠ j)) :=
  (rfl)

end SubtypeNe

end TauCeti
