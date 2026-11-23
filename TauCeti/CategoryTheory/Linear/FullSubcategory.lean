/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Algebra.Hom

/-!
# Additive and linear structure on morphisms of a full subcategory

A full subcategory of a preadditive (resp. `R`-linear) category inherits a preadditive
(resp. `R`-linear) structure. This file records that the underlying morphism of a sum, a
negation, a difference or a scalar multiple of morphisms in the full subcategory is the
corresponding operation applied to the underlying morphisms in the ambient category. The zero
morphism is Mathlib's `CategoryTheory.ObjectProperty.zero_hom`.

## Main results

* `CategoryTheory.ObjectProperty.add_hom`, `CategoryTheory.ObjectProperty.neg_hom`,
  `CategoryTheory.ObjectProperty.sub_hom`: the underlying morphism of a morphism built from the
  preadditive structure.
* `CategoryTheory.ObjectProperty.smul_hom`: the underlying morphism of a scalar multiple.
* `CategoryTheory.ObjectProperty.nsmul_hom`, `CategoryTheory.ObjectProperty.zsmul_hom`:
  the underlying morphism of a natural or integer multiple in a preadditive category.
* `CategoryTheory.ObjectProperty.restrictEndAlgHom`: for `P ≤ Q` and a functor `F` to an
  `R`-linear category, restricting natural endomorphisms of `Q.ι ⋙ F` to the smaller full
  subcategory is an `R`-algebra homomorphism; restriction along `le_rfl` is the identity and
  restrictions compose (`restrictEndAlgHom_refl`, `restrictEndAlgHom_comp`).
-/

public section

namespace CategoryTheory.ObjectProperty

universe w v u

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

section Preadditive

variable [Preadditive C] {X Y : P.FullSubcategory}

/-- The underlying morphism of a sum in a full subcategory is the sum of the underlying
morphisms. -/
@[simp] theorem add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl

/-- The underlying morphism of a negation in a full subcategory is the negation of the underlying
morphism. -/
@[simp] theorem neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := rfl

/-- The underlying morphism of a difference in a full subcategory is the difference of the
underlying morphisms. -/
@[simp] theorem sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := rfl

/-- The underlying morphism of a natural multiple in a full subcategory is the natural
multiple of the underlying morphism. -/
@[simp] theorem nsmul_hom (n : ℕ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl

/-- The underlying morphism of an integer multiple in a full subcategory is the integer
multiple of the underlying morphism. -/
@[simp] theorem zsmul_hom (n : ℤ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl

end Preadditive

/-- The underlying morphism of a scalar multiple in a full subcategory of a linear category is the
scalar multiple of the underlying morphism. -/
@[simp] theorem smul_hom {R : Type w} [Semiring R] [Preadditive C] [Linear R C]
    {X Y : P.FullSubcategory} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom := rfl

section Restrict

variable {D : Type*} [Category* D] [Preadditive D] {R : Type w} [CommSemiring R] [Linear R D]
  {Q S : ObjectProperty C}

/-- For `P ≤ Q`, restricting a natural endomorphism of `Q.ι ⋙ F` to objects satisfying `P` is an
algebra homomorphism `End (Q.ι ⋙ F) →ₐ[R] End (P.ι ⋙ F)`. -/
def restrictEndAlgHom (h : P ≤ Q) (F : C ⥤ D) : End (Q.ι ⋙ F) →ₐ[R] End (P.ι ⋙ F) where
  toFun η := .of
    { app Y := η.asHom.app ((ιOfLE h).obj Y)
      naturality _ _ g := η.asHom.naturality ((ιOfLE h).map g) }
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The components of a restricted natural endomorphism are those of the original one. -/
@[simp]
theorem restrictEndAlgHom_asHom_app (h : P ≤ Q) (F : C ⥤ D) (η : End (Q.ι ⋙ F))
    (Y : P.FullSubcategory) :
    (restrictEndAlgHom (R := R) h F η).asHom.app Y = η.asHom.app ((ιOfLE h).obj Y) :=
  (rfl)

/-- Restriction to the same full subcategory is the identity. -/
@[simp]
theorem restrictEndAlgHom_refl (F : C ⥤ D) :
    restrictEndAlgHom (R := R) (le_refl P) F = AlgHom.id R _ :=
  (rfl)

/-- Restricting in two steps is restricting once. -/
theorem restrictEndAlgHom_comp (h₁ : P ≤ Q) (h₂ : Q ≤ S) (F : C ⥤ D) :
    (restrictEndAlgHom (R := R) h₁ F).comp (restrictEndAlgHom h₂ F) =
      restrictEndAlgHom (h₁.trans h₂) F :=
  (rfl)

end Restrict

end CategoryTheory.ObjectProperty
