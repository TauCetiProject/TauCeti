/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import TauCeti.CategoryTheory.Monoidal.Mon

/-!
# Binary coproducts of commutative monoid objects

In a symmetric monoidal category `C`, the tensor product `A ⊗ B` of two commutative monoid
objects is again a commutative monoid object. It is their coproduct in `CommMon C`: the
inclusions are `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`, and a pair of homomorphisms `f : A ⟶ T`,
`g : B ⟶ T` is induced by `(f ⊗ g) ≫ μ`. For commutative algebras over a commutative ring this
is the familiar statement that `A ⊗[R] B` is the coproduct of commutative `R`-algebras; for
quasicoherent algebras on a scheme it is dual to the fibre product of their relative spectra.

## Main declarations

* `CategoryTheory.CommMon.tensorObj`: the tensor product of commutative monoid objects;
* `CategoryTheory.CommMon.inl`, `CategoryTheory.CommMon.inr`: the two inclusions;
* `CategoryTheory.CommMon.desc`: the homomorphism out of the tensor product induced by a pair;
* `CategoryTheory.CommMon.binaryCofanIsColimit`: these data form a coproduct.

## References

* S. Mac Lane, *Categories for the Working Mathematician*, §VII.3 (monoids in a monoidal
  category).
-/

public section

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

namespace CategoryTheory

universe u v

namespace CommMon

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The tensor product of two commutative monoid objects, with the componentwise unit and
multiplication. -/
abbrev tensorObj (A B : CommMon C) : CommMon C :=
  ⟨A.X ⊗ B.X⟩

/-- The first inclusion `A ⟶ A ⊗ B`, informally `a ↦ a ⊗ 1`. -/
def inl (A B : CommMon C) : A ⟶ tensorObj A B :=
  homMk
    { hom := (ρ_ A.X).inv ≫ A.X ◁ η[B.X]
      isMonHom_hom := inferInstanceAs (IsMonHom ((ρ_ A.X).inv ≫ A.X ◁ η[B.X])) }

/-- The second inclusion `B ⟶ A ⊗ B`, informally `b ↦ 1 ⊗ b`. -/
def inr (A B : CommMon C) : B ⟶ tensorObj A B :=
  homMk
    { hom := (λ_ B.X).inv ≫ η[A.X] ▷ B.X
      isMonHom_hom := inferInstanceAs (IsMonHom ((λ_ B.X).inv ≫ η[A.X] ▷ B.X)) }

@[simp]
theorem inl_hom_hom (A B : CommMon C) :
    (inl A B).hom.hom = (ρ_ A.X).inv ≫ A.X ◁ η[B.X] :=
  (rfl)

@[simp]
theorem inr_hom_hom (A B : CommMon C) :
    (inr A B).hom.hom = (λ_ B.X).inv ≫ η[A.X] ▷ B.X :=
  (rfl)

/-- The homomorphism `A ⊗ B ⟶ T` induced by homomorphisms `f : A ⟶ T` and `g : B ⟶ T`,
informally `a ⊗ b ↦ f a * g b`. -/
def desc {A B T : CommMon C} (f : A ⟶ T) (g : B ⟶ T) : tensorObj A B ⟶ T :=
  homMk
    { hom := (f.hom.hom ⊗ₘ g.hom.hom) ≫ μ[T.X]
      -- The homomorphism instances of `f` and `g` refer to the monoid structures of `toMon`,
      -- so they are passed explicitly to the generic instance.
      isMonHom_hom :=
        have h (M N : C) [MonObj M] [MonObj N] (f : M ⟶ T.X) (g : N ⟶ T.X) [_hf : IsMonHom f]
            [_hg : IsMonHom g] : IsMonHom ((f ⊗ₘ g) ≫ μ[T.X]) :=
          inferInstance
        h A.X B.X f.hom.hom g.hom.hom (_hf := f.hom.isMonHom_hom) (_hg := g.hom.isMonHom_hom) }

@[simp]
theorem desc_hom_hom {A B T : CommMon C} (f : A ⟶ T) (g : B ⟶ T) :
    (desc f g).hom.hom = (f.hom.hom ⊗ₘ g.hom.hom) ≫ μ[T.X] :=
  (rfl)

@[reassoc (attr := simp)]
theorem inl_desc {A B T : CommMon C} (f : A ⟶ T) (g : B ⟶ T) : inl A B ≫ desc f g = f := by
  ext
  -- As in `desc`, the homomorphism instance of `g` is passed explicitly.
  exact (Category.assoc _ _ _).trans <| ((ρ_ A.X).inv ≫= @MonObj.whiskerLeft_one_tensorHom_mul
    _ _ _ _ _ _ _ _ f.hom.hom g.hom.hom g.hom.isMonHom_hom).trans (Iso.inv_hom_id_assoc _ _)

@[reassoc (attr := simp)]
theorem inr_desc {A B T : CommMon C} (f : A ⟶ T) (g : B ⟶ T) : inr A B ≫ desc f g = g := by
  ext
  -- As in `desc`, the homomorphism instance of `f` is passed explicitly.
  exact (Category.assoc _ _ _).trans <| ((λ_ B.X).inv ≫= @MonObj.whiskerRight_one_tensorHom_mul
    _ _ _ _ _ _ _ _ f.hom.hom g.hom.hom f.hom.isMonHom_hom).trans (Iso.inv_hom_id_assoc _ _)

/-- Homomorphisms out of `A ⊗ B` agree once they agree on both inclusions. -/
theorem tensorObj_hom_ext {A B T : CommMon C} {f g : tensorObj A B ⟶ T}
    (hl : inl A B ≫ f = inl A B ≫ g) (hr : inr A B ≫ f = inr A B ≫ g) : f = g := by
  -- As in `desc`, the homomorphism instances of `f` and `g` are passed explicitly.
  have key (h : tensorObj A B ⟶ T) :
      h.hom.hom = ((inl A B ≫ h).hom.hom ⊗ₘ (inr A B ≫ h).hom.hom) ≫ μ[T.X] :=
    (@MonObj.tensorHom_whisker_one_comp_mul _ _ _ _ _ _ _ _ _ _ h.hom.hom
      h.hom.isMonHom_hom).symm
  ext
  rw [key f, key g, hl, hr]

/-- The binary cofan `A ⟶ A ⊗ B ⟵ B` of the two inclusions. -/
abbrev binaryCofan (A B : CommMon C) : BinaryCofan A B :=
  BinaryCofan.mk (inl A B) (inr A B)

/-- The tensor product of commutative monoid objects is their coproduct. -/
def binaryCofanIsColimit (A B : CommMon C) : IsColimit (binaryCofan A B) :=
  BinaryCofan.IsColimit.mk _ desc inl_desc inr_desc fun f g _ hl hr ↦
    tensorObj_hom_ext (hl.trans (inl_desc f g).symm) (hr.trans (inr_desc f g).symm)

instance : HasBinaryCoproducts (CommMon C) :=
  @hasBinaryCoproducts_of_hasColimit_pair _ _ fun {A B} ↦
    ⟨⟨⟨_, binaryCofanIsColimit A B⟩⟩⟩

end CommMon

end CategoryTheory
