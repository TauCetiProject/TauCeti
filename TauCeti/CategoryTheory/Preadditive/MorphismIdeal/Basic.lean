/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Quotient.Linear
public import Mathlib.CategoryTheory.Quotient.Preadditive
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Two-sided ideals of a preadditive category and their quotients

A **two-sided ideal** `I` of a preadditive category `C` assigns to every pair of objects an
additive subgroup `I(X, Y)` of the hom group `X ⟶ Y`, stable under composition with arbitrary
morphisms on either side. Two parallel morphisms are congruent modulo `I` when their difference
lies in `I`; this is a congruence, and the quotient category `C/I` has the objects of `C` and the
hom groups `(X ⟶ Y) ⧸ I(X, Y)`.

Such quotients are how stable categories arise: the stable category of a Frobenius exact category
is the quotient by the ideal of morphisms factoring through a projective-injective object, and
the homotopy category of complexes is the quotient by the ideal of null-homotopic chain maps.
This file supplies the generic part of that construction, for an arbitrary ideal:

* the quotient category is preadditive, the quotient functor is additive, full and essentially
  surjective, and its hom groups are the quotient groups `(X ⟶ Y) ⧸ I(X, Y)`;
* every ideal is the kernel of its quotient functor, and conversely the morphisms an additive
  functor sends to zero form an ideal;
* an additive functor factors through `C/I` exactly when it kills `I`, and the factorization is
  additive (and linear, when the functor is);
* over an `R`-linear category every ideal is automatically stable under the scalar action, so the
  quotient is `R`-linear with an `R`-linear quotient functor.

The quotient is Mathlib's `CategoryTheory.Quotient` by the congruence `TauCeti.MorphismIdeal.rel`,
so its general API — uniqueness of factorizations (`CategoryTheory.Quotient.lift_unique'`),
descent of natural transformations (`CategoryTheory.Quotient.natTransLift`), and fullness and
faithfulness of precomposition with the quotient functor — applies to `C/I` unchanged.

## Main definitions

* `TauCeti.MorphismIdeal C`: a two-sided ideal of the preadditive category `C`, ordered by
  inclusion.
* `CategoryTheory.Functor.kerIdeal F`: the ideal of morphisms an additive functor `F` sends to
  zero.
* `TauCeti.MorphismIdeal.rel I`: congruence modulo `I`.
* `TauCeti.MorphismIdeal.Quotient I` and `TauCeti.MorphismIdeal.quotientFunctor I`: the quotient
  category `C/I` and the quotient functor `C ⥤ C/I`.
* `TauCeti.MorphismIdeal.homAddEquiv I X Y`: the identification of the hom group of `C/I` with
  the quotient group `(X ⟶ Y) ⧸ I(X, Y)`.
* `TauCeti.MorphismIdeal.lift I F hF`: the factorization through `C/I` of a functor killing `I`.

## Main results

* `TauCeti.MorphismIdeal.quotientFunctor_map_eq_zero_iff`: a morphism becomes zero in `C/I`
  exactly when it lies in `I`, and `TauCeti.MorphismIdeal.kerIdeal_quotientFunctor` the resulting
  statement that `I` is the kernel of its quotient functor.
* `TauCeti.MorphismIdeal.exists_quotientFunctor_comp_eq_iff`: an additive functor factors through
  `C/I` exactly when its kernel contains `I`.
* `TauCeti.MorphismIdeal.smul_mem`: an ideal of an `R`-linear category is stable under scalars.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995),
  Chapter IV, Section 1 (ideals of an additive category and the associated quotient categories).
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, LMS Lecture Note Series 119, CUP (1988), Section I.2.
-/

public section

universe v u v' u'

namespace TauCeti

open CategoryTheory

/-- A **two-sided ideal** of a preadditive category `C`: for every pair of objects an additive
subgroup `hom X Y` of the morphisms `X ⟶ Y`, such that a composite of morphisms lies in the ideal
as soon as one of its two factors does. -/
structure MorphismIdeal (C : Type u) [Category.{v} C] [Preadditive C] where
  /-- The morphisms `X ⟶ Y` belonging to the ideal, an additive subgroup of the hom group. -/
  hom (X Y : C) : AddSubgroup (X ⟶ Y)
  /-- Precomposing a member of the ideal with any morphism stays in the ideal. -/
  comp_mem_left {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} : g ∈ hom Y Z → f ≫ g ∈ hom X Z
  /-- Postcomposing a member of the ideal with any morphism stays in the ideal. -/
  comp_mem_right {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) : f ∈ hom X Y → f ≫ g ∈ hom X Z

namespace MorphismIdeal

variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem hom_injective :
    Function.Injective (hom : MorphismIdeal C → ∀ X Y : C, AddSubgroup (X ⟶ Y))
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/-- Two ideals with the same members are equal. -/
@[ext]
theorem ext {I J : MorphismIdeal C}
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), f ∈ I.hom X Y ↔ f ∈ J.hom X Y) : I = J :=
  hom_injective <| funext fun X ↦ funext fun Y ↦ AddSubgroup.ext (h (X := X) (Y := Y))

/-- Ideals are ordered by inclusion. -/
instance : PartialOrder (MorphismIdeal C) :=
  PartialOrder.lift hom hom_injective

theorem le_def {I J : MorphismIdeal C} :
    I ≤ J ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), f ∈ I.hom X Y → f ∈ J.hom X Y :=
  Iff.rfl

/-- Over an `R`-linear category an ideal is automatically stable under the scalar action, since
`a • f = (a • 𝟙 X) ≫ f`. -/
theorem smul_mem {R : Type*} [Semiring R] [Linear R C] (I : MorphismIdeal C) (a : R) {X Y : C}
    {f : X ⟶ Y} (hf : f ∈ I.hom X Y) : a • f ∈ I.hom X Y := by
  simpa using I.comp_mem_left (a • 𝟙 X) hf

end MorphismIdeal

end TauCeti

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] {D : Type u'} [Category.{v'} D]
  [Preadditive D]

/-- The **kernel** of an additive functor `F`: the ideal of morphisms that `F` sends to zero. -/
def kerIdeal (F : C ⥤ D) [F.Additive] : TauCeti.MorphismIdeal C where
  hom _ _ := F.mapAddHom.ker
  comp_mem_left := by
    intro _ _ _ f g hg
    rw [AddMonoidHom.mem_ker, coe_mapAddHom] at hg ⊢
    rw [F.map_comp, hg, Limits.comp_zero]
  comp_mem_right := by
    intro _ _ _ f g hf
    rw [AddMonoidHom.mem_ker, coe_mapAddHom] at hf ⊢
    rw [F.map_comp, hf, Limits.zero_comp]

@[simp]
theorem mem_kerIdeal_hom (F : C ⥤ D) [F.Additive] {X Y : C} {f : X ⟶ Y} :
    f ∈ F.kerIdeal.hom X Y ↔ F.map f = 0 := by
  simp [kerIdeal, AddMonoidHom.mem_ker]

end CategoryTheory.Functor

namespace TauCeti

namespace MorphismIdeal

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] (I : MorphismIdeal C)

/-! ### The congruence modulo an ideal -/

/-- **Congruence modulo `I`**: two parallel morphisms are related when their difference lies in
`I`. -/
def rel : HomRel C :=
  fun X Y f g ↦ f - g ∈ I.hom X Y

theorem rel_iff {X Y : C} {f g : X ⟶ Y} : I.rel f g ↔ f - g ∈ I.hom X Y :=
  Iff.rfl

instance : Congruence I.rel where
  equivalence :=
    { refl f := by simp [rel_iff]
      symm {f g} h := by
        rw [rel_iff, ← neg_sub]
        exact neg_mem h
      trans {f g h} h₁ h₂ := by
        rw [rel_iff, ← sub_add_sub_cancel f g h]
        exact add_mem h₁ h₂ }
  comp_left := by
    intro _ _ _ f _ _ h
    rw [rel_iff, ← Preadditive.comp_sub]
    exact I.comp_mem_left f h
  comp_right := by
    intro _ _ _ _ _ g h
    rw [rel_iff, ← Preadditive.sub_comp]
    exact I.comp_mem_right g h

theorem rel_add {X Y : C} {f₁ f₂ g₁ g₂ : X ⟶ Y} (hf : I.rel f₁ f₂) (hg : I.rel g₁ g₂) :
    I.rel (f₁ + g₁) (f₂ + g₂) := by
  rw [rel_iff, add_sub_add_comm]
  exact add_mem hf hg

/-! ### The quotient category -/

/-- The **quotient category** `C/I`: the objects of `C`, with morphisms taken modulo `I`. It is
Mathlib's quotient category by the congruence `I.rel`, whose API it inherits. -/
abbrev Quotient : Type u :=
  CategoryTheory.Quotient I.rel

/-- The quotient functor `C ⥤ C/I`. It is full and essentially surjective by
`CategoryTheory.Quotient.full_functor` and `CategoryTheory.Quotient.essSurj_functor`. -/
abbrev quotientFunctor : C ⥤ I.Quotient :=
  CategoryTheory.Quotient.functor I.rel

noncomputable instance : Preadditive I.Quotient :=
  CategoryTheory.Quotient.preadditive I.rel fun _ _ _ _ _ _ hf hg ↦ I.rel_add hf hg

instance : I.quotientFunctor.Additive where

theorem quotientFunctor_map_eq_iff {X Y : C} {f g : X ⟶ Y} :
    I.quotientFunctor.map f = I.quotientFunctor.map g ↔ f - g ∈ I.hom X Y :=
  CategoryTheory.Quotient.functor_map_eq_iff I.rel f g

/-- A morphism becomes zero in the quotient category exactly when it lies in the ideal. -/
@[simp]
theorem quotientFunctor_map_eq_zero_iff {X Y : C} {f : X ⟶ Y} :
    I.quotientFunctor.map f = 0 ↔ f ∈ I.hom X Y := by
  rw [← I.quotientFunctor.map_zero X Y, quotientFunctor_map_eq_iff, sub_zero]

/-- Every ideal is the kernel of its quotient functor. -/
@[simp]
theorem kerIdeal_quotientFunctor : I.quotientFunctor.kerIdeal = I := by
  ext
  simp

/-- The hom group of the quotient category between the images of `X` and `Y` is the quotient
group `(X ⟶ Y) ⧸ I(X, Y)`. -/
noncomputable def homAddEquiv (X Y : C) :
    (X ⟶ Y) ⧸ I.hom X Y ≃+ (I.quotientFunctor.obj X ⟶ I.quotientFunctor.obj Y) :=
  QuotientAddGroup.liftEquiv (I.hom X Y) (φ := I.quotientFunctor.mapAddHom)
    I.quotientFunctor.map_surjective
    (AddSubgroup.ext fun _ ↦ by
      rw [AddMonoidHom.mem_ker, Functor.coe_mapAddHom, quotientFunctor_map_eq_zero_iff])

@[simp]
theorem homAddEquiv_mk {X Y : C} (f : X ⟶ Y) :
    I.homAddEquiv X Y (f : (X ⟶ Y) ⧸ I.hom X Y) = I.quotientFunctor.map f :=
  QuotientAddGroup.liftEquiv_coe _ _ _ f

/-! ### The universal property -/

section lift

variable {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive]

/-- Congruence modulo the kernel of `F` is Mathlib's relation `F.homRel` of having the same image
under `F`. -/
theorem rel_kerIdeal_iff {X Y : C} {f g : X ⟶ Y} : F.kerIdeal.rel f g ↔ F.homRel f g := by
  rw [rel_iff, Functor.mem_kerIdeal_hom, F.map_sub, sub_eq_zero, Functor.homRel_iff]

/-- A functor killing `I` sends morphisms congruent modulo `I` to the same morphism. -/
theorem map_eq_of_rel (hF : I ≤ F.kerIdeal) {X Y : C} {f g : X ⟶ Y} (h : I.rel f g) :
    F.map f = F.map g := by
  rw [← sub_eq_zero, ← F.map_sub]
  exact (Functor.mem_kerIdeal_hom F).1 (le_def.1 hF _ h)

/-- The **factorization through the quotient category** of an additive functor killing `I`.
It restricts to `F` along the quotient functor by `CategoryTheory.Quotient.lift_spec`, and is the
unique such functor by `CategoryTheory.Quotient.lift_unique`. -/
abbrev lift (hF : I ≤ F.kerIdeal) : I.Quotient ⥤ D :=
  CategoryTheory.Quotient.lift I.rel F fun _ _ _ _ h ↦ I.map_eq_of_rel F hF h

instance (hF : I ≤ F.kerIdeal) : (I.lift F hF).Additive where
  map_add {X Y} f g := by
    obtain ⟨f, rfl⟩ := I.quotientFunctor.map_surjective f
    obtain ⟨g, rfl⟩ := I.quotientFunctor.map_surjective g
    rw [← I.quotientFunctor.map_add]
    simp only [CategoryTheory.Quotient.lift_map_functor_map, F.map_add]

/-- **An additive functor factors through the quotient category exactly when it kills the
ideal.** -/
theorem exists_quotientFunctor_comp_eq_iff :
    (∃ G : I.Quotient ⥤ D, I.quotientFunctor ⋙ G = F) ↔ I ≤ F.kerIdeal := by
  refine ⟨?_, fun hF ↦ ⟨I.lift F hF, CategoryTheory.Quotient.lift_spec _ _ _⟩⟩
  rintro ⟨G, rfl⟩ X Y f hf
  rw [Functor.mem_kerIdeal_hom, Functor.comp_map, (quotientFunctor_map_eq_zero_iff I).2 hf,
    ← I.quotientFunctor.map_zero, ← Functor.comp_map, Functor.map_zero]

end lift

/-! ### Linear quotients -/

section Linear

variable (R : Type*) [Semiring R] [Linear R C]

theorem rel_smul (a : R) {X Y : C} {f g : X ⟶ Y} (h : I.rel f g) : I.rel (a • f) (a • g) := by
  rw [rel_iff, ← smul_sub]
  exact I.smul_mem a h

/-- Over an `R`-linear category, the quotient by any ideal is `R`-linear. -/
noncomputable instance : Linear R I.Quotient :=
  CategoryTheory.Quotient.linear R I.rel fun a _ _ _ _ h ↦ I.rel_smul R a h

instance : I.quotientFunctor.Linear R :=
  CategoryTheory.Quotient.linear_functor R I.rel fun a _ _ _ _ h ↦ I.rel_smul R a h

/-- The factorization of an `R`-linear functor through the quotient category is `R`-linear. -/
instance {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D] {F : C ⥤ D} [F.Additive]
    [F.Linear R] (hF : I ≤ F.kerIdeal) : (I.lift F hF).Linear R where
  map_smul {X Y} f a := by
    obtain ⟨f, rfl⟩ := I.quotientFunctor.map_surjective f
    rw [← I.quotientFunctor.map_smul]
    simp only [CategoryTheory.Quotient.lift_map_functor_map, F.map_smul]

end Linear

end MorphismIdeal

end TauCeti
