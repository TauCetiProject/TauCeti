/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Basic

/-!
# Homomorphisms and isomorphisms of abelian schemes

A homomorphism of abelian schemes over a base scheme `S` is a morphism of the underlying schemes
over `S` that preserves the unit and multiplication of the group law (`IsMonHom`). These morphisms
form the category `AbelianScheme S`, induced from Mathlib's category `Grp (Over S)` of internal
group objects.

This file provides:

* the category instance on `AbelianScheme S`, the constructors `AbelianScheme.Hom.mk'` and
  `AbelianScheme.Hom.mk`, the forgetful functors `AbelianScheme.Hom.toOverFunctor` and
  `AbelianScheme.Hom.toSchemeFunctor`, and the projections `AbelianScheme.Hom.toOverHom` and
  `AbelianScheme.Hom.toSchemeHom`;
* the isomorphism projections `AbelianScheme.isoToOver`, `AbelianScheme.isoToScheme`, and the
  constructor `AbelianScheme.isoMk`;
* the identification of `AbelianScheme.identity S` as a zero object of `AbelianScheme S`
  (`AbelianScheme.isTerminalIdentity`, `AbelianScheme.isInitialIdentity`,
  `AbelianScheme.isZeroIdentity`).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {S : Scheme.{u}}

noncomputable section

/-- Abelian schemes over a base `S` form a category whose morphisms are group-scheme homomorphisms
over `S`. -/
instance : Category (AbelianScheme S) :=
  inferInstanceAs (Category (InducedCategory _ (fun A ↦ Grp.mk A.toOver)))

/-- A homomorphism of abelian schemes over `S`, i.e., a morphism in `AbelianScheme S`. -/
abbrev Hom (A B : AbelianScheme S) : Type u :=
  A ⟶ B

/-- Construct a homomorphism of abelian schemes from a morphism over `S` carrying an `IsMonHom`
instance. -/
def Hom.mk {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver) [IsMonHom f] : A ⟶ B :=
  InducedCategory.homMk (Grp.homMk f)

/-- Construct a homomorphism of abelian schemes from a morphism over `S` and proofs that it
preserves the unit and multiplication. -/
def Hom.mk' {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) : A ⟶ B :=
  InducedCategory.homMk (Grp.homMk'' f one_f mul_f)

/-- The forgetful functor from abelian schemes over `S` to `Over S`. -/
@[expose] def Hom.toOverFunctor : AbelianScheme S ⥤ Over S :=
  inducedFunctor (fun A : AbelianScheme S ↦ Grp.mk A.toOver) ⋙ Grp.forget (Over S)

/-- The underlying morphism of schemes over `S`. -/
abbrev Hom.toOverHom {A B : AbelianScheme S} (f : A ⟶ B) : A.toOver ⟶ B.toOver :=
  (Hom.toOverFunctor).map f

/-- `toOverHom` is definitionally the underlying morphism through `InducedCategory` and `Grp`. -/
private lemma Hom.toOverHom_def {A B : AbelianScheme S} (f : A ⟶ B) :
    Hom.toOverHom f = f.hom.hom.hom :=
  rfl

/-- `toOverHom` sends the identity homomorphism to the identity over `S`. -/
lemma Hom.toOverHom_id (A : AbelianScheme S) : Hom.toOverHom (𝟙 A) = 𝟙 A.toOver :=
  (Hom.toOverFunctor).map_id A

/-- `toOverHom` sends composition to composition over `S`. -/
@[reassoc]
lemma Hom.toOverHom_comp {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toOverHom (f ≫ g) = Hom.toOverHom f ≫ Hom.toOverHom g :=
  (Hom.toOverFunctor).map_comp f g

/-- The underlying morphism of an abelian-scheme homomorphism is a homomorphism of monoid
objects. -/
instance {A B : AbelianScheme S} (f : A ⟶ B) : IsMonHom (Hom.toOverHom f) :=
  Hom.toOverHom_def f ▸ inferInstance

/-- The underlying morphism over `S` of `Hom.mk f` is `f`. -/
@[simp]
lemma Hom.toOverHom_mk {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    Hom.toOverHom (Hom.mk f) = f :=
  (rfl)

/-- The underlying morphism over `S` of `Hom.mk' f` is `f`. -/
@[simp]
lemma Hom.toOverHom_mk' {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) :
    Hom.toOverHom (Hom.mk' f one_f mul_f) = f := by
  rw [Hom.toOverHom_def]
  exact Grp.homMk''_hom_hom (A := Grp.mk A.toOver) (B := Grp.mk B.toOver) f one_f mul_f

/-- A homomorphism of abelian schemes preserves the unit section. -/
@[reassoc]
lemma Hom.one_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    η[A.toOver] ≫ Hom.toOverHom f = η[B.toOver] :=
  IsMonHom.one_hom (Hom.toOverHom f)

/-- A homomorphism of abelian schemes preserves multiplication. -/
@[reassoc]
lemma Hom.mul_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    μ[A.toOver] ≫ Hom.toOverHom f = (Hom.toOverHom f ⊗ₘ Hom.toOverHom f) ≫ μ[B.toOver] :=
  IsMonHom.mul_hom (Hom.toOverHom f)

/-- A homomorphism of abelian schemes preserves inverses. -/
@[reassoc]
lemma Hom.inv_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    ι[A.toOver] ≫ Hom.toOverHom f = Hom.toOverHom f ≫ ι[B.toOver] :=
  GrpObj.inv_hom (Hom.toOverHom f)

/-- The forgetful functor from abelian schemes over `S` to their underlying schemes. -/
def Hom.toSchemeFunctor : AbelianScheme S ⥤ Scheme :=
  Hom.toOverFunctor ⋙ Over.forget S

/-- The object map of `Hom.toSchemeFunctor` returns the underlying scheme. -/
@[simp]
lemma Hom.toSchemeFunctor_obj (A : AbelianScheme S) :
    (Hom.toSchemeFunctor (S := S)).obj A = A.toScheme :=
  (rfl)

/-- The underlying morphism between the schemes of two abelian schemes. -/
abbrev Hom.toSchemeHom {A B : AbelianScheme S} (f : A ⟶ B) : A.toScheme ⟶ B.toScheme :=
  (Hom.toOverHom f).left

/-- The morphism map of `Hom.toSchemeFunctor` returns the underlying scheme morphism. -/
@[simp]
lemma Hom.toSchemeFunctor_map {A B : AbelianScheme S} (f : A ⟶ B) :
    (Hom.toSchemeFunctor (S := S)).map f =
      eqToHom (Hom.toSchemeFunctor_obj A) ≫ Hom.toSchemeHom f ≫
        eqToHom (Hom.toSchemeFunctor_obj B).symm :=
  (rfl)

/-- The underlying scheme morphism of `Hom.mk f` is `f.left`. -/
@[simp]
lemma Hom.toSchemeHom_mk {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    Hom.toSchemeHom (Hom.mk f) = f.left :=
  (rfl)

/-- The underlying scheme morphism of `Hom.mk' f` is `f.left`. -/
@[simp]
lemma Hom.toSchemeHom_mk' {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) :
    Hom.toSchemeHom (Hom.mk' f one_f mul_f) = f.left :=
  congrArg Over.Hom.left (Hom.toOverHom_mk' f one_f mul_f)

/-- `toSchemeHom` sends the identity homomorphism to the identity scheme morphism. -/
@[simp]
lemma Hom.toSchemeHom_id (A : AbelianScheme S) : Hom.toSchemeHom (𝟙 A) = 𝟙 A.toScheme :=
  congrArg Over.Hom.left (Hom.toOverHom_id A)

/-- `toSchemeHom` sends composition to composition of scheme morphisms. -/
@[simp, reassoc]
lemma Hom.toSchemeHom_comp {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toSchemeHom (f ≫ g) = Hom.toSchemeHom f ≫ Hom.toSchemeHom g :=
  congrArg Over.Hom.left (Hom.toOverHom_comp f g)

/-- The underlying scheme morphism of an abelian-scheme homomorphism commutes with the structure
morphisms to `S`. -/
@[reassoc]
lemma Hom.toSchemeHom_comp_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    Hom.toSchemeHom f ≫ B.toOver.hom = A.toOver.hom :=
  (Hom.toOverHom f).w

/-- Two homomorphisms of abelian schemes are equal when their underlying scheme morphisms are
equal. -/
@[ext]
lemma Hom.ext {A B : AbelianScheme S} {f g : A ⟶ B}
    (h : Hom.toSchemeHom f = Hom.toSchemeHom g) : f = g := by
  simp only [Hom.toSchemeHom, Hom.toOverHom_def] at h
  apply InducedCategory.hom_ext
  apply Grp.hom_ext
  exact Over.OverMorphism.ext h

/-- Forgetting an abelian-scheme homomorphism to its underlying morphism over `S` is faithful. -/
instance : (Hom.toOverFunctor (S := S)).Faithful where
  map_injective h := Hom.ext (congrArg Over.Hom.left h)

/-- Two homomorphisms of abelian schemes with the same underlying morphism over `S` are equal. -/
lemma Hom.toOverHom_injective {A B : AbelianScheme S} {f g : A ⟶ B}
    (h : Hom.toOverHom f = Hom.toOverHom g) : f = g :=
  Hom.toOverFunctor.map_injective h

/-! ### Isomorphisms -/

/-- Construct an isomorphism of abelian schemes from an isomorphism of their underlying schemes
over `S` whose forward morphism is a monoid-object homomorphism. -/
def isoMk {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] : A ≅ B where
  hom := Hom.mk e.hom
  inv := Hom.mk e.inv
  hom_inv_id := Hom.toOverHom_injective (by rw [Hom.toOverHom_comp, Hom.toOverHom_id]; simp)
  inv_hom_id := Hom.toOverHom_injective (by rw [Hom.toOverHom_comp, Hom.toOverHom_id]; simp)

@[simp]
lemma isoMk_hom {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] :
    (isoMk e).hom = Hom.mk e.hom :=
  (rfl)

@[simp]
lemma isoMk_inv {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] :
    (isoMk e).inv = Hom.mk e.inv :=
  (rfl)

/-- The isomorphism of schemes over `S` underlying an isomorphism of abelian schemes. -/
def isoToOver {A B : AbelianScheme S} (e : A ≅ B) : A.toOver ≅ B.toOver :=
  Hom.toOverFunctor.mapIso e

/-- The isomorphism of schemes underlying an isomorphism of abelian schemes. -/
def isoToScheme {A B : AbelianScheme S} (e : A ≅ B) : A.toScheme ≅ B.toScheme :=
  (Over.forget S).mapIso (isoToOver e)

@[simp]
lemma isoToOver_hom {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToOver e).hom = Hom.toOverHom e.hom :=
  (rfl)

@[simp]
lemma isoToOver_inv {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToOver e).inv = Hom.toOverHom e.inv :=
  (rfl)

@[simp]
lemma isoToScheme_hom {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToScheme e).hom = Hom.toSchemeHom e.hom := by simp [isoToScheme]

@[simp]
lemma isoToScheme_inv {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToScheme e).inv = Hom.toSchemeHom e.inv := by simp [isoToScheme]

@[simp]
lemma isoToOver_refl (A : AbelianScheme S) : isoToOver (Iso.refl A) = Iso.refl A.toOver :=
  Hom.toOverFunctor.mapIso_refl A

@[simp]
lemma isoToOver_symm {A B : AbelianScheme S} (e : A ≅ B) :
    isoToOver e.symm = (isoToOver e).symm := Iso.ext (by simp)

@[simp]
lemma isoToOver_trans {A B C : AbelianScheme S} (e : A ≅ B) (f : B ≅ C) :
    isoToOver (e.trans f) = (isoToOver e).trans (isoToOver f) :=
  Hom.toOverFunctor.mapIso_trans e f

@[simp]
lemma isoToScheme_refl (A : AbelianScheme S) :
    isoToScheme (Iso.refl A) = Iso.refl A.toScheme := Iso.ext (by simp)

@[simp]
lemma isoToScheme_symm {A B : AbelianScheme S} (e : A ≅ B) :
    isoToScheme e.symm = (isoToScheme e).symm := Iso.ext (by simp)

@[simp]
lemma isoToScheme_trans {A B C : AbelianScheme S} (e : A ≅ B) (f : B ≅ C) :
    isoToScheme (e.trans f) = (isoToScheme e).trans (isoToScheme f) := Iso.ext (by simp)

/-! ### The identity abelian scheme as a zero object -/

/-- There is a unique homomorphism from any abelian scheme over `S` to `identity S`. -/
instance uniqueHomToIdentity (A : AbelianScheme S) : Unique (A ⟶ identity S) :=
  let e : Grp.mk (identity S).toOver ≅ Grp.trivial (Over S) :=
    Grp.mkIso (eqToIso (identity_toOver S)) (identity_one S) (identity_mul S)
  ((InducedCategory.homEquiv (F := fun A : AbelianScheme S ↦ Grp.mk A.toOver)
      (X := A) (Y := identity S)).trans
    ((Iso.refl _).homCongr e)).unique

/-- There is a unique homomorphism from `identity S` to any abelian scheme over `S`. -/
instance uniqueHomFromIdentity (A : AbelianScheme S) : Unique (identity S ⟶ A) :=
  let e : Grp.mk (identity S).toOver ≅ Grp.trivial (Over S) :=
    Grp.mkIso (eqToIso (identity_toOver S)) (identity_one S) (identity_mul S)
  ((InducedCategory.homEquiv (F := fun A : AbelianScheme S ↦ Grp.mk A.toOver)
      (X := identity S) (Y := A)).trans
    (e.homCongr (Iso.refl _))).unique

/-- The unique homomorphism from an abelian scheme to the identity abelian scheme over `S`. -/
def toIdentity (A : AbelianScheme S) : A ⟶ identity S :=
  default

/-- The unique homomorphism from the identity abelian scheme over `S` to an abelian scheme. -/
def fromIdentity (A : AbelianScheme S) : identity S ⟶ A :=
  default

/-- The morphism over `S` underlying `toIdentity A` is the terminal map `toUnit A.toOver`, after
transporting along `identity_toOver`. -/
@[simp]
lemma toOverHom_toIdentity (A : AbelianScheme S) :
    Hom.toOverHom (toIdentity A) ≫ eqToHom (identity_toOver S) = toUnit A.toOver :=
  isTerminalTensorUnit.hom_ext _ _

/-- The scheme morphism underlying `toIdentity A` is the structure morphism of `A`, after
transporting its codomain to `S`. -/
@[simp]
lemma toSchemeHom_toIdentity (A : AbelianScheme S) :
    Hom.toSchemeHom (toIdentity A) ≫ eqToHom (identity_toScheme S) = A.toOver.hom := by
  rw [← Over.eqToHom_left (identity_toOver S)]
  exact congrArg Over.Hom.left (toOverHom_toIdentity A)

/-- The morphism over `S` underlying `fromIdentity A` is the unit section of `A`, after
transporting along `identity_toOver`. -/
@[simp]
lemma toOverHom_fromIdentity (A : AbelianScheme S) :
    eqToHom (identity_toOver S).symm ≫ Hom.toOverHom (fromIdentity A) = η[A.toOver] := by
  rw [← Hom.one_hom]
  congr 1
  exact (isTerminalIdentityToOver S).hom_ext _ _

/-- The scheme morphism underlying `fromIdentity A` is the zero section of `A`, after transporting
its domain from `S`. -/
@[simp]
lemma toSchemeHom_fromIdentity (A : AbelianScheme S) :
    eqToHom (identity_toScheme S).symm ≫ Hom.toSchemeHom (fromIdentity A) = A.zeroSection := by
  rw [← Over.eqToHom_left (identity_toOver S).symm]
  exact congrArg Over.Hom.left (toOverHom_fromIdentity A)

/-- The identity abelian scheme is terminal in `AbelianScheme S`. -/
def isTerminalIdentity (S : Scheme.{u}) : IsTerminal (identity S) :=
  IsTerminal.ofUnique _

/-- The identity abelian scheme is initial in `AbelianScheme S`. -/
def isInitialIdentity (S : Scheme.{u}) : IsInitial (identity S) :=
  IsInitial.ofUnique _

/-- The identity abelian scheme is a zero object of `AbelianScheme S`. -/
lemma isZeroIdentity (S : Scheme.{u}) : IsZero (identity S) where
  unique_to A := nonempty_unique (identity S ⟶ A)
  unique_from A := nonempty_unique (A ⟶ identity S)

instance (S : Scheme.{u}) : HasZeroObject (AbelianScheme S) :=
  ⟨identity S, isZeroIdentity S⟩

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
