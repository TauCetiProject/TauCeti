/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Basic

/-!
# Scheme-level projections, isomorphisms, and zero object of abelian schemes

This file extends `TauCeti.AlgebraicGeometry.AbelianScheme.Basic` with:

* `AbelianScheme.toSchemeFunctor` and `AbelianScheme.toSchemeHom`: the forgetful functor to
  `Scheme` and the underlying scheme morphism of a homomorphism;
* `AbelianScheme.isoMk`, `AbelianScheme.isoToOver`, and `AbelianScheme.isoToScheme`: constructing
  isomorphisms of abelian schemes from monoid-homomorphism isomorphisms in `Over S` via
  `Grp.mkIso'` and `fullyFaithfulInducedFunctor.preimageIso`, and forgetting them to `Over S` or
  `Scheme`;
* `AbelianScheme.isTerminalIdentity`, `AbelianScheme.isInitialIdentity`, and
  `AbelianScheme.isZeroIdentity`: `AbelianScheme.identity S` is a zero object of
  `AbelianScheme S`.
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

/-! ### Forgetful functor to `Scheme` -/

/-- The forgetful functor from abelian schemes over `S` to their underlying schemes. -/
def toSchemeFunctor : AbelianScheme S ⥤ Scheme :=
  toOverFunctor ⋙ Over.forget S

/-- The object map of `toSchemeFunctor` returns the underlying scheme. -/
@[simp]
lemma toSchemeFunctor_obj (A : AbelianScheme S) :
    (toSchemeFunctor (S := S)).obj A = A.toScheme :=
  (rfl)

/-- The underlying morphism between the schemes of two abelian schemes. -/
abbrev toSchemeHom {A B : AbelianScheme S} (f : A ⟶ B) : A.toScheme ⟶ B.toScheme :=
  (toOverHom f).left

/-- The morphism map of `toSchemeFunctor` returns the underlying scheme morphism. -/
@[simp]
lemma toSchemeFunctor_map {A B : AbelianScheme S} (f : A ⟶ B) :
    (toSchemeFunctor (S := S)).map f =
      eqToHom (toSchemeFunctor_obj A) ≫ toSchemeHom f ≫
        eqToHom (toSchemeFunctor_obj B).symm :=
  (rfl)

/-- The underlying scheme morphism of `homMk f` is `f.left`. -/
@[simp]
lemma toSchemeHom_homMk {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) :
    toSchemeHom (homMk f one_f mul_f) = f.left :=
  congrArg Over.Hom.left (toOverHom_homMk f one_f mul_f)

/-- `toSchemeHom` sends the identity homomorphism to the identity scheme morphism. -/
@[simp]
lemma toSchemeHom_id (A : AbelianScheme S) : toSchemeHom (𝟙 A) = 𝟙 A.toScheme :=
  congrArg Over.Hom.left (toOverHom_id A)

/-- `toSchemeHom` sends composition to composition of scheme morphisms. -/
@[simp, reassoc]
lemma toSchemeHom_comp {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    toSchemeHom (f ≫ g) = toSchemeHom f ≫ toSchemeHom g :=
  congrArg Over.Hom.left (toOverHom_comp f g)

/-- The underlying scheme morphism of an abelian-scheme homomorphism commutes with the structure
morphisms to `S`. -/
@[reassoc]
lemma toSchemeHom_comp_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    toSchemeHom f ≫ B.toOver.hom = A.toOver.hom :=
  (toOverHom f).w

/-! ### Isomorphisms -/

/-- Construct an isomorphism of abelian schemes from an isomorphism of their underlying schemes
over `S` whose forward morphism is a monoid-object homomorphism. -/
def isoMk {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] : A ≅ B :=
  (fullyFaithfulInducedFunctor fun X : AbelianScheme S ↦ Grp.mk X.toOver).preimageIso
    (Grp.mkIso' e)

@[simp]
lemma toOverHom_isoMk_hom {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] :
    toOverHom (isoMk e).hom = e.hom :=
  (rfl)

@[simp]
lemma toOverHom_isoMk_inv {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] :
    toOverHom (isoMk e).inv = e.inv :=
  (rfl)

/-- The isomorphism of schemes over `S` underlying an isomorphism of abelian schemes. -/
def isoToOver {A B : AbelianScheme S} (e : A ≅ B) : A.toOver ≅ B.toOver :=
  toOverFunctor.mapIso e

/-- The isomorphism of schemes underlying an isomorphism of abelian schemes. -/
def isoToScheme {A B : AbelianScheme S} (e : A ≅ B) : A.toScheme ≅ B.toScheme :=
  (Over.forget S).mapIso (isoToOver e)

@[simp]
lemma isoToOver_hom {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToOver e).hom = toOverHom e.hom :=
  (rfl)

@[simp]
lemma isoToOver_inv {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToOver e).inv = toOverHom e.inv :=
  (rfl)

@[simp]
lemma isoToScheme_hom {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToScheme e).hom = toSchemeHom e.hom := by simp [isoToScheme]

@[simp]
lemma isoToScheme_inv {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToScheme e).inv = toSchemeHom e.inv := by simp [isoToScheme]

@[simp]
lemma isoToOver_refl (A : AbelianScheme S) : isoToOver (Iso.refl A) = Iso.refl A.toOver :=
  toOverFunctor.mapIso_refl A

@[simp]
lemma isoToOver_symm {A B : AbelianScheme S} (e : A ≅ B) :
    isoToOver e.symm = (isoToOver e).symm := Iso.ext (by simp)

@[simp]
lemma isoToOver_trans {A B C : AbelianScheme S} (e : A ≅ B) (f : B ≅ C) :
    isoToOver (e.trans f) = (isoToOver e).trans (isoToOver f) :=
  toOverFunctor.mapIso_trans e f

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
    eqToIso (grpMk_identity_toOver S)
  ((InducedCategory.homEquiv (F := fun X : AbelianScheme S ↦ Grp.mk X.toOver)
      (X := A) (Y := identity S)).trans
    ((Iso.refl _).homCongr e)).unique

/-- There is a unique homomorphism from `identity S` to any abelian scheme over `S`. -/
instance uniqueHomFromIdentity (A : AbelianScheme S) : Unique (identity S ⟶ A) :=
  let e : Grp.mk (identity S).toOver ≅ Grp.trivial (Over S) :=
    eqToIso (grpMk_identity_toOver S)
  ((InducedCategory.homEquiv (F := fun X : AbelianScheme S ↦ Grp.mk X.toOver)
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
    toOverHom (toIdentity A) ≫ eqToHom (identity_toOver S) = toUnit A.toOver :=
  isTerminalTensorUnit.hom_ext _ _

/-- The scheme morphism underlying `toIdentity A` is the structure morphism of `A`, after
transporting its codomain to `S`. -/
@[simp]
lemma toSchemeHom_toIdentity (A : AbelianScheme S) :
    toSchemeHom (toIdentity A) ≫ eqToHom (identity_toScheme S) = A.toOver.hom := by
  rw [← Over.eqToHom_left (identity_toOver S)]
  exact congrArg Over.Hom.left (toOverHom_toIdentity A)

/-- The morphism over `S` underlying `fromIdentity A` is the unit section of `A`, after
transporting along `identity_toOver`. -/
@[simp]
lemma toOverHom_fromIdentity (A : AbelianScheme S) :
    eqToHom (identity_toOver S).symm ≫ toOverHom (fromIdentity A) = η[A.toOver] := by
  rw [← one_hom (fromIdentity A)]
  exact Category.id_comp _

/-- The scheme morphism underlying `fromIdentity A` is the zero section of `A`, after transporting
its domain from `S`. -/
@[simp]
lemma toSchemeHom_fromIdentity (A : AbelianScheme S) :
    eqToHom (identity_toScheme S).symm ≫ toSchemeHom (fromIdentity A) = A.zeroSection := by
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
