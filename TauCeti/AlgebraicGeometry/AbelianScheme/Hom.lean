/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Basic

/-!
# Scheme-level projections, isomorphisms, Hom groups, and zero object of abelian schemes

This file extends `TauCeti.AlgebraicGeometry.AbelianScheme.Basic` with:

* `AbelianScheme.toSchemeFunctor` (faithful) and `AbelianScheme.toSchemeHom`: the forgetful functor
  to `Scheme` and the underlying scheme morphism of a homomorphism;
* `AbelianScheme.isoMk`: constructing isomorphisms of abelian schemes from monoid-homomorphism
  isomorphisms in `Over S` via `Grp.mkIso'` and `fullyFaithfulInducedFunctor.preimageIso`;
* `AbelianScheme.instCommGroup`, `AbelianScheme.homMulEquiv`, and `AbelianScheme.toOverHom_one`,
  `toOverHom_mul`, `toOverHom_inv`, `toOverHom_div`: when the target has a commutative group law
  (`[IsCommMonObj B.toOver]`), `A ⟶ B` is a commutative group under the pointwise operations;
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

/-- Forgetting a homomorphism of abelian schemes to its underlying scheme morphism is faithful. -/
instance : (toSchemeFunctor (S := S)).Faithful :=
  inferInstanceAs (Functor.Faithful (toOverFunctor (S := S) ⋙ Over.forget S))

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

/-! ### Pointwise commutative group structure on homomorphisms -/

/-- When the target is commutative, homomorphisms of abelian schemes over `S` form a commutative
group under the pointwise group law, transported from morphisms of group objects in `Over S`. -/
scoped instance instCommGroup (A B : AbelianScheme S) [IsCommMonObj B.toOver] :
    CommGroup (A ⟶ B) :=
  (InducedCategory.homEquiv (F := fun X : AbelianScheme S ↦ Grp.mk X.toOver)).commGroup

/-- Identifying a homomorphism of abelian schemes into a commutative target with its underlying
homomorphism of group objects is a group isomorphism. -/
def homMulEquiv (A B : AbelianScheme S) [IsCommMonObj B.toOver] :
    (A ⟶ B) ≃* (Grp.mk A.toOver ⟶ Grp.mk B.toOver) where
  __ := InducedCategory.homEquiv (F := fun X : AbelianScheme S ↦ Grp.mk X.toOver)
  map_mul' := fun _ _ ↦
    (InducedCategory.homEquiv (F := fun X : AbelianScheme S ↦ Grp.mk X.toOver)).apply_symm_apply _

@[simp]
lemma homMulEquiv_apply {A B : AbelianScheme S} [IsCommMonObj B.toOver] (f : A ⟶ B) :
    homMulEquiv A B f = f.hom :=
  (rfl)

@[simp]
lemma toOverHom_one {A B : AbelianScheme S} [IsCommMonObj B.toOver] :
    toOverHom (1 : A ⟶ B) = 1 := by
  change (homMulEquiv A B 1).hom.hom = 1
  rw [map_one]
  simp only [Grp.Hom.hom_one, Mon.Hom.hom_one]

@[simp]
lemma toOverHom_mul {A B : AbelianScheme S} [IsCommMonObj B.toOver] (f g : A ⟶ B) :
    toOverHom (f * g) = toOverHom f * toOverHom g := by
  change (homMulEquiv A B (f * g)).hom.hom =
    (homMulEquiv A B f).hom.hom * (homMulEquiv A B g).hom.hom
  rw [map_mul]
  simp only [Grp.Hom.hom_mul, Mon.Hom.hom_mul]

@[simp]
lemma toOverHom_inv {A B : AbelianScheme S} [IsCommMonObj B.toOver] (f : A ⟶ B) :
    toOverHom f⁻¹ = (toOverHom f)⁻¹ := by
  change (homMulEquiv A B f⁻¹).hom.hom = (homMulEquiv A B f).hom.hom⁻¹
  rw [map_inv]
  simp only [Grp.Hom.hom_hom_inv]

@[simp]
lemma toOverHom_div {A B : AbelianScheme S} [IsCommMonObj B.toOver] (f g : A ⟶ B) :
    toOverHom (f / g) = toOverHom f / toOverHom g := by
  change (homMulEquiv A B (f / g)).hom.hom =
    (homMulEquiv A B f).hom.hom / (homMulEquiv A B g).hom.hom
  rw [map_div]
  simp only [Grp.Hom.hom_hom_div]

@[simp]
lemma toSchemeHom_one {A B : AbelianScheme S} [IsCommMonObj B.toOver] :
    toSchemeHom (1 : A ⟶ B) = A.toOver.hom ≫ B.zeroSection := by
  rw [toSchemeHom, toOverHom_one, CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left]

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
