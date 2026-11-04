/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Replete
public import TauCeti.CategoryTheory.Sites.EpiMono
public import TauCeti.CategoryTheory.Sites.Limits

/-!
# Sheaves with values in a concrete category on a replete topos

Let `J` be a Grothendieck topology and `A` a concrete category, such as a category of modules,
whose forgetful functor preserves sequential limits. Under the standard assumptions on `A` that
identify epimorphisms of `A`-valued sheaves with locally surjective morphisms, if the topos
`Sheaf J (Type w)` is replete, then so is the category `Sheaf J A` of `A`-valued sheaves
(`TauCeti.isReplete_sheaf`). When `Sheaf J A` is abelian, it follows that countable products of
`A`-valued sheaves are exact (`TauCeti.countableAB4Star_sheaf`): on a replete topos, countable
products of abelian sheaves and of sheaves of modules satisfy Mathlib's `CountableAB4Star`.

The transfer uses the functor `sheafCompose J (forget A) : Sheaf J A ⥤ Sheaf J (Type w)`, which
preserves the limits that `forget A` preserves
(`CategoryTheory.Sheaf.preservesLimitsOfShape_sheafCompose`) and preserves and reflects
epimorphisms (`CategoryTheory.Sheaf.epi_sheafCompose_forget_map_iff`).

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  Proposition 3.1.9.
-/

public section

universe w v u

open CategoryTheory Limits

namespace TauCeti

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [IsReplete (Sheaf J (Type w))]
  [HasSheafify J (Type w)]

/-- **Sheaves on a replete topos form a replete category.** If the topos `Sheaf J (Type w)` is
replete, then so is the category of sheaves with values in a concrete category `A` whose forgetful
functor preserves sequential limits. -/
theorem isReplete_sheaf (A : Type*) [Category* A] {FA : A → A → Type*} {CA : A → Type w}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
    [J.HasSheafCompose (forget A)] [HasSheafify J A]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [J.WEqualsLocallyBijective A]
    [Balanced (Sheaf J A)] [HasLimitsOfShape ℕᵒᵖ A] [PreservesLimitsOfShape ℕᵒᵖ (forget A)] :
    IsReplete (Sheaf J A) :=
  IsReplete.of_reflectsEpimorphisms (sheafCompose J (forget A))

/-- **Countable products of abelian sheaves on a replete topos are exact** (Bhatt–Scholze,
Proposition 3.1.9). If the topos `Sheaf J (Type w)` is replete, then the abelian category of
sheaves with values in a concrete category `A` whose forgetful functor preserves sequential limits,
such as a category of modules, satisfies `CountableAB4Star`. -/
theorem countableAB4Star_sheaf (A : Type*) [Category* A] {FA : A → A → Type*} {CA : A → Type w}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
    [J.HasSheafCompose (forget A)] [HasSheafify J A]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [J.WEqualsLocallyBijective A]
    [HasLimitsOfShape ℕᵒᵖ A] [PreservesLimitsOfShape ℕᵒᵖ (forget A)] [Abelian (Sheaf J A)]
    [HasCountableProducts (Sheaf J A)] :
    CountableAB4Star (Sheaf J A) :=
  have := isReplete_sheaf J A
  inferInstance

end TauCeti
