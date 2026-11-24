/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Replete
public import TauCeti.CategoryTheory.Sites.Continuous
public import TauCeti.CategoryTheory.Sites.CoversTop
public import TauCeti.CategoryTheory.Sites.EpiMono
public import TauCeti.CategoryTheory.Sites.Limits

/-!
# Repleteness of sheaf categories and descent along site covers

Let `J` be a Grothendieck topology on `C`. This file connects repleteness of sheaf categories with
coefficient change and with covers of the base site:

* `TauCeti.isReplete_sheaf` and `TauCeti.countableAB4Star_sheaf`: if the topos `Sheaf J (Type w)`
  is replete and `A` is a concrete category whose forgetful functor preserves sequential limits
  (under the standard hypotheses identifying epimorphisms of `A`-valued sheaves with locally
  surjective morphisms), then `Sheaf J A` is replete and (when abelian) satisfies
  `CountableAB4Star`.
* `TauCeti.isReplete_sheaf_types_of_coversTop` and `TauCeti.isReplete_sheaf_of_coversTop`
  (Bhatt–Scholze, Lemma 3.1.3): if `X : I → C` covers the terminal object for `J` and every slice
  sheaf category `Sheaf (J.over (X i)) (Type w)` (when `J` admits sheafification of
  `Type w`-valued presheaves) or `Sheaf (J.over (X i)) A` (when `A` is a concrete category with
  sequential limits satisfying `[∀ i, (J.over (X i)).HasSheafCompose (forget A)]` and the standard
  hypotheses identifying epimorphisms in `Sheaf J A` with locally surjective morphisms) is replete,
  then `Sheaf J (Type w)` (respectively `Sheaf J A`) is replete, by descending along the jointly
  faithful family of restriction functors `J.overPullback`.

Because `TauCeti.CategoryTheory.Sites.EpiMono` registers
`(MorphismProperty.epimorphisms (Sheaf J (Type w))).IsStableUnderBaseChange`, categorical slice
descent (`TauCeti.IsReplete.of_over_epi` and `TauCeti.isReplete_over_iff` for `Over F` inside
`Sheaf J (Type w)`) also applies directly without extra base-change hypotheses.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  Lemma 3.1.3 and Proposition 3.1.9.
-/

public section

universe w v u

open CategoryTheory Limits

namespace TauCeti

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Sheaves on a replete topos form a replete category.** If the topos `Sheaf J (Type w)` is
replete, then so is the category of sheaves with values in a concrete category `A` whose forgetful
functor preserves sequential limits. -/
theorem isReplete_sheaf [IsReplete (Sheaf J (Type w))] (A : Type*) [Category* A]
    {FA : A → A → Type*} {CA : A → Type w} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory.{w} A FA] [J.HasSheafCompose (forget A)] [HasSheafify J A]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [J.WEqualsLocallyBijective A]
    [Balanced (Sheaf J A)] [HasLimitsOfShape ℕᵒᵖ A] [PreservesLimitsOfShape ℕᵒᵖ (forget A)] :
    IsReplete (Sheaf J A) :=
  IsReplete.of_reflectsEpimorphisms (sheafCompose J (forget A))

/-- **Countable products of abelian sheaves on a replete topos are exact** (Bhatt–Scholze,
Proposition 3.1.9). If the topos `Sheaf J (Type w)` is replete, then the abelian category of
sheaves with values in a concrete category `A` whose forgetful functor preserves sequential limits,
such as a category of modules, satisfies `CountableAB4Star`. -/
theorem countableAB4Star_sheaf [IsReplete (Sheaf J (Type w))] (A : Type*) [Category* A]
    {FA : A → A → Type*} {CA : A → Type w} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory.{w} A FA] [J.HasSheafCompose (forget A)] [HasSheafify J A]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [J.WEqualsLocallyBijective A]
    [HasLimitsOfShape ℕᵒᵖ A] [PreservesLimitsOfShape ℕᵒᵖ (forget A)] [Abelian (Sheaf J A)]
    [HasCountableProducts (Sheaf J A)] :
    CountableAB4Star (Sheaf J A) :=
  have := isReplete_sheaf J A
  inferInstance

variable {J} in
/-- **Repleteness of a topos is local on a site cover** (Bhatt–Scholze, Lemma 3.1.3). If `J`
admits sheafification of `Type w`-valued presheaves (`[HasSheafify J (Type w)]`), `X : I → C`
covers the terminal object for `J`, and every slice topos `Sheaf (J.over (X i)) (Type w)` is
replete, then `Sheaf J (Type w)` is replete. -/
theorem isReplete_sheaf_types_of_coversTop {I : Type*} {X : I → C} (hX : J.CoversTop X)
    [HasSheafify J (Type w)] [∀ i, IsReplete (Sheaf (J.over (X i)) (Type w))] :
    IsReplete (Sheaf J (Type w)) :=
  IsReplete.of_jointlyReflectEpimorphisms (hX.jointlyReflectEpimorphisms_overPullback (Type w))

variable {J} in
/-- **Repleteness of concrete-category-valued sheaves is local on a site cover.** If `X : I → C`
covers the terminal object for `J`, `A` is a concrete category with sequential limits satisfying
`[∀ i, (J.over (X i)).HasSheafCompose (forget A)]` together with the standard hypotheses
identifying epimorphisms in `Sheaf J A` with locally surjective morphisms (`[HasSheafify J A]`,
`[J.HasSheafCompose (forget A)]`, `[J.WEqualsLocallyBijective A]`,
`[ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]`, and `[Balanced (Sheaf J A)]`),
and every slice sheaf category `Sheaf (J.over (X i)) A` is replete, then `Sheaf J A` is replete. -/
theorem isReplete_sheaf_of_coversTop {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (A : Type*) [Category* A] {FA : A → A → Type*} {CA : A → Type w}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
    [HasLimitsOfShape ℕᵒᵖ A] [HasSheafify J A] [J.HasSheafCompose (forget A)]
    [∀ i, (J.over (X i)).HasSheafCompose (forget A)] [J.WEqualsLocallyBijective A]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [Balanced (Sheaf J A)]
    [∀ i, IsReplete (Sheaf (J.over (X i)) A)] :
    IsReplete (Sheaf J A) :=
  IsReplete.of_jointlyReflectEpimorphisms (hX.jointlyReflectEpimorphisms_overPullback A)

end TauCeti
