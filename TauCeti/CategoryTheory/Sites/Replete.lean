/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Limits
public import TauCeti.CategoryTheory.Limits.Replete

/-!
# Sheaves of modules on a replete topos

Let `J` be a Grothendieck topology and `A` a concrete category, such as a category of modules.
If the topos `Sheaf J (Type w)` is replete, then so is the category `Sheaf J A` of `A`-valued
sheaves (`TauCeti.isReplete_sheaf`). When `Sheaf J A` is abelian, it follows that countable
products of `A`-valued sheaves are exact (`TauCeti.countableAB4Star_sheaf`): on a replete topos,
countable products of abelian sheaves and of sheaves of modules satisfy Mathlib's
`CountableAB4Star`.

The transfer uses the functor `sheafCompose J (forget A) : Sheaf J A ⥤ Sheaf J (Type w)`, which
* preserves the limits that `forget A` preserves
  (`CategoryTheory.Sheaf.preservesLimitsOfShape_sheafCompose`), since limits of sheaves are
  computed on presheaves, and
* preserves and reflects epimorphisms (`CategoryTheory.Sheaf.epi_sheafCompose_forget_map_iff`),
  since in both categories the epimorphisms are the locally surjective morphisms and local
  surjectivity of an `A`-valued presheaf map is a condition on its underlying map of presheaves
  of types (`CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget`). This generalizes
  Mathlib's `PreservesEpimorphisms` and `ReflectsEpimorphisms` instances for
  `LightCondensed.forget`, with the same proof, from light condensed modules to arbitrary sites.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  Proposition 3.1.9.
-/

public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- If `F` preserves limits of shape `K`, then so does the induced functor on sheaves, since limits
of sheaves are computed on the underlying presheaves. -/
instance preservesLimitsOfShape_sheafCompose {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) [J.HasSheafCompose F] (K : Type*) [Category* K] [HasLimitsOfShape K A]
    [PreservesLimitsOfShape K F] :
    PreservesLimitsOfShape K (sheafCompose J F) := by
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J B) :=
    inferInstanceAs
      (PreservesLimitsOfShape K (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj F))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J B)

variable {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [J.HasSheafCompose (forget A)] [HasSheafify J (Type w)] [HasSheafify J A]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]
  [J.WEqualsLocallyBijective A] [Balanced (Sheaf J A)]

/-- A morphism of `A`-valued sheaves is an epimorphism if and only if its underlying morphism of
sheaves of types is: both conditions say that the morphism is locally surjective. -/
theorem epi_sheafCompose_forget_map_iff {F G : Sheaf J A} (φ : F ⟶ G) :
    Epi ((sheafCompose J (forget A)).map φ) ↔ Epi φ := by
  rw [← isLocallySurjective_iff_epi, ← isLocallySurjective_iff_epi']
  exact (Presheaf.isLocallySurjective_iff_whisker_forget J φ.hom).symm

instance : (sheafCompose J (forget A)).PreservesEpimorphisms :=
  ⟨fun φ _ ↦ (epi_sheafCompose_forget_map_iff J φ).2 inferInstance⟩

instance : (sheafCompose J (forget A)).ReflectsEpimorphisms :=
  ⟨fun φ h ↦ (epi_sheafCompose_forget_map_iff J φ).1 h⟩

end CategoryTheory.Sheaf

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
