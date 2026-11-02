/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Epimorphisms of sheaves with values in a concrete category

For a concrete category `A`, the functor `sheafCompose J (forget A) : Sheaf J A ⥤ Sheaf J (Type w)`
preserves and reflects epimorphisms (`CategoryTheory.Sheaf.epi_sheafCompose_forget_map_iff`):
in both categories the epimorphisms are the locally surjective morphisms, and local surjectivity of
an `A`-valued presheaf map is a condition on its underlying map of presheaves of types
(`CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget`).

This generalizes Mathlib's `PreservesEpimorphisms` instance for `LightCondensed.forget` in
`Mathlib.Condensed.Light.Epi` (Dagur Asgeirsson), with the same proof, from light condensed modules
to arbitrary sites. Reflection of epimorphisms needs no separate instance:
`sheafCompose J (forget A)` is faithful, so Mathlib's `Functor.reflectsEpimorphisms_of_faithful`
applies.
-/

public section

universe w

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type w}
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

end CategoryTheory.Sheaf
