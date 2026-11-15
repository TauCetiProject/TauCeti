/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.EpiMono
public import TauCeti.CategoryTheory.Sites.Limits

/-!
# Epimorphisms and monomorphisms of sheaves: preservation and base-change stability

For a concrete category `A`, the functor `sheafCompose J (forget A) : Sheaf J A ⥤ Sheaf J (Type w)`
preserves epimorphisms (`CategoryTheory.Sheaf.preservesEpimorphisms_sheafCompose_forget`) and
reflects them, so a morphism of `A`-valued sheaves is an epimorphism if and only if its underlying
morphism of sheaves of types is (`CategoryTheory.Functor.epi_map_iff_epi`): in both categories the
epimorphisms are the locally surjective morphisms, and local surjectivity of an `A`-valued presheaf
map is a condition on its underlying map of presheaves of types
(`CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget`).

This generalizes Mathlib's `PreservesEpimorphisms` instance for `LightCondensed.forget` in
`Mathlib.Condensed.Light.Epi` (Dagur Asgeirsson), with the same proof, from light condensed modules
to arbitrary sites. Reflection of epimorphisms needs no separate instance:
`sheafCompose J (forget A)` is faithful, so Mathlib's `Functor.reflectsEpimorphisms_of_faithful`
applies.

This file also proves that local surjectivity of presheaves and sheaves is stable under pullback
(`CategoryTheory.Presheaf.isLocallySurjective_of_isPullback`,
`CategoryTheory.Sheaf.isStableUnderBaseChange_locallySurjective_types`,
`CategoryTheory.Sheaf.isStableUnderBaseChange_locallySurjective`), and consequently that
epimorphisms in `Sheaf J (Type w)` and in `Sheaf J A` (when `forget A` preserves pullbacks) satisfy
`MorphismProperty.IsStableUnderBaseChange`
(`CategoryTheory.Sheaf.isStableUnderBaseChange_epimorphisms_types`,
`CategoryTheory.Sheaf.isStableUnderBaseChange_epimorphisms`). Together with
`TauCeti.IsReplete.of_over_epi`, `TauCeti.IsReplete.epi_limMap`, and
`TauCeti.IsReplete.epi_pi_map`, this makes base-change stability of epimorphisms automatic on
sheaf topoi.

Finally, a monomorphism of sheaves with values in a concrete category whose forgetful functor
preserves pullbacks is injective on the sections over every object
(`CategoryTheory.Sheaf.injective_app_of_mono`).
-/

public section

universe w

open CategoryTheory Limits

namespace CategoryTheory.Presheaf

/-- Local surjectivity of morphisms of presheaves of types is stable under pullback: in any
pullback square `IsPullback f' g' g f` in `Cᵒᵖ ⥤ Type w`, if `g` is locally surjective for `J`,
then so is `g'`. -/
theorem isLocallySurjective_of_isPullback {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {P X Y Z : Cᵒᵖ ⥤ Type w} {f' : P ⟶ Y} {g' : P ⟶ X} {g : Y ⟶ Z} {f : X ⟶ Z}
    (sq : IsPullback f' g' g f) [IsLocallySurjective J g] :
    IsLocallySurjective J g' where
  imageSieve_mem {U} x := by
    refine J.superset_covering ?_ (imageSieve_mem J g (f.app (Opposite.op U) x))
    rintro V i ⟨y, hy⟩
    have hx : g.app (Opposite.op V) y = f.app (Opposite.op V) (X.map i.op x) :=
      hy.trans (NatTrans.naturality_apply f i.op x).symm
    obtain ⟨p, -, hp⟩ :=
      Types.exists_of_isPullback (sq.map ((evaluation Cᵒᵖ (Type w)).obj (Opposite.op V)))
        y (X.map i.op x) hx
    exact ⟨p, hp⟩

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

section ConcreteEpi

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [HasSheafify J A] [J.HasSheafCompose (forget A)] [J.WEqualsLocallyBijective A]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [Balanced (Sheaf J A)]

/-- An epimorphism of sheaves with values in a concrete category is an epimorphism of the
underlying sheaves of sets: both are the locally surjective morphisms. -/
instance preservesEpimorphisms_sheafCompose_forget :
    (sheafCompose J (forget A)).PreservesEpimorphisms where
  preserves φ _ := by
    have : IsLocallySurjective φ := (isLocallySurjective_iff_epi' (φ := φ)).2 ‹_›
    infer_instance

end ConcreteEpi

section BaseChange

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)

variable {J} in
/-- Local surjectivity of morphisms of sheaves of types is stable under pullback. -/
theorem isLocallySurjective_of_isPullback_types {P X Y Z : Sheaf J (Type w)}
    {f' : P ⟶ Y} {g' : P ⟶ X} {g : Y ⟶ Z} {f : X ⟶ Z}
    (sq : IsPullback f' g' g f) [IsLocallySurjective g] :
    IsLocallySurjective g' := by
  have : Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map g) := by
    rwa [isLocallySurjective_sheafToPresheaf_map_iff]
  rw [← isLocallySurjective_sheafToPresheaf_map_iff]
  exact Presheaf.isLocallySurjective_of_isPullback J (sq.map (sheafToPresheaf J (Type w)))

/-- Locally surjective morphisms of sheaves of types are stable under base change. -/
instance isStableUnderBaseChange_locallySurjective_types :
    (locallySurjective J (Type w)).IsStableUnderBaseChange where
  of_isPullback sq hg :=
    have : IsLocallySurjective _ := hg
    isLocallySurjective_of_isPullback_types sq

/-- Epimorphisms in a Grothendieck topos `Sheaf J (Type w)` are stable under base change. -/
instance isStableUnderBaseChange_epimorphisms_types [HasSheafify J (Type w)] :
    (MorphismProperty.epimorphisms (Sheaf J (Type w))).IsStableUnderBaseChange where
  of_isPullback sq hg := by
    rw [MorphismProperty.epimorphisms.iff] at hg ⊢
    have : IsLocallySurjective _ := (isLocallySurjective_iff_epi _).2 hg
    have := isLocallySurjective_of_isPullback_types sq
    infer_instance

/-- Locally surjective morphisms of sheaves valued in a concrete category whose forgetful functor
preserves pullbacks are stable under base change. -/
instance isStableUnderBaseChange_locallySurjective {A : Type*} [Category* A]
    {FA : A → A → Type*} {CA : A → Type w} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory.{w} A FA] [HasPullbacks A]
    [PreservesLimitsOfShape WalkingCospan (forget A)] [J.HasSheafCompose (forget A)] :
    (locallySurjective J A).IsStableUnderBaseChange where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    have : IsLocallySurjective g := hg
    exact (Presheaf.isLocallySurjective_iff_whisker_forget J g'.hom).2
      (isLocallySurjective_of_isPullback_types (sq.map (sheafCompose J (forget A))))

/-- Epimorphisms of sheaves valued in a concrete category whose forgetful functor preserves
pullbacks (and under the standard hypotheses identifying epimorphisms with locally surjective
morphisms) are stable under base change. -/
instance isStableUnderBaseChange_epimorphisms {A : Type*} [Category* A]
    {FA : A → A → Type*} {CA : A → Type w} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory.{w} A FA] [HasPullbacks A]
    [PreservesLimitsOfShape WalkingCospan (forget A)] [HasSheafify J A]
    [J.HasSheafCompose (forget A)] [J.WEqualsLocallyBijective A]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [Balanced (Sheaf J A)] :
    (MorphismProperty.epimorphisms (Sheaf J A)).IsStableUnderBaseChange where
  of_isPullback sq hg := by
    rw [MorphismProperty.epimorphisms.iff] at hg ⊢
    have : (locallySurjective J A) _ := (isLocallySurjective_iff_epi' (φ := _)).2 hg
    have : IsLocallySurjective _ :=
      MorphismProperty.of_isPullback (P := locallySurjective J A) sq this
    infer_instance

end BaseChange

section Mono

variable {D : Type*} [Category D] {J : GrothendieckTopology D}
  {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
  [HasPullbacks C]
  [PreservesLimitsOfShape WalkingCospan (forget C)] {F G : Sheaf J C}

/-- A monomorphism of sheaves of a concrete category, whose forgetful functor preserves pullbacks,
is injective on sections over every object. -/
theorem injective_app_of_mono (f : F ⟶ G) [Mono f] (W : Dᵒᵖ) :
    Function.Injective (f.hom.app W) := by
  have : Mono f.hom := (sheafToPresheaf J C).map_mono f
  have : Mono (f.hom.app W) := inferInstance
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (f.hom.app W)

end Mono

end CategoryTheory.Sheaf
