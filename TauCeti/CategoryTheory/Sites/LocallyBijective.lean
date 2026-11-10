/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Products of locally injective and locally surjective morphisms

For presheaves of types on a site, the cartesian product `f ⊗ₘ g` of two locally injective
(resp. locally surjective) morphisms is locally injective (resp. locally surjective): two
sections of a product presheaf agree on the intersection of the sieves on which their two
components agree, and a section of a product lifts on the intersection of the sieves on which
its two components lift.

Through Mathlib's `CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective`, such products
are inverted by sheafification; this is how the action of a sheaf of groups on a presheaf is
extended to its sheafification.

The file also records that sections of a sheaf of sets are determined by their restrictions
along the sieve on which a given section lifts through a locally surjective morphism
(`CategoryTheory.Presheaf.ext_of_isLocallySurjective`), and that at an object whose only
covering sieve is the maximal one, such as the terminal object of a local site, a locally
injective (resp. locally surjective) morphism is injective (resp. surjective) on sections.
-/

public section

open CategoryTheory MonoidalCategory Opposite

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ Type w} (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂)

/-- The product of two locally injective morphisms of presheaves of types is locally
injective. -/
instance isLocallyInjective_tensorHom [IsLocallyInjective J f] [IsLocallyInjective J g] :
    IsLocallyInjective J (f ⊗ₘ g) where
  equalizerSieve_mem {X} x y h := by
    have h₁ : f.app X x.1 = f.app X y.1 := congrArg _root_.Prod.fst h
    have h₂ : g.app X x.2 = g.app X y.2 := congrArg _root_.Prod.snd h
    refine J.superset_covering ?_ (J.intersection_covering
      (equalizerSieve_mem J f x.1 y.1 h₁) (equalizerSieve_mem J g x.2 y.2 h₂))
    rintro V a ⟨h₁, h₂⟩
    exact Prod.ext h₁ h₂

/-- The product of two locally surjective morphisms of presheaves of types is locally
surjective. -/
instance isLocallySurjective_tensorHom [IsLocallySurjective J f] [IsLocallySurjective J g] :
    IsLocallySurjective J (f ⊗ₘ g) where
  imageSieve_mem y := by
    refine J.superset_covering ?_ (J.intersection_covering
      (imageSieve_mem J f (U := Opposite.op _) y.1) (imageSieve_mem J g (U := Opposite.op _) y.2))
    rintro V a ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    exact ⟨(x₁, x₂), Prod.ext hx₁ hx₂⟩

/-- Two sections `a`, `b` of a sheaf of sets over `U` agree as soon as they agree after
restriction along every `f : V ⟶ U` along which a given section `q` of `Q` over `U` lifts
through a locally surjective morphism `η : F ⟶ Q`. -/
lemma ext_of_isLocallySurjective {F Q : Cᵒᵖ ⥤ Type w} (η : F ⟶ Q)
    [IsLocallySurjective J η] {Z : Sheaf J (Type w)} {U : Cᵒᵖ} (q : Q.obj U)
    {a b : Z.obj.obj U}
    (h : ∀ ⦃V : C⦄ (f : V ⟶ U.unop) (x : F.obj (op V)), η.app _ x = Q.map f.op q →
      Z.obj.map f.op a = Z.obj.map f.op b) :
    a = b :=
  (((isSheaf_iff_isSheaf_of_type J _).1 Z.property).isSeparated _
    (imageSieve_mem J η q)).ext fun _ f ⟨x, hx⟩ ↦ h f x hx

/-- At an object whose only covering sieve is the maximal sieve, a locally surjective morphism
of presheaves of types is surjective on sections. -/
lemma surjective_app_of_isLocallySurjective {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G)
    [IsLocallySurjective J η] {X : C} (hX : ∀ S ∈ J X, S = ⊤) :
    Function.Surjective (η.app (op X)) := by
  intro s
  have hs : imageSieve η s (𝟙 X) := by
    rw [hX _ (imageSieve_mem J η s)]
    trivial
  obtain ⟨t, ht⟩ := hs
  exact ⟨t, by simpa using ht⟩

/-- At an object whose only covering sieve is the maximal sieve, a locally injective morphism
of presheaves of types is injective on sections. -/
lemma injective_app_of_isLocallyInjective {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G)
    [IsLocallyInjective J η] {X : C} (hX : ∀ S ∈ J X, S = ⊤) :
    Function.Injective (η.app (op X)) := fun x y hxy ↦
  (equalizerSieve_eq_top_iff (F := F) x y).mp (hX _ (equalizerSieve_mem J η x y hxy))

end CategoryTheory.Presheaf
