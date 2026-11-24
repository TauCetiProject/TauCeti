/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Exactness properties of the pushforward along a continuous functor

Let `u : C ⥤ D` be a continuous functor from a site `(C, J)` to a site `(D, K)`. The pushforward
`u.sheafPushforwardContinuous A J K`, sending a sheaf `F` on `D` to `F ∘ u` on `C`, is additive
when `A` is preadditive, and preserves limits of any shape `I` that `A` has (in particular finite
limits and sequential limits), since limits of sheaves are computed on the underlying presheaves.

When `u` is moreover cocontinuous (`u.IsCocontinuous J K`), precomposition with `u.op` preserves
locally surjective morphisms (`CategoryTheory.Presheaf.isLocallySurjective_whisker`), so
`u.sheafPushforwardContinuous` preserves local surjectivity, and hence preserves epimorphisms of
`Type w`-valued sheaves when `K` admits sheafification (`[HasSheafify K (Type w)]`), and of
`A`-valued sheaves under `[J.HasSheafCompose (forget A)]` and the standard hypotheses on `(D, K)`
and `A` identifying epimorphisms in `Sheaf K A` with locally surjective morphisms.
-/

public section

universe w

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (u : C ⥤ D)
  (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K]

/-- The pushforward of sheaves along a continuous functor is additive. -/
instance [Preadditive A] : (u.sheafPushforwardContinuous A J K).Additive where
  map_add := rfl

/-- The pushforward of sheaves along a continuous functor preserves limits of any shape that `A`
has, since limits of sheaves are computed on the underlying presheaves. -/
instance preservesLimitsOfShape_sheafPushforwardContinuous {I : Type*} [Category* I]
    [HasLimitsOfShape I A] :
    PreservesLimitsOfShape I (u.sheafPushforwardContinuous A J K) := by
  have : PreservesLimitsOfShape I (u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A) :=
    preservesLimitsOfShape_of_natIso (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J A)

/-- The pushforward of sheaves along a continuous functor preserves finite limits, since limits
of sheaves are computed on the underlying presheaves. -/
instance [HasFiniteLimits A] : PreservesFiniteLimits (u.sheafPushforwardContinuous A J K) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- If `u : C ⥤ D` is both continuous and cocontinuous, then `u.sheafPushforwardContinuous A J K`
preserves locally surjective morphisms of sheaves. -/
instance isLocallySurjective_sheafPushforwardContinuous_map
    {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [u.IsCocontinuous J K] {F G : Sheaf K A} (φ : F ⟶ G)
    [Sheaf.IsLocallySurjective φ] :
    Sheaf.IsLocallySurjective ((u.sheafPushforwardContinuous A J K).map φ) := by
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff,
    ← Presheaf.isLocallySurjective_comp_iff J _
      ((u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).hom.app G),
    ← Functor.comp_map,
    (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).hom.naturality φ,
    Presheaf.comp_isLocallySurjective_iff, Functor.comp_map, whiskeringLeft_obj_map]
  have : Presheaf.IsLocallySurjective K ((sheafToPresheaf K A).map φ) :=
    (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff φ).2 ‹_›
  exact Presheaf.isLocallySurjective_whisker J K u ((sheafToPresheaf K A).map φ)

/-- If `u : C ⥤ D` is both continuous and cocontinuous and `K` admits sheafification of
`Type w`-valued presheaves, then `u.sheafPushforwardContinuous (Type w) J K` preserves
epimorphisms. -/
instance preservesEpimorphisms_sheafPushforwardContinuous_types
    [u.IsCocontinuous J K] [HasSheafify K (Type w)] :
    (u.sheafPushforwardContinuous (Type w) J K).PreservesEpimorphisms where
  preserves φ _ := by
    have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi φ).2 ‹_›
    infer_instance

/-- If `u : C ⥤ D` is both continuous and cocontinuous, then `u.sheafPushforwardContinuous A J K`
preserves epimorphisms of `A`-valued sheaves under `[J.HasSheafCompose (forget A)]` and the
standard hypotheses on `(D, K)` and `A` identifying epimorphisms in `Sheaf K A` with locally
surjective morphisms. -/
instance preservesEpimorphisms_sheafPushforwardContinuous
    {FA : A → A → Type*} {CA : A → Type w} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory.{w} A FA] [u.IsCocontinuous J K]
    [HasSheafify K A] [K.HasSheafCompose (forget A)] [J.HasSheafCompose (forget A)]
    [K.WEqualsLocallyBijective A]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [Balanced (Sheaf K A)] :
    (u.sheafPushforwardContinuous A J K).PreservesEpimorphisms where
  preserves φ _ := by
    have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 ‹_›
    infer_instance

end CategoryTheory.Functor
