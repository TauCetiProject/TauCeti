/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Exactness properties of the pushforward along a continuous functor

Let `u : C ⥤ D` be a continuous functor from a site `(C, J)` to a site `(D, K)`. The pushforward
`u.sheafPushforwardContinuous A J K`, sending a sheaf `F` on `D` to `F ∘ u` on `C`, is additive
when `A` is preadditive, and preserves finite limits when `A` has them, since limits of sheaves are
computed on the underlying presheaves. In particular it is left exact for abelian `A`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (u : C ⥤ D)
  (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K]

/-- The pushforward of sheaves along a continuous functor is additive. -/
instance [Preadditive A] : (u.sheafPushforwardContinuous A J K).Additive where
  map_add := rfl

/-- The pushforward of sheaves along a continuous functor preserves finite limits, since limits
of sheaves are computed on the underlying presheaves. -/
instance [HasFiniteLimits A] : PreservesFiniteLimits (u.sheafPushforwardContinuous A J K) := by
  have : PreservesFiniteLimits (u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A) :=
    inferInstanceAs
      (PreservesFiniteLimits (sheafToPresheaf K A ⋙ (whiskeringLeft _ _ _).obj u.op))
  exact ⟨fun _ _ _ ↦ preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J A)⟩

end CategoryTheory.Functor
