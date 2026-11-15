/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of the constant diagram functor

For any indexing category `J` and preadditive target category `A`, addition of natural
transformations in `J ⥤ A` is pointwise, so the constant diagram functor
`CategoryTheory.Functor.const J : A ⥤ J ⥤ A` is additive (`CategoryTheory.Functor.additive_const`).
-/

public section

namespace CategoryTheory.Functor

/-- For a preadditive target category `A`, the constant diagram functor `A ⥤ J ⥤ A` is additive. -/
instance additive_const (J : Type*) [Category* J] {A : Type*} [Category* A] [Preadditive A] :
    (Functor.const J : A ⥤ J ⥤ A).Additive where

end CategoryTheory.Functor
