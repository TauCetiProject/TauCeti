/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.Groupoid

/-!
# Codiscrete categories are groupoids

The unique morphism in the reverse direction inverts every morphism of a codiscrete
category. This lets the native pair category be used wherever a groupoid is required,
without replacing its category structure.
-/

public section

namespace CategoryTheory.Codiscrete

/-- Every arrow in a codiscrete category is invertible. -/
instance isGroupoid (X : Type*) : IsGroupoid (Codiscrete X) where
  all_isIso _ := ⟨⟨default, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

end CategoryTheory.Codiscrete
