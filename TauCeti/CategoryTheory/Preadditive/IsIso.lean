/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Isomorphisms in preadditive categories

In a preadditive category the negative `-f` of an isomorphism `f` is an isomorphism, with
inverse `-inv f` (`CategoryTheory.Preadditive.isIso_neg`).
-/

public section

namespace CategoryTheory.Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

/-- The negative of an isomorphism in a preadditive category is an isomorphism. -/
instance isIso_neg {P Q : C} (f : P ⟶ Q) [IsIso f] : IsIso (-f) :=
  ⟨-inv f, by simp, by simp⟩

end CategoryTheory.Preadditive
