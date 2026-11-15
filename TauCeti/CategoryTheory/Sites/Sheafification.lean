/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Additivity of sheafification for preadditive coefficients

Whenever `A` is a preadditive category and a site `(C, J)` admits weak sheafification with values in
`A`, sheafification `presheafToSheaf J A` is a left adjoint between preadditive categories and is
therefore additive (`CategoryTheory.additive_presheafToSheaf`), generalizing the abelian coefficient
instance in `Mathlib.CategoryTheory.Sites.Abelian`.
-/

public section

namespace CategoryTheory

/-- Sheafification `presheafToSheaf J A` is additive whenever `A` is preadditive and `(C, J)` admits
weak sheafification in `A`, as a left adjoint between preadditive categories. -/
noncomputable instance additive_presheafToSheaf {C : Type*} [Category* C]
    (J : GrothendieckTopology C) (A : Type*) [Category* A] [Preadditive A] [HasWeakSheafify J A] :
    (presheafToSheaf J A).Additive :=
  (sheafificationAdjunction J A).left_adjoint_additive

end CategoryTheory
