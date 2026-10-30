/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Preadditive

/-!
# The projections of short complexes are additive

In a preadditive category, the three projections `ShortComplex.π₁`, `ShortComplex.π₂` and
`ShortComplex.π₃` from short complexes to their terms are additive functors, because morphisms of
short complexes are added componentwise. In particular each component of a finite sum of
morphisms of short complexes is the sum of the components (`CategoryTheory.Functor.map_sum`).
-/

public section

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Preadditive C]

instance additive_π₁ : (π₁ : ShortComplex C ⥤ C).Additive where
  map_add {_ _ f g} := add_τ₁ f g

instance additive_π₂ : (π₂ : ShortComplex C ⥤ C).Additive where
  map_add {_ _ f g} := add_τ₂ f g

instance additive_π₃ : (π₃ : ShortComplex C ⥤ C).Additive where
  map_add {_ _ f g} := add_τ₃ f g

end CategoryTheory.ShortComplex
