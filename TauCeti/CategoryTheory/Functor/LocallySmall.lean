/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Local smallness of functor categories with essentially small source

Mathlib shows that functors from a small category to a `w`-locally small category form a
`w`-locally small category. The same holds when the source is only essentially small: whiskering
with the equivalence `equivSmallModel` identifies natural transformations between functors on
`C` with natural transformations between their restrictions to the small model of `C`
(`CategoryTheory.locallySmall_functor_of_essentiallySmall`).

Automorphism groups in a `w`-locally small category are `w`-small (`TauCeti.small_aut`). Together,
a functor from a `w`-essentially small category to a `w`-locally small category has a `w`-small
automorphism group. This is how the automorphism group of a fibre functor of a Galois
category, which lives in a larger universe than its fibres, is seen to have a small model.
-/

public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- Functors from a `w`-essentially small category to a `w`-locally small category form a
`w`-locally small category. -/
instance locallySmall_functor_of_essentiallySmall {C : Type u₁} [Category.{v₁} C]
    [EssentiallySmall.{w} C] {D : Type u₂} [Category.{v₂} D] [LocallySmall.{w} D] :
    LocallySmall.{w} (C ⥤ D) :=
  locallySmall_of_faithful (equivSmallModel.{w} C).congrLeft.functor

end CategoryTheory
