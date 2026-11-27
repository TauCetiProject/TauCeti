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
`w`-locally small category. The same holds when only the isomorphism classes of the source form a
`w`-small type, with no condition on its hom types: whiskering with `fromSkeleton` identifies
natural transformations between functors on `C` with natural transformations between their
restrictions to the skeleton of `C`, and these are determined by their components
(`TauCeti.locallySmall_functor_of_small_skeleton`). In particular this applies to a
`w`-essentially small source.

Automorphism groups in a `w`-locally small category are `w`-small (`TauCeti.small_aut`). Together,
a functor from a `w`-essentially small category to a `w`-locally small category has a `w`-small
automorphism group. This is how the automorphism group of a fibre functor of a Galois
category, which lives in a larger universe than its fibres, is seen to have a small model.
-/
public section

universe w v₁ v₂ u₁ u₂

namespace TauCeti

open CategoryTheory

/-- Functors from a category whose isomorphism classes form a `w`-small type to a `w`-locally
small category form a `w`-locally small category. -/
instance locallySmall_functor_of_small_skeleton {C : Type u₁} [Category.{v₁} C]
    [Small.{w} (Skeleton C)] {D : Type u₂} [Category.{v₂} D] [LocallySmall.{w} D] :
    LocallySmall.{w} (C ⥤ D) :=
  have : LocallySmall.{w} (Skeleton C ⥤ D) :=
    ⟨fun _ _ ↦ small_of_injective (f := NatTrans.app) fun _ _ ↦ NatTrans.ext⟩
  locallySmall_of_faithful (skeletonEquivalence C).congrLeft.inverse

end TauCeti
