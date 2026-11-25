/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import TauCeti.AlgebraicGeometry.Sites.Etale.Over.Basic

/-!
# Sheafification on a localized small étale site

For `U : S.Etale`, the localized site `(Over U, (smallEtaleTopology S).over U)` is identified with
the small étale site of `U.left` through `AlgebraicGeometry.Scheme.Etale.iteratedSliceEquiv`
(`AlgebraicGeometry.Scheme.Etale.isDenseSubsite_iteratedSliceEquiv_inverse`). Transporting
Mathlib's results for small étale sites along this identification, sheaves with values in a
concrete category `A` with suitable limits and colimits (for instance `ModuleCat Λ`) admit a
sheafification on the localized site, and a morphism of presheaves becomes an isomorphism after
sheafification exactly when it is locally bijective.

## Main declarations

* `AlgebraicGeometry.Scheme.Etale.hasSheafify_over`: sheafification on `Over U`.
* `AlgebraicGeometry.Scheme.Etale.wEqualsLocallyBijective_over`: on `Over U`, the morphisms
  inverted by sheafification are the locally bijective ones.
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} (U : S.Etale) {A : Type*} [Category.{u} A]

variable {FA : A → A → Type*} {CA : A → Type u} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory.{u} A FA] [PreservesLimits (CategoryTheory.forget A)] [HasColimits A]
  [HasLimits A] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- Sheaves on the localized small étale site `Over U` admit a sheafification. -/
instance hasSheafify_over : HasSheafify ((smallEtaleTopology S).over U) A :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (smallEtaleTopology U.left) ((smallEtaleTopology S).over U) U.iteratedSliceEquiv.inverse

/-- On the localized small étale site `Over U`, a morphism of presheaves becomes an isomorphism
after sheafification exactly when it is locally injective and locally surjective. -/
instance wEqualsLocallyBijective_over :
    ((smallEtaleTopology S).over U).WEqualsLocallyBijective A :=
  .transport _ (smallEtaleTopology U.left) U.iteratedSliceEquiv.inverse
    (Functor.IsDenseSubsite.coverPreserving (smallEtaleTopology U.left) _ _)

end AlgebraicGeometry.Scheme.Etale
