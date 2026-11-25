/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Topological properties of universally open morphisms of schemes

Every universally open morphism of schemes is an open map
(`AlgebraicGeometry.Scheme.Hom.isOpenMap`). When it is also surjective, its underlying map of
topological spaces is an open quotient map (`AlgebraicGeometry.Scheme.Hom.isOpenQuotientMap`).
Since both surjectivity and universal openness are stable under base change, this applies in
particular to any pullback projection along a surjective universally open morphism, such as base
change along an extension of ground fields. Without surjectivity, such a projection still pulls
dense opens back to dense opens
(`AlgebraicGeometry.Scheme.dense_preimage_of_isPullback_of_universallyOpen`).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A surjective universally open morphism of schemes is an open quotient map on underlying
topological spaces. -/
theorem isOpenQuotientMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [UniversallyOpen f] :
    IsOpenQuotientMap f :=
  ⟨f.surjective, f.continuous, f.isOpenMap⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

universe u

/-- The preimage of a dense open under the base change of a universally open morphism is dense. -/
theorem dense_preimage_of_isPullback_of_universallyOpen {X X' S S' : Scheme.{u}} {πX : X' ⟶ X}
    {sX' : X' ⟶ S'} {sX : X ⟶ S} {p : S' ⟶ S} (hX : IsPullback πX sX' sX p) [UniversallyOpen p]
    {U : X.Opens} (hU : Dense (U : Set X)) : Dense (πX ⁻¹ᵁ U : Set X') := by
  have : UniversallyOpen πX := MorphismProperty.of_isPullback hX.flip inferInstance
  exact hU.preimage πX.isOpenMap

end AlgebraicGeometry.Scheme
