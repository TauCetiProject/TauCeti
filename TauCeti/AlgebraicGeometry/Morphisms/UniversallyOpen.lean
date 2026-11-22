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
change along an extension of ground fields.
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
