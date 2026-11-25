/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# The category of finite-type schemes over a base

A finite-type scheme over a base is a scheme with a quasi-compact morphism to the base that is
locally of finite type. The category inherits all morphisms over the base.
-/

public section

universe u

open CategoryTheory

namespace TauCeti

open AlgebraicGeometry

/-- Locally finite-type, quasi-compact morphisms remain so after base change. This instance
lets the morphism-property pullback functor act on the finite-type over-category. -/
-- The generic intersection instance needs explicit property arguments at this boundary.
instance : MorphismProperty.IsStableUnderBaseChange
    (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
  .inf (P := @LocallyOfFiniteType) (Q := @QuasiCompact)

/-- Composites of locally finite-type, quasi-compact morphisms remain locally of finite type
and quasi-compact. -/
instance : MorphismProperty.IsStableUnderComposition
    (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
  .inf (P := @LocallyOfFiniteType) (Q := @QuasiCompact)

end TauCeti

namespace AlgebraicGeometry.Scheme

/-- The full subcategory of schemes over the base whose structure morphisms are of finite type. -/
protected abbrev FiniteType (S : Scheme.{u}) :=
  (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}).Over ⊤ S

instance {S : Scheme.{u}} (X : S.FiniteType) : LocallyOfFiniteType X.hom := X.prop.1

instance {S : Scheme.{u}} (X : S.FiniteType) : QuasiCompact X.hom := X.prop.2

/-- Regard a locally finite-type, quasi-compact structure morphism as a finite-type scheme
over its target. -/
abbrev FiniteType.mk {S X : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [QuasiCompact f] : S.FiniteType :=
  MorphismProperty.Over.mk ⊤ f ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
