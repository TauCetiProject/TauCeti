/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# The category of finite-type schemes over a base

A finite-type scheme over a base is a scheme with a quasi-compact morphism to the base that is
locally of finite type. The category inherits all morphisms over the base.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The full subcategory of schemes over the base whose structure morphisms are of finite type. -/
protected abbrev FiniteType (S : Scheme.{u}) :=
  (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}).Over ⊤ S

/-- The inclusion of finite-type schemes into all schemes over the base. -/
abbrev FiniteType.forget (S : Scheme.{u}) : S.FiniteType ⥤ Over S :=
  MorphismProperty.Over.forget _ _ _

instance {S : Scheme.{u}} (X : S.FiniteType) : LocallyOfFiniteType X.hom := X.prop.1

instance {S : Scheme.{u}} (X : S.FiniteType) : QuasiCompact X.hom := X.prop.2

end AlgebraicGeometry.Scheme
