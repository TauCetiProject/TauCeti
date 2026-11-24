/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Monoid schemes are surjective over their base

The unit section of a monoid object `X` in `Over S` is a section of its structure morphism
`X.hom : X.left ⟶ S`, so the structure morphism is surjective. In particular every group scheme
over `S` is surjective over `S`, and a flat group scheme is faithfully flat. No finiteness,
flatness or commutativity is needed.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace TauCeti.GroupScheme

universe u

/-- The structure morphism of a monoid object in `Over S` is surjective, since its unit section is
a section of it. -/
instance surjective_hom_of_monObj {S : Scheme.{u}} (X : Over S) [MonObj X] : Surjective X.hom := by
  have : Surjective (η[X].left ≫ X.hom) := by
    rw [Over.w, Over.tensorUnit_hom]
    -- The rewritten goal states `𝟙 S` through the category instance of `Over S`; the ascription
    -- restates it in `Scheme`, where the instance for isomorphisms applies.
    exact (inferInstance : Surjective (𝟙 S))
  exact .of_comp η[X].left _

end TauCeti.GroupScheme
