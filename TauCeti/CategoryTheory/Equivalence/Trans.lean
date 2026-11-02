/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-!
# Unit and counit of a composite equivalence

The unit and counit of the composite `e.trans f` of equivalences `e : C ≌ D` and `f : D ≌ E` are
assembled from those of `e` and `f` by whiskering. This file records their components: the unit
at `X` is the unit of `e` at `X` followed by `e.inverse` applied to the unit of `f` at
`e.functor.obj X`, and dually for the counit. These formulas compute the unit and counit of an
equivalence built as a composite, without unfolding the whiskering and unitors of
`CategoryTheory.Equivalence.trans`.
-/

public section

namespace CategoryTheory.Equivalence

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] (e : C ≌ D) (f : D ≌ E)

/-- The unit of a composite equivalence `e.trans f` at `X` is the unit of `e` at `X`, followed by
`e.inverse` applied to the unit of `f` at `e.functor.obj X`. -/
theorem trans_unit_app (X : C) :
    (e.trans f).unit.app X = e.unit.app X ≫ e.inverse.map (f.unit.app (e.functor.obj X)) := by
  simp [Equivalence.unit]

/-- The counit of a composite equivalence `e.trans f` at `Y` is `f.functor` applied to the counit
of `e` at `f.inverse.obj Y`, followed by the counit of `f` at `Y`. -/
theorem trans_counit_app (Y : E) :
    (e.trans f).counit.app Y = f.functor.map (e.counit.app (f.inverse.obj Y)) ≫ f.counit.app Y := by
  simp [Equivalence.counit]

end CategoryTheory.Equivalence
