/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Countable
import Mathlib.Basic.Countable.Basic

/-!
# Countability of categorical indexing data

A category is countable exactly when its total arrow type is countable. This allows a bound on
the size of an indexing category to be tested on a single type.
-/

public section

open CategoryTheory

namespace TauCeti

/-- A countable category has countably many arrows in total. -/
instance instCountableArrow {C : Type*} [Category* C] [CountableCategory C] :
    Countable (Arrow C) :=
  Countable.of_equiv _ (Arrow.equivSigma C).symm

/-- A category has countably many objects and morphisms if and only if its total arrow type is
countable. -/
theorem countable_arrow_iff (C : Type*) [Category* C] :
    Countable (Arrow C) ↔ CountableCategory C := by
  constructor
  · intro h
    exact
      { countableObj := Function.Injective.countable (f := fun X : C ↦ Arrow.mk (𝟙 X))
          (fun _ _ he ↦ by simpa only [Arrow.mk_left] using congrArg Arrow.left he)
        countableHom X Y := (Arrow.mk_injective X Y).countable }
  · intro h
    infer_instance

end TauCeti
