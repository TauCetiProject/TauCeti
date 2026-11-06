/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The forgetful functor of commutative rings preserves small filtered colimits

Mathlib shows that the forgetful functor `CommRingCat.{u} ⥤ Type u` preserves filtered colimits
indexed by categories in universe `u`. This file records that it also preserves filtered colimits
indexed by categories in universe `0`, such as the colimit of a sequence `R₀ → R₁ → ⋯` indexed by
`ℕ`, so that these are computed on underlying types for rings in any universe.
-/

public section

open CategoryTheory Limits

universe u

namespace CommRingCat

/-- The forgetful functor `CommRingCat.{u} ⥤ Type u` preserves filtered colimits indexed by
categories in universe `0`, for instance by `ℕ`. -/
instance : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
  preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} _

end CommRingCat
