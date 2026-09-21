/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finrank of a zero object of `ModuleCat`

Vanishing of an object of `ModuleCat R` is naturally expressed categorically, as
`CategoryTheory.Limits.IsZero`, while the dimension counts that consume it speak of
`Module.finrank`. This file supplies the one translation between the two: a zero object has
finrank zero.

That translation is what bounds the `Module.finrank` support of a bounded complex of vector
spaces by its bounding interval, which is in turn what makes Mathlib's `finsum`-based Euler
characteristic of such a complex an honest finite sum.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] [Nontrivial R]

/-- A zero object in `ModuleCat R` has finrank zero. -/
theorem finrank_eq_zero_of_isZero {X : ModuleCat.{v} R} (hX : IsZero X) :
    Module.finrank R X = 0 := by
  let _ : Subsingleton X := ModuleCat.subsingleton_of_isZero hX
  exact Module.finrank_zero_of_subsingleton

end ModuleCat
