/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finrank in `ModuleCat`

This file records basic categorical properties of finrank for vector spaces.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {k : Type u} [DivisionRing k]

/-- A zero object in `ModuleCat k` has finrank zero. -/
theorem finrank_eq_zero_of_isZero {X : ModuleCat.{v} k} (hX : IsZero X) :
    Module.finrank k X = 0 := by
  let _ : Subsingleton X := ModuleCat.subsingleton_of_isZero hX
  exact Module.finrank_zero_of_subsingleton

end ModuleCat

end TauCeti
