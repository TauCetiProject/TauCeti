/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Notation.Indicator

/-!
# Sums of indicator functions of disjoint sets

For disjoint sets `U` and `V`, the function `U.indicator f + V.indicator g` is `f` on `U` and `g`
on `V`.

## Main results

* `Disjoint.indicator_add_indicator_apply_of_mem_left`: on `U`, `U.indicator f + V.indicator g`
  is `f`.
* `Disjoint.indicator_add_indicator_apply_of_mem_right`: on `V`, `U.indicator f + V.indicator g`
  is `g`.
-/

public section

open Set

variable {X β : Type*} [AddZeroClass β] {U V : Set X}

/-- On the first of two disjoint sets `U` and `V`, the function `U.indicator f + V.indicator g` is
`f`. -/
theorem Disjoint.indicator_add_indicator_apply_of_mem_left (hd : Disjoint U V) (f g : X → β)
    {x : X} (hx : x ∈ U) : (U.indicator f + V.indicator g) x = f x := by
  rw [Pi.add_apply, indicator_of_mem hx, indicator_of_notMem (hd.notMem_of_mem_left hx), add_zero]

/-- On the second of two disjoint sets `U` and `V`, the function `U.indicator f + V.indicator g`
is `g`. -/
theorem Disjoint.indicator_add_indicator_apply_of_mem_right (hd : Disjoint U V) (f g : X → β)
    {x : X} (hx : x ∈ V) : (U.indicator f + V.indicator g) x = g x := by
  rw [Pi.add_apply, indicator_of_mem hx, indicator_of_notMem (hd.notMem_of_mem_right hx), zero_add]
