/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Set.Disjoint

/-!
# Unions of interval products

A sequence tending to `atTop` exhausts each upper ray by bounded half-open intervals.
Taking products with a fixed set preserves this union.
-/

public section

open Filter

namespace Set

/-- Rectangles with a fixed left endpoint and right endpoints tending to `atTop`
exhaust the product of the upper ray with the same spatial set. -/
theorem iUnion_Ioc_prod_eq_Ioi_prod {ι Ω : Type*} [LinearOrder ι] {u : ℕ → ι}
    (hu : Tendsto u atTop atTop) (s : ι) (A : Set Ω) :
    (⋃ n, Ioc s (u n) ×ˢ A) = Ioi s ×ˢ A := by
  rw [← iUnion_prod_const, iUnion_Ioc_eq_Ioi_self_iff.mpr
    (fun x _ => (hu.eventually (eventually_ge_atTop x)).exists)]

end Set
