/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Set.Disjoint

/-!
# Products with intervals

A sequence tending to `atTop` exhausts each upper ray by bounded half-open intervals.
Taking products with a fixed set preserves this union.

A product `Ioi c ×ˢ s` of an upper ray with a set is stable under translation by `(a, 0)` with
`0 ≤ a` (`Set.add_mk_zero_mem_Ioi_prod`).
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

/-- Translating a point of `Ioi c ×ˢ s` by `(a, 0)` with `0 ≤ a` stays in `Ioi c ×ˢ s`. -/
theorem add_mk_zero_mem_Ioi_prod {α β : Type*} [AddZeroClass α] [Preorder α] [AddLeftMono α]
    [AddZeroClass β] {c a : α} {s : Set β} {z : α × β} (hz : z ∈ Ioi c ×ˢ s) (ha : 0 ≤ a) :
    z + (a, 0) ∈ Ioi c ×ˢ s := by
  simpa using And.intro (lt_add_of_lt_of_nonneg (mem_Ioi.1 hz.1) ha) hz.2

end Set
