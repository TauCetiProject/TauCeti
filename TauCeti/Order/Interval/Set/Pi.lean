/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Basic

/-!
# Closed intervals in `pi`-space with an updated endpoint

A point of the box `Icc a b` in `Π i, π i` stays in the box obtained by moving one coordinate of
an endpoint past the point: lowering `b i` to some `s ≥ x i`, or raising `a i` to some `s ≤ x i`.
These are the two halves of the box `Icc a b` cut along the coordinate `i` at `s`.
-/

public section

open Function

namespace Set

variable {ι : Type*} {π : ι → Type*} [DecidableEq ι] [∀ i, Preorder (π i)] {a b x : ∀ i, π i}
  {i : ι} {s : π i}

/-- A point of the box `Icc a b` whose `i`-th coordinate is at most `s` lies in the box whose
upper endpoint has its `i`-th coordinate replaced by `s`. -/
theorem mem_Icc_update_right (hx : x ∈ Icc a b) (hxs : x i ≤ s) : x ∈ Icc a (update b i s) :=
  ⟨hx.1, le_update_iff.2 ⟨hxs, fun j _ ↦ hx.2 j⟩⟩

/-- A point of the box `Icc a b` whose `i`-th coordinate is at least `s` lies in the box whose
lower endpoint has its `i`-th coordinate replaced by `s`. -/
theorem mem_Icc_update_left (hx : x ∈ Icc a b) (hsx : s ≤ x i) : x ∈ Icc (update a i s) b :=
  ⟨update_le_iff.2 ⟨hsx, fun j _ ↦ hx.1 j⟩, hx.2⟩

end Set
