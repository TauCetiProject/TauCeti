/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Order.Interval.Set.Basic

/-!
# Closed intervals in `pi`-space

A point `x` of the box `Icc a b` in `Π i, π i` stays in the box obtained by replacing `b i`
with `s ≥ x i`, or by replacing `a i` with `s ≤ x i`. Only the indicated comparison with
`x i` is required. When `π i` is linearly ordered and `s ∈ Icc (a i) (b i)`, the two updated
boxes cover the original box and describe its cut along coordinate `i` at `s`.

A point `x` lies in a symmetric box `Icc (-a) a` of a product of linearly ordered additive groups
exactly when `|x i| ≤ a i` for every `i` (`Set.mem_Icc_neg_iff_forall_abs_le`).
-/

public section

open Function

namespace Set

section Preorder

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

end Preorder

section LinearOrder

variable {ι : Type*} {π : ι → Type*} [DecidableEq ι] [∀ j, Preorder (π j)]

/-- When the cut coordinate `π i` is linearly ordered, splitting a closed box `Icc a b` along
coordinate `i` at `s ∈ Icc (a i) (b i)` decomposes it as the union of its lower and upper
sub-boxes. -/
theorem Icc_update_union_Icc_update (a b : ∀ j, π j) (i : ι) [Std.IsLinearOrder (π i)]
    {s : π i} (hs : s ∈ Icc (a i) (b i)) :
    Icc a (update b i s) ∪ Icc (update a i s) b = Icc a b := by
  refine Subset.antisymm (union_subset
      (Icc_subset_Icc le_rfl (update_le_iff.2 ⟨hs.2, fun _ _ ↦ le_rfl⟩))
      (Icc_subset_Icc (le_update_iff.2 ⟨hs.1, fun _ _ ↦ le_rfl⟩) le_rfl)) fun x hx ↦ ?_
  rcases Std.Total.total (r := (· ≤ ·)) (x i) s with hxs | hsx
  · exact Or.inl (mem_Icc_update_right hx hxs)
  · exact Or.inr (mem_Icc_update_left hx hsx)

end LinearOrder

section Abs

variable {ι : Type*} {π : ι → Type*} [∀ i, AddCommGroup (π i)] [∀ i, LinearOrder (π i)]
  [∀ i, IsOrderedAddMonoid (π i)] {a x : ∀ i, π i}

/-- A point lies in the symmetric box `Icc (-a) a` exactly when each coordinate satisfies
`|x i| ≤ a i`. -/
theorem mem_Icc_neg_iff_forall_abs_le : x ∈ Icc (-a) a ↔ ∀ i, |x i| ≤ a i := by
  simp only [mem_Icc, Pi.le_def, Pi.neg_apply, abs_le, forall_and]

end Abs

end Set
