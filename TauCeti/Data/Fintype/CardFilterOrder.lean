/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Monotone.Defs

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting the values of a function in a lower set

For a function `u` on a finite type with values in a preorder, we compare the numbers of indices
`l` at which `u l` lies in a lower set, as `u` grows pointwise, and split the number of values at
most `i` into the numbers of values equal to each `j ≤ i`.

## Main results

* `TauCeti.card_filter_le_card_filter_of_le`: a pointwise larger function has at most as many
  values in a lower set.
* `TauCeti.exists_card_filter_lt_card_filter`: if `u ≤ w` are distinct monotone functions, then
  at some value `u j` of `u`, fewer values of `w` than of `u` are at most `u j`.
* `TauCeti.card_filter_le_eq_sum_card_filter_eq`: for a function with values in a finite set
  `σ`, the number of values at most `i` is the sum over `j ≤ i` in `σ` of the number of values
  equal to `j`.
-/

public section

open Finset

namespace TauCeti

variable {α ι : Type*} [Fintype α]

/-- If `u ≤ w` pointwise, then `w` has at most as many values as `u` in the lower set `p`. -/
theorem card_filter_le_card_filter_of_le [Preorder ι] {u w : α → ι} (huw : u ≤ w)
    {p : ι → Prop} [DecidablePred p] (hp : Antitone p) : #{l | p (w l)} ≤ #{l | p (u l)} :=
  card_le_card (monotone_filter_right _ fun l _ hl => hp (huw l) hl)

/-- If `u ≤ w` are distinct monotone functions, then at some value `u j` of `u`, fewer values of
`w` than of `u` are at most `u j`. -/
theorem exists_card_filter_lt_card_filter [LinearOrder α] [PartialOrder ι] [DecidableLE ι]
    {u w : α → ι} (hu : Monotone u) (hw : Monotone w) (huw : u ≤ w) (hne : u ≠ w) :
    ∃ j, #{l | w l ≤ u j} < #{l | u l ≤ u j} := by
  obtain ⟨j, hlt⟩ := (Pi.lt_def.mp (lt_of_le_of_ne huw hne)).2
  refine ⟨j, ?_⟩
  calc #{l | w l ≤ u j} ≤ #{l | l < j} := card_le_card fun l hl => by
        simp only [mem_filter, mem_univ, true_and] at hl ⊢
        exact lt_of_not_ge fun hjl => (hlt.trans_le (hw hjl)).not_ge hl
    _ < #{l | l ≤ j} := card_lt_card <| (ssubset_iff_of_subset
        (monotone_filter_right _ fun _ _ hl => hl.le)).mpr ⟨j, by simp, by simp⟩
    _ ≤ #{l | u l ≤ u j} := card_le_card (monotone_filter_right _ fun _ _ hl => hu hl)

/-- For a function with values in `σ`, the number of values at most `i` is the sum over the
elements `j ≤ i` of `σ` of the number of values equal to `j`. -/
theorem card_filter_le_eq_sum_card_filter_eq [Preorder ι] [DecidableEq ι] [DecidableLE ι]
    {σ : Finset ι} {u : α → ι} (hu : ∀ l, u l ∈ σ) (i : σ) :
    #{l | u l ≤ i.1} = ∑ j ∈ ({j | j ≤ i} : Finset σ), #{l | u l = j.1} := by
  rw [card_eq_sum_card_fiberwise (f := fun l => (⟨u l, hu l⟩ : σ)) (t := {j | j ≤ i})
    fun l hl => by simpa [← Subtype.coe_le_coe] using hl]
  refine sum_congr rfl fun j hj => ?_
  rw [filter_filter]
  congr 1
  ext l
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact ⟨fun h => congrArg Subtype.val h.2, fun h => ⟨h ▸ hj, Subtype.ext h⟩⟩

end TauCeti
