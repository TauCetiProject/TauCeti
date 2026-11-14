/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.PiLex
import TauCeti.Order.Monotone.Basic

/-!
# Comparisons and level-set decompositions for lexicographically ordered products

Mathlib equips `Lex (∀ i, β i)` with `<` defined via `Pi.Lex (· < ·) (· < ·)` wrapped in `id` to
prevent unwanted definitional reduction (`Mathlib.Order.PiLex`). This module provides explicit
iff-bridges `TauCeti.toLex_lt_toLex` and `TauCeti.toLex_le_toLex` between inequalities on
`Lex (∀ i, β i)` and `Pi.Lex`, together with decompositions of lexicographic superlevel and
sublevel sets `{x ∈ u | y ≤ toLex (f x)}` and `{x ∈ u | toLex (f x) ≤ y}` into unions of
coordinatewise superlevel and sublevel sets over attained values `v ∈ f '' u`
(`TauCeti.setOf_mem_and_le_toLex_eq_biUnion`, `TauCeti.setOf_mem_and_toLex_le_eq_biUnion`).

## Main results

* `TauCeti.toLex_lt_toLex`, `TauCeti.toLex_le_toLex`: explicit iff characterizations of
  `toLex x < toLex y` and `toLex x ≤ toLex y` in terms of `Pi.Lex`.
* `TauCeti.setOf_mem_and_le_toLex_eq_biUnion`, `TauCeti.setOf_mem_and_toLex_le_eq_biUnion`:
  on any subset `u`, a lexicographic superlevel (resp. sublevel) set of `toLex ∘ f` is the union of
  the pointwise superlevel (resp. sublevel) sets at the attained values `v ∈ f '' u` satisfying the
  lexicographic bound.
-/

public section

namespace TauCeti

section Comparison

variable {ι : Type*} {β : ι → Type*}

/-- Strict inequality on `Lex (∀ i, β i)` is `Pi.Lex (· < ·) (· < ·)`. -/
theorem toLex_lt_toLex [LT ι] [∀ i, LT (β i)] {x y : ∀ i, β i} :
    toLex x < toLex y ↔ Pi.Lex (· < ·) (· < ·) x y := (Iff.rfl)

/-- Nonstrict inequality on `Lex (∀ i, β i)` is equality or `Pi.Lex (· < ·) (· < ·)`. -/
theorem toLex_le_toLex [LinearOrder ι] [∀ i, PartialOrder (β i)] {x y : ∀ i, β i} :
    toLex x ≤ toLex y ↔ x = y ∨ Pi.Lex (· < ·) (· < ·) x y :=
  le_iff_eq_or_lt.trans (or_congr toLex_inj toLex_lt_toLex)

end Comparison

section LevelSets

variable {α ι : Type*} {β : ι → Type*} [LinearOrder ι] [WellFoundedLT ι] [∀ i, PartialOrder (β i)]

/-- On any set `u`, the lexicographic superlevel set `{x ∈ u | y ≤ toLex (f x)}` is the union over
attained values `v ∈ f '' u` with `y ≤ toLex v` of the pointwise superlevel sets
`{x ∈ u | v ≤ f x}`. -/
theorem setOf_mem_and_le_toLex_eq_biUnion
    (f : α → ∀ i, β i) (u : Set α) (y : Lex (∀ i, β i)) :
    {x ∈ u | y ≤ toLex (f x)} = ⋃ v ∈ {v ∈ f '' u | y ≤ toLex v}, {x ∈ u | v ≤ f x} :=
  Pi.toLex_monotone.setOf_mem_and_le_eq_biUnion f u y

/-- On any set `u`, the lexicographic sublevel set `{x ∈ u | toLex (f x) ≤ y}` is the union over
attained values `v ∈ f '' u` with `toLex v ≤ y` of the pointwise sublevel sets
`{x ∈ u | f x ≤ v}`. -/
theorem setOf_mem_and_toLex_le_eq_biUnion
    (f : α → ∀ i, β i) (u : Set α) (y : Lex (∀ i, β i)) :
    {x ∈ u | toLex (f x) ≤ y} = ⋃ v ∈ {v ∈ f '' u | toLex v ≤ y}, {x ∈ u | f x ≤ v} :=
  Pi.toLex_monotone.setOf_mem_and_ge_eq_biUnion f u y

end LevelSets

end TauCeti
