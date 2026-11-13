/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.NhdsWithin

/-!
# Semicontinuity of lexicographically ordered product-valued functions

Let `ι` be a well-ordered index type (`[LinearOrder ι] [WellFoundedLT ι]`) and `β : ι → Type*` a
family of linear orders. Coordinatewise continuity or upper semicontinuity of `f : α → ∀ i, β i`
does not in general imply upper semicontinuity of `fun x ↦ toLex (f x) : α → Lex (∀ i, β i)`: for
example, `t ↦ (|t|, 0)` on `ℝ` is coordinatewise continuous at `0`, satisfies
`toLex (0, 0) < toLex (0, 1)` at `t = 0`, yet satisfies `toLex (0, 1) < toLex (|t|, 0)` for every
`t ≠ 0`.

When `f` locally takes finitely many values, however, coordinatewise upper (resp. lower)
semicontinuity does lift to the lexicographic order. On any set `u : Set α`, monotonicity of
`toLex` (`Pi.toLex_monotone`) decomposes every lexicographic superlevel set
`{x ∈ u | y ≤ toLex (f x)}` as the union over attained values `v ∈ f '' u` with `y ≤ toLex v` of
the pointwise superlevel sets `{x ∈ u | v ≤ f x}` (`TauCeti.setOf_mem_and_le_toLex_eq_biUnion`).
When `f '' u` is finite on a neighbourhood of `x` within `s`, any frequent violation of `< y` near
`x` repeats a single attained value `v` with `y ≤ toLex v`, whose coordinates are then bounded by
`f x` via coordinatewise semicontinuity.

This mechanism underlies Zariski upper semicontinuity of lexicographically ordered invariants (such
as Hilbert–Samuel functions on closed points) once pointwise upper semicontinuity and local
finiteness of attained values are established.

## Main results

* `TauCeti.setOf_mem_and_le_toLex_eq_biUnion`, `TauCeti.setOf_mem_and_toLex_le_eq_biUnion`:
  on any subset `u`, a lexicographic superlevel (resp. sublevel) set of `toLex ∘ f` is the union of
  the pointwise superlevel (resp. sublevel) sets at the attained values `v ∈ f '' u` satisfying the
  lexicographic bound.
* `TauCeti.upperSemicontinuousWithinAt_toLex`, `TauCeti.upperSemicontinuousAt_toLex`,
  `TauCeti.upperSemicontinuousOn_toLex`, `TauCeti.upperSemicontinuous_toLex`: coordinatewise upper
  semicontinuity lifts to `Lex (∀ i, β i)` whenever `f` locally takes finitely many values.
* `TauCeti.lowerSemicontinuousWithinAt_toLex`, `TauCeti.lowerSemicontinuousAt_toLex`,
  `TauCeti.lowerSemicontinuousOn_toLex`, `TauCeti.lowerSemicontinuous_toLex`: the dual lower
  semicontinuity statements.

## References

* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *$\mathbb{Q}$-universal
  desingularization*, Asian J. Math. 15 (2011), 229–250, §6.1.
-/

public section

open scoped Topology
open Filter Set

namespace TauCeti

section LevelSets

variable {α ι : Type*} {β : ι → Type*} [LinearOrder ι] [WellFoundedLT ι]

/-- On any set `u`, the lexicographic superlevel set `{x ∈ u | y ≤ toLex (f x)}` is the union over
attained values `v ∈ f '' u` with `y ≤ toLex v` of the pointwise superlevel sets
`{x ∈ u | v ≤ f x}`. -/
theorem setOf_mem_and_le_toLex_eq_biUnion [∀ i, PartialOrder (β i)]
    (f : α → ∀ i, β i) (u : Set α) (y : Lex (∀ i, β i)) :
    {x ∈ u | y ≤ toLex (f x)} = ⋃ v ∈ {v ∈ f '' u | y ≤ toLex v}, {x ∈ u | v ≤ f x} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  exact ⟨fun ⟨hx, hy⟩ ↦ ⟨f x, ⟨⟨x, hx, rfl⟩, hy⟩, hx, le_rfl⟩,
    fun ⟨v, ⟨_, hy⟩, hx, hvx⟩ ↦ ⟨hx, hy.trans (Pi.toLex_monotone hvx)⟩⟩

/-- On any set `u`, the lexicographic sublevel set `{x ∈ u | toLex (f x) ≤ y}` is the union over
attained values `v ∈ f '' u` with `toLex v ≤ y` of the pointwise sublevel sets
`{x ∈ u | f x ≤ v}`. -/
theorem setOf_mem_and_toLex_le_eq_biUnion [∀ i, PartialOrder (β i)]
    (f : α → ∀ i, β i) (u : Set α) (y : Lex (∀ i, β i)) :
    {x ∈ u | toLex (f x) ≤ y} = ⋃ v ∈ {v ∈ f '' u | toLex v ≤ y}, {x ∈ u | f x ≤ v} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  exact ⟨fun ⟨hx, hy⟩ ↦ ⟨f x, ⟨⟨x, hx, rfl⟩, hy⟩, hx, le_rfl⟩,
    fun ⟨v, ⟨_, hy⟩, hx, hvx⟩ ↦ ⟨hx, (Pi.toLex_monotone hvx).trans hy⟩⟩

end LevelSets

section Semicontinuity

variable {α ι : Type*} {β : ι → Type*} [TopologicalSpace α]
  [LinearOrder ι] [WellFoundedLT ι] [∀ i, LinearOrder (β i)]

/-- If each coordinate of `f` is upper semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `fun x' ↦ toLex (f x')` is upper semicontinuous
within `s` at `x`. -/
theorem upperSemicontinuousWithinAt_toLex {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, UpperSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x := by
  rw [upperSemicontinuousWithinAt_iff_frequently]
  intro y hfreq
  obtain ⟨u, hu, hufin⟩ := hfin
  have hV : {v ∈ f '' u | y ≤ toLex v}.Finite := hufin.subset (sep_subset _ _)
  have hex : ∃ᶠ x' in 𝓝[s] x, ∃ v ∈ {v ∈ f '' u | y ≤ toLex v}, f x' = v :=
    (hfreq.and_eventually hu).mono fun x' ⟨hy, hx'⟩ ↦ ⟨f x', ⟨⟨x', hx', rfl⟩, hy⟩, rfl⟩
  obtain ⟨v, ⟨-, hyv⟩, hvfreq⟩ := hV.frequently_exists.mp hex
  have hvx : v ≤ f x := fun i ↦
    (hf i).frequently (v i) (hvfreq.mono fun _ hx' ↦ (congr_fun hx' i).symm.le)
  exact hyv.trans (Pi.toLex_monotone hvx)

/-- If each coordinate of `f` is upper semicontinuous at `x` and `f` takes finitely many values on
a neighbourhood of `x`, then `fun x' ↦ toLex (f x')` is upper semicontinuous at `x`. -/
theorem upperSemicontinuousAt_toLex {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, UpperSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    UpperSemicontinuousAt (fun x' ↦ toLex (f x')) x := by
  rw [← upperSemicontinuousWithinAt_univ_iff]
  refine upperSemicontinuousWithinAt_toLex
    (fun i ↦ (hf i).upperSemicontinuousWithinAt univ) ?_
  rwa [nhdsWithin_univ]

/-- If each coordinate of `f` is upper semicontinuous on `s` and `f` locally takes finitely many
values within `s`, then `fun x' ↦ toLex (f x')` is upper semicontinuous on `s`. -/
theorem upperSemicontinuousOn_toLex {f : α → ∀ i, β i} {s : Set α}
    (hf : ∀ i, UpperSemicontinuousOn (f · i) s)
    (hfin : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousOn (fun x' ↦ toLex (f x')) s :=
  fun x hx ↦ upperSemicontinuousWithinAt_toLex (fun i ↦ hf i x hx) (hfin x hx)

/-- If each coordinate of `f` is upper semicontinuous and `f` locally takes finitely many values,
then `fun x' ↦ toLex (f x')` is upper semicontinuous. -/
theorem upperSemicontinuous_toLex {f : α → ∀ i, β i}
    (hf : ∀ i, UpperSemicontinuous (f · i))
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    UpperSemicontinuous (fun x' ↦ toLex (f x')) :=
  fun x ↦ upperSemicontinuousAt_toLex (fun i ↦ hf i x) (hfin x)

/-- If each coordinate of `f` is lower semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `fun x' ↦ toLex (f x')` is lower semicontinuous
within `s` at `x`. -/
theorem lowerSemicontinuousWithinAt_toLex {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, LowerSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    LowerSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x := by
  rw [lowerSemicontinuousWithinAt_iff_frequently]
  intro y hfreq
  obtain ⟨u, hu, hufin⟩ := hfin
  have hV : {v ∈ f '' u | toLex v ≤ y}.Finite := hufin.subset (sep_subset _ _)
  have hex : ∃ᶠ x' in 𝓝[s] x, ∃ v ∈ {v ∈ f '' u | toLex v ≤ y}, f x' = v :=
    (hfreq.and_eventually hu).mono fun x' ⟨hy, hx'⟩ ↦ ⟨f x', ⟨⟨x', hx', rfl⟩, hy⟩, rfl⟩
  obtain ⟨v, ⟨-, hvy⟩, hvfreq⟩ := hV.frequently_exists.mp hex
  have hvx : f x ≤ v := fun i ↦
    (hf i).frequently (v i) (hvfreq.mono fun _ hx' ↦ (congr_fun hx' i).le)
  exact (Pi.toLex_monotone hvx).trans hvy

/-- If each coordinate of `f` is lower semicontinuous at `x` and `f` takes finitely many values on
a neighbourhood of `x`, then `fun x' ↦ toLex (f x')` is lower semicontinuous at `x`. -/
theorem lowerSemicontinuousAt_toLex {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, LowerSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    LowerSemicontinuousAt (fun x' ↦ toLex (f x')) x := by
  rw [← lowerSemicontinuousWithinAt_univ_iff]
  refine lowerSemicontinuousWithinAt_toLex
    (fun i ↦ (hf i).lowerSemicontinuousWithinAt univ) ?_
  rwa [nhdsWithin_univ]

/-- If each coordinate of `f` is lower semicontinuous on `s` and `f` locally takes finitely many
values within `s`, then `fun x' ↦ toLex (f x')` is lower semicontinuous on `s`. -/
theorem lowerSemicontinuousOn_toLex {f : α → ∀ i, β i} {s : Set α}
    (hf : ∀ i, LowerSemicontinuousOn (f · i) s)
    (hfin : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    LowerSemicontinuousOn (fun x' ↦ toLex (f x')) s :=
  fun x hx ↦ lowerSemicontinuousWithinAt_toLex (fun i ↦ hf i x hx) (hfin x hx)

/-- If each coordinate of `f` is lower semicontinuous and `f` locally takes finitely many values,
then `fun x' ↦ toLex (f x')` is lower semicontinuous. -/
theorem lowerSemicontinuous_toLex {f : α → ∀ i, β i}
    (hf : ∀ i, LowerSemicontinuous (f · i))
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    LowerSemicontinuous (fun x' ↦ toLex (f x')) :=
  fun x ↦ lowerSemicontinuousAt_toLex (fun i ↦ hf i x) (hfin x)

end Semicontinuity

end TauCeti
