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
# Semicontinuity of locally finite product-valued functions and lexicographic order

Coordinatewise continuity or upper semicontinuity of `f : α → ∀ i, β i` does not in general imply
upper semicontinuity of `fun x ↦ toLex (f x) : α → Lex (∀ i, β i)`: for example, `t ↦ (|t|, 0)`
on `ℝ` is coordinatewise continuous at `0`, satisfies `toLex (0, 0) < toLex (0, 1)` at `t = 0`,
yet satisfies `toLex (0, 1) < toLex (|t|, 0)` for every `t ≠ 0`.

When `f` locally takes finitely many values, however, coordinatewise upper semicontinuity forces
`f x' ≤ f x` eventually near `x` without any ordering on the index type `ι`
(`TauCeti.eventually_le_of_upperSemicontinuousWithinAt`): any frequent violation of `f x' ≤ f x`
on a finite-range neighbourhood repeats a single attained value `v` with `¬ v ≤ f x`, contradicting
coordinatewise upper semicontinuity at a witnessing coordinate. Post-composing with any monotone map
into a preorder—in particular `toLex : (∀ i, β i) → Lex (∀ i, β i)` when `ι` is well-ordered
(`Pi.toLex_monotone`)—then preserves upper semicontinuity
(`Monotone.upperSemicontinuousWithinAt_comp_of_finite`,
`TauCeti.upperSemicontinuousWithinAt_toLex`), and dually for lower semicontinuity via `OrderDual`.

This mechanism underlies Zariski upper semicontinuity of lexicographically ordered invariants (such
as Hilbert–Samuel functions on closed points) once pointwise upper semicontinuity and local
finiteness of attained values are established.

## Main results

* `TauCeti.eventually_le_of_upperSemicontinuousWithinAt`,
  `TauCeti.eventually_ge_of_lowerSemicontinuousWithinAt`: coordinatewise upper (resp. lower)
  semicontinuity together with locally finite range implies `f x' ≤ f x` (resp. `f x ≤ f x'`)
  eventually near `x`.
* `Monotone.upperSemicontinuousWithinAt_comp_of_finite`,
  `Monotone.lowerSemicontinuousWithinAt_comp_of_finite`: post-composing a coordinatewise
  semicontinuous locally finite family with any monotone map preserves semicontinuity.
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

section Eventually

variable {α ι : Type*} {β : ι → Type*} [TopologicalSpace α] [∀ i, LinearOrder (β i)]

/-- If each coordinate of `f` is upper semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `f x' ≤ f x` eventually in `𝓝[s] x`. -/
theorem eventually_le_of_upperSemicontinuousWithinAt {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, UpperSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝[s] x, f x' ≤ f x := by
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  obtain ⟨u, hu, hufin⟩ := hfin
  have hV : {v ∈ f '' u | ¬ v ≤ f x}.Finite := hufin.subset (sep_subset _ _)
  have hex : ∃ᶠ x' in 𝓝[s] x, ∃ v ∈ {v ∈ f '' u | ¬ v ≤ f x}, f x' = v :=
    (hnot.and_eventually hu).mono fun x' ⟨hnotle, hx'⟩ ↦ ⟨f x', ⟨⟨x', hx', rfl⟩, hnotle⟩, rfl⟩
  obtain ⟨v, ⟨-, hnotle⟩, hvfreq⟩ := hV.frequently_exists.mp hex
  exact hnotle fun i ↦
    (hf i).frequently (v i) (hvfreq.mono fun _ hx' ↦ (congr_fun hx' i).symm.le)

/-- If each coordinate of `f` is lower semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `f x ≤ f x'` eventually in `𝓝[s] x`. -/
theorem eventually_ge_of_lowerSemicontinuousWithinAt {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, LowerSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝[s] x, f x ≤ f x' := by
  let f' : α → ∀ i, (β i)ᵒᵈ := fun a i ↦ OrderDual.toDual (f a i)
  have hf' : ∀ i, UpperSemicontinuousWithinAt (f' · i) s x := fun i y hy ↦
    (hf i (OrderDual.ofDual y) (OrderDual.toDual_lt.mp hy)).mono
      fun _ hx' ↦ OrderDual.toDual_lt.mpr hx'
  have hfin' : ∃ u ∈ 𝓝[s] x, (f' '' u).Finite := by
    obtain ⟨u, hu, hufin⟩ := hfin
    refine ⟨u, hu, ?_⟩
    have himg : f' '' u = (fun v i ↦ OrderDual.toDual (v i)) '' (f '' u) := by
      rw [← Set.image_comp]
      rfl
    rw [himg]
    exact hufin.image _
  exact (eventually_le_of_upperSemicontinuousWithinAt hf' hfin').mono
    fun _ hx' i ↦ OrderDual.toDual_le_toDual.mp (hx' i)

end Eventually

end TauCeti

section MonotoneComp

variable {α ι γ : Type*} {β : ι → Type*} [TopologicalSpace α] [∀ i, LinearOrder (β i)]
  [Preorder γ]

/-- Post-composing a coordinatewise upper semicontinuous locally finite family with a monotone map
preserves `UpperSemicontinuousWithinAt`. -/
theorem Monotone.upperSemicontinuousWithinAt_comp_of_finite {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, UpperSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousWithinAt (fun x' ↦ g (f x')) s x := fun _ hy ↦
  (TauCeti.eventually_le_of_upperSemicontinuousWithinAt hf hfin).mono
    fun _ hx' ↦ (hg hx').trans_lt hy

/-- Post-composing a coordinatewise lower semicontinuous locally finite family with a monotone map
preserves `LowerSemicontinuousWithinAt`. -/
theorem Monotone.lowerSemicontinuousWithinAt_comp_of_finite {g : (∀ i, β i) → γ}
    (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, LowerSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    LowerSemicontinuousWithinAt (fun x' ↦ g (f x')) s x := fun _ hy ↦
  (TauCeti.eventually_ge_of_lowerSemicontinuousWithinAt hf hfin).mono
    fun _ hx' ↦ hy.trans_le (hg hx')

end MonotoneComp

namespace TauCeti

section PiLex

variable {α ι : Type*} {β : ι → Type*} [TopologicalSpace α]
  [LinearOrder ι] [WellFoundedLT ι] [∀ i, LinearOrder (β i)]

/-- If each coordinate of `f` is upper semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `fun x' ↦ toLex (f x')` is upper semicontinuous
within `s` at `x`. -/
theorem upperSemicontinuousWithinAt_toLex {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, UpperSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x :=
  Pi.toLex_monotone.upperSemicontinuousWithinAt_comp_of_finite hf hfin

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
    LowerSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x :=
  Pi.toLex_monotone.lowerSemicontinuousWithinAt_comp_of_finite hf hfin

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

end PiLex

end TauCeti
