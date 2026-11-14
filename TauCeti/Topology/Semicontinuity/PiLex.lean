/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Semicontinuity for the lexicographic order on product types

For a family of ordered codomains `β : ι → Type*` indexed by a well-ordered type `ι`, the
lexicographic order `Lex (∀ i, β i)` extends the pointwise order (`Pi.toLex_monotone`). Coordinate
upper semicontinuity of `f : X → ∀ i, β i` alone does not imply upper semicontinuity of
`toLex ∘ f`: for `f : ℝ → Fin 2 → ℝ` given by `f x 0 = |x|` and `f x 1 = 0`, both coordinates are
continuous, yet `{x | toLex ![0, 1] ≤ toLex (f x)} = ℝ \ {0}` is not closed because `|x|` takes
infinitely many positive values near `0`.

When `f` locally takes only finitely many values, lexicographic upper sets restrict on each finite-
value neighbourhood `U` to finite unions of pointwise upper sets
(`TauCeti.setOf_mem_and_le_toLex_eq_biUnion`), so closedness of pointwise upper sets transfers to
lexicographic upper sets (`TauCeti.isClosed_preimage_Ici_toLex`) and coordinatewise upper (or lower)
semicontinuity transfers to `toLex ∘ f` (`TauCeti.upperSemicontinuous_toLex`,
`TauCeti.lowerSemicontinuous_toLex`). This is the topological mechanism behind upper semicontinuity
of lexicographically scheduled invariants in resolution of singularities.

## Main results

* `TauCeti.setOf_mem_and_le_toLex_eq_biUnion`: on any `U : Set X`, `{x ∈ U | v ≤ toLex (f x)}` is
  the union over `w ∈ f '' U` with `v ≤ toLex w` of the pointwise upper sets `{x ∈ U | w ≤ f x}`.
* `TauCeti.isClosed_preimage_Ici_toLex`: if every pointwise upper set `{x | w ≤ f x}` is closed and
  `f` locally takes finitely many values, then every lexicographic upper set `{x | v ≤ toLex (f x)}`
  is closed.
* `TauCeti.upperSemicontinuousWithinAt_toLex`, `TauCeti.upperSemicontinuousAt_toLex`,
  `TauCeti.upperSemicontinuousOn_toLex`, `TauCeti.upperSemicontinuous_toLex`: coordinatewise upper
  semicontinuity plus local finiteness of values implies lexicographic upper semicontinuity.
* `TauCeti.lowerSemicontinuousWithinAt_toLex`, `TauCeti.lowerSemicontinuousAt_toLex`,
  `TauCeti.lowerSemicontinuousOn_toLex`, `TauCeti.lowerSemicontinuous_toLex`: the dual lower
  semicontinuity statements.

## References

* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *ℚ-universal desingularization*, Asian J.
  Math. 15 (2011), 229–250, §6.1.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

section PartialOrder

variable {X ι : Type*} {β : ι → Type*} [LinearOrder ι] [WellFoundedLT ι] [∀ i, PartialOrder (β i)]

/-- On any subset `U : Set X`, the lexicographic upper set `{x ∈ U | v ≤ toLex (f x)}` decomposes as
the union over attained values `w ∈ f '' U` satisfying `v ≤ toLex w` of the pointwise upper sets
`{x ∈ U | w ≤ f x}`. -/
theorem setOf_mem_and_le_toLex_eq_biUnion (f : X → ∀ i, β i) (U : Set X) (v : Lex (∀ i, β i)) :
    {x ∈ U | v ≤ toLex (f x)} =
      ⋃ w ∈ {w ∈ f '' U | v ≤ toLex w}, {x ∈ U | w ≤ f x} := by
  ext x
  simp only [mem_sep_iff, mem_iUnion, exists_prop]
  exact ⟨fun ⟨hxU, hvx⟩ ↦ ⟨f x, ⟨mem_image_of_mem f hxU, hvx⟩, hxU, le_rfl⟩,
    fun ⟨w, ⟨_, hvw⟩, hxU, hwx⟩ ↦ ⟨hxU, hvw.trans (Pi.toLex_monotone hwx)⟩⟩

/-- If every pointwise upper set `{x | w ≤ f x}` is closed and `f` locally takes only finitely many
values, then every lexicographic upper set `{x | v ≤ toLex (f x)}` is closed. -/
theorem isClosed_preimage_Ici_toLex [TopologicalSpace X] {f : X → ∀ i, β i}
    (hf : ∀ w : ∀ i, β i, IsClosed {x | w ≤ f x})
    (hfin : ∀ x : X, ∃ U ∈ 𝓝 x, (f '' U).Finite) (v : Lex (∀ i, β i)) :
    IsClosed {x | v ≤ toLex (f x)} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hF⟩ := hfin x
  let S : Set (∀ i, β i) := {w ∈ f '' U | v ≤ toLex w}
  have hS : S.Finite := hF.subset fun _ hw ↦ hw.1
  have hC : IsClosed (⋃ w ∈ S, {y | w ≤ f y}) := hS.isClosed_biUnion fun w _ ↦ hf w
  have hxC : x ∉ ⋃ w ∈ S, {y | w ≤ f y} := by
    simp only [mem_iUnion, mem_ofPred_eq, not_exists]
    intro w hw hwx
    exact hx (hw.2.trans (Pi.toLex_monotone hwx))
  filter_upwards [hU, hC.isOpen_compl.mem_nhds hxC] with y hyU hyC
  intro hvy
  exact hyC (mem_iUnion₂.mpr ⟨f y, ⟨mem_image_of_mem f hyU, hvy⟩, show f y ≤ f y from le_rfl⟩)

end PartialOrder

section LinearOrder

variable {X ι : Type*} {β : ι → Type*} [TopologicalSpace X]
  [LinearOrder ι] [WellFoundedLT ι] [∀ i, LinearOrder (β i)]
  {f : X → ∀ i, β i} {s : Set X} {x : X}

/-- If `f` is coordinatewise upper semicontinuous within `s` at `x` and takes finitely many values
on a neighbourhood of `x` within `s`, then `toLex ∘ f` is upper semicontinuous within `s` at `x`. -/
theorem upperSemicontinuousWithinAt_toLex
    (hf : ∀ i, UpperSemicontinuousWithinAt (fun y ↦ f y i) s x)
    (hfin : ∃ U ∈ 𝓝[s] x, (f '' U).Finite) :
    UpperSemicontinuousWithinAt (fun y ↦ toLex (f y)) s x := by
  intro v hv
  obtain ⟨U, hU, hF⟩ := hfin
  let S : Set (∀ i, β i) := {w ∈ f '' U | v ≤ toLex w}
  have hS : S.Finite := hF.subset fun _ hw ↦ hw.1
  have hne : ∀ w ∈ S, ∀ᶠ y in 𝓝[s] x, f y ≠ w := by
    intro w hw
    obtain ⟨i, _, hlt⟩ : toLex (f x) < toLex w := hv.trans_le hw.2
    filter_upwards [hf i (w i) hlt] with y hy hfy
    exact (hfy ▸ hy).false
  filter_upwards [hU, (eventually_all_finite hS).mpr hne] with y hyU hyS
  exact lt_of_not_ge fun hvy ↦ hyS (f y) ⟨mem_image_of_mem f hyU, hvy⟩ rfl

/-- If `f` is coordinatewise upper semicontinuous at `x` and takes finitely many values on a
neighbourhood of `x`, then `toLex ∘ f` is upper semicontinuous at `x`. -/
theorem upperSemicontinuousAt_toLex
    (hf : ∀ i, UpperSemicontinuousAt (fun y ↦ f y i) x)
    (hfin : ∃ U ∈ 𝓝 x, (f '' U).Finite) :
    UpperSemicontinuousAt (fun y ↦ toLex (f y)) x := by
  rw [← upperSemicontinuousWithinAt_univ_iff]
  refine upperSemicontinuousWithinAt_toLex
    (fun i ↦ (upperSemicontinuousWithinAt_univ_iff).mpr (hf i)) ?_
  rwa [nhdsWithin_univ]

/-- If `f` is coordinatewise upper semicontinuous on `s` and locally takes finitely many values
within `s`, then `toLex ∘ f` is upper semicontinuous on `s`. -/
theorem upperSemicontinuousOn_toLex
    (hf : ∀ i, UpperSemicontinuousOn (fun y ↦ f y i) s)
    (hfin : ∀ x ∈ s, ∃ U ∈ 𝓝[s] x, (f '' U).Finite) :
    UpperSemicontinuousOn (fun y ↦ toLex (f y)) s :=
  fun x hx ↦ upperSemicontinuousWithinAt_toLex (fun i ↦ hf i x hx) (hfin x hx)

/-- If `f` is coordinatewise upper semicontinuous and locally takes finitely many values, then
`toLex ∘ f` is upper semicontinuous. -/
theorem upperSemicontinuous_toLex
    (hf : ∀ i, UpperSemicontinuous (fun y ↦ f y i))
    (hfin : ∀ x, ∃ U ∈ 𝓝 x, (f '' U).Finite) :
    UpperSemicontinuous (fun y ↦ toLex (f y)) :=
  fun x ↦ upperSemicontinuousAt_toLex (fun i ↦ hf i x) (hfin x)

/-- If `f` is coordinatewise lower semicontinuous within `s` at `x` and takes finitely many values
on a neighbourhood of `x` within `s`, then `toLex ∘ f` is lower semicontinuous within `s` at `x`. -/
theorem lowerSemicontinuousWithinAt_toLex
    (hf : ∀ i, LowerSemicontinuousWithinAt (fun y ↦ f y i) s x)
    (hfin : ∃ U ∈ 𝓝[s] x, (f '' U).Finite) :
    LowerSemicontinuousWithinAt (fun y ↦ toLex (f y)) s x := by
  intro v hv
  obtain ⟨U, hU, hF⟩ := hfin
  let S : Set (∀ i, β i) := {w ∈ f '' U | toLex w ≤ v}
  have hS : S.Finite := hF.subset fun _ hw ↦ hw.1
  have hne : ∀ w ∈ S, ∀ᶠ y in 𝓝[s] x, f y ≠ w := by
    intro w hw
    obtain ⟨i, _, hlt⟩ : toLex w < toLex (f x) := hw.2.trans_lt hv
    filter_upwards [hf i (w i) hlt] with y hy hfy
    exact (hfy ▸ hy).false
  filter_upwards [hU, (eventually_all_finite hS).mpr hne] with y hyU hyS
  exact lt_of_not_ge fun hvy ↦ hyS (f y) ⟨mem_image_of_mem f hyU, hvy⟩ rfl

/-- If `f` is coordinatewise lower semicontinuous at `x` and takes finitely many values on a
neighbourhood of `x`, then `toLex ∘ f` is lower semicontinuous at `x`. -/
theorem lowerSemicontinuousAt_toLex
    (hf : ∀ i, LowerSemicontinuousAt (fun y ↦ f y i) x)
    (hfin : ∃ U ∈ 𝓝 x, (f '' U).Finite) :
    LowerSemicontinuousAt (fun y ↦ toLex (f y)) x := by
  rw [← lowerSemicontinuousWithinAt_univ_iff]
  refine lowerSemicontinuousWithinAt_toLex
    (fun i ↦ (lowerSemicontinuousWithinAt_univ_iff).mpr (hf i)) ?_
  rwa [nhdsWithin_univ]

/-- If `f` is coordinatewise lower semicontinuous on `s` and locally takes finitely many values
within `s`, then `toLex ∘ f` is lower semicontinuous on `s`. -/
theorem lowerSemicontinuousOn_toLex
    (hf : ∀ i, LowerSemicontinuousOn (fun y ↦ f y i) s)
    (hfin : ∀ x ∈ s, ∃ U ∈ 𝓝[s] x, (f '' U).Finite) :
    LowerSemicontinuousOn (fun y ↦ toLex (f y)) s :=
  fun x hx ↦ lowerSemicontinuousWithinAt_toLex (fun i ↦ hf i x hx) (hfin x hx)

/-- If `f` is coordinatewise lower semicontinuous and locally takes finitely many values, then
`toLex ∘ f` is lower semicontinuous. -/
theorem lowerSemicontinuous_toLex
    (hf : ∀ i, LowerSemicontinuous (fun y ↦ f y i))
    (hfin : ∀ x, ∃ U ∈ 𝓝 x, (f '' U).Finite) :
    LowerSemicontinuous (fun y ↦ toLex (f y)) :=
  fun x ↦ lowerSemicontinuousAt_toLex (fun i ↦ hf i x) (hfin x)

end LinearOrder

end TauCeti
