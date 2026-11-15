/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lexicographic semicontinuity of locally finitely-valued families

For a well-founded linearly ordered index type `ι` and linearly ordered coordinate spaces `β i`,
pointwise semicontinuity of the coordinate functions `x ↦ H x i` of `H : X → ∀ i, β i` does not by
itself make `x ↦ toLex (H x)` semicontinuous: on `ℝ` with the Euclidean topology, `x ↦ ![x, 0]` is
continuous in each coordinate, yet `toLex ![0, 0] < toLex ![0, 1] < toLex ![x, 0]` for every
`0 < x`.

When `H` locally takes only finitely many values near `x`, however, coordinatewise upper (or lower)
semicontinuity implies upper (or lower) semicontinuity of `x ↦ toLex (H x)`: on a neighborhood `U`
where `H '' U` is finite, only finitely many attained values `w ∈ H '' U` satisfy `v ≤ toLex w`, and
each strictly larger attained value exceeds `H x` at the least coordinate where they differ. In
global form, each closed lexicographic upper set `{x | v ≤ toLex (H x)}` is locally a finite union
of closed pointwise upper sets `{x | w ≤ H x}`.

## Main results

* `TauCeti.upperSemicontinuousWithinAt_toLex`, `TauCeti.upperSemicontinuousAt_toLex`,
  `TauCeti.upperSemicontinuousOn_toLex`, `TauCeti.upperSemicontinuous_toLex`: coordinatewise upper
  semicontinuity together with local finiteness of attained values implies upper semicontinuity in
  the lexicographic order `Lex (∀ i, β i)`.
* `TauCeti.isClosed_le_toLex`: if each coordinate upper set `{x | c ≤ H x i}` is closed and `H`
  locally takes finitely many values, then every lexicographic upper set `{x | v ≤ toLex (H x)}` is
  closed.
* `TauCeti.lowerSemicontinuousWithinAt_toLex`, `TauCeti.lowerSemicontinuousAt_toLex`,
  `TauCeti.lowerSemicontinuousOn_toLex`, `TauCeti.lowerSemicontinuous_toLex`: the dual results for
  lower semicontinuity.

## References

* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *ℚ-universal desingularization*,
  Asian J. Math. 15 (2011), no. 2, 229–250, §6.1.
-/

public section

open Filter Set Topology

namespace TauCeti

section Semicontinuity

variable {X ι : Type*} [TopologicalSpace X] [LinearOrder ι] [WellFoundedLT ι]
  {β : ι → Type*} [∀ i, LinearOrder (β i)] {H : X → ∀ i, β i} {s : Set X} {x : X}

/-- If `H : X → ∀ i, β i` is coordinatewise upper semicontinuous within `s` at `x` and takes
finitely many values on some neighborhood of `x` within `s`, then `y ↦ toLex (H y)` is upper
semicontinuous within `s` at `x`. -/
theorem upperSemicontinuousWithinAt_toLex
    (hH : ∀ i, UpperSemicontinuousWithinAt (H · i) s x)
    (hfin : ∃ U ∈ 𝓝[s] x, (H '' U).Finite) :
    UpperSemicontinuousWithinAt (fun y ↦ toLex (H y)) s x := by
  intro v hv
  obtain ⟨U, hU, hUfin⟩ := hfin
  let S : Set (∀ i, β i) := {w ∈ H '' U | v ≤ toLex w}
  have hSfin : S.Finite := hUfin.subset fun _ hw ↦ hw.1
  have hne : ∀ w ∈ S, ∀ᶠ y in 𝓝[s] x, H y ≠ w := by
    intro w hw
    obtain ⟨i, _, hi⟩ : toLex (H x) < toLex w := hv.trans_le hw.2
    exact (hH i (w i) hi).mono fun y hy hEq ↦ hy.ne (congrFun hEq i)
  filter_upwards [hU, hSfin.eventually_all.mpr hne] with y hyU hyS
  exact lt_of_not_ge fun hle ↦ hyS (H y) ⟨mem_image_of_mem H hyU, hle⟩ rfl

/-- If `H : X → ∀ i, β i` is coordinatewise upper semicontinuous at `x` and takes finitely many
values on some neighborhood of `x`, then `y ↦ toLex (H y)` is upper semicontinuous at `x`. -/
theorem upperSemicontinuousAt_toLex
    (hH : ∀ i, UpperSemicontinuousAt (H · i) x)
    (hfin : ∃ U ∈ 𝓝 x, (H '' U).Finite) :
    UpperSemicontinuousAt (fun y ↦ toLex (H y)) x := by
  rw [← upperSemicontinuousWithinAt_univ_iff]
  refine upperSemicontinuousWithinAt_toLex
    (fun i ↦ (hH i).upperSemicontinuousWithinAt univ) ?_
  rwa [nhdsWithin_univ]

/-- If `H : X → ∀ i, β i` is coordinatewise upper semicontinuous on `s` and locally takes finitely
many values on `s`, then `y ↦ toLex (H y)` is upper semicontinuous on `s`. -/
theorem upperSemicontinuousOn_toLex
    (hH : ∀ i, UpperSemicontinuousOn (H · i) s)
    (hfin : ∀ x ∈ s, ∃ U ∈ 𝓝[s] x, (H '' U).Finite) :
    UpperSemicontinuousOn (fun y ↦ toLex (H y)) s :=
  fun x hx ↦ upperSemicontinuousWithinAt_toLex (fun i ↦ hH i x hx) (hfin x hx)

/-- If `H : X → ∀ i, β i` is coordinatewise upper semicontinuous and locally takes finitely many
values, then `y ↦ toLex (H y)` is upper semicontinuous. -/
theorem upperSemicontinuous_toLex
    (hH : ∀ i, UpperSemicontinuous (H · i))
    (hfin : ∀ x, ∃ U ∈ 𝓝 x, (H '' U).Finite) :
    UpperSemicontinuous (fun y ↦ toLex (H y)) :=
  fun x ↦ upperSemicontinuousAt_toLex (fun i ↦ hH i x) (hfin x)

/-- If every coordinate upper set `{x | c ≤ H x i}` is closed and `H` locally takes finitely many
values, then every lexicographic upper set `{x | v ≤ toLex (H x)}` is closed. -/
theorem isClosed_le_toLex
    (hH : ∀ i c, IsClosed {x | c ≤ H x i})
    (hfin : ∀ x, ∃ U ∈ 𝓝 x, (H '' U).Finite) (v : Lex (∀ i, β i)) :
    IsClosed {x | v ≤ toLex (H x)} :=
  (upperSemicontinuous_toLex
    (fun i ↦ upperSemicontinuous_iff_isClosed_preimage.mpr (hH i)) hfin).isClosed_preimage v

/-- If `H : X → ∀ i, β i` is coordinatewise lower semicontinuous within `s` at `x` and takes
finitely many values on some neighborhood of `x` within `s`, then `y ↦ toLex (H y)` is lower
semicontinuous within `s` at `x`. -/
theorem lowerSemicontinuousWithinAt_toLex
    (hH : ∀ i, LowerSemicontinuousWithinAt (H · i) s x)
    (hfin : ∃ U ∈ 𝓝[s] x, (H '' U).Finite) :
    LowerSemicontinuousWithinAt (fun y ↦ toLex (H y)) s x := by
  intro v ⟨i, hv_eq, hvi⟩
  obtain ⟨U, hU, hUfin⟩ := hfin
  let dual : (∀ i, β i) → ∀ i, (β i)ᵒᵈ := fun w j ↦ OrderDual.toDual (w j)
  have hUfin' : ((dual ∘ H) '' U).Finite := by
    rw [image_comp]
    exact hUfin.image dual
  have hlex := upperSemicontinuousWithinAt_toLex (H := dual ∘ H) hH ⟨U, hU, hUfin'⟩
    (toLex (dual (ofLex v)))
    ⟨i, fun j hj ↦ congrArg OrderDual.toDual (hv_eq j hj).symm, hvi⟩
  exact hlex.mono fun y ⟨k, hk_eq, hky⟩ ↦
    ⟨k, fun j hj ↦ OrderDual.toDual_inj.mp (hk_eq j hj).symm, hky⟩

/-- If `H : X → ∀ i, β i` is coordinatewise lower semicontinuous at `x` and takes finitely many
values on some neighborhood of `x`, then `y ↦ toLex (H y)` is lower semicontinuous at `x`. -/
theorem lowerSemicontinuousAt_toLex
    (hH : ∀ i, LowerSemicontinuousAt (H · i) x)
    (hfin : ∃ U ∈ 𝓝 x, (H '' U).Finite) :
    LowerSemicontinuousAt (fun y ↦ toLex (H y)) x := by
  rw [← lowerSemicontinuousWithinAt_univ_iff]
  refine lowerSemicontinuousWithinAt_toLex
    (fun i ↦ (hH i).lowerSemicontinuousWithinAt univ) ?_
  rwa [nhdsWithin_univ]

/-- If `H : X → ∀ i, β i` is coordinatewise lower semicontinuous on `s` and locally takes finitely
many values on `s`, then `y ↦ toLex (H y)` is lower semicontinuous on `s`. -/
theorem lowerSemicontinuousOn_toLex
    (hH : ∀ i, LowerSemicontinuousOn (H · i) s)
    (hfin : ∀ x ∈ s, ∃ U ∈ 𝓝[s] x, (H '' U).Finite) :
    LowerSemicontinuousOn (fun y ↦ toLex (H y)) s :=
  fun x hx ↦ lowerSemicontinuousWithinAt_toLex (fun i ↦ hH i x hx) (hfin x hx)

/-- If `H : X → ∀ i, β i` is coordinatewise lower semicontinuous and locally takes finitely many
values, then `y ↦ toLex (H y)` is lower semicontinuous. -/
theorem lowerSemicontinuous_toLex
    (hH : ∀ i, LowerSemicontinuous (H · i))
    (hfin : ∀ x, ∃ U ∈ 𝓝 x, (H '' U).Finite) :
    LowerSemicontinuous (fun y ↦ toLex (H y)) :=
  fun x ↦ lowerSemicontinuousAt_toLex (fun i ↦ hH i x) (hfin x)

end Semicontinuity

end TauCeti
