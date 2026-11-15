/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Topology.Semicontinuity.Basic

import Mathlib.Order.Filter.Finite

/-!
# Lexicographic semicontinuity of locally finite-valued function families

When a family `f : X → ∀ i, β i` indexed by a well-ordered type `ι` with linearly ordered fibres
`β i` takes only finitely many values near each point, pointwise semicontinuity passes to the
lexicographic total order `Lex (∀ i, β i)`. Near `x`, the set of points `x'` where
`c ≤ toLex (f x')` is covered by the level sets `f x' = v` of the finitely many values `v` of `f`
near `x` with `c ≤ toLex v`; if any such value occurs frequently near `x`, pointwise upper
semicontinuity forces `v ≤ f x` and hence `c ≤ toLex v ≤ toLex (f x)` by `Pi.toLex_monotone`.

In algebraic and analytic geometry, local numerical invariants valued in `ℕ → ℕ` or `ℕ → ℕ∞`
(such as local Hilbert–Samuel functions on a Noetherian scheme) are locally finite-valued and
upper semicontinuous in the pointwise partial order in the sense that `{x | ¬ f y ≤ f x}` is open
for every `y` (or because each coordinate `x ↦ f x i` is upper semicontinuous). The results here
upgrade this to upper semicontinuity for `Lex (∀ i, β i)`, so every lexicographic upper level set
`{x | c ≤ toLex (f x)}` is closed without assuming Noetherianity of `X`.

## Main results

* `TauCeti.upperSemicontinuousWithinAt_toLex_of_nhdsWithin`: local finiteness on `U ∈ 𝓝[s] x`
  together with openness of `{x' | ¬ f y ≤ f x'}` near `x` within `s` for `y ∈ U` implies
  `UpperSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x`.
* `TauCeti.upperSemicontinuous_toLex_of_isOpen_not_le` and
  `TauCeti.upperSemicontinuous_toLex_of_isClosed_le`: global lexicographic upper semicontinuity
  from local finiteness and openness of `{x | ¬ f y ≤ f x}` (or closedness of `{x | f y ≤ f x}`).
* `TauCeti.upperSemicontinuousWithinAt_toLex`, `TauCeti.upperSemicontinuousAt_toLex`,
  `TauCeti.upperSemicontinuousOn_toLex`, `TauCeti.upperSemicontinuous_toLex`: coordinatewise upper
  semicontinuity plus local finiteness implies lexicographic upper semicontinuity.
* `TauCeti.isClosed_setOf_le_toLex`: lexicographic upper level sets `{x | c ≤ toLex (f x)}` are
  closed.
* `TauCeti.lowerSemicontinuousWithinAt_toLex_of_nhdsWithin`,
  `TauCeti.lowerSemicontinuousWithinAt_toLex`, `TauCeti.lowerSemicontinuousAt_toLex`,
  `TauCeti.lowerSemicontinuousOn_toLex`, `TauCeti.lowerSemicontinuous_toLex`,
  `TauCeti.lowerSemicontinuous_toLex_of_isOpen_not_ge`: the dual lower-semicontinuity statements.

## References

* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *ℚ-universal desingularization*,
  Asian J. Math. 15 (2011), 229–250, §6.1.
-/

public section

open Filter Set Topology

namespace TauCeti

section UpperSemicontinuous

variable {X ι : Type*} {β : ι → Type*} [TopologicalSpace X] [LinearOrder ι] [WellFoundedLT ι]
  [∀ i, LinearOrder (β i)] {f : X → ∀ i, β i} {s : Set X} {x : X}

/-- If `f` takes finitely many values on a neighborhood `U ∈ 𝓝[s] x` and whenever `y ∈ U` fails
`f y ≤ f x` it also fails `f y ≤ f x'` near `x` within `s`, then `x' ↦ toLex (f x')` is upper
semicontinuous within `s` at `x`. -/
theorem upperSemicontinuousWithinAt_toLex_of_nhdsWithin {U : Set X} (hU : U ∈ 𝓝[s] x)
    (hfin : (f '' U).Finite)
    (hle : ∀ y ∈ U, ¬ f y ≤ f x → ∀ᶠ x' in 𝓝[s] x, ¬ f y ≤ f x') :
    UpperSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x := by
  refine UpperSemicontinuousWithinAt.of_frequently fun c hc ↦ ?_
  have hS : {v ∈ f '' U | c ≤ toLex v}.Finite := hfin.subset fun _ hv ↦ hv.1
  have hfreq : ∃ᶠ x' in 𝓝[s] x, ∃ v ∈ {v ∈ f '' U | c ≤ toLex v}, f x' = v :=
    (hc.and_eventually hU).mono fun x' ⟨hcx', hx'U⟩ ↦
      ⟨f x', ⟨mem_image_of_mem f hx'U, hcx'⟩, rfl⟩
  obtain ⟨v, ⟨⟨y, hyU, rfl⟩, hcv⟩, hfv⟩ := (hS.frequently_exists.mp hfreq)
  have hyx : f y ≤ f x := by
    by_contra hnot
    exact (hfv.and_eventually (hle y hyU hnot)).exists.elim fun x' ⟨heq, hne⟩ ↦ hne heq.ge
  exact hcv.trans (Pi.toLex_monotone hyx)

/-- At a point where `f` is locally finite-valued and `{x' | ¬ f y ≤ f x'}` is a neighborhood of
`x` whenever `¬ f y ≤ f x`, `x' ↦ toLex (f x')` is upper semicontinuous at `x`. -/
theorem upperSemicontinuousAt_toLex_of_nhds {U : Set X} (hU : U ∈ 𝓝 x) (hfin : (f '' U).Finite)
    (hle : ∀ y ∈ U, ¬ f y ≤ f x → ∀ᶠ x' in 𝓝 x, ¬ f y ≤ f x') :
    UpperSemicontinuousAt (fun x' ↦ toLex (f x')) x := by
  rw [← upperSemicontinuousWithinAt_univ_iff]
  rw [← nhdsWithin_univ] at hU
  exact upperSemicontinuousWithinAt_toLex_of_nhdsWithin hU hfin fun y hy hnot ↦ by
    rw [nhdsWithin_univ]
    exact hle y hy hnot

/-- **Bierstone–Milman–Temkin §6.1**: if `f : X → ∀ i, β i` is locally finite-valued and
`{x | ¬ f y ≤ f x}` is open for every `y`, then `x ↦ toLex (f x)` is upper semicontinuous. -/
theorem upperSemicontinuous_toLex_of_isOpen_not_le (hfin : ∀ x, ∃ U ∈ 𝓝 x, (f '' U).Finite)
    (hopen : ∀ y, IsOpen {x | ¬ f y ≤ f x}) :
    UpperSemicontinuous fun x ↦ toLex (f x) := by
  rw [upperSemicontinuous_iff]
  intro x
  obtain ⟨U, hU, hfinU⟩ := hfin x
  exact upperSemicontinuousAt_toLex_of_nhds hU hfinU fun y _ hyx ↦
    (hopen y).mem_nhds hyx

/-- If `f : X → ∀ i, β i` is locally finite-valued and every pointwise upper level set
`{x | f y ≤ f x}` is closed, then `x ↦ toLex (f x)` is upper semicontinuous. -/
theorem upperSemicontinuous_toLex_of_isClosed_le (hfin : ∀ x, ∃ U ∈ 𝓝 x, (f '' U).Finite)
    (hclosed : ∀ y, IsClosed {x | f y ≤ f x}) :
    UpperSemicontinuous fun x ↦ toLex (f x) :=
  upperSemicontinuous_toLex_of_isOpen_not_le hfin fun y ↦ (hclosed y).isOpen_compl

/-- If `f` is locally finite-valued within `s` at `x` and each coordinate `x' ↦ f x' i` is upper
semicontinuous within `s` at `x`, then `x' ↦ toLex (f x')` is upper semicontinuous within `s` at
`x`. -/
theorem upperSemicontinuousWithinAt_toLex (hfin : ∃ U ∈ 𝓝[s] x, (f '' U).Finite)
    (hf : ∀ i, UpperSemicontinuousWithinAt (fun x' ↦ f x' i) s x) :
    UpperSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x := by
  obtain ⟨U, hU, hfinU⟩ := hfin
  refine upperSemicontinuousWithinAt_toLex_of_nhdsWithin hU hfinU fun y _ hnot ↦ ?_
  rw [Pi.le_def, not_forall] at hnot
  obtain ⟨i, hi⟩ := hnot
  exact (hf i (f y i) (lt_of_not_ge hi)).mono fun x' hx' hle ↦ hx'.not_ge (hle i)

/-- If `f` is locally finite-valued at `x` and each coordinate `x' ↦ f x' i` is upper
semicontinuous at `x`, then `x' ↦ toLex (f x')` is upper semicontinuous at `x`. -/
theorem upperSemicontinuousAt_toLex (hfin : ∃ U ∈ 𝓝 x, (f '' U).Finite)
    (hf : ∀ i, UpperSemicontinuousAt (fun x' ↦ f x' i) x) :
    UpperSemicontinuousAt (fun x' ↦ toLex (f x')) x := by
  rw [← upperSemicontinuousWithinAt_univ_iff]
  refine upperSemicontinuousWithinAt_toLex ?_ fun i ↦ (hf i).upperSemicontinuousWithinAt univ
  rwa [nhdsWithin_univ]

/-- If `f` is locally finite-valued on `s` and each coordinate `x' ↦ f x' i` is upper
semicontinuous on `s`, then `x' ↦ toLex (f x')` is upper semicontinuous on `s`. -/
theorem upperSemicontinuousOn_toLex (hfin : ∀ x ∈ s, ∃ U ∈ 𝓝[s] x, (f '' U).Finite)
    (hf : ∀ i, UpperSemicontinuousOn (fun x' ↦ f x' i) s) :
    UpperSemicontinuousOn (fun x' ↦ toLex (f x')) s :=
  fun x hx ↦ upperSemicontinuousWithinAt_toLex (hfin x hx) fun i ↦ hf i x hx

/-- If `f` is locally finite-valued and each coordinate `x ↦ f x i` is upper semicontinuous, then
`x ↦ toLex (f x)` is upper semicontinuous. -/
theorem upperSemicontinuous_toLex (hfin : ∀ x, ∃ U ∈ 𝓝 x, (f '' U).Finite)
    (hf : ∀ i, UpperSemicontinuous fun x ↦ f x i) :
    UpperSemicontinuous fun x ↦ toLex (f x) :=
  upperSemicontinuous_iff.mpr fun x ↦
    upperSemicontinuousAt_toLex (hfin x) fun i ↦ (hf i).upperSemicontinuousAt x

/-- For a locally finite-valued family `f` with upper semicontinuous coordinates, every
lexicographic upper level set `{x | c ≤ toLex (f x)}` is closed. -/
theorem isClosed_setOf_le_toLex (hfin : ∀ x, ∃ U ∈ 𝓝 x, (f '' U).Finite)
    (hf : ∀ i, UpperSemicontinuous fun x ↦ f x i) (c : Lex (∀ i, β i)) :
    IsClosed {x | c ≤ toLex (f x)} :=
  (upperSemicontinuous_toLex hfin hf).isClosed_preimage c

end UpperSemicontinuous

section LowerSemicontinuous

variable {X ι : Type*} {β : ι → Type*} [TopologicalSpace X] [LinearOrder ι] [WellFoundedLT ι]
  [∀ i, LinearOrder (β i)] {f : X → ∀ i, β i} {s : Set X} {x : X}

/-- Dual of `upperSemicontinuousWithinAt_toLex_of_nhdsWithin`: local finiteness on `U ∈ 𝓝[s] x`
together with openness of `{x' | ¬ f x' ≤ f y}` near `x` within `s` for `y ∈ U` implies
`LowerSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x`. -/
theorem lowerSemicontinuousWithinAt_toLex_of_nhdsWithin {U : Set X} (hU : U ∈ 𝓝[s] x)
    (hfin : (f '' U).Finite)
    (hle : ∀ y ∈ U, ¬ f x ≤ f y → ∀ᶠ x' in 𝓝[s] x, ¬ f x' ≤ f y) :
    LowerSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x := by
  refine LowerSemicontinuousWithinAt.of_frequently fun c hc ↦ ?_
  have hS : {v ∈ f '' U | toLex v ≤ c}.Finite := hfin.subset fun _ hv ↦ hv.1
  have hfreq : ∃ᶠ x' in 𝓝[s] x, ∃ v ∈ {v ∈ f '' U | toLex v ≤ c}, f x' = v :=
    (hc.and_eventually hU).mono fun x' ⟨hcx', hx'U⟩ ↦
      ⟨f x', ⟨mem_image_of_mem f hx'U, hcx'⟩, rfl⟩
  obtain ⟨v, ⟨⟨y, hyU, rfl⟩, hvc⟩, hfv⟩ := hS.frequently_exists.mp hfreq
  have hxy : f x ≤ f y := by
    by_contra hnot
    exact (hfv.and_eventually (hle y hyU hnot)).exists.elim fun x' ⟨heq, hne⟩ ↦ hne heq.le
  exact (Pi.toLex_monotone hxy).trans hvc

/-- Dual of `upperSemicontinuous_toLex_of_isOpen_not_le`: if `f` is locally finite-valued and
`{x | ¬ f x ≤ f y}` is open for every `y`, then `x ↦ toLex (f x)` is lower semicontinuous. -/
theorem lowerSemicontinuous_toLex_of_isOpen_not_ge (hfin : ∀ x, ∃ U ∈ 𝓝 x, (f '' U).Finite)
    (hopen : ∀ y, IsOpen {x | ¬ f x ≤ f y}) :
    LowerSemicontinuous fun x ↦ toLex (f x) := by
  rw [lowerSemicontinuous_iff]
  intro x
  obtain ⟨U, hU, hfinU⟩ := hfin x
  rw [← lowerSemicontinuousWithinAt_univ_iff]
  rw [← nhdsWithin_univ] at hU
  refine lowerSemicontinuousWithinAt_toLex_of_nhdsWithin hU hfinU fun y _ hxy ↦ ?_
  rw [nhdsWithin_univ]
  exact (hopen y).mem_nhds hxy

/-- If `f` is locally finite-valued within `s` at `x` and each coordinate `x' ↦ f x' i` is lower
semicontinuous within `s` at `x`, then `x' ↦ toLex (f x')` is lower semicontinuous within `s` at
`x`. -/
theorem lowerSemicontinuousWithinAt_toLex (hfin : ∃ U ∈ 𝓝[s] x, (f '' U).Finite)
    (hf : ∀ i, LowerSemicontinuousWithinAt (fun x' ↦ f x' i) s x) :
    LowerSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x := by
  obtain ⟨U, hU, hfinU⟩ := hfin
  refine lowerSemicontinuousWithinAt_toLex_of_nhdsWithin hU hfinU fun y _ hnot ↦ ?_
  rw [Pi.le_def, not_forall] at hnot
  obtain ⟨i, hi⟩ := hnot
  exact (hf i (f y i) (lt_of_not_ge hi)).mono fun x' hx' hle ↦ hx'.not_ge (hle i)

/-- If `f` is locally finite-valued at `x` and each coordinate `x' ↦ f x' i` is lower
semicontinuous at `x`, then `x' ↦ toLex (f x')` is lower semicontinuous at `x`. -/
theorem lowerSemicontinuousAt_toLex (hfin : ∃ U ∈ 𝓝 x, (f '' U).Finite)
    (hf : ∀ i, LowerSemicontinuousAt (fun x' ↦ f x' i) x) :
    LowerSemicontinuousAt (fun x' ↦ toLex (f x')) x := by
  rw [← lowerSemicontinuousWithinAt_univ_iff]
  refine lowerSemicontinuousWithinAt_toLex ?_ fun i ↦ (hf i).lowerSemicontinuousWithinAt univ
  rwa [nhdsWithin_univ]

/-- If `f` is locally finite-valued on `s` and each coordinate `x' ↦ f x' i` is lower
semicontinuous on `s`, then `x' ↦ toLex (f x')` is lower semicontinuous on `s`. -/
theorem lowerSemicontinuousOn_toLex (hfin : ∀ x ∈ s, ∃ U ∈ 𝓝[s] x, (f '' U).Finite)
    (hf : ∀ i, LowerSemicontinuousOn (fun x' ↦ f x' i) s) :
    LowerSemicontinuousOn (fun x' ↦ toLex (f x')) s :=
  fun x hx ↦ lowerSemicontinuousWithinAt_toLex (hfin x hx) fun i ↦ hf i x hx

/-- If `f` is locally finite-valued and each coordinate `x ↦ f x i` is lower semicontinuous, then
`x ↦ toLex (f x)` is lower semicontinuous. -/
theorem lowerSemicontinuous_toLex (hfin : ∀ x, ∃ U ∈ 𝓝 x, (f '' U).Finite)
    (hf : ∀ i, LowerSemicontinuous fun x ↦ f x i) :
    LowerSemicontinuous fun x ↦ toLex (f x) :=
  lowerSemicontinuous_iff.mpr fun x ↦
    lowerSemicontinuousAt_toLex (hfin x) fun i ↦ (hf i).lowerSemicontinuousAt x

end LowerSemicontinuous

end TauCeti
