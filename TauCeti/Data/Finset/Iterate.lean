/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Iterates of inflationary maps on the finsets of a finite type

A map `f` on the finsets of a finite type `α` that enlarges every finset, `s ⊆ f s`, can grow a
finset `s` strictly only `Fintype.card α - #s` times before it stops. This file records the
resulting bound: once `Fintype.card α ≤ #s + n`, the `n`-th iterate of `f` at `s` is a fixed point
of `f`; in particular the `Fintype.card α`-th iterate is, whatever the starting finset. It is the
termination argument behind every closure computed by "repeat until nothing changes" on a finite
carrier, stated once so that such computations can iterate a fixed number of times and remain
executable.

Mathlib's `Finset.image_iterate_stabilises_le_card` is the analogous statement for the decreasing
sequence of images of a finset under the iterates of a self-map of `α`; here the sequence is
increasing and the map acts on finsets.

## Main results

* `Finset.isFixedPt_iterate_of_card_le_card_add`: for `f` with `s ⊆ f s` for all `s`, the finset
  `f^[n] s` is a fixed point of `f` as soon as `Fintype.card α ≤ #s + n`.
-/

public section

namespace TauCeti

open Finset Function

variable {α : Type*} [Fintype α]

/-- An inflationary self-map of the finsets of a finite type reaches a fixed point from `s` after
`Fintype.card α - #s` iterations: the iterates form an increasing chain of finsets starting at
`s`, and such a chain can grow strictly at most `Fintype.card α - #s` times. Taking
`n = Fintype.card α` gives a bound independent of the starting finset. -/
theorem _root_.Finset.isFixedPt_iterate_of_card_le_card_add {f : Finset α → Finset α}
    (hf : ∀ s, s ⊆ f s) {s : Finset α} {n : ℕ} (hn : Fintype.card α ≤ #s + n) :
    IsFixedPt f (f^[n] s) := by
  -- Until the iterates reach a fixed point, each one is strictly larger than the previous one.
  have key (k : ℕ) : IsFixedPt f (f^[k] s) ∨ #s + k ≤ #(f^[k] s) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      by_cases hk : IsFixedPt f (f^[k] s)
      · exact .inl hk.apply
      · exact .inr ((ih.resolve_left hk).trans_lt
          (card_lt_card ((hf _).ssubset_of_ne (Ne.symm hk))))
  -- Otherwise the `n`-th iterate has `Fintype.card α` elements, so it is `univ`.
  refine (key n).elim id fun h => ?_
  rw [(card_eq_iff_eq_univ _).1 ((card_le_univ _).antisymm (hn.trans h))]
  exact univ_subset_iff.1 (hf _)

end TauCeti
