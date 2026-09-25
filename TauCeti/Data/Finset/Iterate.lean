/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Iterates of inflationary maps on the finsets of a finite type

A map `f` on the finsets of a finite type `α` that enlarges every finset, `s ⊆ f s`, can grow a
finset only `Fintype.card α` times before it stops. This file records the resulting bound: the
`Fintype.card α`-th iterate of `f` at any starting finset is a fixed point of `f`. It is the
termination argument behind every closure computed by "repeat until nothing changes" on a finite
carrier, stated once so that such computations can iterate a fixed number of times and remain
executable.

Mathlib's `Finset.image_iterate_stabilises_le_card` is the analogous statement for the decreasing
sequence of images of a finset under the iterates of a self-map of `α`; here the sequence is
increasing and the map acts on finsets.

## Main results

* `Finset.isFixedPt_iterate_card`: for `f` with `s ⊆ f s` for all `s`, the finset
  `f^[Fintype.card α] s` is a fixed point of `f`.
-/

public section

namespace TauCeti

variable {α : Type*} [Fintype α]

/-- An inflationary self-map of the finsets of a finite type reaches a fixed point after
`Fintype.card α` iterations, whatever the starting finset: the iterates form an increasing chain
of finsets, and such a chain can grow strictly at most `Fintype.card α` times. -/
theorem _root_.Finset.isFixedPt_iterate_card {f : Finset α → Finset α} (hf : ∀ s, s ⊆ f s)
    (s : Finset α) : Function.IsFixedPt f (f^[Fintype.card α] s) := by
  have hsub : ∀ k, f^[k] s ⊆ f^[k + 1] s := fun k => by
    rw [Function.iterate_succ_apply']; exact hf _
  -- The sizes of the iterates form a monotone sequence bounded by `Fintype.card α`, and once two
  -- consecutive iterates have the same size they coincide, so the sequence is constant from there.
  have hmono : Monotone fun k => (f^[k] s).card :=
    monotone_nat_of_le_succ fun k => Finset.card_le_card (hsub k)
  have hstab : ∀ k, (f^[k] s).card = (f^[k + 1] s).card →
      (f^[k + 1] s).card = (f^[k + 2] s).card := fun k hk => by
    have heq : f^[k] s = f^[k + 1] s := Finset.eq_of_subset_of_card_le (hsub k) hk.ge
    rw [Function.iterate_succ_apply' f (k + 1), ← heq, ← Function.iterate_succ_apply' f k s, ← heq]
  have hcard := Nat.stabilises_of_monotone hmono (fun k => Finset.card_le_univ (f^[k] s)) hstab
    (Nat.le_succ (Fintype.card α))
  exact (Finset.eq_of_subset_of_card_le (hf _)
    (by rw [← Function.iterate_succ_apply' f (Fintype.card α) s]; exact hcard.le)).symm

end TauCeti
