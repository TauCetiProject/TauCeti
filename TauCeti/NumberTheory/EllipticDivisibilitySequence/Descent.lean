/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Recurrence
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# An elliptic net from its two doubling recurrences

For an odd sequence vanishing at zero, with `W 1` and `W 2` nonzerodivisors, the full elliptic
net relation is equivalent to the odd doubling recurrence from `m = 2` and the even doubling
recurrence from `m = 3`. The corresponding elliptic-sequence criterion follows as well.

## Main results

* `IsEllipticNet.of_rel`: the bounded doubling recurrences in relator form imply the net relation.
* `isEllipticNet_iff`: the net relation is equivalent to the two bounded doubling recurrences.
* `isEllipticSequence_iff`: the corresponding equivalence for the three-index sequence relation.

Mathlib's `IsEllipticNet.of_even_odd` supplies the reverse implication once the recurrences
are extended to all integer indices. Oddness reduces negative indices to nonnegative ones,
and the omitted small indices follow from `W 0 = 0` and oddness.

## Provenance

The bounded recurrence criteria adapt D. K. Angdinata's
`IsEllSequence.of_oddRec_evenRec` in `LutzNagell/EllipticDivisibilitySequence.lean`, AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`).
That file credits David Kurniadi Angdinata as its author. The descent is supplied by Mathlib's
`IsEllipticNet.of_even_odd`; the sequence criterion follows by
`IsEllipticNet.isEllipticSequence`.
-/

public section

namespace IsEllipticNet

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {W : ℤ → R}

/-- **An elliptic net from the two doubling recurrences.** A sequence that is odd, vanishes at
`0`, has `W 1` and `W 2` nonzerodivisors, and satisfies the odd recurrence from `m = 2` and the
even one from `m = 3`, satisfies the full four-index relation at *every* quadruple. -/
theorem of_rel (odd : W.Odd) (zero : W 0 = 0) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m : ℤ, 2 ≤ m → rel W (m + 1) m 1 0 = 0)
    (evenRec : ∀ m : ℤ, 3 ≤ m → rel W (m + 1) (m - 1) 1 0 = 0) :
    IsEllipticNet W := by
  have neg (m : ℤ) : W (-m) = -W m := odd m
  apply of_even_odd odd one two
  · intro m
    wlog hm : 0 ≤ m generalizing m
    · have h := this (-m) (by omega)
      rw [rel_even] at h ⊢
      grind only
    by_cases hthree : 3 ≤ m
    · exact evenRec m hthree
    rw [rel_even]
    interval_cases m <;> norm_num [zero, neg] <;> ring
  · intro m
    wlog hm : 0 ≤ m generalizing m
    · have h := this (-m - 1) (by omega)
      rw [rel_odd] at h ⊢
      grind only
    by_cases htwo : 2 ≤ m
    · exact oddRec m htwo
    rw [rel_odd]
    interval_cases m <;> norm_num [zero, neg]

end IsEllipticNet

/-- **Being an elliptic net is exactly satisfying the two doubling recurrences.** For a sequence
that is odd, vanishes at `0` and has `W 1`, `W 2` nonzerodivisors, the **four**-index relation at
every quadruple is equivalent to the odd recurrence from `m = 2` and the even one from `m = 3` —
finitely many equations per index rather than a condition on quadruples.

Under these hypotheses, therefore, being an elliptic net and being an elliptic sequence are the
same condition. They are not the same condition in general: `normEDS b c d` at arbitrary
parameters need not have `W 2 = b` a nonzerodivisor, and Mathlib's `IsEllipticNet.normEDS`
obtains the net there without this equivalence. The reverse implication here uses Mathlib's
`IsEllipticNet.of_even_odd`, via the bounded-index criterion `IsEllipticNet.of_rel`. -/
theorem isEllipticNet_iff {R : Type*} [CommRing R] {W : ℤ → R} (odd : W.Odd) (zero : W 0 = 0)
    (one : W 1 ∈ nonZeroDivisors R) (two : W 2 ∈ nonZeroDivisors R) :
    IsEllipticNet W ↔
      (∀ m : ℤ, 2 ≤ m → W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3)
        ∧ ∀ m : ℤ, 3 ≤ m → W (2 * m) * W 2 * W 1 ^ 2 =
            W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2) := by
  refine ⟨fun h ↦ ⟨fun m _ ↦ h.isEllipticSequence.rel_odd m,
    fun m _ ↦ h.isEllipticSequence.rel_even m⟩, fun ⟨hodd, heven⟩ ↦ ?_⟩
  refine IsEllipticNet.of_rel odd zero one two (fun m hm ↦ ?_) fun m hm ↦ ?_
  · rw [IsEllipticNet.rel_odd]
    linear_combination hodd m hm
  · rw [IsEllipticNet.rel_even]
    linear_combination heven m hm

/-- **Being an elliptic sequence is exactly satisfying the two doubling recurrences.** For a
sequence that is odd, vanishes at `0` and has `W 1`, `W 2` nonzerodivisors, the whole
three-index relation is equivalent to the odd recurrence from `m = 2` and the even one from
`m = 3` — finitely many equations per index rather than a condition on triples.

This is the classical statement, about the predicate `IsEllipticSequence`; `isEllipticNet_iff`
is its four-index strengthening. -/
theorem isEllipticSequence_iff {R : Type*} [CommRing R] {W : ℤ → R} (odd : W.Odd) (zero : W 0 = 0)
    (one : W 1 ∈ nonZeroDivisors R) (two : W 2 ∈ nonZeroDivisors R) :
    IsEllipticSequence W ↔
      (∀ m : ℤ, 2 ≤ m → W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3)
        ∧ ∀ m : ℤ, 3 ≤ m → W (2 * m) * W 2 * W 1 ^ 2 =
            W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2) :=
  ⟨fun h ↦ ⟨fun m _ ↦ h.rel_odd m, fun m _ ↦ h.rel_even m⟩,
    fun h ↦ ((isEllipticNet_iff odd zero one two).mpr h).isEllipticSequence⟩
