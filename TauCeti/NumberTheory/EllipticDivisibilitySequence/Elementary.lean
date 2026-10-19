/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Vanishing at zero from a nonzerodivisor even term

Mathlib's `IsEllipticSequence.zero` proves vanishing at `0` when `W 2` is a
nonzerodivisor. This module retains the stronger statement: any even term may supply
that hypothesis. Oddness is supplied by Mathlib's `IsEllipticSequence.neg`.

The proof specialises the relator at `(m, m, 2 * m)`. The two outer terms cancel,
leaving `W 0 * W (2 * m) ^ 3 = 0`, so the nonzerodivisor hypothesis forces `W 0 = 0`.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declaration `IsEllSequence.zero`.
The upstream file credits David Kurniadi Angdinata as its author.
-/

public section

open scoped nonZeroDivisors

namespace IsEllipticSequence

variable {R : Type*} [CommRing R] {W : ℤ → R}

/-- **An elliptic sequence vanishes at `0`**, given that some even term is a nonzerodivisor. -/
theorem zero_of_even_mem_nonZeroDivisors (h : IsEllipticSequence W) (m : ℤ)
    (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have key : W 0 * W (2 * m) ^ 3 = 0 := by
    have := h m m (2 * m)
    rw [IsEllipticNet.rel] at this
    ring_nf at this ⊢
    linear_combination this
  exact (pow_mem mem 3).2 _ key

end IsEllipticSequence
