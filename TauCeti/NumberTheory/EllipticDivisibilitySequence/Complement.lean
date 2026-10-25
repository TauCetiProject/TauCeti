/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# The complement of a normalised EDS at a divisor

Mathlib's `normEDS_mul_complEDS` proves that the complement witnesses divisibility at
every multiple. This module reindexes that identity at a divisor, using
`Int.ediv_mul_cancel`. The reduced-invariant cancellation in `ReducedInvariant.lean`
uses this form in its residue cases.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at `dev/modular-curves @ 9fec8eba7652`,
the revision pinned for the NagellLutz project in `TauCetiRoadmap/EllipticCurves/README.md`.
The source declaration is `normEDS_mul_complEDS_div`; the upstream file credits David
Kurniadi Angdinata as its author.
-/

public section

variable {R : Type*} [CommRing R] {b c d : R}

/-- **The complement at a divisor.** When `k ∣ n`, the `k`-complement at index `n / k` multiplies
`normEDS b c d k` back up to `normEDS b c d n`. This is the divisor-indexed form of
Mathlib's `normEDS_mul_complEDS`, which is stated at `n * k`. -/
theorem normEDS_mul_complEDS_div (k n : ℤ) (hn : k ∣ n) :
    normEDS b c d k * complEDS b c d k (n / k) = normEDS b c d n := by
  rw [normEDS_mul_complEDS, Int.ediv_mul_cancel hn]
