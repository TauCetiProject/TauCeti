/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Special values of a normalised elliptic divisibility sequence

Mathlib identifies `normEDS (2 : ℤ) 3 2` with the identity sequence and computes its
2-complement. This module transports those identities along `Int.castRingHom` to
arbitrary commutative rings.

## Main results

* `normEDS_two_three_two_eq_intCast`: `normEDS (2 : R) 3 2 = Int.cast`.
* `complEDS₂_two_three_two_eq_two`: the 2-complement is constantly `2` over any
  commutative ring, extending Mathlib's integer-valued result.

## Provenance

Adapted from D. K. Angdinata's `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`
in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`). The upstream file credits David Kurniadi
Angdinata as its author. The special values extend its `normEDS_two_three_two` and
`compl₂EDS_two_three_two` from integers to arbitrary commutative rings.

-/

public section

/-- **The 2-complement of `normEDS 2 3 2` is the constant `2`, over any commutative ring**:
the complement of `n` in `2n` for the integer-cast sequence. -/
@[simp]
theorem complEDS₂_two_three_two_eq_two (R : Type*) [CommRing R] (n : ℤ) :
    complEDS₂ (2 : R) 3 2 n = 2 := by
  have h := map_complEDS₂ (f := Int.castRingHom R) (b := (2 : ℤ)) (c := 3) (d := 2) n
  rw [complEDS₂_two_three_two] at h
  simpa using h.symm

/-- **`normEDS 2 3 2` is the integer cast, over any commutative ring.** The identity on `ℤ`
transported along the unique ring map out of it. -/
@[simp]
theorem normEDS_two_three_two_eq_intCast (R : Type*) [CommRing R] :
    normEDS (2 : R) 3 2 = Int.cast := by
  funext n
  have h := map_normEDS (f := Int.castRingHom R) (b := (2 : ℤ)) (c := 3) (d := 2) n
  rw [normEDS_two_three_two] at h
  simpa using h.symm
