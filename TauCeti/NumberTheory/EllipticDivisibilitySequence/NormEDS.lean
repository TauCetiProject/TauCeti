/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Universal
import TauCeti.NumberTheory.EllipticDivisibilitySequence.Ext

/-!
# Special values of a normalised elliptic divisibility sequence

Mathlib proves that `normEDS b c d` is an elliptic net and an elliptic sequence, via
`IsEllipticNet.normEDS` and `IsEllipticSequence.normEDS`. This file identifies the
specialisation `normEDS 2 3 2` with the integer-cast sequence and uses it to show that the
universal normalised EDS vanishes only at zero.

## Main results

* `normEDS_two_three_two_eq_intCast`: `normEDS (2 : R) 3 2 = Int.cast` over any commutative ring.
* `normEDS_two_three_two_eq_id`: its `R = ℤ` case, used to specialise the universal parameters.
  Only the general form is a simp lemma, so the two statements do not compete as rewrites.
* `complEDS₂_two_three_two`: the 2-complement of the integer-cast sequence is the constant `2`.
* `universalNormEDS_ne_zero`: the universal sequence vanishes only at `0`.

The identity on `ℤ` follows from `IsEllipticSequence.ext`: the two elliptic sequences agree at
`1, 2, 3, 4`, and the first two values `1` and `2` are nonzerodivisors in `ℤ`. Transport along
`Int.castRingHom` gives the general identity. Specialising the universal parameters at `(2, 3, 2)`
then proves nonvanishing.

The nonvanishing lemma lives here rather than beside the definition in `Universal.lean` because
it depends on the special-value identity, which uses `IsEllipticSequence.ext` from `Ext.lean`.

## Provenance

Adapted from D. K. Angdinata's `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`
in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`). That file's header reads `Authors: David Kurniadi
Angdinata`; following this repository's convention, upstream authorship is credited here.

`normEDS_two_three_two_eq_id` adapts its `normEDS_two_three_two` (`:1236`), renamed to state its
conclusion. That declaration is byte-identical at the roadmap's NagellLutz pin
(`dev/modular-curves @ 9fec8eba7652`, `:1235`). Its proof uses `IsEllipticSequence.id` in place
of the deprecated `isEllSequence_id` alias and discharges the four base values with `simp`.

`complEDS₂_two_three_two` adapts that same file's `compl₂EDS_two_three_two` (`:1243`, at the
`main` revision named above), restated over an arbitrary commutative ring — the source states
only the `ℤ` case — and rerouted: the `ℤ` proof reads the value off Mathlib's `complEDS₂_mul_b`
at the identity sequence, with no case split, where the source cancels `n` off
`normEDS_mul_complEDS₂` behind an `n = 0` split; the general form transports along
`Int.castRingHom`, exactly as `normEDS_two_three_two_eq_intCast` above.

`universalNormEDS_ne_zero` adapts the same file's `universalNormEDS_ne_zero` (`:1251`) at the
roadmap's NagellLutz pin `dev/modular-curves @ 9fec8eba7652`. One departure: the source proves it
by `simp only [universalNormEDS, …]`, unfolding the definition. That does not port —
`universalNormEDS`'s body is unexposed across module boundaries — so the proof goes through the
`@[simp]` equation lemma instead, which is also why it collapses to `simpa`. The source's adjacent
`universalNormEDS_mem_nonZeroDivisors` (`:1258`) is not ported: apply
`mem_nonZeroDivisors_of_ne_zero` to the nonvanishing lemma when needed.
-/

public section

open MvPolynomial NormEDSParam

/-- **`normEDS 2 3 2` is the identity sequence on `ℤ`.** -/
theorem normEDS_two_three_two_eq_id : normEDS (2 : ℤ) 3 2 = id := by
  refine (IsEllipticSequence.normEDS 2 3 2).ext IsEllipticSequence.id ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

/-- The 2-complement of the identity sequence on `ℤ` is the constant `2`. -/
private theorem complEDS₂_two_three_two_int (n : ℤ) : complEDS₂ (2 : ℤ) 3 2 n = 2 := by
  -- Read off `complEDS₂_mul_b`, whose right side is `4` once `normEDS 2 3 2 = id`.
  have h := complEDS₂_mul_b (b := (2 : ℤ)) (c := 3) (d := 2) n
  rw [normEDS_two_three_two_eq_id] at h
  simp only [id_eq] at h
  -- `omega` is linear, so the cubic right side must first collapse to the constant it equals.
  have h4 : (n - 1) ^ 2 * (n + 2) - (n - 2) * (n + 1) ^ 2 = 4 := by ring
  rw [h4] at h
  omega

/-- **The 2-complement of `normEDS 2 3 2` is the constant `2`, over any commutative ring**:
the complement of `n` in `2n` for the integer-cast sequence. -/
@[simp]
theorem complEDS₂_two_three_two (R : Type*) [CommRing R] (n : ℤ) :
    complEDS₂ (2 : R) 3 2 n = 2 := by
  have h := map_complEDS₂ (f := Int.castRingHom R) (b := (2 : ℤ)) (c := 3) (d := 2) n
  rw [complEDS₂_two_three_two_int] at h
  simpa using h.symm

/-- **`normEDS 2 3 2` is the integer cast, over any commutative ring.** The identity on `ℤ`
transported along the unique ring map out of it. -/
@[simp]
theorem normEDS_two_three_two_eq_intCast (R : Type*) [CommRing R] :
    normEDS (2 : R) 3 2 = Int.cast := by
  funext n
  have h := map_normEDS (f := Int.castRingHom R) (b := (2 : ℤ)) (c := 3) (d := 2) n
  rw [normEDS_two_three_two_eq_id] at h
  simpa using h.symm

/-- **The universal normalised EDS is nonzero away from `0`.** Specialising the three
indeterminates at `(2, 3, 2)` sends `universalNormEDS n` to `n` itself, by
`normEDS_two_three_two_eq_id`, so a vanishing value forces a vanishing index. -/
theorem universalNormEDS_ne_zero {n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0 := fun h ↦ hn <| by
  apply_fun aeval (NormEDSParam.rec (2 : ℤ) 3 2) at h
  simpa using h

