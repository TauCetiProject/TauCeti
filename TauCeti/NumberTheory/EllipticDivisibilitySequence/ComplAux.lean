/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic.Ring

/-!
# The auxiliary term of the second complement of a normalised EDS

Mathlib defines the second complement of a normalised EDS as a difference,

`complEDS₂ b c d k =
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2)
    - preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2)
    * (if Even k then 1 else b)`,

with the two summands written out inline. This file names the subtracted one,

`complEDS₂Aux b c d m =
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * (if Even m then 1 else b)`,

so that the decomposition `complEDS₂ = (first term) - complEDS₂Aux` can be used as an identity
rather than re-expanded at each use. That decomposition is what expresses the second complement
through the invariant of an elliptic net, and the auxiliary term is an ingredient of the division
polynomial `ω` of a Weierstrass curve.

## Main definitions

* `complEDS₂Aux`: the subtracted summand of Mathlib's `complEDS₂`.

## Main results

* `complEDS₂_eq_sub_complEDS₂Aux`: `complEDS₂` is its first summand minus `complEDS₂Aux`.
* `complEDS₂Aux_mul_b`: one factor of `b` turns the auxiliary term into
  `normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2`. This is the companion of Mathlib's
  `complEDS₂_mul_b`.
* `complEDS₂Aux_zero`, `complEDS₂Aux_one`, `complEDS₂Aux_two`: the values `-1`, `-b` and `0` at
  the base indices.
* `map_complEDS₂Aux`: the auxiliary term is natural in the coefficient ring.

## Implementation notes

The definition is stated with `preNormEDS` and the parity factor `if Even m then 1 else b`, exactly
as in Mathlib's `complEDS₂`, rather than through `normEDS`. This keeps it literally a summand of
Mathlib's definition. Since `normEDS b c d n` is
`preNormEDS (b ^ 4) c d n * (if Even n then b else 1)`, passing to `normEDS` in
`complEDS₂Aux_mul_b` only moves parity factors; the `b ^ 4` rescaling is the same on both sides.

## Provenance

Ported from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `compl₂EDSAux`, `compl₂EDSAux_two`, `compl₂EDSAux_mul_b` and `map_compl₂EDSAux`, which
also appear in Mathlib PR #13057 by the same author. They are renamed here after Mathlib's later
rename `compl₂EDS → complEDS₂`, and kept in the root namespace beside `complEDS₂`, `normEDS` and
`preNormEDS`.
-/

public section

variable {R S : Type*} [CommRing R] [CommRing S] (b c d : R) (m : ℤ)

/-- The subtracted summand of Mathlib's `complEDS₂`, named so that the decomposition of the second
complement into its two terms is available as an identity. -/
def complEDS₂Aux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

/-- The defining formula for `complEDS₂Aux`. It is deliberately not `@[simp]`, so that `simp` does
not undo the naming of the term; rewrite with `complEDS₂_eq_sub_complEDS₂Aux` when the
decomposition of `complEDS₂` is what is wanted. -/
theorem complEDS₂Aux_def : complEDS₂Aux b c d m =
    preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 *
      if Even m then 1 else b := (rfl)

/-- The auxiliary term at `0` is `-1`. -/
@[simp]
theorem complEDS₂Aux_zero : complEDS₂Aux b c d 0 = -1 := by simp [complEDS₂Aux_def]

/-- The auxiliary term at `1` is `-b`. -/
@[simp]
theorem complEDS₂Aux_one : complEDS₂Aux b c d 1 = -b := by simp [complEDS₂Aux_def]

/-- The auxiliary term vanishes at `2`, since its first factor is `preNormEDS _ _ _ 0`. -/
@[simp]
theorem complEDS₂Aux_two : complEDS₂Aux b c d 2 = 0 := by simp [complEDS₂Aux_def]

/-- The second complement is its first summand minus `complEDS₂Aux`. -/
theorem complEDS₂_eq_sub_complEDS₂Aux :
    complEDS₂ b c d m =
      preNormEDS (b ^ 4) c d (m - 1) ^ 2 * preNormEDS (b ^ 4) c d (m + 2) *
        (if Even m then 1 else b) - complEDS₂Aux b c d m := by
  rw [complEDS₂, complEDS₂Aux_def, sub_mul]

/-- **Multiplying the auxiliary term by `b` returns it to the normalised sequence.** The single `b`
converts the auxiliary term's own parity factor into the two that `normEDS` carries at `m - 2` and
`m + 1`: each side contributes `b` for even `m` and `b ^ 2` for odd `m`. Companion of Mathlib's
`complEDS₂_mul_b`. -/
theorem complEDS₂Aux_mul_b :
    complEDS₂Aux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [complEDS₂Aux_def, normEDS, Int.even_add, Int.even_sub, Int.not_even_one, even_two,
    iff_false, iff_true]
  split_ifs <;> ring1

variable {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)

/-- The auxiliary term is natural in the coefficient ring. -/
@[simp]
theorem map_complEDS₂Aux :
    f (complEDS₂Aux b c d m) = complEDS₂Aux (f b) (f c) (f d) m := by
  simp [complEDS₂Aux_def, apply_ite f]
