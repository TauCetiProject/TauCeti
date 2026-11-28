/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import TauCeti.RingTheory.WittVector.Regular.Basic

import TauCeti.RingTheory.Regular.RegularSequence
import TauCeti.RingTheory.WittVector.Units

/-!
# Regular pairs in Witt vectors of a perfect ring

Let `R` be a perfect ring of characteristic `p` and `𝕎 R = WittVector p R` its ring of `p`-typical
Witt vectors. Combining the scalar and quotient regularity results of
`TauCeti.RingTheory.WittVector.Regular.Basic` with `RingTheory.Sequence`, this file shows that
whenever `x.coeff 0 ∈ R⁰`:

* both `[p, x]` and `[x, p]` are weakly regular sequences on `𝕎 R`;
* when in addition `¬ IsUnit (x.coeff 0)` (in particular when `x` is killed by a homomorphism to a
  nontrivial ring), both `[p, x]` and `[x, p]` are regular sequences on `𝕎 R`.

## Main results

* `WittVector.isWeaklyRegular_pair_natCast_of_coeff_zero` and
  `WittVector.isWeaklyRegular_pair_of_coeff_zero`: `[p, x]` and `[x, p]` are weakly regular.
* `WittVector.isRegular_natCast_cons_singleton`,
  `WittVector.isRegular_natCast_cons_singleton_of_map_eq_zero`, and
  `WittVector.isRegular_pair_of_coeff_zero`: `[p, x]` and `[x, p]` are regular when
  `x.coeff 0 ∈ R⁰` and `¬ IsUnit (x.coeff 0)`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Proposition 3.17 and Lemma 3.23.
-/

public section

namespace WittVector

open Ideal RingTheory.Sequence
open scoped nonZeroDivisors

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

local notation "𝕎" => WittVector p

/-- If `x.coeff 0 ∈ R⁰`, then `[p, x]` is a weakly regular sequence on `𝕎 R`. -/
theorem isWeaklyRegular_pair_natCast_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰) :
    IsWeaklyRegular (𝕎 R) [(p : 𝕎 R), x] :=
  IsWeaklyRegular.cons isSMulRegular_natCast
    ((isWeaklyRegular_singleton_iff _ x).mpr ((isSMulRegular_quotSMulTop_natCast_iff x).mpr hx))

/-- If `x.coeff 0 ∈ R⁰`, then `[x, p]` is a weakly regular sequence on `𝕎 R`. -/
theorem isWeaklyRegular_pair_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰) :
    IsWeaklyRegular (𝕎 R) [x, (p : 𝕎 R)] :=
  IsWeaklyRegular.cons (isSMulRegular_of_coeff_zero hx)
    ((isWeaklyRegular_singleton_iff _ (p : 𝕎 R)).mpr
      (isSMulRegular_quotSMulTop_natCast_of_coeff_zero hx))

/-- **Regular pairs `(p, x)`.** Over a perfect ring `R` of characteristic `p`, if the zeroth Witt
coordinate of `x : 𝕎 R` is a nonzerodivisor and not a unit, then `p, x` is a regular sequence in
`𝕎 R`. -/
theorem isRegular_natCast_cons_singleton (x : 𝕎 R) (hx : x.coeff 0 ∈ R⁰)
    (hu : ¬IsUnit (x.coeff 0)) : IsRegular (𝕎 R) [(p : 𝕎 R), x] :=
  (isRegular_pair_iff_isWeaklyRegular_of_span_ne_top
    ((span_pair_natCast_ne_top_iff x).mpr hu)).mpr
      (isWeaklyRegular_pair_natCast_of_coeff_zero hx)

/-- If the zeroth Witt coordinate of `x : 𝕎 R` is a nonzerodivisor and `x` is killed by a ring
homomorphism to a nontrivial ring, then `p, x` is a regular sequence in `𝕎 R`. -/
theorem isRegular_natCast_cons_singleton_of_map_eq_zero (x : 𝕎 R) (hx : x.coeff 0 ∈ R⁰)
    {B : Type*} [CommRing B] [Nontrivial B] (f : 𝕎 R →+* B) (hf : f x = 0) :
    IsRegular (𝕎 R) [(p : 𝕎 R), x] := by
  refine isRegular_natCast_cons_singleton x hx fun hu ↦ ?_
  have := (isUnit_iff_isUnit_coeff_zero.mpr hu).map f
  rw [hf] at this
  exact not_isUnit_zero this

/-- If `x.coeff 0 ∈ R⁰` and `¬ IsUnit (x.coeff 0)`, then `[x, p]` is a regular sequence on `𝕎 R`.
-/
theorem isRegular_pair_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰)
    (hnu : ¬ IsUnit (x.coeff 0)) : IsRegular (𝕎 R) [x, (p : 𝕎 R)] :=
  (isRegular_pair_iff_isWeaklyRegular_of_span_ne_top
    (by rw [Set.pair_comm]; exact (span_pair_natCast_ne_top_iff x).mpr hnu)).mpr
      (isWeaklyRegular_pair_of_coeff_zero hx)

end WittVector
