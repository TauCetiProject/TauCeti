/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Log
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Data.Nat.Factorization.Basic
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.Data.Nat.Choose.Multinomial

/-!
# Clearing multinomial denominators in a local ring

In a local ring where the prime `p` is not a unit, every integer prime to `p` is a unit.
Consequently one common power of `p` clears the multinomial denominators in all degrees below
`p ^ f`. This enables the use of integral diagonal weights in polynomial pairings.

The denominator bound is used in `New.Average.exists_isAdjointWeight` in
`grh/src/New/UpperBound/ElementaryDivisors/InvariantAverage.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

namespace IsLocalRing

/-- In a local ring where the prime `p` is not a unit, `p ^ e` clears the multinomial
denominator if `e` is at least `s.card - 1` times the base-`p` logarithm of the sum of the
parts. In particular, `s.card * f` works uniformly when that sum is at most `p ^ f`. -/
theorem exists_multinomial_mul_eq_prime_pow {R ι : Type*} [CommRing R] [IsLocalRing R]
    {p e : ℕ} (hp : p.Prime) (hpR : ¬ IsUnit (p : R)) (s : Finset ι) (a : ι → ℕ)
    (he : (s.card - 1) * Nat.log p (∑ i ∈ s, a i) ≤ e) :
    ∃ c : R, (Nat.multinomial s a : R) * c = (p : R) ^ e := by
  let n := Nat.multinomial s a
  have hn : n ≠ 0 := (Nat.multinomial_pos s a).ne'
  have hfac : n.factorization p ≤ e := (Nat.factorization_multinomial_le s a p).trans he
  have hchar : ringChar (ResidueField R) = p :=
    (hp.eq_one_or_self_of_dvd _ (not_not.mp (isUnit_natCast_iff_not_dvd.not.mp hpR))).resolve_left
      (CharP.ringChar_ne_one (R := ResidueField R))
  have hu : IsUnit ((n / p ^ n.factorization p : ℕ) : R) :=
    isUnit_natCast_iff_not_dvd.mpr (by rw [hchar]; exact Nat.not_dvd_ordCompl hp hn)
  obtain ⟨u, hu⟩ := hu
  have hsplit : (n : R) = (p : R) ^ n.factorization p * ↑u := by
    rw [hu]
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg (Nat.cast : ℕ → R) (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  refine ⟨↑u⁻¹ * (p : R) ^ (e - n.factorization p), ?_⟩
  calc
    (n : R) * (↑u⁻¹ * (p : R) ^ (e - n.factorization p)) =
        (p : R) ^ n.factorization p * (p : R) ^ (e - n.factorization p) := by
      rw [hsplit, mul_assoc, ← mul_assoc (↑u : R), Units.mul_inv, one_mul]
    _ = (p : R) ^ e := by rw [← pow_add, Nat.add_sub_of_le hfac]

end IsLocalRing
