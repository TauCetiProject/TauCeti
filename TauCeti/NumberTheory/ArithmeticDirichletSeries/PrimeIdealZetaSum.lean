/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity

/-!
# Deleting a finite set of primes from the partial Dirichlet series

Let `K` be a number field and `S` a finite set of nonzero prime ideals of `𝓞 K`. Mathlib's partial
Dirichlet series `NumberField.Set.primeIdealZetaSum` sums `𝔑𝔭 ^ (-s)` over a set of primes, and
this file compares the sum over the complement `Sᶜ` with the sum over all primes: deleting `S`
never increases the sum, and for `s ≥ 0` it lowers it by at most the number of primes deleted.

## Main results

* `NumberField.Set.primeIdealZetaSum_compl_le_univ_of_finite`: deleting a finite set of primes
  does not increase the sum.
* `NumberField.Set.primeIdealZetaSum_univ_sub_compl_le_ncard_of_finite`: for `s ≥ 0`, deleting a
  finite set of primes lowers the sum by at most `S.ncard`.

## Implementation notes

`primeIdealZetaSum S s` is a `tsum`, so it takes the value `0` on a family that is not summable,
and `Set.ncard` is `0` on an infinite set. Finiteness of `S` is therefore essential to both
statements rather than a convenience, and both fail without it. Take `S = {𝔭₀}ᶜ`, which is itself
infinite and whose complement `{𝔭₀}` is a single prime. At `s = 0` every term is `1`, so the sum
over all primes diverges and is read as `0` while the sum over `{𝔭₀}` is `1`: the first bound
reads `1 ≤ 0`. At `s = 2` both sums converge while `S.ncard` is read as `0`, so the second bound
reads `(∑' 𝔭, 𝔑𝔭 ^ (-2)) - 𝔑𝔭₀ ^ (-2) ≤ 0`, whose left-hand side is the positive sum over the
primes other than `𝔭₀`.

Finiteness reaches the two proofs by different routes. The first goes through Mathlib's
`Set.Finite.summable_compl_iff`: deleting finitely many primes cannot restore convergence, so the
restricted and the unrestricted sum are junk together and the bound reads `0 ≤ 0`. The second goes
through Mathlib's `NumberField.Set.primeIdealZetaSum_le_card_of_finite`, the divergent case being
absorbed by nonnegativity of the two partial sums.
-/

public section

namespace NumberField.Set

open IsDedekindDomain (HeightOneSpectrum)

-- `primeIdealZetaSum` lives in `NumberField.Set`, so dot notation on a set of primes finds it
-- only while `NumberField` is open.
open NumberField

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **Deleting a finite set of primes does not increase the sum.** -/
theorem primeIdealZetaSum_compl_le_univ_of_finite (hS : S.Finite) (s : ℝ) :
    Sᶜ.primeIdealZetaSum s ≤ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def,
    tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)]
  by_cases hsum : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
  · exact hsum.tsum_subtype_le _ _ fun _ ↦ by positivity
  · rw [tsum_eq_zero_of_not_summable hsum]
    exact (tsum_eq_zero_of_not_summable (mt hS.summable_compl_iff.mp hsum)).le

/-- **A finite set of primes costs at most its number.** Deleting a finite set `S` of primes from
the all-prime sum lowers it by at most `S.ncard`, uniformly in `s ≥ 0`. -/
theorem primeIdealZetaSum_univ_sub_compl_le_ncard_of_finite (hS : S.Finite) {s : ℝ} (hs : 0 ≤ s) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s - Sᶜ.primeIdealZetaSum s ≤
      S.ncard := by
  have hsplit : (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s ≤
      S.primeIdealZetaSum s + Sᶜ.primeIdealZetaSum s := by
    rw [primeIdealZetaSum_def, primeIdealZetaSum_def, primeIdealZetaSum_def,
      tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)]
    by_cases hsum : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
    · exact ((hsum.subtype _).tsum_add_tsum_compl (hsum.subtype _)).ge
    · exact (tsum_eq_zero_of_not_summable hsum).trans_le (by positivity)
  linarith [primeIdealZetaSum_le_card_of_finite hS hs]

end NumberField.Set
