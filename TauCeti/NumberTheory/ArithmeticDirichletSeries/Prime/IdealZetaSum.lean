/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity

/-!
# Partitioning the partial Dirichlet series over a set of primes

Let `K` be a number field. Mathlib's partial Dirichlet series `NumberField.Set.primeIdealZetaSum`
sums `𝔑𝔭 ^ (-s)` over a set of nonzero prime ideals of `𝓞 K`, and this file cuts that sum along a
partition of the primes. Over a summable family the sum is additive along a finite pairwise
disjoint union. For a finite set `S` of primes it also compares the sum over the complement `Sᶜ`
with the sum over all primes: deleting `S` never increases the sum, and for `s ≥ 0` it lowers it
by at most the number of primes deleted.

## Main results

* `NumberField.Set.primeIdealZetaSum_biUnion_of_pairwiseDisjoint`: over a summable family the sum
  over a finite pairwise disjoint union is the sum of the sums over the pieces.
* `NumberField.Set.primeIdealZetaSum_compl_le_univ_of_finite`: deleting a finite set of primes
  does not increase the sum.
* `NumberField.Set.primeIdealZetaSum_univ_sub_compl_le_ncard_of_finite`: for `s ≥ 0`, deleting a
  finite set of primes lowers the sum by at most `S.ncard`.

## Implementation notes

`primeIdealZetaSum S s` is a `tsum`, so it takes the value `0` on a family that is not summable.
That junk value is not additive along a partition, which is why the disjoint-union identity
carries a summability hypothesis.

The same junk value, together with `Set.ncard` being `0` on an infinite set, makes finiteness of
`S` essential to the two complement statements rather than a convenience, and both fail without
it. Take `S = {𝔭₀}ᶜ`, which is itself infinite and whose complement `{𝔭₀}` is a single prime. At
`s = 0` every term is `1`, so the sum over all primes diverges and is read as `0` while the sum
over `{𝔭₀}` is `1`: the first bound reads `1 ≤ 0`. At `s = 2` both sums converge while `S.ncard`
is read as `0`, so the second bound reads `(∑' 𝔭, 𝔑𝔭 ^ (-2)) - 𝔑𝔭₀ ^ (-2) ≤ 0`, whose left-hand
side is the positive sum over the primes other than `𝔭₀`.

Finiteness reaches those two proofs by different routes. The first goes through Mathlib's
`Set.Finite.summable_compl_iff`: deleting finitely many primes cannot restore convergence, so the
restricted and the unrestricted sum are junk together and the bound reads `0 ≤ 0`. The second goes
through Mathlib's `NumberField.Set.primeIdealZetaSum_le_card_of_finite`, the divergent case being
absorbed by nonnegativity of the two partial sums.

## References

The corresponding statements for a source-local `primeIdealZetaSum` over `Set (Ideal (𝓞 K))` are
`primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, `primeIdealZetaSum_union_of_disjoint` and
`primeIdealZetaSum_le_of_subset` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. Those are gated on `1 < s`;
the statements here take the weaker hypotheses that each proof actually uses — summability for the
disjoint-union identity, finiteness for the two complement bounds.
-/

public section

namespace NumberField.Set

open IsDedekindDomain (HeightOneSpectrum)

-- `primeIdealZetaSum` lives in `NumberField.Set`, so dot notation on a set of primes finds it
-- only while `NumberField` is open.
open NumberField

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The sum is additive along a finite disjoint union.** For a summable family, the sum over a
finite pairwise disjoint union of sets of primes is the sum of the sums over the pieces. -/
theorem primeIdealZetaSum_biUnion_of_pairwiseDisjoint {ι : Type*} (t : Finset ι)
    (g : ι → Set (HeightOneSpectrum (𝓞 K))) (hg : (t : Set ι).PairwiseDisjoint g) {s : ℝ}
    (hsum : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :
    (⋃ i ∈ t, g i).primeIdealZetaSum s = ∑ i ∈ t, (g i).primeIdealZetaSum s := by
  simp only [primeIdealZetaSum_def]
  exact (hasSum_sum_disjoint t hg fun i _ ↦ (hsum.subtype _).hasSum).tsum_eq

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
