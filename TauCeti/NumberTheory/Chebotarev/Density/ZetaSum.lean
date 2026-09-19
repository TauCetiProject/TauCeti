/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.ZetaSumPartition
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet

/-!
# The prime zeta sum over the Frobenius fibres

Let `L / K` be a finite Galois extension of number fields. The Artin class partitions the primes
of `𝓞 K` outside the finite set `ramifiedPrimes K L` into the fibres `frobeniusPrimeSet K L C`,
one for each conjugacy class `C` of `Gal(L/K)`. This file transports that partition through
Mathlib's partial Dirichlet series `NumberField.Set.primeIdealZetaSum`, whose ratios define
`NumberField.Set.HasDirichletDensity`: whenever each fibre series is summable, the fibre sums add
up to the sum over the primes unramified in `L`, so the Frobenius fibres account for the all-prime
sum up to an error which is bounded by `#(ramifiedPrimes K L)`, uniformly in `s ≥ 0`.

Both ingredients are generic. Additivity along a finite pairwise disjoint union is
`NumberField.Set.primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, and the error bound is
`NumberField.Set.primeIdealZetaSum_univ_sub_compl_le_ncard_of_finite`: deleting a finite set of
primes from the all-prime sum costs at most the number of primes deleted. Only their
specializations to the Artin fibres and to `ramifiedPrimes K L` are Chebotarev-specific.

## Main results

* `NumberField.Chebotarev.sum_primeIdealZetaSum_frobeniusPrimeSet`: for `s` at which every fibre
  series is summable, the fibre sums add up to the sum over the complement of `ramifiedPrimes K L`.
* `NumberField.Chebotarev.abs_primeIdealZetaSum_sub_sum_primeIdealZetaSum_frobeniusPrimeSet_le`:
  for such `s` with `0 ≤ s`, the all-prime sum and the total fibre sum differ by at most
  `#(ramifiedPrimes K L)`.

## Implementation notes

`primeIdealZetaSum S s` is a `tsum`, so it takes the value `0` on a family that is not summable,
and `0` is not additive along a partition. The fibre identity therefore carries a summability
hypothesis, and only a per-fibre one: nothing here needs the series over all primes to converge.

## References

The Artin-class partition of the unramified primes and the bound on the ramified contribution are
adapted from `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, where they are stated for a
source-local `primeIdealZetaSum` over `Set (Ideal (𝓞 K))` and gated on `1 < s`. Here the carrier is
Mathlib's `NumberField.Set.primeIdealZetaSum` over `HeightOneSpectrum (𝓞 K)`, and the hypothesis is
summability, which `1 < s` implies.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)

-- `primeIdealZetaSum` lives in `NumberField.Set`, so dot notation on a set of primes finds it
-- only while `NumberField` is open.
open NumberField

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {s : ℝ} [IsGalois K L]

open scoped Classical in
variable (K L) in
/-- **The Frobenius fibres reassemble the unramified sum.** Summing `primeIdealZetaSum` over the
Artin fibres of all conjugacy classes of `Gal(L/K)` gives the sum over the complement of
`ramifiedPrimes K L`, provided each fibre series converges.

Summability is what makes the fibre sums add; see the module docstring. It is needed only on each
fibre, which `Summable.subtype` supplies from summability over all primes. -/
theorem sum_primeIdealZetaSum_frobeniusPrimeSet
    (hsum : ∀ C : ConjClasses (L ≃ₐ[K] L),
      Summable fun 𝔭 : frobeniusPrimeSet K L C ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    ∑ C : ConjClasses (L ≃ₐ[K] L), (frobeniusPrimeSet K L C).primeIdealZetaSum s =
      (↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ.primeIdealZetaSum s := by
  have hcov : (↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ =
      ⋃ C ∈ (Finset.univ : Finset (ConjClasses (L ≃ₐ[K] L))), frobeniusPrimeSet K L C := by simp
  rw [hcov]
  exact (Set.primeIdealZetaSum_biUnion_of_pairwiseDisjoint _ _
    ((pairwise_disjoint_frobeniusPrimeSet K L).set_pairwise _)
    fun C _ ↦ hsum C).symm

open scoped Classical in
variable (K L) in
/-- **The Frobenius fibres account for the all-prime sum up to the ramified primes.** At an
`s ≥ 0` where every fibre series is summable, the all-prime sum and the total over the Artin
fibres differ by at most `#(ramifiedPrimes K L)` — a bound uniform in `s`. -/
theorem abs_primeIdealZetaSum_sub_sum_primeIdealZetaSum_frobeniusPrimeSet_le (hs : 0 ≤ s)
    (hsum : ∀ C : ConjClasses (L ≃ₐ[K] L),
      Summable fun 𝔭 : frobeniusPrimeSet K L C ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    |(Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s -
        ∑ C : ConjClasses (L ≃ₐ[K] L), (frobeniusPrimeSet K L C).primeIdealZetaSum s| ≤
      (ramifiedPrimes K L).card := by
  rw [sum_primeIdealZetaSum_frobeniusPrimeSet K L hsum, abs_of_nonneg <| sub_nonneg.2 <|
    Set.primeIdealZetaSum_compl_le_univ_of_finite (ramifiedPrimes K L).finite_toSet s,
    ← Set.ncard_coe_finset (ramifiedPrimes K L)]
  exact Set.primeIdealZetaSum_univ_sub_compl_le_ncard_of_finite (ramifiedPrimes K L).finite_toSet hs

end NumberField.Chebotarev
