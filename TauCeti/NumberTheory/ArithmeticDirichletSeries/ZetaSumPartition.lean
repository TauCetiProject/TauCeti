/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.Algebra.Order.Group.Indicator

/-!
# Partitioning the partial Dirichlet series over a set of primes

Let `K` be a number field. Mathlib's partial Dirichlet series `NumberField.Set.primeIdealZetaSum`
sums `𝔑𝔭 ^ (-s)` over a set of nonzero prime ideals of `𝓞 K`, and this file cuts that sum along a
partition of the primes. The sum is additive along a finite pairwise disjoint union, given
summability on each piece, and subadditive along an arbitrary union of two sets. For a finite
set `S` of primes it also compares the sum over the complement `Sᶜ` with the sum over all primes:
deleting `S` never increases the sum, and for `s ≥ 0` it lowers it by at most the number of
primes deleted.

## Main results

* `NumberField.Set.primeIdealZetaSum_biUnion_of_pairwiseDisjoint`: given summability on each
  piece, the sum over a finite pairwise disjoint union is the sum of the sums over the pieces.
* `NumberField.Set.primeIdealZetaSum_union_le`: given summability on both sets, the sum over a
  union is at most the sum of the two sums.
* `NumberField.Set.primeIdealZetaSum_le_add_symmDiff`: given summability over `T` and over
  `S ∆ T`, the sum over `S` exceeds the sum over `T` by at most the sum over `S ∆ T`.
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

## References

The corresponding statements for a source-local `primeIdealZetaSum` over `Set (Ideal (𝓞 K))` are
`primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, `primeIdealZetaSum_union_of_disjoint` and
`primeIdealZetaSum_le_of_subset` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. Those are gated on `1 < s`;
the statements here take the weaker hypotheses that each proof actually uses — summability on the
participating pieces for the disjoint-union identity, finiteness for the two complement bounds.
-/

public section

namespace NumberField.Set

open IsDedekindDomain (HeightOneSpectrum)
open scoped symmDiff

-- `primeIdealZetaSum` lives in `NumberField.Set`, so dot notation on a set of primes finds it
-- only while `NumberField` is open.
open NumberField

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The sum is additive along a finite disjoint union.** The sum over a finite pairwise
disjoint union of sets of primes is the sum of the sums over the pieces.

Summability is asked for on each participating piece rather than on all primes at once: a
finite union of summable pieces is summable even at an `s` where the full prime series
diverges, and the identity holds there too. -/
theorem primeIdealZetaSum_biUnion_of_pairwiseDisjoint {ι : Type*} (t : Finset ι)
    (g : ι → Set (HeightOneSpectrum (𝓞 K))) (hg : (t : Set ι).PairwiseDisjoint g) {s : ℝ}
    (hsum : ∀ i ∈ t, Summable fun 𝔭 : g i ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    (⋃ i ∈ t, g i).primeIdealZetaSum s = ∑ i ∈ t, (g i).primeIdealZetaSum s := by
  simp only [primeIdealZetaSum_def]
  -- `f` is pinned because `hasSum_sum_disjoint` states each piece as `f ∘ Subtype.val`, and
  -- recovering `f` from `fun 𝔭 : g i ↦ f 𝔭.1` would be a higher-order unification.
  exact (hasSum_sum_disjoint (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) t hg fun i hi ↦ (hsum i hi).hasSum).tsum_eq

/-- **The sum is subadditive along a union.** Given summability over `S` and over `T`, the sum
over `S ∪ T` is at most the sum over `S` plus the sum over `T`. -/
theorem primeIdealZetaSum_union_le {S T : Set (HeightOneSpectrum (𝓞 K))} {s : ℝ}
    (hS : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))
    (hT : Summable fun 𝔭 : T ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    (S ∪ T).primeIdealZetaSum s ≤ S.primeIdealZetaSum s + T.primeIdealZetaSum s := by
  have hsub : T \ S ⊆ T := Set.sdiff_subset
  have hdiff : Summable fun 𝔭 : ↥(T \ S) ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
    simpa only [Function.comp_def, Set.coe_inclusion] using
      hT.comp_injective (Set.inclusion_injective hsub)
  have hsplit := hS.tsum_union_disjoint (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) Set.disjoint_sdiff_right hdiff
  have hle : ∑' 𝔭 : ↥(T \ S), (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) ≤
      ∑' 𝔭 : T, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) :=
    hdiff.tsum_le_tsum_of_inj (Set.inclusion hsub) (Set.inclusion_injective hsub)
      (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl) hT
  -- `S ∪ T` is the disjoint union of `S` and `T \ S`, and `T \ S` is contained in `T`.
  rw [← Set.union_sdiff_self (s := S)]
  simp only [primeIdealZetaSum_def]
  rw [hsplit]
  exact add_le_add_right hle _

/-- **Changing a set by a small symmetric difference changes the sum by little.** Given
summability over `T` and over `S ∆ T`, the sum over `S` is at most the sum over `T` plus the sum
over `S ∆ T`. -/
theorem primeIdealZetaSum_le_add_symmDiff {S T : Set (HeightOneSpectrum (𝓞 K))} {s : ℝ}
    (hT : Summable fun 𝔭 : T ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))
    (hST : Summable fun 𝔭 : ↥(S ∆ T) ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    S.primeIdealZetaSum s ≤ T.primeIdealZetaSum s + (S ∆ T).primeIdealZetaSum s := by
  set f := fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
  have hf : 0 ≤ f := fun _ ↦ by positivity
  have hT' := (summable_subtype_iff_indicator (f := f)).1 hT
  have hST' := (summable_subtype_iff_indicator (f := f)).1 hST
  -- Pointwise, `S` is covered by `T ∪ S ∆ T`.
  have hle : S.indicator f ≤ T.indicator f + (S ∆ T).indicator f := fun 𝔭 ↦ by
    have : 0 ≤ f 𝔭 := hf 𝔭
    by_cases hS : 𝔭 ∈ S <;> by_cases hT : 𝔭 ∈ T <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_symmDiff, *]
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def, primeIdealZetaSum_def, tsum_subtype S f,
    tsum_subtype T f, tsum_subtype (S ∆ T) f, ← hT'.tsum_add hST']
  exact ((hT'.add hST').of_nonneg_of_le (Set.indicator_nonneg fun _ _ ↦ hf _) hle).tsum_le_tsum
    hle (hT'.add hST')

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
