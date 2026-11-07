/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.Algebra.Order.Group.Indicator
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence

/-!
# Partitioning the partial Dirichlet series over a set of primes

Let `K` be a number field. Mathlib's partial Dirichlet series `NumberField.Set.primeIdealZetaSum`
sums `𝔑𝔭 ^ (-s)` over a set of nonzero prime ideals of `𝓞 K`, and this file cuts that sum along a
partition of the primes. The sum is additive along a finite pairwise disjoint union, given
summability on each piece, and subadditive along an arbitrary union of two sets. For a set `S` of
primes it also compares the sum over the complement `Sᶜ` with the sum over all primes: deleting a
summable (for instance finite) `S` never increases the sum, and for finite `S` and `s ≥ 0` it
lowers it by at most the number of primes deleted.

## Main results

* `NumberField.Set.primeIdealZetaSum_biUnion_of_pairwiseDisjoint`: given summability on each
  piece, the sum over a finite pairwise disjoint union is the sum of the sums over the pieces.
* `NumberField.Set.primeIdealZetaSum_union_le`: the sum over a union is at most the sum of the
  two sums.
* `NumberField.Set.primeIdealZetaSum_le_add_symmDiff`: given summability over `T`, the sum over
  `S` exceeds the sum over `T` by at most the sum over `S ∆ T`.
* `NumberField.Set.primeIdealZetaSum_compl_le_univ`: deleting a summable set of primes does not
  increase the sum.
* `NumberField.Set.primeIdealZetaSum_univ_sub_compl_le_ncard_of_finite`: for `s ≥ 0`, deleting a
  finite set of primes lowers the sum by at most `S.ncard`.

## Implementation notes

`primeIdealZetaSum S s` is a `tsum`, so it takes the value `0` on a family that is not summable.
That junk value is not additive along a partition, which is why the disjoint-union identity
carries a summability hypothesis. Since every term is nonnegative, the series over a set of
primes diverges as soon as the series over some subset does, so its sum is then read as `0`; this
is why the subadditivity bound needs no hypothesis at all, and the symmetric-difference bound
needs summability over `T` only.

The same junk value, together with `Set.ncard` being `0` on an infinite set, makes a hypothesis
on `S` essential to the two complement statements, and both fail without it. Take
`S = {𝔭₀}ᶜ`, which is itself infinite and whose complement `{𝔭₀}` is a single prime. At `s = 0`
every term is `1`, so the sum over all primes diverges and is read as `0` while the sum over
`{𝔭₀}` is `1`: the first bound reads `1 ≤ 0`. At `s = 2` both sums converge while `S.ncard` is
read as `0`, so the second bound reads `(∑' 𝔭, 𝔑𝔭 ^ (-2)) - 𝔑𝔭₀ ^ (-2) ≤ 0`, whose left-hand
side is the positive sum over the primes other than `𝔭₀`.

## References

The corresponding statements for a source-local `primeIdealZetaSum` over `Set (Ideal (𝓞 K))` are
`primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, `primeIdealZetaSum_union_of_disjoint` and
`primeIdealZetaSum_le_of_subset` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. Those are gated on `1 < s`;
the statements here take the weaker hypotheses that each proof actually uses — summability on the
participating pieces for the disjoint-union identity, summability over `S` or finiteness of `S`
for the two complement bounds.
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
  -- `f` is pinned because `Summable.tsum_finset_bUnion_disjoint` states each piece as
  -- `f ∘ Subtype.val`, and recovering `f` from `fun 𝔭 : g i ↦ f 𝔭.1` would be a higher-order
  -- unification.
  exact Summable.tsum_finset_bUnion_disjoint (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) hg hsum

/-- **The sum is subadditive along a union.** The sum over `S ∪ T` is at most the sum over `S`
plus the sum over `T`.

No summability is needed: if the series over `S ∪ T` diverges, its sum is read as `0`. -/
theorem primeIdealZetaSum_union_le (S T : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    (S ∪ T).primeIdealZetaSum s ≤ S.primeIdealZetaSum s + T.primeIdealZetaSum s := by
  set f := fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
  have hf : ∀ (A : Set (HeightOneSpectrum (𝓞 K))) 𝔭, 0 ≤ A.indicator f 𝔭 :=
    fun _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) _
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def, primeIdealZetaSum_def, tsum_subtype (S ∪ T) f,
    tsum_subtype S f, tsum_subtype T f]
  by_cases h : Summable ((S ∪ T).indicator f)
  · have hS := h.of_nonneg_of_le (hf S)
      (Set.indicator_le_indicator_of_subset Set.subset_union_left fun _ ↦ by positivity)
    have hT := h.of_nonneg_of_le (hf T)
      (Set.indicator_le_indicator_of_subset Set.subset_union_right fun _ ↦ by positivity)
    rw [← hS.tsum_add hT]
    -- Pointwise, the indicators of `S ∪ T` and `S ∩ T` add up to those of `S` and `T`.
    refine h.tsum_le_tsum (fun 𝔭 ↦ ?_) (hS.add hT)
    rw [← Set.indicator_union_add_inter_apply f S T 𝔭]
    exact le_add_of_nonneg_right (hf _ 𝔭)
  · rw [tsum_eq_zero_of_not_summable h]
    exact add_nonneg (tsum_nonneg (hf S)) (tsum_nonneg (hf T))

/-- **Changing a set by a small symmetric difference changes the sum by little.** Given
summability over `T`, the sum over `S` is at most the sum over `T` plus the sum over `S ∆ T`.

No summability over `S ∆ T` is needed: if that series diverges, then so does the one over `S`. -/
theorem primeIdealZetaSum_le_add_symmDiff {S T : Set (HeightOneSpectrum (𝓞 K))} {s : ℝ}
    (hT : Summable fun 𝔭 : T ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    S.primeIdealZetaSum s ≤ T.primeIdealZetaSum s + (S ∆ T).primeIdealZetaSum s := by
  by_cases hS : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)
  · -- `S` lies in `S ∪ T = T ∪ S ∆ T`, which is summable because `S` and `T \ S` are.
    have hST : Summable fun 𝔭 : ↥(S ∪ T) ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
      have hdiff : Summable fun 𝔭 : ↥(T \ S) ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
        simpa only [Function.comp_def, Set.coe_inclusion] using
          hT.comp_injective (Set.inclusion_injective Set.sdiff_subset)
      have := hS.hasSum.add_disjoint (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) Set.disjoint_sdiff_right hdiff.hasSum
      rw [Set.union_sdiff_self] at this
      exact this.summable
    calc S.primeIdealZetaSum s ≤ (S ∪ T).primeIdealZetaSum s :=
          primeIdealZetaSum_mono_set Set.subset_union_left hST
      _ = (T ∪ S ∆ T).primeIdealZetaSum s :=
          congrArg (primeIdealZetaSum · s) (right_sup_symmDiff S T).symm
      _ ≤ _ := primeIdealZetaSum_union_le T (S ∆ T) s
  · rw [primeIdealZetaSum_def S, tsum_eq_zero_of_not_summable hS]
    exact add_nonneg (primeIdealZetaSum_nonneg T s) (primeIdealZetaSum_nonneg _ s)

/-- **Deleting a summable set of primes does not increase the sum.** In particular this applies
to a finite set of primes. -/
theorem primeIdealZetaSum_compl_le_univ {s : ℝ}
    (hS : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    Sᶜ.primeIdealZetaSum s ≤ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_univ]
  by_cases hsum : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
  · exact hsum.tsum_subtype_le _ _ fun _ ↦ by positivity
  · rw [tsum_eq_zero_of_not_summable hsum]
    exact (tsum_eq_zero_of_not_summable (mt hS.summable_compl_iff.mp hsum)).le

/-- **A finite set of primes costs at most its number.** Deleting a finite set `S` of primes from
the all-prime sum lowers it by at most `S.ncard`, uniformly in `s ≥ 0`. -/
theorem primeIdealZetaSum_univ_sub_compl_le_ncard_of_finite (hS : S.Finite) {s : ℝ} (hs : 0 ≤ s) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s - Sᶜ.primeIdealZetaSum s ≤
      S.ncard := by
  have := primeIdealZetaSum_union_le S Sᶜ s
  rw [Set.union_compl_self] at this
  linarith [primeIdealZetaSum_le_card_of_finite hS hs]

end NumberField.Set
