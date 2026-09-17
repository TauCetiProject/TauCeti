/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.ZetaSumPartition
public import TauCeti.NumberTheory.NumberField.DirichletDensityBounds
import Mathlib.Algebra.BigOperators.Field

/-!
# The Boolean calculus of Dirichlet density

For a number field `K`, Mathlib's `NumberField.Set.HasDirichletDensity S δ` says that

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s → δ` as `s → 1⁺`.

This file proves the elementary calculus of this predicate: uniqueness, the value `1` on all
primes, monotonicity, additivity on finite disjoint unions, complements, and the squeeze of a set
between two sets of the same density. It also shows that one-sided density bounds move along
inclusions of sets, which is what makes the squeeze work.

All of these are statements about the ratio for `s` close to `1` from the right, and on that
side both inputs they need are available: for `1 < s` each partial sum is a genuine sum rather
than the `tsum` junk value (`TauCeti.summable_absNorm_rpow_subtype_of_one_lt`), and the all-prime
denominator is positive (`NumberField.Set.primeIdealZetaSum_univ_pos_of_one_lt`). In particular
nothing here uses the divergence of the all-prime sum at `s = 1`. That divergence is what makes a
finite set of primes have density zero, and those finite-error statements are not proved here.

## Main results

* `NumberField.Set.hasDirichletDensity_univ`: all primes have Dirichlet density `1`.
* `NumberField.Set.HasDirichletDensity.mono`: inclusion of prime sets orders their densities.
* `NumberField.Set.HasDirichletDensity.union` and
  `NumberField.Set.hasDirichletDensity_biUnion_finset`: Dirichlet density is additive on finite
  disjoint unions.
* `NumberField.Set.HasDirichletDensity.compl`: the complement of a set of density `δ` has
  density `1 - δ`.
* `NumberField.Set.IsLowerDirichletDensityBound.mono_set` and
  `NumberField.Set.IsUpperDirichletDensityBound.mono_set`: lower bounds pass to supersets and
  upper bounds to subsets.
* `NumberField.Set.hasDirichletDensity_of_subset_of_subset`: a set squeezed between two sets of
  density `δ` has density `δ`.

## References

* The declarations and proof structure are adapted from the `HasNaturalDensity` calculus in
  `TauCeti.NumberTheory.ArithmeticDirichletSeries.NaturalDensity`.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

namespace NumberField.Set

open Filter IsDedekindDomain NumberField TauCeti
open scoped NumberField Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T U : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}

/-- A set of prime ideals has at most one Dirichlet density. -/
theorem HasDirichletDensity.unique (hδ : HasDirichletDensity S δ)
    (hε : HasDirichletDensity S ε) : δ = ε :=
  tendsto_nhds_unique (hasDirichletDensity_iff.1 hδ) (hasDirichletDensity_iff.1 hε)

/-- The set of all prime ideals has Dirichlet density one. -/
@[simp]
theorem hasDirichletDensity_univ :
    HasDirichletDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  refine hasDirichletDensity_iff.2 <| tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  exact (div_self (primeIdealZetaSum_univ_pos_of_one_lt hs).ne').symm

/-- The Dirichlet density of the set of all prime ideals is one. -/
@[simp]
theorem dirichletDensity_univ :
    dirichletDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = 1 :=
  hasDirichletDensity_univ.dirichletDensity_eq

/-- Inclusion of prime sets orders their Dirichlet densities, when both densities exist. -/
theorem HasDirichletDensity.mono (hST : S ⊆ T) (hS : HasDirichletDensity S δ)
    (hT : HasDirichletDensity T ε) : δ ≤ ε := by
  refine le_of_tendsto_of_tendsto (hasDirichletDensity_iff.1 hS) (hasDirichletDensity_iff.1 hT) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  exact div_le_div_of_nonneg_right (primeIdealZetaSum_mono_set_of_one_lt hST hs)
    (primeIdealZetaSum_nonneg _ s)

/-- Dirichlet density is additive on a finite family of pairwise disjoint prime sets. -/
theorem hasDirichletDensity_biUnion_finset {ι : Type*} {s : Finset ι}
    {f : ι → Set (HeightOneSpectrum (𝓞 K))} {d : ι → ℝ}
    (hf : ∀ i ∈ s, HasDirichletDensity (f i) (d i))
    (hdisj : (s : Set ι).PairwiseDisjoint f) :
    HasDirichletDensity (⋃ i ∈ s, f i) (∑ i ∈ s, d i) := by
  refine hasDirichletDensity_iff.2 <|
    (tendsto_finsetSum s fun i hi ↦ hasDirichletDensity_iff.1 (hf i hi)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
  rw [primeIdealZetaSum_biUnion_of_pairwiseDisjoint s f hdisj
    fun i _ ↦ summable_absNorm_rpow_subtype_of_one_lt (f i) ht, Finset.sum_div]

/-- Dirichlet density is additive on disjoint unions of prime sets. -/
theorem HasDirichletDensity.union (hS : HasDirichletDensity S δ)
    (hT : HasDirichletDensity T ε) (hST : Disjoint S T) :
    HasDirichletDensity (S ∪ T) (δ + ε) := by
  have hdisj : ((↑({false, true} : Finset Bool)) : Set Bool).PairwiseDisjoint
      (fun b ↦ if b then S else T) := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · simpa [Function.onFun] using hST.symm
    · simpa [Function.onFun] using hST
    · exact (hij rfl).elim
  have hsets : (⋃ b ∈ ({false, true} : Finset Bool), if b then S else T) = S ∪ T := by
    rw [Finset.set_biUnion_insert, Finset.set_biUnion_singleton]
    simp [Set.union_comm]
  have hfinite := hasDirichletDensity_biUnion_finset
      (s := {false, true}) (f := fun b : Bool ↦ if b then S else T)
      (d := fun b : Bool ↦ if b then δ else ε)
      (by intro i _; cases i <;> assumption) hdisj
  rw [hsets] at hfinite
  simpa [add_comm] using hfinite

/-- The complement of a set of Dirichlet density `δ` has Dirichlet density `1 - δ`. -/
theorem HasDirichletDensity.compl (hS : HasDirichletDensity S δ) :
    HasDirichletDensity Sᶜ (1 - δ) := by
  refine hasDirichletDensity_iff.2 <|
    (hasDirichletDensity_iff.1 (hasDirichletDensity_univ :
      HasDirichletDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1)).sub
      (hasDirichletDensity_iff.1 hS) |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have hne : primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s ≠ 0 :=
    (primeIdealZetaSum_univ_pos_of_one_lt hs).ne'
  have hsplit : primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s =
      primeIdealZetaSum S s + primeIdealZetaSum Sᶜ s := by
    have hdisj : ((↑({false, true} : Finset Bool)) : Set Bool).PairwiseDisjoint
        (fun b ↦ if b then S else Sᶜ) := by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · simpa [Function.onFun] using (disjoint_compl_left : Disjoint Sᶜ S)
      · simpa [Function.onFun] using (disjoint_compl_right : Disjoint S Sᶜ)
      · exact (hij rfl).elim
    have hsets : (⋃ b ∈ ({false, true} : Finset Bool), if b then S else Sᶜ) = Set.univ := by
      rw [Finset.set_biUnion_insert, Finset.set_biUnion_singleton]
      simp [Set.union_comm]
    have hzeta := primeIdealZetaSum_biUnion_of_pairwiseDisjoint
      ({false, true} : Finset Bool)
        (fun b ↦ if b then S else Sᶜ) hdisj
        (fun i _ ↦ by cases i <;> exact summable_absNorm_rpow_subtype_of_one_lt _ hs)
    rw [hsets] at hzeta
    simpa [add_comm] using hzeta
  rw [div_self hne, eq_div_iff hne, sub_mul, one_mul, div_mul_cancel₀ _ hne]
  linarith

/-- **Lower Dirichlet-density bounds pass to supersets.** -/
theorem IsLowerDirichletDensityBound.mono_set (hST : S ⊆ T)
    (hS : IsLowerDirichletDensityBound S δ) : IsLowerDirichletDensityBound T δ := by
  refine isLowerDirichletDensityBound_iff.2 fun η hη ↦ ?_
  filter_upwards [isLowerDirichletDensityBound_iff.1 hS η hη,
    self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
  exact hs.trans_le <| div_le_div_of_nonneg_right (primeIdealZetaSum_mono_set_of_one_lt hST hs1)
    (primeIdealZetaSum_nonneg _ s)

/-- **Upper Dirichlet-density bounds pass to subsets.** -/
theorem IsUpperDirichletDensityBound.mono_set (hST : S ⊆ T)
    (hT : IsUpperDirichletDensityBound T δ) : IsUpperDirichletDensityBound S δ := by
  refine isUpperDirichletDensityBound_iff.2 fun η hη ↦ ?_
  filter_upwards [isUpperDirichletDensityBound_iff.1 hT η hη,
    self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
  exact (div_le_div_of_nonneg_right (primeIdealZetaSum_mono_set_of_one_lt hST hs1)
    (primeIdealZetaSum_nonneg _ s)).trans_lt hs

/-- **Squeeze.** A set of primes lying between two sets of Dirichlet density `δ` has Dirichlet
density `δ`. -/
theorem hasDirichletDensity_of_subset_of_subset (hST : S ⊆ T) (hTU : T ⊆ U)
    (hS : HasDirichletDensity S δ) (hU : HasDirichletDensity U δ) :
    HasDirichletDensity T δ :=
  hasDirichletDensity_of_upperBound_of_lowerBound
    (hU.isUpperDirichletDensityBound.mono_set hTU)
    (hS.isLowerDirichletDensityBound.mono_set hST)

end NumberField.Set
