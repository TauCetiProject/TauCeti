/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Asymptotics.Lemmas
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting

/-!
# Natural density of sets of prime ideals

For a number field `K`, this file defines the natural density of a set `S` of nonzero prime
ideals as the limit

```text
  primeCount K S x / primeCount K Set.univ x
```

as the inclusive real cutoff `x` tends to infinity. This normalization matches Mathlib's
ratio-normalized `NumberField.Set.HasDirichletDensity`: a density is measured relative to all
prime ideals of the same number field, rather than relative to an external approximation such as
`x / log x`.

The denominator really tends to infinity. Indeed, lying over supplies a prime of `𝓞 K` above
every rational prime, so the height-one spectrum is infinite. Its bounded-norm subsets are finite
and exhaust the spectrum, whence their cardinalities tend to infinity. This fact both makes the
whole spectrum have density one and ensures that a fixed finite error disappears in the ratio.

## Main results

* `NumberField.Set.HasNaturalDensity`: ratio-normalized natural density for a set of prime ideals.
* `NumberField.Set.hasNaturalDensity_def`: the defining ratio-convergence characterization.
* `NumberField.Set.HasNaturalDensity.union`,
  `NumberField.Set.hasNaturalDensity_biUnion_finset` and
  `NumberField.Set.HasNaturalDensity.compl`: finite Boolean calculus for natural density.
* `NumberField.Set.HasNaturalDensity.of_finite_symmDiff`: changing a prime set on finitely many
  primes preserves its natural density.
* `NumberField.Set.hasNaturalDensity_of_finite`: every finite set of prime ideals has natural
  density zero.

The definition and elementary calculus are standard; see J.-P. Serre, *Corps locaux*, Chapter
VI, or J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

namespace NumberField.Set

open Filter IsDedekindDomain
open scoped NumberField Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}

/-- A set `S` of height-one primes of a number field has natural density `δ` when the proportion
of primes of `S` below `x`, relative to all primes below `x`, tends to `δ` as `x → ∞`.

Both counts use the inclusive real cutoff fixed by `TauCeti.primeCount`. -/
def HasNaturalDensity (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ => TauCeti.primeCount K S x /
    TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 δ)

/-- Unfolds `HasNaturalDensity` to the convergence of the ratio of prime counts. -/
theorem hasNaturalDensity_def :
    HasNaturalDensity S δ ↔ Tendsto (fun x : ℝ => TauCeti.primeCount K S x /
      TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 δ) :=
  (Iff.rfl)

/-- A set of prime ideals has at most one natural density. -/
theorem HasNaturalDensity.unique (hδ : HasNaturalDensity S δ) (hε : HasNaturalDensity S ε) :
    δ = ε :=
  tendsto_nhds_unique hδ hε

/-- The empty set of prime ideals has natural density zero. -/
@[simp]
theorem hasNaturalDensity_empty :
    HasNaturalDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) 0 := by
  simp [hasNaturalDensity_def]

/-- The set of all prime ideals has natural density one. -/
@[simp]
theorem hasNaturalDensity_univ :
    HasNaturalDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  rw [hasNaturalDensity_def]
  have hne : ∀ᶠ x : ℝ in atTop,
      TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x ≠ 0 :=
    ((TauCeti.tendsto_primeCount_univ_atTop K).eventually_gt_atTop 0).mono
      fun _ hx => hx.ne'
  exact tendsto_const_nhds.congr' (hne.mono fun _ hx => (div_self hx).symm)

/-- A natural density is nonnegative. -/
theorem HasNaturalDensity.nonneg (h : HasNaturalDensity S δ) : 0 ≤ δ :=
  ge_of_tendsto h <| Eventually.of_forall fun x =>
    div_nonneg (TauCeti.primeCount_nonneg S x) (TauCeti.primeCount_nonneg Set.univ x)

/-- A natural density is at most one. -/
theorem HasNaturalDensity.le_one (h : HasNaturalDensity S δ) : δ ≤ 1 :=
  le_of_tendsto h <| Eventually.of_forall fun x =>
    div_le_one_of_le₀ (TauCeti.primeCount_mono_set (Set.subset_univ S) x)
      (TauCeti.primeCount_nonneg Set.univ x)

/-- Inclusion of prime sets orders their natural densities, when both densities exist. -/
theorem HasNaturalDensity.mono (hST : S ⊆ T) (hS : HasNaturalDensity S δ)
    (hT : HasNaturalDensity T ε) : δ ≤ ε := by
  refine le_of_tendsto_of_tendsto hS hT (Eventually.of_forall fun x => ?_)
  exact div_le_div_of_nonneg_right (TauCeti.primeCount_mono_set hST x)
    (TauCeti.primeCount_nonneg Set.univ x)

/-- Natural density is additive on disjoint unions of prime sets. -/
theorem HasNaturalDensity.union (hS : HasNaturalDensity S δ) (hT : HasNaturalDensity T ε)
    (hST : Disjoint S T) : HasNaturalDensity (S ∪ T) (δ + ε) := by
  rw [hasNaturalDensity_def] at hS hT ⊢
  simpa only [TauCeti.primeCount_union hST, add_div] using hS.add hT

/-- Natural density is additive on a finite family of pairwise disjoint prime sets. -/
theorem hasNaturalDensity_biUnion_finset {ι : Type*} {s : Finset ι}
    {f : ι → Set (HeightOneSpectrum (𝓞 K))} {d : ι → ℝ}
    (hf : ∀ i ∈ s, HasNaturalDensity (f i) (d i))
    (hdisj : (s : Set ι).PairwiseDisjoint f) :
    HasNaturalDensity (⋃ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    refine (hf a (Finset.mem_insert_self a s)).union
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (hdisj.subset (by simp))) ?_
    rw [_root_.Set.disjoint_iUnion₂_right]
    intro i hi
    exact hdisj (by simp) (by simp [hi]) fun h => ha (h ▸ hi)

/-- The complement of a set of natural density `δ` has natural density `1 - δ`. -/
theorem HasNaturalDensity.compl (hS : HasNaturalDensity S δ) :
    HasNaturalDensity Sᶜ (1 - δ) := by
  rw [hasNaturalDensity_def] at hS ⊢
  have hne : ∀ᶠ x : ℝ in atTop,
      TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x ≠ 0 :=
    ((TauCeti.tendsto_primeCount_univ_atTop K).eventually_gt_atTop 0).mono
      fun _ hx => hx.ne'
  refine (tendsto_const_nhds.sub hS).congr' (hne.mono fun x hx => ?_)
  simp only
  rw [← div_self hx, ← sub_div]
  have hdisj : Disjoint S Sᶜ := _root_.Set.disjoint_left.mpr fun _ hmem hcompl => hcompl hmem
  have hcount : TauCeti.primeCount K Set.univ x =
      TauCeti.primeCount K S x + TauCeti.primeCount K Sᶜ x := by
    rw [← TauCeti.primeCount_union hdisj, _root_.Set.union_compl_self]
  rw [hcount]
  ring

/-- Changing a set on finitely many prime ideals preserves its natural density. -/
theorem HasNaturalDensity.of_finite_symmDiff (hT : HasNaturalDensity T δ)
    (hST : (symmDiff S T).Finite) : HasNaturalDensity S δ := by
  rw [hasNaturalDensity_def] at hT ⊢
  let c : ℝ := ∑ v ∈ hST.toFinset, (S.indicator 1 v - T.indicator 1 v)
  have hzero : Tendsto (fun x : ℝ =>
      (TauCeti.primeCount K S x - TauCeti.primeCount K T x) /
        TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 0) := by
    refine ((TauCeti.tendsto_primeCount_univ_atTop K).const_div_atTop c).congr' ?_
    filter_upwards [TauCeti.eventually_primeCount_sub_eq hST] with x hx
    rw [hx]
  have hsum := hT.add hzero
  simp only [add_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun x => ?_)
  ring

/-- Two prime sets with finite symmetric difference have natural density `δ` simultaneously. -/
theorem hasNaturalDensity_iff_of_finite_symmDiff (hST : (symmDiff S T).Finite) :
    HasNaturalDensity S δ ↔ HasNaturalDensity T δ := by
  refine ⟨fun h => h.of_finite_symmDiff ?_, fun h => h.of_finite_symmDiff hST⟩
  simpa [symmDiff_comm] using hST

/-- Every finite set of prime ideals has natural density zero. -/
theorem hasNaturalDensity_of_finite (hS : S.Finite) : HasNaturalDensity S 0 := by
  refine hasNaturalDensity_empty.of_finite_symmDiff ?_
  simpa [Set.symmDiff_def] using hS

end NumberField.Set
