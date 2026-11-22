/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Radical.Basic

import TauCeti.RingTheory.Polynomial.Localization

/-!
# Zeros and separability of the radical of a polynomial

Let `f` be a polynomial over a unique factorization monoid `R`, and `radical f` its radical in
`R[X]`, the product of its normalized prime factors.

* `Polynomial.roots_toFinset_map_radical`: after any map to a domain, `radical f` and `f` have
  the same zeros, since `radical f ∣ f ∣ radical f ^ n`.
* `Polynomial.separable_map_radical`: if the fraction field `K` of `R` is perfect, the image of
  `radical f` is separable over every `K`-algebra. It is squarefree over `K` because
  squarefreeness passes to localizations (`Squarefree.map_localization_map`).
-/

public section

open UniqueFactorizationMonoid

namespace Polynomial

/-- After a map to a domain, the radical of a polynomial over a unique factorization monoid has
the same zeros as the polynomial itself, since `radical f ∣ f ∣ radical f ^ n`. -/
theorem roots_toFinset_map_radical {R S : Type*} [CommRing R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [CommRing S] [IsDomain S] [DecidableEq S] (φ : R →+* S)
    (f : R[X]) : ((radical f).map φ).roots.toFinset = (f.map φ).roots.toFinset := by
  rcases eq_or_ne f 0 with hf | hf
  · simp [hf]
  obtain ⟨n, hn⟩ := exists_dvd_radical_self_pow hf
  have hn' : f.map φ ∣ (radical f).map φ ^ n := by
    rw [← Polynomial.map_pow]
    exact Polynomial.map_dvd φ hn
  have hr := Polynomial.map_dvd φ (radical_dvd_self (a := f))
  rcases eq_or_ne (f.map φ) 0 with hf' | hf'
  · rw [hf', zero_dvd_iff] at hn'
    rw [hf', eq_zero_of_pow_eq_zero hn']
  refine Finset.Subset.antisymm (Multiset.toFinset_subset.2 ?_) fun α hα ↦ ?_
  · exact Multiset.subset_of_le (roots.le_of_dvd hf' hr)
  · have hα' := Multiset.mem_of_le
      (roots.le_of_dvd (pow_ne_zero n (ne_zero_of_dvd_ne_zero hf' hr)) hn')
      (Multiset.mem_toFinset.1 hα)
    rw [roots_pow] at hα'
    exact Multiset.mem_toFinset.2 (Multiset.mem_of_mem_nsmul hα')

/-- The radical of a polynomial over a unique factorization monoid `R` whose fraction field `K`
is perfect is separable over every `K`-algebra. -/
theorem separable_map_radical {R : Type*} (K L : Type*) [CommRing R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField K]
    [CommSemiring L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] (f : R[X]) :
    ((radical f).map (algebraMap R L)).Separable := by
  have hK : ((radical f).map (algebraMap R K)).Separable :=
    PerfectField.separable_iff_squarefree.2 <|
      squarefree_radical.map_localization_map (nonZeroDivisors R)
  have h := hK.map (f := algebraMap K L)
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h

end Polynomial
