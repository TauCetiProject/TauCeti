/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Radical.Basic

import TauCeti.RingTheory.Polynomial.Localization

/-!
# Zeros and separability of the radical of a polynomial

Let `R` be a commutative ring equipped with normalization (`NormalizationMonoid`) and unique
factorization (`UniqueFactorizationMonoid`), and let `f` be a polynomial in `R[X]`. For `f ≠ 0`,
`radical f` is the product of the distinct normalized prime factors of `f` in `R[X]`, each
occurring once; for `f = 0`, `radical 0 = 1`.

* `Polynomial.roots_toFinset_map_radical`: after any ring map to a domain, the images of
  `radical f` and `f` have the same finite set of roots (`roots.toFinset`). For `f ≠ 0` this holds
  because `radical f ∣ f ∣ radical f ^ n` (by Mathlib's
  `UniqueFactorizationMonoid.radical_dvd_self` and
  `UniqueFactorizationMonoid.exists_dvd_radical_self_pow`), so the two images vanish together, and
  `roots 0` is empty. For `f = 0` both sets are empty, as `radical 0 = 1`.
* `Polynomial.separable_map_radical`: if the fraction field `K` of `R` is perfect, then for every
  commutative `K`-algebra `L` (compatibly an `R`-algebra via `R → K → L`), the image of `radical f`
  along `algebraMap R L` is separable. By `UniqueFactorizationMonoid.squarefree_radical`,
  `radical f` is squarefree in `R[X]`; squarefreeness passes to `K[X]` by
  `Squarefree.map_localization_map`, becomes separability over `K` by
  `PerfectField.separable_iff_squarefree`, and then maps along `K → L`.
-/

public section

open UniqueFactorizationMonoid

namespace Polynomial

/-- After a ring map to a domain, the radical of a polynomial over a commutative ring equipped
with normalization and unique factorization has the same finite set of roots (`roots.toFinset`) as
the polynomial itself. For `f ≠ 0` this follows from `radical f ∣ f ∣ radical f ^ n`: the two
images vanish together, and then both sets are empty, since `roots 0 = 0`. For `f = 0` both sets
are empty, as `radical 0 = 1`. -/
theorem roots_toFinset_map_radical {R S : Type*} [CommRing R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [CommRing S] [IsDomain S] [DecidableEq S] (f : R[X])
    (φ : R →+* S) : ((radical f).map φ).roots.toFinset = (f.map φ).roots.toFinset := by
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
  refine Finset.Subset.antisymm (Multiset.toFinset_subset.2 ?_) (Multiset.toFinset_subset.2 ?_)
  · exact Multiset.subset_of_le (roots.le_of_dvd hf' hr)
  · have hsub := Multiset.subset_of_le
      (roots.le_of_dvd (pow_ne_zero n (ne_zero_of_dvd_ne_zero hf' hr)) hn')
    rw [roots_pow] at hsub
    exact Multiset.Subset.trans hsub (Multiset.smul_subset_self _ n)

/-- Let `R` be a commutative ring equipped with normalization and unique factorization whose
fraction field `K` is perfect. The radical of a polynomial `f : R[X]` maps to a separable
polynomial along `R → K → L` for every commutative `K`-algebra `L`. -/
theorem separable_map_radical {R : Type*} [CommRing R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] (f : R[X]) (K L : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] [PerfectField K] [CommSemiring L] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] : ((radical f).map (algebraMap R L)).Separable := by
  have hK : ((radical f).map (algebraMap R K)).Separable :=
    PerfectField.separable_iff_squarefree.2 <|
      squarefree_radical.map_localization_map (nonZeroDivisors R)
  have h := hK.map (f := algebraMap K L)
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h

end Polynomial
