/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Separation and integral elements of the finite adele ring

Mathlib's `IsDedekindDomain.FiniteAdeleRing R K` is the restricted product of the completions
`v.adicCompletion K` over the height one primes `v` of a Dedekind domain `R` with fraction field
`K`, with respect to the integer rings `v.adicCompletionIntegers K`.  This file records two basic
facts about it that are not stated in Mathlib:

* the finite adele ring is Hausdorff, since each completion is;
* an element of `K` is integral at every finite place exactly when it lies in `R`, so the integral
  finite adeles meet the diagonal copy of `K` in `R`.

The second fact is the finite half of the discreteness of a number field in its adele ring.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.forall_algebraMap_mem_adicCompletionIntegers_iff`: the diagonal
  image of `x : K` is integral at every finite place if and only if `x` lies in `R`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II.
-/

public section

namespace IsDedekindDomain.FiniteAdeleRing

open HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

instance : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs <| T2Space <|
    RestrictedProduct (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
      (fun v ↦ v.adicCompletionIntegers K) Filter.cofinite

variable {R K} in
/-- The diagonal image of an element of `K` in the finite adele ring is integral at every finite
place exactly when the element lies in `R`. -/
theorem forall_algebraMap_mem_adicCompletionIntegers_iff (x : K) :
    (∀ v : HeightOneSpectrum R,
        algebraMap K (FiniteAdeleRing R K) x v ∈ v.adicCompletionIntegers K) ↔
      x ∈ (algebraMap R K).range := by
  simp only [algebraMap_apply, mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']
  refine ⟨mem_integers_of_valuation_le_one K x, ?_⟩
  rintro ⟨r, rfl⟩ v
  exact v.valuation_le_one r

end IsDedekindDomain.FiniteAdeleRing
