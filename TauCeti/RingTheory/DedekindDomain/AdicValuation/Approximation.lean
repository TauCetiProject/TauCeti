/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Simultaneous approximation in finitely many adic completions

Let `R` be a Dedekind domain with fraction field `K`. Given finitely many height one primes `v` of
`R` and an element of the ring of integers `𝒪_v` of `K_v` at each of them, a single element of `R`
approximates all of them at once, to any prescribed precision at each place. This combines the
single-place density of `R` in `𝒪_v` (`HeightOneSpectrum.exists_valued_sub_le`) with the Chinese
remainder theorem for pairwise distinct primes (`IsDedekindDomain.exists_forall_sub_mem_ideal`).

## Main results

* `IsDedekindDomain.HeightOneSpectrum.exists_forall_valued_sub_le`: finitely many local integers
  are simultaneously approximated by one element of `R`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §3 (the Chinese remainder theorem).
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

open WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **Simultaneous approximation by elements of `R`.** Finitely many elements of the rings of
integers `𝒪_v` of the completions of `K` are approximated by a single element of `R`, to any
prescribed precision at each of the finitely many places. -/
theorem exists_forall_valued_sub_le (s : Finset (HeightOneSpectrum R))
    (x : ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) (n : HeightOneSpectrum R → ℕ) :
    ∃ r : R, ∀ v ∈ s,
      Valued.v ((x v : v.adicCompletion K) - algebraMap R (v.adicCompletion K) r) ≤
        exp (-(n v : ℤ)) := by
  choose a ha using fun v : HeightOneSpectrum R ↦ v.exists_valued_sub_le (x v) (n v)
  obtain ⟨r, hr⟩ := exists_forall_sub_mem_ideal (s := s) (fun v ↦ v.asIdeal) n
    (fun v _ ↦ v.prime) (fun _ _ _ _ hvw h ↦ hvw (HeightOneSpectrum.ext h)) (fun v ↦ a v)
  refine ⟨r, fun v hv ↦ ?_⟩
  rw [← sub_add_sub_cancel _ (algebraMap R (v.adicCompletion K) (a v))]
  refine Valuation.map_add_le _ (ha v) ?_
  rw [← map_sub, valuedAdicCompletion_eq_valuation, valuation_of_algebraMap,
    Valuation.map_sub_swap, intValuation_le_pow_iff_mem]
  exact hr v hv

end IsDedekindDomain.HeightOneSpectrum
