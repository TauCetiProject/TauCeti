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
* `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap_pi`: the diagonal image of `R` is
  dense in the product of the completed integer rings at a finite set of places.

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

/-- The diagonal image of a Dedekind domain is dense in the product of the completed integer rings
over any subtype of its height one primes. Product neighborhoods involve only finitely many
coordinates, so no finiteness assumption on the subtype is needed. -/
theorem denseRange_algebraMap_pi_subtype (p : HeightOneSpectrum R → Prop) :
    DenseRange fun (x : R) (v : {v : HeightOneSpectrum R // p v}) ↦
      algebraMap R (v.1.adicCompletionIntegers K) x := by
  classical
  intro y
  refine mem_closure_iff_nhds.mpr fun U hU ↦ ?_
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hIt⟩ := hU
  have hzero (v : {v : HeightOneSpectrum R // p v}) :
      (fun z : v.1.adicCompletionIntegers K ↦ y v - z) ⁻¹' t v ∈ nhds 0 :=
    (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht v)
  let n : {v : HeightOneSpectrum R // p v} → ℕ := fun v ↦
    (v.1.exists_maximalIdeal_pow_subset_of_mem_nhds (K := K) (hzero v)).choose
  have hn (v : {v : HeightOneSpectrum R // p v}) :=
    (v.1.exists_maximalIdeal_pow_subset_of_mem_nhds (K := K) (hzero v)).choose_spec
  let x : ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K := fun v ↦
    if hv : p v then y ⟨v, hv⟩ else 0
  let m : HeightOneSpectrum R → ℕ := fun v ↦
    if hv : p v then n ⟨v, hv⟩ else 0
  obtain ⟨r, hr⟩ := exists_forall_valued_sub_le
    (K := K) (hI.toFinset.image fun v ↦ v.1) x m
  refine ⟨(fun v ↦ algebraMap R (v.1.adicCompletionIntegers K) r), ?_, r, rfl⟩
  apply hIt
  intro v hv
  have happ := hr v.1 (Finset.mem_image.mpr ⟨v, hI.mem_toFinset.mpr hv, rfl⟩)
  have hmem : y v - algebraMap R (v.1.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (v.1.adicCompletionIntegers K) ^ n v := by
    rw [v.1.mem_maximalIdeal_pow_iff (K := K)]
    -- The maximal-ideal criterion coerces local integers into the completion; expose that
    -- stable subtype coercion to match the valuation estimate returned by approximation.
    change Valued.v ((y v : v.1.adicCompletion K) -
      algebraMap R (v.1.adicCompletion K) r) ≤ exp (-(n v : ℤ))
    have hxv : x v.1 = y v := by simp only [x, dite_eq_left v.2]
    have hmv : m v.1 = n v := by simp only [m, dite_eq_left v.2]
    rw [hxv, hmv] at happ
    exact happ
  have := hn v hmem
  simpa only [Set.mem_preimage, sub_sub_cancel] using this

/-- The diagonal image of a Dedekind domain is dense in the product of the completed integer rings
at any finite set of height one primes. -/
theorem denseRange_algebraMap_pi (s : Finset (HeightOneSpectrum R)) :
    DenseRange fun (x : R) (v : {v : HeightOneSpectrum R // v ∈ s}) ↦
      algebraMap R (v.1.adicCompletionIntegers K) x :=
  denseRange_algebraMap_pi_subtype (K := K) (fun v ↦ v ∈ s)

end IsDedekindDomain.HeightOneSpectrum
