/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Radical.Basic
public import TauCeti.NumberTheory.NumberField.PrimeIdeal

/-!
# Norm products of conjugate factors of rational integers

When `z * conj z = M` in the integers of a CM field, the absolute norm of `(z)` is
`M` to the power of the number of infinite places. If `(M)` is squarefree, the same
formula holds for the product of the norms of the distinct primes containing `z`.
In particular, this computes the product for distinct unramified level primes, including
primes that split completely.

The level-prime application is `New.Data.prod_q_chosenPlace` in
`grh/src/New/UpperBound/Objects/LiftChains.lean` of lsernau/grh-lean (commit `72fead1`).
-/

public section

open Ideal Module IsDedekindDomain UniqueFactorizationMonoid

namespace NumberField.IsCMField

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]

/-- A factor of a rational integer in a conjugate factorization has absolute ideal norm
`M` raised to the number of infinite places. -/
theorem absNorm_span_singleton_of_mul_conj_eq_natCast (z : 𝓞 E) {M : ℕ}
    (hz : z * ringOfIntegersComplexConj E z = M) :
    absNorm (span {z}) = M ^ Fintype.card (InfinitePlace E) := by
  let σ := (ringOfIntegersComplexConj E).restrictScalars ℤ
  have hn : absNorm (span {σ z}) = absNorm (span {z}) := by
    simp only [absNorm_span_singleton, Algebra.norm_eq_of_algEquiv σ]
  have hdegree : finrank ℤ (𝓞 E) = 2 * Fintype.card (InfinitePlace E) := by
    rw [RingOfIntegers.rank, IsTotallyComplex.finrank,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  apply Nat.pow_left_injective (n := 2) (by decide)
  calc
    absNorm (span {z}) ^ 2 = absNorm (span {z} * span {σ z}) := by
      rw [map_mul, hn, pow_two]
    _ = absNorm (span {(M : 𝓞 E)}) := by
      dsimp only [σ, AlgEquiv.restrictScalars_apply]
      rw [span_singleton_mul_span_singleton, hz]
    _ = (M ^ Fintype.card (InfinitePlace E)) ^ 2 := by
      rw [absNorm_span_natCast, hdegree, mul_comm 2, pow_mul]

/-- If `(z)` is squarefree and `z * conj z = M`, the product of the norms of the prime
ideals dividing `(z)` is `M` to the power of the number of infinite places. -/
theorem prod_absNorm_primeFactors_span_singleton_of_mul_conj_eq_natCast (z : 𝓞 E) {M : ℕ}
    (hz : z * ringOfIntegersComplexConj E z = M)
    (hsq : Squarefree (span {z} : Ideal (𝓞 E))) :
    ∏ P ∈ primeFactors (span {z} : Ideal (𝓞 E)), absNorm P =
      M ^ Fintype.card (InfinitePlace E) := by
  have h₀ : (span {z} : Ideal (𝓞 E)) ≠ ⊥ := hsq.ne_zero
  have hrad := associated_iff_eq.mp
    (radical_associated ((isRadical_iff_squarefree_of_ne_zero h₀).mpr hsq) h₀)
  rw [← map_prod]
  exact (congrArg absNorm hrad).trans (absNorm_span_singleton_of_mul_conj_eq_natCast E z hz)

open Classical in
/-- For a finite set of distinct unramified rational primes with product `z * conj z`,
select the prime ideals above them that contain `z`. The product of their absolute norms is
the rational prime product raised to the number of infinite places. -/
theorem prod_absNorm_filter_mem_of_mul_conj_eq_prod (z : 𝓞 E) {T : Finset ℕ}
    (hT : ∀ p ∈ T, p.Prime)
    (hun : ∀ p ∈ T, ∀ P : Ideal (𝓞 E), ∀ [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      Algebra.IsUnramifiedAt (𝓞 ℚ) P)
    (hz : z * ringOfIntegersComplexConj E z = ((∏ p ∈ T, p : ℕ) : 𝓞 E)) :
    ∏ P ∈ (T.biUnion fun p ↦ primesOverFinset (span {(p : ℤ)}) (𝓞 E)).filter (fun P ↦ z ∈ P),
      absNorm P = (∏ p ∈ T, p) ^ Fintype.card (InfinitePlace E) := by
  let S := T.biUnion fun p ↦ primesOverFinset (span {(p : ℤ)}) (𝓞 E)
  let M := ∏ p ∈ T, p
  let I : Ideal (𝓞 E) := span {(M : 𝓞 E)}
  have hprod : ∏ P ∈ S, P = I :=
    TauCeti.NumberField.prod_biUnion_primesOverFinset_eq_span_prod hT hun
  have hS (P : Ideal (𝓞 E)) (hP : P ∈ S) : Prime P := by
    obtain ⟨p, hp, hprime, _⟩ :=
      (TauCeti.NumberField.mem_biUnion_primesOverFinset_iff (K := E) hT).mp hP
    have hP₀ : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot (p := span {(p : ℤ)})
      (by simp [(hT p hp).ne_zero]) P
    exact prime_of_isPrime hP₀ hprime
  have hfac : normalizedFactors I = S.val := by
    rw [← hprod, Finset.prod_eq_multiset_prod, Multiset.map_id']
    exact normalizedFactors_prod_of_prime fun P hP ↦ hS P (Finset.mem_def.mpr hP)
  have h₀ : I ≠ ⊥ := by
    rw [← hprod]
    exact Finset.prod_ne_zero_iff.mpr fun P hP ↦ (hS P hP).ne_zero
  have hsq : Squarefree I := (squarefree_iff_nodup_normalizedFactors h₀).mpr (hfac ▸ S.nodup)
  have hd : (span {z} : Ideal (𝓞 E)) ∣ I :=
    ⟨span {ringOfIntegersComplexConj E z}, by rw [span_singleton_mul_span_singleton, hz]⟩
  have hsqz := hsq.squarefree_of_dvd hd
  have hz₀ : (span {z} : Ideal (𝓞 E)) ≠ ⊥ := hsqz.ne_zero
  have hfilter : primeFactors (span {z} : Ideal (𝓞 E)) = S.filter (fun P ↦ z ∈ P) := by
    ext P
    simp only [mem_primeFactors, Finset.mem_filter,
      UniqueFactorizationMonoid.mem_normalizedFactors_iff hz₀, dvd_span_singleton]
    refine ⟨fun ⟨hP, hmem⟩ ↦ ⟨?_, hmem⟩, fun ⟨hP, hmem⟩ ↦ ⟨hS P hP, hmem⟩⟩
    have hPI : P ∈ normalizedFactors I :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff h₀).mpr
        ⟨hP, (dvd_span_singleton.mpr hmem).trans hd⟩
    exact Finset.mem_def.mpr (hfac ▸ hPI)
  rw [← hfilter]
  exact prod_absNorm_primeFactors_span_singleton_of_mul_conj_eq_natCast E z hz hsqz

end NumberField.IsCMField
