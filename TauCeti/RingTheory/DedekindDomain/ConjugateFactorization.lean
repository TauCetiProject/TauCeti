/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import TauCeti.Combinatorics.Enumerative.InvolutionTransversal
public import TauCeti.RingTheory.UniqueFactorizationDomain.SubsetProduct

/-!
# Factoring a product of conjugate primes in a Dedekind domain

Let `R` be a Dedekind domain carrying a ring involution `σ`, and let `S` be a finite set of
nonzero primes of `R` which `σ` permutes, involutively and without fixing any of them, so that
`S` splits into conjugate pairs `{p, σ p}`. This file describes the ideals `A` with
`A * σ A = ∏ p ∈ S, p`: they are exactly the products over the transversals of `σ` on `S`, one
prime chosen from each conjugate pair, and there are exactly `2 ^ (#S / 2)` of them.

The count is what makes such factorizations a source of many ideals with a prescribed conjugate
product: taking `S` to be a set of primes above rational primes that split into conjugate pairs,
the theorem produces exactly `2 ^ (#S / 2)` ideals `A` with `A · σA` the prescribed ideal. The
argument is the interplay of two facts: a divisor of a product of distinct primes is the product
of a subset of them (`UniqueFactorizationMonoid.exists_subset_finset_prod_eq_of_dvd`), and the
transversals of a fixed-point-free involution are counted by
`TauCeti.ncard_setOf_isInvolutionTransversal`.

## References

The existence half of the count is `exists_transversal_family` in the formalization
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), written for
Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where it is stated as
the lower bound `2 ^ (#S / 2) ≤ #G` for a family `G` of such ideals. The induction on `S` that
strips off one conjugate pair at a time is taken from there; it is carried out here on the
transversals rather than on the ideals, which turns the bound into the exact count and separates
the combinatorics from the arithmetic.

## Main results

* `TauCeti.mul_map_eq_prod_iff`: `A * σ A = ∏ p ∈ S, p` exactly when `A` is the product over a
  transversal of `σ` on `S`.
* `TauCeti.ncard_setOf_mul_map_eq_prod`: there are exactly `2 ^ (#S / 2)` such `A`.
-/

public section

namespace TauCeti

open UniqueFactorizationMonoid

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {σ : R ≃+* R} {S : Finset (Ideal R)}

/-- **The conjugate factorizations of a product of paired primes.** If a ring involution `σ`
permutes a finite set `S` of nonzero primes without fixing any of them, then the ideals `A` with
`A * σ A = ∏ p ∈ S, p` are exactly the products over the transversals of `σ` on `S`. -/
theorem mul_map_eq_prod_iff (hprime : ∀ p ∈ S, p.IsPrime) (hbot : ∀ p ∈ S, p ≠ ⊥)
    (hmaps : ∀ p ∈ S, Ideal.map σ p ∈ S) (hinvol : ∀ p ∈ S, Ideal.map σ (Ideal.map σ p) = p)
    {A : Ideal R} :
    A * Ideal.map σ A = ∏ p ∈ S, p ↔
      ∃ T, IsInvolutionTransversal (Ideal.map σ) S T ∧ A = ∏ p ∈ T, p := by
  classical
  have hp : ∀ p ∈ S, Prime p :=
    fun p hpS => (Ideal.prime_iff_isPrime (hbot p hpS)).2 (hprime p hpS)
  have hmapprod : ∀ T : Finset (Ideal R), Ideal.map σ (∏ p ∈ T, p) = ∏ p ∈ T, Ideal.map σ p :=
    fun T => map_prod (Ideal.mapHom σ) (fun p : Ideal R => p) T
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨T, hTS, rfl⟩ :=
      exists_subset_finset_prod_eq_of_dvd hp ⟨Ideal.map σ A, h.symm⟩
    refine ⟨T, ?_, rfl⟩
    -- The conjugates of `T` form a second subset `T'` of `S`, and `T` and `T'` partition `S`.
    set T' := T.image (Ideal.map σ)
    have hT'S : T' ⊆ S := by
      intro q hq
      obtain ⟨p, hp', rfl⟩ := Finset.mem_image.1 hq
      exact hmaps p (hTS hp')
    have hinj : Set.InjOn (Ideal.map σ) T := fun x hx y hy hxy => by
      rw [← hinvol x (hTS hx), ← hinvol y (hTS hy), hxy]
    have hprodT' : ∏ q ∈ T', q = ∏ p ∈ T, Ideal.map σ p := Finset.prod_image hinj
    have hsum : T.val + T'.val = S.val := by
      have hTne : ∏ p ∈ T, p ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun p hp' => (hp p (hTS hp')).ne_zero
      have hT'ne : ∏ q ∈ T', q ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun q hq => (hp q (hT'S hq)).ne_zero
      have := congrArg normalizedFactors h
      rwa [hmapprod, ← hprodT', normalizedFactors_mul hTne hT'ne,
        normalizedFactors_finset_prod_of_prime fun p hp' => hp p (hTS hp'),
        normalizedFactors_finset_prod_of_prime fun q hq => hp q (hT'S hq),
        normalizedFactors_finset_prod_of_prime hp] at this
    have hdisj : ∀ a ∈ T, a ∉ T' := by
      intro a haT haT'
      have hcount : 2 ≤ Multiset.count a S.val := by
        rw [← hsum, Multiset.count_add]
        have h1 := Multiset.count_eq_one_of_mem T.nodup haT
        have h2 := Multiset.count_eq_one_of_mem T'.nodup haT'
        omega
      exact absurd (Multiset.nodup_iff_count_le_one.1 S.nodup a) (by omega)
    refine isInvolutionTransversal_of_cover hinvol hTS (fun a ha h => hdisj _ h ?_) fun a ha => ?_
    · exact Finset.mem_image.2 ⟨a, ha, rfl⟩
    · have : a ∈ T.val + T'.val := hsum ▸ ha
      rcases Multiset.mem_add.1 this with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Finset.mem_image.1 h')
  · rintro ⟨T, hT, rfl⟩
    rw [hmapprod]
    exact hT.prod_mul_prod_comp (fun p => p) hmaps hinvol

/-- **The conjugate factorization count.** A finite set `S` of nonzero primes permuted by a ring
involution `σ` without fixed points admits exactly `2 ^ (#S / 2)` factorizations
`A * σ A = ∏ p ∈ S, p`: one for each choice of a prime from each conjugate pair. -/
theorem ncard_setOf_mul_map_eq_prod (hprime : ∀ p ∈ S, p.IsPrime) (hbot : ∀ p ∈ S, p ≠ ⊥)
    (hmaps : ∀ p ∈ S, Ideal.map σ p ∈ S) (hinvol : ∀ p ∈ S, Ideal.map σ (Ideal.map σ p) = p)
    (hfree : ∀ p ∈ S, Ideal.map σ p ≠ p) :
    {A : Ideal R | A * Ideal.map σ A = ∏ p ∈ S, p}.ncard = 2 ^ (S.card / 2) := by
  have hp : ∀ p ∈ S, Prime p :=
    fun p hpS => (Ideal.prime_iff_isPrime (hbot p hpS)).2 (hprime p hpS)
  have hinj : Set.InjOn (fun T : Finset (Ideal R) => ∏ p ∈ T, p)
      {T | IsInvolutionTransversal (Ideal.map σ) S T} := fun T₁ h₁ T₂ h₂ h =>
    (finset_prod_eq_iff_of_prime (fun p hp' => hp p (h₁.subset hp'))
      (fun p hp' => hp p (h₂.subset hp'))).1 h
  have hset : {A : Ideal R | A * Ideal.map σ A = ∏ p ∈ S, p} =
      (fun T : Finset (Ideal R) => ∏ p ∈ T, p) ''
        {T | IsInvolutionTransversal (Ideal.map σ) S T} :=
    Set.ext fun A => (mul_map_eq_prod_iff hprime hbot hmaps hinvol).trans
      ⟨fun ⟨T, hT, hA⟩ => ⟨T, hT, hA.symm⟩, fun ⟨T, hT, hA⟩ => ⟨T, hT, hA.symm⟩⟩
  rw [hset, hinj.ncard_image, ncard_setOf_isInvolutionTransversal hmaps hinvol hfree]

end TauCeti
