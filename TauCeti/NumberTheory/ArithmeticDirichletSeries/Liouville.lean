/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight

/-!
# The ideal Liouville weight

The ideal Liouville weight of a number field `K` is `I ↦ (-1) ^ Ω(I)` on nonzero integral ideals
of `𝓞 K` (and `0` at `⊥`), where `Ω(I)` is the number of prime ideal factors of `I` counted with
multiplicity. Unlike the ideal Möbius function (`TauCeti.IdealArithmeticFunction.moebius`), it is
completely multiplicative with no bad primes, so it packages directly as a
`TauCeti.MultiplicativeIdealWeight K` whose pointwise square is `1`.

## Main definitions

* `TauCeti.MultiplicativeIdealWeight.liouville`: the ideal Liouville weight `I ↦ (-1) ^ Ω(I)` on
  integral ideals of `𝓞 K`.

## Main results

* `TauCeti.MultiplicativeIdealWeight.liouville_apply`: formula on nonzero integral ideals.
* `TauCeti.MultiplicativeIdealWeight.liouville_prime`: value `-1` at every height-one prime.
* `TauCeti.MultiplicativeIdealWeight.badPrimes_liouville`: the bad-prime set is empty.
* `TauCeti.MultiplicativeIdealWeight.liouville_sq`: `liouville K ^ 2 = 1`.
* `TauCeti.MultiplicativeIdealWeight.isTrivialOnGood_liouville_sq`:
  `(liouville K ^ 2).IsTrivialOnGood`.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti.MultiplicativeIdealWeight

open IsDedekindDomain NumberField
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- Underlying monoid-with-zero homomorphism for `liouville K`. -/
private noncomputable def liouvilleHom : Ideal (𝓞 K) →*₀ ℂ where
  toFun I := if I = ⊥ then 0 else (-1 : ℂ) ^ (UniqueFactorizationMonoid.normalizedFactors I).card
  map_zero' := by simp
  map_one' := by
    simp only [Ideal.one_eq_top, top_ne_bot, ↓reduceIte]
    rw [← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]
    simp
  map_mul' I J := by
    by_cases hI : I = ⊥
    · simp [hI]
    by_cases hJ : J = ⊥
    · simp [hJ]
    have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
    simp only [hI, hJ, hIJ, ↓reduceIte]
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.card_add, pow_add]

-- Reduces the `MonoidWithZeroHom` coercion of `liouvilleHom` to its `if`-expression.
private theorem liouvilleHom_apply (I : Ideal (𝓞 K)) :
    liouvilleHom K I =
      if I = ⊥ then 0 else (-1 : ℂ) ^ (UniqueFactorizationMonoid.normalizedFactors I).card :=
  rfl

/-- **The ideal Liouville weight** `I ↦ (-1) ^ Ω(I)` on integral ideals of `𝓞 K` (with value `0`
at `⊥`), where `Ω(I)` is the number of prime ideal factors of `I` counted with multiplicity.

It has no bad primes and satisfies `liouville K ^ 2 = 1`. -/
noncomputable def liouville : MultiplicativeIdealWeight K where
  toMonoidWithZeroHom := liouvilleHom K
  finite_setOf_apply_eq_zero := by
    refine Set.finite_empty.subset fun P hP ↦ ?_
    rw [Set.mem_ofPred_eq, liouvilleHom_apply] at hP
    simp [P.ne_bot] at hP

-- Reduces the `MultiplicativeIdealWeight` coercion of `liouville K` to `liouvilleHom K`.
private theorem liouville_eq_liouvilleHom (I : Ideal (𝓞 K)) :
    liouville K I = liouvilleHom K I :=
  rfl

/-- Defining formula for `liouville K` on nonzero ideals. -/
theorem liouville_apply {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    liouville K I = (-1 : ℂ) ^ (UniqueFactorizationMonoid.normalizedFactors I).card := by
  rw [liouville_eq_liouvilleHom, liouvilleHom_apply]
  simp [hI]

/-- The ideal Liouville weight takes the value `-1` at every height-one prime. -/
@[simp]
theorem liouville_prime (P : HeightOneSpectrum (𝓞 K)) : liouville K P.asIdeal = -1 := by
  rw [liouville_apply K P.ne_bot,
    UniqueFactorizationMonoid.normalizedFactors_irreducible P.prime.irreducible]
  simp

/-- The ideal Liouville weight has no bad primes. -/
@[simp]
theorem badPrimes_liouville : (liouville K).badPrimes = ∅ := by
  ext P
  simp [mem_badPrimes]

/-- The pointwise square of the ideal Liouville weight is the trivial weight. -/
@[simp]
theorem liouville_sq : liouville K ^ 2 = 1 := by
  apply ext_heightOneSpectrum
  intro P
  simp [pow_apply _ two_ne_zero, one_apply, P.ne_bot]

/-- The square of the ideal Liouville weight is trivial on its good ideals. -/
theorem isTrivialOnGood_liouville_sq : (liouville K ^ 2).IsTrivialOnGood := by
  rw [liouville_sq]
  exact isTrivialOnGood_one

end TauCeti.MultiplicativeIdealWeight
