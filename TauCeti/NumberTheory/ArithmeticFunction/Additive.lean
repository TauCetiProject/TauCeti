/-
Copyright (c) 2023 Arend Mellendijk and 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Additive arithmetic functions and normalization

`ArithmeticFunction.IsAdditiveOnCoprime` is the positive coprime-product law alone. It does not
require the value at one to vanish: with a noncancellative target, that value may be a nonzero
additive idempotent. `ArithmeticFunction.IsAdditive` includes the normalization at one. With the
usual additive zero laws, left cancellation makes the two conditions agree. The predicates need
only zero and addition; no associativity or commutativity is imposed.

Both predicates use Mathlib's `ArithmeticFunction`, so the value at zero is zero. The weak coprime
law retains positive-input guards. For `AddZeroClass` targets, its instance at zero and one would
force normalization, and an unrestricted complete product-to-sum law at zero would force every
value to zero.
The weak relation and the motivating exponentiation consequence come from Arend Mellendijk's
PNT+ Iwaniec–Kowalski Chapter 1 formalization.

`ArithmeticFunction.IsAdditive.isMultiplicative_of_eq_monoidHom` sends a normalized additive
function through a monoid homomorphism from `Multiplicative A`. Its conclusion uses Mathlib's
multiplicative predicate, including the cases of zero inputs. Natural powers are a specialization
through Mathlib's `powersHom`; the output's value at zero is supplied by its arithmetic carrier.

For complete additivity with an `AddZeroClass` target, Mathlib's non-unital homomorphisms from
positive naturals to `Multiplicative A` express the unnormalized positive-product law; the unital
homomorphisms also express the normalization at one. No separate complete-additive predicate is
introduced here.
-/

public section

namespace ArithmeticFunction

/-- The additive law on positive coprime inputs, without normalization at one. -/
structure IsAdditiveOnCoprime {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) : Prop where
  /-- Values add on positive coprime products. -/
  map_mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m + f n

/-- A normalized additive arithmetic function has value zero at one and adds on positive
coprime products. -/
structure IsAdditive {A : Type*} [Zero A] [Add A] (f : ArithmeticFunction A) : Prop
    extends IsAdditiveOnCoprime f where
  /-- The value at one vanishes. -/
  @[simp] map_one : f 1 = 0

/-- Left cancellation forces the value at one to vanish, so the coprime-product law is normalized.
No associativity or commutativity of addition is needed. -/
theorem IsAdditiveOnCoprime.isAdditive {A : Type*} [AddZeroClass A] [IsLeftCancelAdd A]
    {f : ArithmeticFunction A} (hf : IsAdditiveOnCoprime f) : IsAdditive f := by
  refine ⟨hf, ?_⟩
  have h : f 1 + 0 = f 1 + f 1 := by
    simpa using hf.map_mul one_ne_zero one_ne_zero (Nat.coprime_one_left 1)
  exact (add_left_cancel h).symm

/-- Applying a monoid homomorphism to the positive values of a normalized additive function
produces a multiplicative arithmetic function. The output's zero value is already part of its
arithmetic-function carrier. -/
theorem IsAdditive.isMultiplicative_of_eq_monoidHom {A R : Type*} [AddZeroClass A]
    [MonoidWithZero R] {f : ArithmeticFunction A} (hf : IsAdditive f)
    (φ : Multiplicative A →* R) {g : ArithmeticFunction R}
    (hg : ∀ n : ℕ, n ≠ 0 → g n = φ (Multiplicative.ofAdd (f n))) :
    g.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨?_, ?_⟩
  · simpa [hf.map_one] using hg 1 one_ne_zero
  intro m n hm hn hmn
  rw [hg (m * n) (mul_ne_zero hm hn), hf.map_mul hm hn hmn,
    Multiplicative.ofAdd_add, map_mul, hg m hm, hg n hn]

end ArithmeticFunction
