/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Graded supercommutativity

In a (possibly nonunital, nonassociative) ring `A` equipped with a family of homogeneous pieces
`ℬ : ι → σ` indexed by a Koszul-signed degree semiring `ι` (`[CommSemiring ι]
[Module ι (Additive ℤˣ)]`, in particular `ℤ`, `ℕ`, and `ZMod 2`), Koszul graded commutativity
`a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a)` for `a ∈ ℬ p` and `b ∈ ℬ q` has two direct consequences:

* When `ℬ` gives a `DirectSum.Decomposition` of `A`, every homogeneous element whose degree `p`
  has Koszul sign `(-1 : ℤˣ) ^ p = 1` (in particular, degree `0`) commutes with every element of
  `A`.
* Without requiring a decomposition, every homogeneous element whose degree `p` has Koszul sign
  `(-1 : ℤˣ) ^ p = -1` (in particular, degree `1`) satisfies `a * a = -(a * a)`.

## Main results

* `TauCeti.commute_of_mul_eq_uzpow_smul_mul`: a homogeneous element of degree `p` with
  `(-1 : ℤˣ) ^ p = 1` commutes with every element of `A`.
* `TauCeti.commute_of_mul_eq_uzpow_smul_mul_of_mem_zero`: every element of degree `0` commutes
  with every element of `A`.
* `TauCeti.mul_self_eq_neg_of_mul_eq_uzpow_smul_mul`: a homogeneous element of degree `p` with
  `(-1 : ℤˣ) ^ p = -1` satisfies `a * a = -(a * a)`.
* `TauCeti.mul_self_eq_neg_of_mul_eq_uzpow_smul_mul_of_mem_one`: every element of degree `1`
  satisfies `a * a = -(a * a)`.
-/

public section

open DirectSum

namespace TauCeti

universe uA uι

section SignedComm

variable {A : Type uA} {ι : Type uι} {σ : Type*}
  [NonUnitalNonAssocRing A] [CommSemiring ι] [Module ι (Additive ℤˣ)] [SetLike σ A]

/-- In an internally graded ring with Koszul signs, every homogeneous element whose degree `p`
satisfies `(-1 : ℤˣ) ^ p = 1` commutes with the entire ring. -/
theorem commute_of_mul_eq_uzpow_smul_mul [DecidableEq ι] [AddSubmonoidClass σ A] {ℬ : ι → σ}
    [Decomposition ℬ]
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {p : ι} {a : A} (ha : a ∈ ℬ p) (hp : (-1 : ℤˣ) ^ p = 1) (b : A) : Commute a b := by
  induction b using Decomposition.inductionOn ℬ with
  | zero => simp [Commute, SemiconjBy]
  | @homogeneous q b => simpa [Commute, SemiconjBy, uzpow_mul, hp] using hcomm ha b.property
  | add x y hx hy => simp only [Commute, SemiconjBy, mul_add, add_mul, hx.eq, hy.eq]

/-- In an internally graded ring with Koszul signs, every element of degree `0` commutes with the
entire ring. -/
theorem commute_of_mul_eq_uzpow_smul_mul_of_mem_zero [DecidableEq ι] [AddSubmonoidClass σ A]
    {ℬ : ι → σ} [Decomposition ℬ]
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {a : A} (ha : a ∈ ℬ 0) (b : A) : Commute a b :=
  commute_of_mul_eq_uzpow_smul_mul hcomm ha (uzpow_zero (-1)) b

/-- Under Koszul graded commutativity, every homogeneous element whose degree `p` satisfies
`(-1 : ℤˣ) ^ p = -1` squares to its own negative. -/
theorem mul_self_eq_neg_of_mul_eq_uzpow_smul_mul {ℬ : ι → σ}
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {p : ι} {a : A} (ha : a ∈ ℬ p) (hp : (-1 : ℤˣ) ^ p = -1) : a * a = -(a * a) := by
  simpa [uzpow_mul, hp] using hcomm ha ha

/-- Under Koszul graded commutativity, every element of degree `1` squares to its own negative. -/
theorem mul_self_eq_neg_of_mul_eq_uzpow_smul_mul_of_mem_one {ℬ : ι → σ}
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {a : A} (ha : a ∈ ℬ 1) : a * a = -(a * a) :=
  mul_self_eq_neg_of_mul_eq_uzpow_smul_mul hcomm ha (uzpow_one (-1))

end SignedComm

end TauCeti
