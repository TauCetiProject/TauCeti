/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic.LinearCombination

/-!
# Additive cancellation in characteristic two

In a possibly nonassociative semiring of characteristic two, each element is its own additive
inverse. Consequently addition is cancellative, even when the given semiring structure lacks
additive cancellation. This supplies the cancellation needed by the grid commutation chain-map
criterion. The same holds in any module over a semiring of characteristic two
(`TauCeti.add_self_eq_zero_of_charTwo`), which is how terms appearing twice cancel in sign-free
differentials, and there `a + b = 0` exactly when `a = b` (`TauCeti.add_eq_zero_iff_eq_of_charTwo`).
Adding two homotopy relations `a + p = D k + k'` and `p + b = D t + t'` cancels the shared term `p`
(`TauCeti.add_eq_map_add_add_of_charTwo`).

Two consequences for quadratic equations follow. In a ring of characteristic two without zero
divisors, two roots of `X ^ 2 + t X - s` are equal or differ by `t`
(`TauCeti.eq_or_eq_add_of_sq_add_mul_eq_of_charTwo`). An algebra endomorphism over a ring of
characteristic two that translates an element by a scalar is an involution on that element
(`AlgHom.apply_apply_of_apply_eq_add_algebraMap`), as for the translations permuting these roots.
Finally, every unit of `ℤ` casts to `1` in any additive group with one of characteristic two
(`TauCeti.intCast_units_eq_one_of_charTwo`).

Since `1 + 1 = 0`, the exclusive-or of bits is their sum: the indicator of a bit of an exclusive-or
of natural numbers accumulated over a list is the sum of the indicators of that bit of the terms
(`TauCeti.ite_testBit_foldl_xor_of_charTwo`). This compares a computation on binary
representations with a sum in the semiring.

A nontrivial semiring that is an algebra over `ZMod 2` has characteristic two
(`TauCeti.charP_two_of_algebra_zmod_two`). This is the instance-shaped `p = 2` case of Mathlib's
`charP_of_injective_algebraMap'`, usable as a local instance for `ZMod 2`-algebras. Without any
nontriviality, `2 = 0` passes from a commutative semiring to every algebra over it
(`TauCeti.two_eq_zero_of_algebra`).

-/

public section

namespace TauCeti

/-- Addition in a possibly nonassociative semiring of characteristic two is cancellative. -/
theorem isCancelAdd_of_charTwo (R : Type*) [NonAssocSemiring R] [CharP R 2] : IsCancelAdd R where
  add_left_cancel a b c h := by
    have h' := congrArg (fun t => a + t) h
    simpa only [CharTwo.add_cancel_left] using h'
  add_right_cancel a b c h := by
    have h' := congrArg (fun t => t + a) h
    simpa only [CharTwo.add_cancel_right] using h'

/-- In a module over a semiring of characteristic two, each element is its own additive inverse. -/
theorem add_self_eq_zero_of_charTwo (R : Type*) {M : Type*} [Semiring R] [CharP R 2]
    [AddCommMonoid M] [Module R M] (x : M) : x + x = 0 := by
  rw [← two_smul R, CharTwo.two_eq_zero, zero_smul]

/-- In a ring of characteristic two without zero divisors, two roots of `X ^ 2 + t X - s` are
equal or differ by `t`. -/
theorem eq_or_eq_add_of_sq_add_mul_eq_of_charTwo {S : Type*} [CommRing S] [NoZeroDivisors S]
    [CharP S 2] {t s a b : S} (ha : a ^ 2 + t * a = s) (hb : b ^ 2 + t * b = s) :
    b = a ∨ b = a + t := by
  have h2 : (2 : S) = 0 := CharTwo.two_eq_zero
  have h : (b + a) * (b + a + t) = 0 := by linear_combination hb + ha + (a * b + s) * h2
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (by linear_combination h - a * h2)
  · exact Or.inr (by linear_combination h - (a + t) * h2)

/-- In a module over a semiring of characteristic two, `a + b = 0` exactly when `a = b`. -/
theorem add_eq_zero_iff_eq_of_charTwo (R : Type*) {M : Type*} [Semiring R] [CharP R 2]
    [AddCommMonoid M] [Module R M] {a b : M} : a + b = 0 ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ add_self_eq_zero_of_charTwo R a⟩
  rw [← add_zero a, ← add_self_eq_zero_of_charTwo R b, ← add_assoc, h, zero_add]

/-- In a module over a semiring of characteristic two, adding the homotopy relations
`a + p = D k + k'` and `p + b = D t + t'` for an additive map `D` cancels the shared term `p`:
`a + b = D (k + t) + (k' + t')`. -/
theorem add_eq_map_add_add_of_charTwo (R : Type*) {V W F : Type*} [Semiring R] [CharP R 2]
    [AddCommMonoid V] [AddCommMonoid W] [Module R W] [FunLike F V W] [AddHomClass F V W] (D : F)
    {a b p k' t' : W} {k t : V} (h₁ : a + p = D k + k') (h₂ : p + b = D t + t') :
    a + b = D (k + t) + (k' + t') := by
  rw [map_add, add_add_add_comm, ← h₁, ← h₂, add_assoc, ← add_assoc p,
    add_self_eq_zero_of_charTwo R, zero_add]

/-- In an additive group with one of characteristic two, every unit of `ℤ` casts to `1`. -/
theorem intCast_units_eq_one_of_charTwo {R : Type*} [AddGroupWithOne R] [CharP R 2] (ε : ℤˣ) :
    ((ε : ℤ) : R) = 1 := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [CharTwo.neg_one_eq_one]

/-- In characteristic two, the indicator of a bit of an exclusive-or accumulated over a list is
the sum of the indicators of that bit of the initial value and of the terms. -/
theorem ite_testBit_foldl_xor_of_charTwo {R α : Type*} [NonAssocSemiring R] [CharP R 2]
    (f : α → ℕ) (l : List α) (a p : ℕ) :
    (if (l.foldl (fun acc i ↦ acc ^^^ f i) a).testBit p then (1 : R) else 0) =
      (if a.testBit p then (1 : R) else 0) +
        (l.map fun i ↦ if (f i).testBit p then (1 : R) else 0).sum := by
  induction l generalizing a with
  | nil => rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons x l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_xor, List.map_cons, List.sum_cons, ← add_assoc]
    cases a.testBit p <;> cases (f x).testBit p <;> simp [CharTwo.add_self_eq_zero]

/-- A nontrivial semiring that is an algebra over `ZMod 2` has characteristic two, the algebra map
from the field `ZMod 2` being injective. -/
theorem charP_two_of_algebra_zmod_two (k : Type*) [Semiring k] [Nontrivial k]
    [Algebra (ZMod 2) k] : CharP k 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2

/-- If `2 = 0` in a commutative semiring `R`, then `2 = 0` in every `R`-algebra. -/
theorem two_eq_zero_of_algebra {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (h2 : (2 : R) = 0) : (2 : A) = 0 := by
  rw [← map_ofNat (algebraMap R A) 2, h2, map_zero]

end TauCeti

/-- Over a ring of characteristic two, an algebra endomorphism translating `x` by a scalar sends
`x + a` back to `x`, so applying it twice fixes `x`. -/
theorem AlgHom.apply_apply_of_apply_eq_add_algebraMap {R A : Type*} [CommSemiring R] [CharP R 2]
    [Semiring A] [Algebra R A] (f : A →ₐ[R] A) {x : A} {a : R} (h : f x = x + algebraMap R A a) :
    f (f x) = x := by
  rw [h, map_add, h, AlgHom.commutes, add_assoc, TauCeti.add_self_eq_zero_of_charTwo R, add_zero]
