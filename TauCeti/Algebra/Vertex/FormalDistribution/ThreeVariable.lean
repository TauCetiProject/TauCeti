/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Hom
import Mathlib.Tactic.Ring
import TauCeti.Data.Nat.Choose.Sum

/-!
# Multiplication of three-variable formal distributions by the variables

A three-variable formal distribution in `x`, `w` and `z` is an arbitrary coefficient family
`d : ℤ → ℤ → ℤ → M`, where `d a b c` is the coefficient of `x^(-a-1) w^(-b-1) z^(-c-1)`.
Multiplication by each variable shifts the corresponding index by one, so it is defined for
every distribution, and the three multiplications commute. Polynomials in them, such as
`(x - w)^N`, act through the ring structure of `AddMonoid.End (ℤ → ℤ → ℤ → M)` when `M` is an
additive group, and multiplication by `(x - w)^N` is the corresponding binomial sum of shifts.

## Main definitions

* `TauCeti.FormalDistribution.ThreeVariable.mulX`,
  `TauCeti.FormalDistribution.ThreeVariable.mulW`,
  `TauCeti.FormalDistribution.ThreeVariable.mulZ`: multiplication by `x`, `w` and `z`.

## Main results

* `TauCeti.FormalDistribution.ThreeVariable.mulX_pow_apply` and its analogues: multiplication
  by `x^k` shifts the first index by `k`.
* `TauCeti.FormalDistribution.ThreeVariable.commute_mulX_mulW` and its analogues: the
  multiplications by the three variables commute.
* `TauCeti.FormalDistribution.ThreeVariable.mulX_sub_mulW_pow_apply` and its analogues: the
  binomial coefficient formula for multiplication by `(x - w)^N`, `(x - z)^N` and `(w - z)^N`.
-/

public section

namespace TauCeti.FormalDistribution.ThreeVariable

section AddMonoid

variable {M : Type*} [AddMonoid M]

/-- Multiplication of a three-variable distribution `d a b c`, the coefficient of
`x^(-a-1) w^(-b-1) z^(-c-1)`, by the first variable `x`. -/
def mulX : AddMonoid.End (ℤ → ℤ → ℤ → M) where
  toFun d a b c := d (a + 1) b c
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Multiplication of a three-variable distribution by the second variable `w`. -/
def mulW : AddMonoid.End (ℤ → ℤ → ℤ → M) where
  toFun d a b c := d a (b + 1) c
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Multiplication of a three-variable distribution by the third variable `z`. -/
def mulZ : AddMonoid.End (ℤ → ℤ → ℤ → M) where
  toFun d a b c := d a b (c + 1)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem mulX_apply (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    mulX (M := M) d a b c = d (a + 1) b c :=
  (rfl)

@[simp]
theorem mulW_apply (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    mulW (M := M) d a b c = d a (b + 1) c :=
  (rfl)

@[simp]
theorem mulZ_apply (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    mulZ (M := M) d a b c = d a b (c + 1) :=
  (rfl)

/-- Multiplication by the `k`th power of the first variable shifts the first index by `k`. -/
@[simp]
theorem mulX_pow_apply (k : ℕ) (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    (mulX (M := M) ^ k) d a b c = d (a + k) b c := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, mulX_apply, ih]
    congr 1
    push_cast
    ring

/-- Multiplication by the `k`th power of the second variable shifts the second index by `k`. -/
@[simp]
theorem mulW_pow_apply (k : ℕ) (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    (mulW (M := M) ^ k) d a b c = d a (b + k) c := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, mulW_apply, ih]
    congr 1
    push_cast
    ring

/-- Multiplication by the `k`th power of the third variable shifts the third index by `k`. -/
@[simp]
theorem mulZ_pow_apply (k : ℕ) (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    (mulZ (M := M) ^ k) d a b c = d a b (c + k) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, mulZ_apply, ih]
    congr 1
    push_cast
    ring

/-- Multiplications by `x` and by `w` commute. -/
theorem commute_mulX_mulW : Commute (mulX (M := M)) mulW :=
  AddMonoidHom.ext fun _ ↦ rfl

/-- Multiplications by `x` and by `z` commute. -/
theorem commute_mulX_mulZ : Commute (mulX (M := M)) mulZ :=
  AddMonoidHom.ext fun _ ↦ rfl

/-- Multiplications by `w` and by `z` commute. -/
theorem commute_mulW_mulZ : Commute (mulW (M := M)) mulZ :=
  AddMonoidHom.ext fun _ ↦ rfl

end AddMonoid

section AddCommGroup

variable {M : Type*} [AddCommGroup M]

/-- The binomial coefficient formula for multiplication by `(x - w)^N`. -/
theorem mulX_sub_mulW_pow_apply (N : ℕ) (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    ((mulX - mulW : AddMonoid.End (ℤ → ℤ → ℤ → M)) ^ N) d a b c = ∑ ij ∈ Finset.antidiagonal N,
      N.choose ij.1 • (-1 : ℤ) ^ ij.2 • d (a + ij.1) (b + ij.2) c := by
  simp only [(commute_mulX_mulW (M := M)).sub_pow', ← AddMonoid.End.smul_def, Finset.sum_smul,
    smul_assoc, Finset.sum_apply, Pi.smul_apply, mul_smul]
  simp only [AddMonoid.End.smul_def, mulX_pow_apply, mulW_pow_apply]

/-- The binomial coefficient formula for multiplication by `(x - z)^N`. -/
theorem mulX_sub_mulZ_pow_apply (N : ℕ) (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    ((mulX - mulZ : AddMonoid.End (ℤ → ℤ → ℤ → M)) ^ N) d a b c = ∑ ij ∈ Finset.antidiagonal N,
      N.choose ij.1 • (-1 : ℤ) ^ ij.2 • d (a + ij.1) b (c + ij.2) := by
  simp only [(commute_mulX_mulZ (M := M)).sub_pow', ← AddMonoid.End.smul_def, Finset.sum_smul,
    smul_assoc, Finset.sum_apply, Pi.smul_apply, mul_smul]
  simp only [AddMonoid.End.smul_def, mulX_pow_apply, mulZ_pow_apply]

/-- The binomial coefficient formula for multiplication by `(w - z)^N`. -/
theorem mulW_sub_mulZ_pow_apply (N : ℕ) (d : ℤ → ℤ → ℤ → M) (a b c : ℤ) :
    ((mulW - mulZ : AddMonoid.End (ℤ → ℤ → ℤ → M)) ^ N) d a b c = ∑ ij ∈ Finset.antidiagonal N,
      N.choose ij.1 • (-1 : ℤ) ^ ij.2 • d a (b + ij.1) (c + ij.2) := by
  simp only [(commute_mulW_mulZ (M := M)).sub_pow', ← AddMonoid.End.smul_def, Finset.sum_smul,
    smul_assoc, Finset.sum_apply, Pi.smul_apply, mul_smul]
  simp only [AddMonoid.End.smul_def, mulW_pow_apply, mulZ_pow_apply]

end AddCommGroup

end TauCeti.FormalDistribution.ThreeVariable
