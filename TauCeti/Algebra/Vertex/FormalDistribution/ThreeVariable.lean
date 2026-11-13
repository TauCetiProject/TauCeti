/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Ring

/-!
# Multiplication of three-variable formal distributions by the variables

A three-variable formal distribution in `x`, `w` and `z` is an arbitrary coefficient family
`d : ℤ → ℤ → ℤ → M`, where `d a b c` is the coefficient of `x^(-a-1) w^(-b-1) z^(-c-1)`.
Multiplication by each variable shifts the corresponding index by one, so it is defined for
every distribution, and the three multiplications commute. Polynomials in them, such as
`(x - w)^N`, act through the ring structure of `Module.End ℤ (ℤ → ℤ → ℤ → M)`.

## Main definitions

* `TauCeti.FormalDistribution.mulX`, `TauCeti.FormalDistribution.mulW`,
  `TauCeti.FormalDistribution.mulZ`: multiplication by `x`, `w` and `z`.

## Main results

* `TauCeti.FormalDistribution.mulX_pow_apply` and its analogues: multiplication by `x^k`
  shifts the first index by `k`.
* `TauCeti.FormalDistribution.commute_mulX_mulW` and its analogues: the multiplications by the
  three variables commute.
-/

public section

namespace TauCeti.FormalDistribution

variable {M : Type*} [AddCommGroup M]

/-- Multiplication of a three-variable distribution `d a b c`, the coefficient of
`x^(-a-1) w^(-b-1) z^(-c-1)`, by the first variable `x`. -/
def mulX : Module.End ℤ (ℤ → ℤ → ℤ → M) where
  toFun d a b c := d (a + 1) b c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication of a three-variable distribution by the second variable `w`. -/
def mulW : Module.End ℤ (ℤ → ℤ → ℤ → M) where
  toFun d a b c := d a (b + 1) c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication of a three-variable distribution by the third variable `z`. -/
def mulZ : Module.End ℤ (ℤ → ℤ → ℤ → M) where
  toFun d a b c := d a b (c + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

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
    rw [pow_succ', mul_apply_eq_comp, mulX_apply, ih]
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
    rw [pow_succ', mul_apply_eq_comp, mulW_apply, ih]
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
    rw [pow_succ', mul_apply_eq_comp, mulZ_apply, ih]
    congr 1
    push_cast
    ring

/-- Multiplications by `x` and by `w` commute. -/
theorem commute_mulX_mulW : Commute (mulX (M := M)) mulW :=
  LinearMap.ext fun _ ↦ rfl

/-- Multiplications by `x` and by `z` commute. -/
theorem commute_mulX_mulZ : Commute (mulX (M := M)) mulZ :=
  LinearMap.ext fun _ ↦ rfl

/-- Multiplications by `w` and by `z` commute. -/
theorem commute_mulW_mulZ : Commute (mulW (M := M)) mulZ :=
  LinearMap.ext fun _ ↦ rfl

end TauCeti.FormalDistribution
