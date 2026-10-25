/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.HasseWronskian
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete checks for the Hasse Wronskian

These checks distinguish the Hasse determinant from the classical determinant, test the
characteristic-zero hypothesis of the independence criterion, and test the domain hypothesis of
the dependence-to-vanishing implication.
-/

public section

open Polynomial

namespace TauCeti.Examples.HasseWronskian

local instance instFactPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The divided Wronskian of `(1, X, X²)` over `ℚ` is one. -/
theorem rational_one_X_sq : hasseWronskian (![1, X, X ^ 2] : Fin 3 → ℚ[X]) = 1 := by
  norm_num [hasseWronskian_def, Matrix.det_fin_three, X_pow_eq_monomial, hasseDeriv_monomial,
    hasseDeriv_X, hasseDeriv_apply_one]

/-- The dependent pair `(X, 2X)` has zero Hasse Wronskian. -/
theorem rational_X_two_mul_X : hasseWronskian (![X, 2 * X] : Fin 2 → ℚ[X]) = 0 := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hasseWronskian_fin_two, wronskian, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, derivative_mul,
    derivative_ofNat, zero_mul, derivative_X, mul_one, zero_add, one_mul]
  ring

/-- The Hasse Wronskian of `(1, X)` is one. -/
theorem rational_one_X : hasseWronskian (![1, X] : Fin 2 → ℚ[X]) = 1 := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hasseWronskian_fin_two, wronskian, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, derivative_X, mul_one,
    derivative_one, zero_mul, sub_zero]

/-- The ordinary Wronskian of `(1, X, X²)` is two, distinguishing the normalization. -/
theorem rational_classical_one_X_sq : (derivative' : Derivation ℚ ℚ[X] ℚ[X]).wronskian
    (![1, X, X ^ 2] : Fin 3 → ℚ[X]) = 2 := by
  rw [← prod_factorial_mul_hasseWronskian]
  norm_num [rational_one_X_sq, Fin.prod_univ_succ]

/-- In characteristic two, `(1, X²)` has zero Hasse Wronskian. -/
theorem zmod_two_one_X_sq : hasseWronskian (![1, X ^ 2] : Fin 2 → (ZMod 2)[X]) = 0 := by
  norm_num [wronskian]
  decide

/-- The pair `(1, X²)` remains linearly independent in characteristic two. -/
theorem zmod_two_one_X_sq_linearIndependent :
    LinearIndependent (ZMod 2) (![1, X ^ 2] : Fin 2 → (ZMod 2)[X]) := by
  rw [linearIndependent_fin2]
  constructor
  · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, X_ne_zero]
  · intro a h
    have h0 := congrArg (coeff · 0) h
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, coeff_smul,
      coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, smul_eq_mul, mul_zero,
      Matrix.cons_val_zero, coeff_one_zero, zero_ne_one] at h0

/-- Over `ℤ/4ℤ`, the singleton constant two has Hasse Wronskian two. -/
theorem zmod_four_singleton_two :
    hasseWronskian (fun _ : Fin 1 => (2 : (ZMod 4)[X])) = 2 := by simp only
      [hasseWronskian_fin_one]

/-- The singleton constant two is linearly dependent over `ℤ/4ℤ`. -/
theorem zmod_four_singleton_two_not_linearIndependent :
    ¬ LinearIndependent (ZMod 4) (fun _ : Fin 1 => (2 : (ZMod 4)[X])) := by
  intro h
  have h' := h.smul_left_injective (i := (0 : Fin 1)) (a₁ := (2 : ZMod 4)) (a₂ := 0)
  have he : (2 : ZMod 4) • (2 : (ZMod 4)[X]) = 0 := by
    rw [smul_eq_C_mul]
    rw [← C_ofNat (n := 2), ← C_mul]
    simpa only [map_zero] using
      congrArg (C : ZMod 4 →+* (ZMod 4)[X]) (by decide : (2 : ZMod 4) * 2 = 0)
  exact (by decide : (2 : ZMod 4) ≠ 0) (h' (by simpa using he))

/-- The dependent singleton over `ℤ/4ℤ` has nonzero Hasse Wronskian. -/
theorem zmod_four_singleton_two_ne_zero :
    hasseWronskian (fun _ : Fin 1 => (2 : (ZMod 4)[X])) ≠ 0 := by
  rw [hasseWronskian_fin_one]
  intro h
  exact (by decide : (2 : ZMod 4) ≠ 0) (by simpa using congrArg (coeff · 0) h)

/-- The singleton idempotent `(1, 0)` has nonzero Hasse Wronskian over `ℚ × ℚ`. -/
theorem rational_prod_singleton_idempotent_ne_zero :
    hasseWronskian (fun _ : Fin 1 => C ((1, 0) : ℚ × ℚ)) ≠ 0 := by
  simp only [hasseWronskian_fin_one, ne_eq, C_eq_zero, Prod.mk_eq_zero, one_ne_zero, and_true,
    not_false_eq_true]

/-- The singleton idempotent `(1, 0)` is dependent over the characteristic-zero
ring `ℚ × ℚ`. -/
theorem rational_prod_singleton_idempotent_not_linearIndependent :
    ¬ LinearIndependent (ℚ × ℚ) (fun _ : Fin 1 => C ((1, 0) : ℚ × ℚ)) := by
  intro h
  have h' := h.smul_left_injective (i := (0 : Fin 1))
    (a₁ := ((0, 1) : ℚ × ℚ)) (a₂ := 0)
  have he : ((0, 1) : ℚ × ℚ) • C ((1, 0) : ℚ × ℚ) = 0 := by
    rw [smul_eq_C_mul, ← C_mul]
    simp only [Prod.mk_mul_mk, mul_one, mul_zero, C_eq_zero, Prod.mk_eq_zero, and_self]
  have hc := h' (by simpa only [zero_smul] using he)
  have := congrArg Prod.snd hc
  norm_num at this

end TauCeti.Examples.HasseWronskian
