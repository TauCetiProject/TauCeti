/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Clearing denominators of rational characters

A rational-valued additive character on a finite product of copies of `ℤ` becomes
integer valued after multiplication by a positive natural number. This supplies a
discrete grading from a rational one while preserving its strict inequalities.
The common denominator is obtained from Mathlib's `Matrix.den` and `Matrix.num`.
-/

public section

namespace AddMonoidHom

/-- A positive natural multiple of a rational character on a finite integer product is
the cast of an integer character. -/
theorem exists_pos_nat_mul_eq_intCast {ι : Type*} [Finite ι] (f : (ι → ℤ) →+ ℚ) :
    ∃ (n : ℕ) (degree : (ι → ℤ) →+ ℤ), 0 < n ∧
      ∀ μ, n * f μ = (degree μ : ℚ) := by
  classical
  let := Fintype.ofFinite ι
  let a : Matrix Unit ι ℚ := fun _ i => f (Pi.single i 1)
  let degree : (ι → ℤ) →+ ℤ :=
    { toFun μ := ∑ i, a.num () i * μ i
      map_zero' := by simp
      map_add' := fun μ ν => by simp [mul_add, Finset.sum_add_distrib] }
  refine ⟨a.den, degree, Nat.pos_of_ne_zero a.den_ne_zero, fun μ => Eq.symm ?_⟩
  have hnum (i : ι) : (a.num () i : ℚ) = a.den * a () i := by
    have h := (div_eq_iff (Nat.cast_ne_zero.mpr a.den_ne_zero)).mp (a.num_div_den () i)
    simpa only [mul_comm] using h
  have hμ : μ = ∑ i, μ i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Pi.single_apply]
  have hmap : f μ = ∑ i, μ i • a () i := by
    conv_lhs => rw [hμ, map_sum]
    simp only [map_zsmul, a]
  calc
    (degree μ : ℚ) = ∑ i, (a.den : ℚ) * (μ i • a () i) := by
      simp [degree, hnum, zsmul_eq_mul, mul_comm, mul_assoc]
    _ = a.den * f μ := by
      rw [hmap, Finset.mul_sum]

end AddMonoidHom
