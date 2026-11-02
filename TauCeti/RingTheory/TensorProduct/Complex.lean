/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Zero divisors after complexifying a complex algebra over the reals

For every nontrivial complex algebra `A` with a compatible real algebra structure, the real
tensor product `ℂ ⊗[ℝ] A` has zero divisors. Explicit factors are `I ⊗ 1 - 1 ⊗ I` and
`I ⊗ 1 + 1 ⊗ I`, where the second occurrence of `I` is mapped into `A`.

In particular, extending real scalars to `ℂ` never yields a domain when the algebra already
contains `ℂ`. This is distinct from the nonreduced tensor products caused by inseparability.
-/

public section

open TensorProduct

namespace TauCeti

-- Use the given real algebra's module rather than restriction of the complex module.
attribute [local instance high] Algebra.toModule

/-- Complexifying a nontrivial complex algebra over the reals produces two nonzero elements
whose product is zero. The factors are `I ⊗ 1 - 1 ⊗ I` and `I ⊗ 1 + 1 ⊗ I`. -/
theorem exists_ne_zero_mul_eq_zero_complex_tensorProduct (A : Type*) [Ring A]
    [Nontrivial A] [Algebra ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A] :
    ∃ x y : ℂ ⊗[ℝ] A, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 := by
  -- Tensor multiplication and Mathlib's `Complex.conjAe` detect the nonvanishing
  -- of the two factors.
  let μ : ℂ ⊗[ℝ] A →ₐ[ℝ] A := Algebra.TensorProduct.mulLeft.restrictScalars ℝ
  let ν : ℂ ⊗[ℝ] A →ₐ[ℝ] A :=
    μ.comp (Algebra.TensorProduct.map Complex.conjAe.toAlgHom (AlgHom.id ℝ A))
  let a : ℂ ⊗[ℝ] A := Complex.I ⊗ₜ[ℝ] (1 : A)
  let b : ℂ ⊗[ℝ] A := (1 : ℂ) ⊗ₜ[ℝ] algebraMap ℂ A Complex.I
  have htwoI : (2 : A) * algebraMap ℂ A Complex.I ≠ 0 := by
    rw [← map_ofNat (algebraMap ℂ A) 2, ← map_mul]
    exact (map_ne_zero (algebraMap ℂ A)).mpr (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hminus : a - b ≠ 0 := by
    intro h
    have : -algebraMap ℂ A Complex.I - algebraMap ℂ A Complex.I = 0 := by
      simpa [ν, μ, a, b, Complex.conjAe_coe] using congrArg ν h
    apply htwoI
    simpa [two_mul, sub_eq_add_neg] using congrArg Neg.neg this
  have hplus : a + b ≠ 0 := by
    intro h
    have : algebraMap ℂ A Complex.I + algebraMap ℂ A Complex.I = 0 := by
      simpa [μ, a, b] using congrArg μ h
    apply htwoI
    simpa [two_mul] using this
  refine ⟨a - b, a + b, hminus, hplus, ?_⟩
  have ha : a * a = -1 := by
    simp [a, Complex.I_mul_I, neg_tmul, ← Algebra.TensorProduct.one_def]
  have hb : b * b = -1 := by
    simp [b, ← map_mul, Complex.I_mul_I, tmul_neg, ← Algebra.TensorProduct.one_def]
  have hab : Commute a b := (Commute.one_right _).tmul (Commute.one_left _)
  calc
    (a - b) * (a + b) = a * a - b * b := hab.mul_self_sub_mul_self_eq'.symm
    _ = 0 := by rw [ha, hb, sub_self]

/-- A nontrivial complex algebra does not become a domain when tensored with `ℂ` over `ℝ`. -/
theorem not_isDomain_complex_tensorProduct (A : Type*) [Ring A] [Nontrivial A]
    [Algebra ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A] : ¬ IsDomain (ℂ ⊗[ℝ] A) := by
  intro h
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_ne_zero_mul_eq_zero_complex_tensorProduct A
  exact (mul_eq_zero.mp hxy).elim hx hy

end TauCeti
