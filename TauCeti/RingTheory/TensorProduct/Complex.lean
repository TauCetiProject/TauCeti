/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.LinearCombination

/-!
# Zero divisors after complexifying a complex algebra over the reals

For every nontrivial commutative complex algebra `A`, the real tensor product `ℂ ⊗[ℝ] A`
has zero divisors. Explicit factors are `I ⊗ 1 - 1 ⊗ I` and `I ⊗ 1 + 1 ⊗ I`, where the
second occurrence of `I` is mapped into `A`. Multiplication, with or without conjugation
on the first factor, detects their nonvanishing.

In particular, extending real constants to complex constants need not preserve integrality
when the original field already contains complex constants. This is distinct from the
nonreduced tensor products caused by inseparability.

The construction uses Mathlib's `Complex.conjAe` and `Algebra.TensorProduct.lift`.
-/

public section

open TensorProduct

namespace TauCeti

/-- Complexifying a nontrivial complex algebra over the reals produces two nonzero elements
whose product is zero. The factors are `I ⊗ 1 - 1 ⊗ I` and `I ⊗ 1 + 1 ⊗ I`. -/
theorem exists_ne_zero_mul_eq_zero_complex_tensorProduct (A : Type*) [CommRing A]
    [Nontrivial A] [Algebra ℂ A] :
    ∃ x y : ℂ ⊗[ℝ] A, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 := by
  let f : ℂ →ₐ[ℝ] A := IsScalarTower.toAlgHom ℝ ℂ A
  let μ : ℂ ⊗[ℝ] A →ₐ[ℝ] A :=
    Algebra.TensorProduct.lift f (AlgHom.id ℝ A) (fun _ _ ↦ Commute.all _ _)
  let ν : ℂ ⊗[ℝ] A →ₐ[ℝ] A :=
    Algebra.TensorProduct.lift (f.comp Complex.conjAe.toAlgHom) (AlgHom.id ℝ A)
      (fun _ _ ↦ Commute.all _ _)
  let a : ℂ ⊗[ℝ] A := Complex.I ⊗ₜ[ℝ] (1 : A)
  let b : ℂ ⊗[ℝ] A := (1 : ℂ) ⊗ₜ[ℝ] algebraMap ℂ A Complex.I
  have htwoI : (2 : A) * algebraMap ℂ A Complex.I ≠ 0 := by
    rw [← map_ofNat (algebraMap ℂ A) 2, ← map_mul]
    exact (map_ne_zero (algebraMap ℂ A)).mpr (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hminus : a - b ≠ 0 := by
    intro h
    have := congrArg ν h
    simp [ν, f, a, b, Complex.conjAe_coe] at this
    apply htwoI
    linear_combination -this
  have hplus : a + b ≠ 0 := by
    intro h
    have := congrArg μ h
    simp [μ, f, a, b] at this
    apply htwoI
    linear_combination this
  refine ⟨a - b, a + b, hminus, hplus, ?_⟩
  have ha : a * a = -1 := by
    simp [a, Complex.I_mul_I, neg_tmul, ← Algebra.TensorProduct.one_def]
  have hb : b * b = -1 := by
    simp [b, ← map_mul, Complex.I_mul_I, tmul_neg, ← Algebra.TensorProduct.one_def]
  calc
    (a - b) * (a + b) = a * a - b * b := by ring
    _ = 0 := by rw [ha, hb, sub_self]

/-- A nontrivial complex algebra does not become a domain when tensored with `ℂ` over `ℝ`. -/
theorem not_isDomain_complex_tensorProduct (A : Type*) [CommRing A] [Nontrivial A]
    [Algebra ℂ A] : ¬ IsDomain (ℂ ⊗[ℝ] A) := by
  intro h
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_ne_zero_mul_eq_zero_complex_tensorProduct A
  exact (mul_eq_zero.mp hxy).elim hx hy

end TauCeti
