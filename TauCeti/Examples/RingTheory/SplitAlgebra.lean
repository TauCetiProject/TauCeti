/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.SplitAlgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.NormNum

/-!
# Examples distinguishing linear splittings from injectivity and ring retractions

Evaluation at zero splits a polynomial algebra, and first projection splits a diagonal
product algebra. Real part splits the complex numbers over the reals, despite not being
multiplicative. Conversely, the inclusion of the integers in the rationals is injective
but cannot split: a retraction would make one divisible by two in the integers.
-/

public section

open TauCeti TensorProduct

example (R : Type*) [CommSemiring R] : SplitAlgebra R (Polynomial R) :=
  Module.isUnimodular_iff.mpr ⟨(Polynomial.aeval (0 : R)).toLinearMap, by simp⟩

example (R : Type*) [CommSemiring R] : SplitAlgebra R (R × R) :=
  Module.isUnimodular_iff.mpr ⟨LinearMap.fst R R R, rfl⟩

example : SplitAlgebra ℝ ℂ :=
  Module.isUnimodular_iff.mpr ⟨Complex.reLm, Complex.one_re⟩

example (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Nontrivial A] :
    SplitAlgebra K A := Module.Free.isUnimodular_one

example : Complex.reLm (Complex.I * Complex.I) ≠
    Complex.reLm Complex.I * Complex.reLm Complex.I := by
  simp

example : ¬ SplitAlgebra ℤ ℚ := by
  intro h
  obtain ⟨ρ, hρ⟩ := Module.isUnimodular_iff.mp h
  have h := ρ.map_smul (2 : ℤ) (1 / 2 : ℚ)
  norm_num [hρ] at h
  omega

example (R : Type*) [CommSemiring R] :
    SplitAlgebra R (Polynomial R × Polynomial R) := by
  have h : SplitAlgebra R (Polynomial R) :=
    Module.isUnimodular_iff.mpr ⟨(Polynomial.aeval (0 : R)).toLinearMap, by simp⟩
  exact h.of_algHom
      (AlgHom.fst R (Polynomial R) (Polynomial R))

example (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    SplitAlgebra A (A ⊗[R] (R × R)) := by
  have h : SplitAlgebra R (R × R) :=
    Module.isUnimodular_iff.mpr ⟨LinearMap.fst R R R, rfl⟩
  exact h.baseChange A

example (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M] :
    Function.Injective (fun m : M ↦ m ⊗ₜ[R] (1 : R × R)) := by
  have h : SplitAlgebra R (R × R) :=
    Module.isUnimodular_iff.mpr ⟨LinearMap.fst R R R, rfl⟩
  exact h.tensorUnit_injective M
