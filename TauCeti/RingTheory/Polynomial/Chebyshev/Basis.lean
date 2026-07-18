module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# The Chebyshev polynomials as a basis

This file packages the Chebyshev polynomials of the first kind as a basis of `ℝ[X]`.  Mathlib
already proves that `T ℝ n` has degree `n`, records its leading coefficient, and bundles the
family as `Polynomial.Chebyshev.chebyshevTsequence`.  Its generic polynomial-sequence API then
gives a basis whenever all leading coefficients are units.

The resulting basis is an algebraic prerequisite for Part C of the `OrthogonalL2Bases` roadmap.
In the Chebyshev completeness argument, orthogonality to every `Tₙ` must imply orthogonality to
every polynomial.  The extensionality and span lemmas below expose exactly that passage without
repeating a triangular induction in the analytic file.

## Main declarations

* `Polynomial.Chebyshev.chebyshevTBasis`: the basis `n ↦ T ℝ n` of `ℝ[X]`;
* `Polynomial.Chebyshev.span_T_Iio`: the first `m` modes span the polynomials of degree `< m`;
* `Polynomial.Chebyshev.linearMap_eq_zero_of_forall_map_T_eq_zero`: a linear map out of `ℝ[X]`
  vanishing on all Chebyshev modes vanishes identically.
-/

public section

namespace Polynomial.Chebyshev

open Submodule

/-- The leading coefficient of every real Chebyshev polynomial of the first kind is a unit. -/
private lemma isUnit_leadingCoeff_T_real (n : ℕ) : IsUnit (T ℝ n).leadingCoeff := by
  rw [leadingCoeff_T]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))

/-- The Chebyshev polynomials of the first kind, indexed by their nonnegative degree, form a
basis of the real polynomial ring. -/
noncomputable def chebyshevTBasis : Module.Basis ℕ ℝ ℝ[X] :=
  (chebyshevTsequence ℝ).basis isUnit_leadingCoeff_T_real

/-- The `n`th vector of the real Chebyshev basis is `T ℝ n`. -/
@[simp]
lemma chebyshevTBasis_apply (n : ℕ) : chebyshevTBasis n = T ℝ n :=
  Polynomial.Sequence.basis_eq_self _ _ n

/-- The first `m` real Chebyshev polynomials span precisely the polynomials of degree less than
`m`.  This is the finite triangular form of `chebyshevTBasis`. -/
lemma span_T_Iio (m : ℕ) :
    span ℝ ((fun n : ℕ ↦ T ℝ n) '' Set.Iio m) = Polynomial.degreeLT ℝ m := by
  exact (chebyshevTsequence ℝ).span_degreeLT fun n _ ↦ isUnit_leadingCoeff_T_real n

/-- The Chebyshev polynomials span the real polynomial ring. -/
lemma span_range_T : span ℝ (Set.range fun n : ℕ ↦ T ℝ n) = ⊤ := by
  exact (chebyshevTsequence ℝ).span isUnit_leadingCoeff_T_real

/-- Every real polynomial is a finite linear combination of Chebyshev polynomials whose indices
do not exceed its natural degree. -/
lemma mem_span_T_Iic (p : ℝ[X]) :
    p ∈ span ℝ ((fun n : ℕ ↦ T ℝ n) '' Set.Iic p.natDegree) := by
  change p ∈ span ℝ ((chebyshevTsequence ℝ) '' Set.Iic p.natDegree)
  rw [(chebyshevTsequence ℝ).span_degreeLE fun n _ ↦ isUnit_leadingCoeff_T_real n]
  exact Polynomial.mem_degreeLE.mpr Polynomial.degree_le_natDegree

/-- A linear map out of `ℝ[X]` is determined by its values on the Chebyshev polynomials.

This is the form used by completeness arguments: once a linear functional vanishes on every
Chebyshev mode, it vanishes on every polynomial, hence in particular on every monomial. -/
lemma linearMap_eq_zero_of_forall_map_T_eq_zero {M : Type*} [AddCommGroup M] [Module ℝ M]
    (L : ℝ[X] →ₗ[ℝ] M) (hL : ∀ n : ℕ, L (T ℝ n) = 0) : L = 0 := by
  apply chebyshevTBasis.ext
  intro n
  simp [hL n]

/-- Elementwise form of `linearMap_eq_zero_of_forall_map_T_eq_zero`: a linear map vanishing on
all real Chebyshev polynomials vanishes on every real polynomial. -/
lemma LinearMap.map_eq_zero_of_forall_map_T_eq_zero {M : Type*} [AddCommGroup M] [Module ℝ M]
    (L : ℝ[X] →ₗ[ℝ] M) (hL : ∀ n : ℕ, L (T ℝ n) = 0) (p : ℝ[X]) : L p = 0 := by
  rw [linearMap_eq_zero_of_forall_map_T_eq_zero L hL]
  rfl

/-- Two linear maps out of `ℝ[X]` agreeing on all Chebyshev polynomials agree everywhere. -/
lemma linearMap_ext_T {M : Type*} [AddCommGroup M] [Module ℝ M]
    {L₁ L₂ : ℝ[X] →ₗ[ℝ] M} (h : ∀ n : ℕ, L₁ (T ℝ n) = L₂ (T ℝ n)) : L₁ = L₂ := by
  apply chebyshevTBasis.ext
  intro n
  simpa using h n

end Polynomial.Chebyshev
