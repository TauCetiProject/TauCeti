module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# The Chebyshev polynomials as a basis

This file packages the Chebyshev polynomials of the first kind as a basis of `R[X]` for a field
`R` of characteristic different from two.  Mathlib
already proves that `T R n` has degree `n`, records its leading coefficient, and bundles the
family as `Polynomial.Chebyshev.chebyshevTsequence`.  Its generic polynomial-sequence API then
gives a basis whenever all leading coefficients are units.

The resulting basis is an algebraic prerequisite for Part C of the `OrthogonalL2Bases` roadmap.
In the Chebyshev completeness argument, orthogonality to every `Tₙ` must imply orthogonality to
every polynomial.  The extensionality and span lemmas below expose exactly that passage without
repeating a triangular induction in the analytic file.

## Main declarations

* `Polynomial.Chebyshev.chebyshevTBasis`: the basis `n ↦ T R n` of `R[X]`;
* `Polynomial.Chebyshev.span_T_Iio`: the first `m` modes span the polynomials of degree `< m`;
* `Polynomial.Chebyshev.linearMap_eq_zero_of_forall_map_T_eq_zero`: a linear map out of `R[X]`
  vanishing on all Chebyshev modes vanishes identically.
-/

public section

namespace Polynomial.Chebyshev

open Submodule

variable {R : Type*} [Field R] [NeZero (2 : R)]

/-- The leading coefficient of every Chebyshev polynomial of the first kind over `R` is a unit. -/
private lemma isUnit_leadingCoeff_T (n : ℕ) : IsUnit (T R n).leadingCoeff := by
  rw [leadingCoeff_T]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (NeZero.ne 2))

/-- The Chebyshev polynomials of the first kind, indexed by their nonnegative degree, form a
basis of `R[X]`. -/
noncomputable def chebyshevTBasis : Module.Basis ℕ R R[X] :=
  (chebyshevTsequence R).basis isUnit_leadingCoeff_T

/-- The `n`th vector of the Chebyshev basis is `T R n`. -/
@[simp]
lemma chebyshevTBasis_apply (n : ℕ) : chebyshevTBasis n = T R n :=
  Polynomial.Sequence.basis_eq_self _ _ n

/-- The first `m` Chebyshev polynomials span precisely the polynomials of degree less than
`m`.  This is the finite triangular form of `chebyshevTBasis`. -/
lemma span_T_Iio (m : ℕ) :
    span R ((fun n : ℕ ↦ T R n) '' Set.Iio m) = Polynomial.degreeLT R m := by
  exact (chebyshevTsequence R).span_degreeLT fun n _ ↦ isUnit_leadingCoeff_T n

/-- The Chebyshev polynomials span the polynomial ring. -/
lemma span_range_T : span R (Set.range fun n : ℕ ↦ T R n) = ⊤ := by
  exact (chebyshevTsequence R).span isUnit_leadingCoeff_T

/-- Every polynomial is a finite linear combination of Chebyshev polynomials whose indices
do not exceed its natural degree. -/
lemma mem_span_T_Iic (p : R[X]) :
    p ∈ span R ((fun n : ℕ ↦ T R n) '' Set.Iic p.natDegree) := by
  rw [show (fun n : ℕ ↦ T R n) = chebyshevTsequence R by
    funext n
    simp [chebyshevTsequence]]
  rw [(chebyshevTsequence R).span_degreeLE fun n _ ↦ isUnit_leadingCoeff_T n]
  exact Polynomial.mem_degreeLE.mpr Polynomial.degree_le_natDegree

/-- A linear map out of `R[X]` is determined by its values on the Chebyshev polynomials.

This is the form used by completeness arguments: once a linear functional vanishes on every
Chebyshev mode, it vanishes on every polynomial, hence in particular on every monomial. -/
lemma linearMap_eq_zero_of_forall_map_T_eq_zero {M : Type*} [AddCommGroup M] [Module R M]
    (L : R[X] →ₗ[R] M) (hL : ∀ n : ℕ, L (T R n) = 0) : L = 0 := by
  apply chebyshevTBasis.ext
  intro n
  simp [hL n]

/-- Elementwise form of `linearMap_eq_zero_of_forall_map_T_eq_zero`: a linear map vanishing on
all Chebyshev polynomials vanishes on every polynomial. -/
lemma LinearMap.map_eq_zero_of_forall_map_T_eq_zero {M : Type*} [AddCommGroup M] [Module R M]
    (L : R[X] →ₗ[R] M) (hL : ∀ n : ℕ, L (T R n) = 0) (p : R[X]) : L p = 0 := by
  rw [linearMap_eq_zero_of_forall_map_T_eq_zero L hL]
  rfl

/-- Two linear maps out of `R[X]` agreeing on all Chebyshev polynomials agree everywhere. -/
lemma linearMap_ext_T {M : Type*} [AddCommGroup M] [Module R M]
    {L₁ L₂ : R[X] →ₗ[R] M} (h : ∀ n : ℕ, L₁ (T R n) = L₂ (T R n)) : L₁ = L₂ := by
  apply chebyshevTBasis.ext
  intro n
  simpa using h n

end Polynomial.Chebyshev
