/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous decompositions as Laurent polynomials

An integer-indexed internal decomposition of a semiring gives an additive map to its Laurent
polynomial ring, recording the degree of each homogeneous component as an exponent.
For a graded ring this is its multiplicative coaction; for a compatibly graded module on the
same underlying semiring it intertwines multiplication with the scalar coaction. This is useful
for studying gradings on free modules of rank one.
-/

public section

open DirectSum
open scoped LaurentPolynomial

namespace TauCeti

noncomputable section

variable {A σ : Type*} [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A]
    (ℳ : ℤ → σ) [Decomposition ℳ]

/-- Record each homogeneous component as the coefficient at its degree. -/
def decomposeLaurent : A →+ A[T;T⁻¹] :=
  (DirectSum.toAddMonoid fun i ↦
    (AddMonoidAlgebra.singleAddHom i).comp (AddSubmonoidClass.subtype (ℳ i))).comp
    (decomposeAddEquiv ℳ).toAddMonoidHom

/-- On a homogeneous element, the decomposition Laurent polynomial is a single monomial. -/
theorem decomposeLaurent_of_mem {x : A} {i : ℤ} (hx : x ∈ ℳ i) :
    decomposeLaurent ℳ x = LaurentPolynomial.C x * LaurentPolynomial.T i := by
  simp [decomposeLaurent, decompose_of_mem ℳ hx]

/-- The coefficients of the decomposition Laurent polynomial are the homogeneous components. -/
@[simp]
theorem coeff_decomposeLaurent (x : A) (i : ℤ) :
    (decomposeLaurent ℳ x).coeff i = (decompose ℳ x i : A) := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | @homogeneous j x =>
    rw [decomposeLaurent_of_mem ℳ x.2]
    by_cases h : j = i
    · subst i
      simp [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
    · simp [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), h]

variable {τ : Type*} [SetLike τ A] [AddSubmonoidClass τ A]
    (𝒜 : ℤ → τ) [Decomposition 𝒜] [SetLike.GradedSMul 𝒜 ℳ]

/-- Compatible homogeneous decompositions turn scalar multiplication into multiplication
of Laurent polynomials. The scalar action here is the semiring's multiplication. -/
theorem decomposeLaurent_mul (a x : A) :
    decomposeLaurent ℳ (a * x) = decomposeLaurent 𝒜 a * decomposeLaurent ℳ x := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb => simp [add_mul, ha, hb]
  | @homogeneous i a =>
    induction x using Decomposition.inductionOn ℳ with
    | zero => simp
    | add x y hx hy => simp [mul_add, hx, hy]
    | @homogeneous j x =>
      have hax : (a : A) * x ∈ ℳ (i + j) := SetLike.GradedSMul.smul_mem a.2 x.2
      rw [decomposeLaurent_of_mem ℳ hax, decomposeLaurent_of_mem 𝒜 a.2,
        decomposeLaurent_of_mem ℳ x.2]
      simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.single_mul_single]

end

end TauCeti
