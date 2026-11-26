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

/-- The decomposition Laurent polynomial is the sum of the homogeneous components, each times the
monomial of its degree. -/
theorem decomposeLaurent_eq_sum [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (x : A) :
    decomposeLaurent ℳ x = ∑ n ∈ (decompose ℳ x).support,
      LaurentPolynomial.C (decompose ℳ x n : A) * LaurentPolynomial.T n := by
  conv_lhs => rw [← sum_support_decompose ℳ x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ ↦ decomposeLaurent_of_mem ℳ (decompose ℳ x n).property

/-- The coefficients of the decomposition Laurent polynomial are the homogeneous components. -/
@[simp]
theorem coeff_decomposeLaurent (x : A) (i : ℤ) :
    (decomposeLaurent ℳ x).coeff i = (decompose ℳ x i : A) := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | @homogeneous j x =>
    rw [decomposeLaurent_of_mem ℳ x.property]
    by_cases h : j = i
    · subst i
      simp [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
    · simp [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), h]

/-- An element is homogeneous of degree `i` exactly when its decomposition Laurent polynomial is
the single monomial in degree `i`. -/
theorem decomposeLaurent_eq_C_mul_T_iff {x : A} {i : ℤ} :
    decomposeLaurent ℳ x = LaurentPolynomial.C x * LaurentPolynomial.T i ↔ x ∈ ℳ i := by
  refine ⟨fun h ↦ ?_, decomposeLaurent_of_mem ℳ⟩
  have hi := coeff_decomposeLaurent ℳ x i
  simp only [h, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same] at hi
  exact hi ▸ (decompose ℳ x i).property

/-- If `1` is homogeneous of degree `0`, as in a graded ring, its decomposition Laurent polynomial
is `1`. -/
@[simp]
theorem decomposeLaurent_one [SetLike.GradedOne ℳ] : decomposeLaurent ℳ (1 : A) = 1 := by
  simp [decomposeLaurent_of_mem ℳ (SetLike.one_mem_graded ℳ)]

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
      have hax : (a : A) * x ∈ ℳ (i + j) := SetLike.GradedSMul.smul_mem a.property x.property
      rw [decomposeLaurent_of_mem ℳ hax, decomposeLaurent_of_mem 𝒜 a.property,
        decomposeLaurent_of_mem ℳ x.property]
      simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.single_mul_single]

/-- Multiplication by an element homogeneous of degree `i` multiplies the decomposition Laurent
polynomial by a monomial of degree `i`. -/
theorem decomposeLaurent_mul_of_mem {a : A} {i : ℤ} (ha : a ∈ 𝒜 i) (x : A) :
    decomposeLaurent ℳ (a * x) =
      LaurentPolynomial.C a * LaurentPolynomial.T i * decomposeLaurent ℳ x := by
  rw [decomposeLaurent_mul ℳ 𝒜, decomposeLaurent_of_mem 𝒜 ha]

/-- The scalar coaction of the degree-`i` component `mᵢ` of `1`, times the Laurent polynomial of
the homogeneous components of `1`, is the monomial `mᵢ Tⁱ`. -/
theorem decomposeLaurent_decompose_one_mul (i : ℤ) :
    decomposeLaurent 𝒜 (decompose ℳ (1 : A) i : A) * decomposeLaurent ℳ (1 : A) =
      LaurentPolynomial.C (decompose ℳ (1 : A) i : A) * LaurentPolynomial.T i := by
  rw [← decomposeLaurent_mul ℳ 𝒜, mul_one]
  exact decomposeLaurent_of_mem ℳ (decompose ℳ (1 : A) i).property

section CommSemiring

variable {A σ : Type*} [CommSemiring A] [SetLike σ A] [AddSubmonoidClass σ A]
    (ℳ : ℤ → σ) [Decomposition ℳ]

/-- Evaluating the decomposition Laurent polynomial at `1` sums the homogeneous components back
to the element. -/
@[simp]
theorem eval₂_one_decomposeLaurent (x : A) :
    LaurentPolynomial.eval₂ (RingHom.id A) 1 (decomposeLaurent ℳ x) = x := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | homogeneous x => simp [decomposeLaurent_of_mem ℳ x.property, LaurentPolynomial.eval₂_C_mul_T]

end CommSemiring

end

end TauCeti
