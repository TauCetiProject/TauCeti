/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Algebraic independence of matrix linear combinations

Given a matrix `C : Matrix m n R` over a commutative ring `R` and a tuple `x : n → A` in an
`R`-algebra `A`, the linear combinations `y i = ∑ j, C i j • x j` are `(Fintype.linearCombination R
x) ∘ C`. When `y` is algebraically independent over `R`, it is `R`-linearly independent, so the rows
of `C` are `R`-linearly independent (`AlgebraicIndependent.linearIndependent_of_sum_smul`) and, when
`R` is nontrivial and `m` is finite, `Fintype.card m ≤ Fintype.card n`
(`AlgebraicIndependent.card_le_of_sum_smul`).

Matrix multiplication composes linear combinations (`Matrix.sum_mul_smul`). For an invertible square
matrix `C : Matrix n n R`, the linear substitution `X i ↦ ∑ j, C i j • X j` is an `R`-algebra
automorphism of `MvPolynomial n R`, so replacing `x` by `fun i ↦ ∑ j, C i j • x j` preserves the
generated subalgebra, algebraic independence, and finiteness of polynomial evaluation.

## Main results

* `Matrix.sum_mul_smul`: `∑ k, (M * N) i k • x k = ∑ j, M i j • ∑ k, N j k • x k`.
* `AlgebraicIndependent.linearIndependent_of_sum_smul`: if `fun i ↦ ∑ j, C i j • x j` is
  algebraically independent over `R`, then the rows of `C` are `R`-linearly independent.
* `AlgebraicIndependent.card_le_of_sum_smul`: over a nontrivial commutative ring, algebraic
  independence of `m` linear combinations of `n` elements implies `Fintype.card m ≤ Fintype.card n`.
* `TauCeti.algebraicIndependent_sum_smul_iff_of_isUnit`: invertible linear change of generators
  preserves algebraic independence.
-/

public section

open MvPolynomial

namespace Matrix

/-- Matrix multiplication composes scalar linear combinations in a module. -/
theorem sum_mul_smul {l m n R M : Type*} [Fintype m] [Fintype n] [Semiring R]
    [AddCommMonoid M] [Module R M] (A : Matrix l m R) (B : Matrix m n R) (x : n → M) (i : l) :
    ∑ k, (A * B) i k • x k = ∑ j, A i j • ∑ k, B j k • x k := by
  simp_rw [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

end Matrix

section CommSemiring

variable {l m n R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Evaluating a polynomial after a linear substitution of variables agrees with evaluating at the
corresponding linear combinations. -/
theorem MvPolynomial.aeval_comp_aeval_sum_smul_X [Fintype n] (C : Matrix m n R) (x : n → A) :
    (aeval x).comp (aeval fun i : m ↦ ∑ j : n, C i j • (X j : MvPolynomial n R)) =
      aeval fun i : m ↦ ∑ j : n, C i j • x j := by
  ext i
  simp [map_sum]

/-- Composing two linear variable substitutions corresponds to multiplying their coefficient
matrices in reverse order. -/
theorem MvPolynomial.aeval_sum_smul_X_comp [Fintype m] [Fintype n]
    (C : Matrix l m R) (D : Matrix m n R) :
    (aeval fun j : m ↦ ∑ k : n, D j k • (X k : MvPolynomial n R)).comp
        (aeval fun i : l ↦ ∑ j : m, C i j • (X j : MvPolynomial m R)) =
      aeval fun i : l ↦ ∑ k : n, (C * D) i k • (X k : MvPolynomial n R) := by
  ext i
  simp [map_sum, Matrix.sum_mul_smul]

/-- An invertible square matrix over `R` induces an `R`-algebra automorphism of `MvPolynomial n R`
by linear substitution of variables. -/
noncomputable def MvPolynomial.linearSubstAlgEquiv [Fintype n] [DecidableEq n]
    (u : (Matrix n n R)ˣ) : MvPolynomial n R ≃ₐ[R] MvPolynomial n R :=
  AlgEquiv.ofAlgHom
    (aeval fun i ↦ ∑ j, (u : Matrix n n R) i j • X j)
    (aeval fun i ↦ ∑ j, (↑u⁻¹ : Matrix n n R) i j • X j)
    (by
      rw [aeval_sum_smul_X_comp, Units.inv_mul]
      ext i
      simp [Matrix.one_apply])
    (by
      rw [aeval_sum_smul_X_comp, Units.mul_inv]
      ext i
      simp [Matrix.one_apply])

/-- `MvPolynomial.linearSubstAlgEquiv u` sends `X i` to the `i`-th row linear combination of `X`. -/
@[simp]
theorem MvPolynomial.linearSubstAlgEquiv_X [Fintype n] [DecidableEq n]
    (u : (Matrix n n R)ˣ) (i : n) :
    linearSubstAlgEquiv u (X i) = ∑ j, (u : Matrix n n R) i j • X j := by
  simp [linearSubstAlgEquiv]

/-- The inverse of `MvPolynomial.linearSubstAlgEquiv u` sends `X i` to the `i`-th row linear
combination of `X` with coefficients from `u⁻¹`. -/
@[simp]
theorem MvPolynomial.linearSubstAlgEquiv_symm_X [Fintype n] [DecidableEq n]
    (u : (Matrix n n R)ˣ) (i : n) :
    (linearSubstAlgEquiv u).symm (X i) = ∑ j, (↑u⁻¹ : Matrix n n R) i j • X j := by
  simp [linearSubstAlgEquiv]

/-- An invertible linear transformation of generators preserves the generated `R`-subalgebra. -/
theorem Algebra.adjoin_range_sum_smul_of_isUnit [Fintype n] [DecidableEq n]
    {C : Matrix n n R} (hC : IsUnit C) (x : n → A) :
    Algebra.adjoin R (Set.range fun i ↦ ∑ j, C i j • x j) = Algebra.adjoin R (Set.range x) := by
  obtain ⟨u, rfl⟩ := hC
  have hcomp :
      aeval (fun i ↦ ∑ j, (u : Matrix n n R) i j • x j) =
        (aeval x).comp (linearSubstAlgEquiv u).toAlgHom :=
    (MvPolynomial.aeval_comp_aeval_sum_smul_X (u : Matrix n n R) x).symm
  rw [Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_range_eq_range_aeval, hcomp]
  ext a
  simp only [AlgHom.mem_range, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  exact ((linearSubstAlgEquiv u).surjective.exists (p := fun y ↦ aeval x y = a)).symm

end CommSemiring

section CommRing

variable {m n R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

namespace AlgebraicIndependent

/-- If the linear combinations `fun i ↦ ∑ j, C i j • x j` are algebraically independent over `R`,
then the rows of `C` are `R`-linearly independent. -/
theorem linearIndependent_of_sum_smul [Fintype n] {C : Matrix m n R} {x : n → A}
    (hy : AlgebraicIndependent R fun i ↦ ∑ j, C i j • x j) :
    LinearIndependent R C :=
  LinearIndependent.of_comp (Fintype.linearCombination R x) hy.linearIndependent

/-- Over a nontrivial commutative ring, if `m` linear combinations of `n` elements are
algebraically independent, then `Fintype.card m ≤ Fintype.card n`. -/
theorem card_le_of_sum_smul [Fintype m] [Fintype n] [Nontrivial R] {C : Matrix m n R} {x : n → A}
    (hy : AlgebraicIndependent R fun i ↦ ∑ j, C i j • x j) :
    Fintype.card m ≤ Fintype.card n := by
  simpa using LinearIndependent.fintype_card_le_finrank hy.linearIndependent_of_sum_smul

end AlgebraicIndependent

/-- An invertible linear transformation of generators preserves algebraic independence. -/
theorem TauCeti.algebraicIndependent_sum_smul_iff_of_isUnit [Fintype n] [DecidableEq n]
    {C : Matrix n n R} (hC : IsUnit C) (x : n → A) :
    (AlgebraicIndependent R fun i ↦ ∑ j, C i j • x j) ↔ AlgebraicIndependent R x := by
  obtain ⟨u, rfl⟩ := hC
  have hcomp :
      aeval (fun i ↦ ∑ j, (u : Matrix n n R) i j • x j) =
        (aeval x).comp (linearSubstAlgEquiv u).toAlgHom :=
    (MvPolynomial.aeval_comp_aeval_sum_smul_X (u : Matrix n n R) x).symm
  rw [algebraicIndependent_iff_injective_aeval, algebraicIndependent_iff_injective_aeval, hcomp,
    AlgHom.coe_comp, AlgEquiv.coe_toAlgHom]
  exact Function.Injective.of_comp_iff' _ (linearSubstAlgEquiv u).bijective

/-- An invertible linear transformation of generators preserves finiteness of polynomial
evaluation. -/
theorem MvPolynomial.finite_aeval_sum_smul_iff_of_isUnit [Fintype n] [DecidableEq n]
    {C : Matrix n n R} (hC : IsUnit C) (x : n → A) :
    (aeval fun i ↦ ∑ j, C i j • x j : MvPolynomial n R →ₐ[R] A).Finite ↔
      (aeval x : MvPolynomial n R →ₐ[R] A).Finite := by
  obtain ⟨u, rfl⟩ := hC
  have hcomp :
      aeval (fun i ↦ ∑ j, (u : Matrix n n R) i j • x j) =
        (aeval x).comp (linearSubstAlgEquiv u).toAlgHom :=
    (MvPolynomial.aeval_comp_aeval_sum_smul_X (u : Matrix n n R) x).symm
  have hinv :
      aeval x =
        (aeval fun i ↦ ∑ j, (u : Matrix n n R) i j • x j).comp
          (linearSubstAlgEquiv u).symm.toAlgHom := by
    rw [hcomp, AlgHom.comp_assoc]
    ext i
    simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hinv]
    exact h.comp (AlgHom.Finite.of_surjective _ (linearSubstAlgEquiv u).symm.surjective)
  · rw [hcomp]
    exact h.comp (AlgHom.Finite.of_surjective _ (linearSubstAlgEquiv u).surjective)

end CommRing
