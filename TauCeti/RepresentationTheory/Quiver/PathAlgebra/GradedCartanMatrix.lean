/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Algebra.Polynomial.Laurent.Coeff
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedSimple

/-!
# The graded Cartan matrix of a path algebra

Let `Q` be a finite acyclic quiver, so that its path algebra `kQ` is finite-dimensional, and give
`kQ` its path-length grading. The degree-zero piece is spanned by the vertex idempotents `eᵢ`,
so the graded vertex projectives `kQ eᵢ` form a basis of `K₀^gr(proj kQ)` over `ℤ[q,q⁻¹]`
(`TauCeti.gradedIdempotentProjectiveBasis`), just as the graded vertex simples form a basis of
`G₀^gr(mod kQ)`.

In these two bases the graded Cartan matrix is the path-counting matrix: the coefficient of `qⁿ`
in its `(i, j)` entry is the number of paths of length `n` from `j` to `i`, and there are no
negative powers of `q`. Rows are indexed by simples and columns by projectives, following the
left-module convention for Cartan matrices.

Counting paths by their last arrow turns this into a closed formula. If the `(i, j)` entry of `A`
counts arrows `i ⟶ j`, then the graded Cartan matrix is `(1 - q Aᵀ)⁻¹`. Applying `q ↦ q⁻¹`
entrywise and transposing, its conjugate transpose inverts `1 - q⁻¹ A`, the matrix of the graded
Ringel form; this is the input for identifying the q-Euler matrix of the graded vertex simples
with the inverse conjugate-transposed graded Cartan matrix.

## Main definitions

* `TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis`: the basis `[kQ eᵢ]` of
  `K₀^gr(proj kQ)`.

## Main results

* `TauCeti.PathAlgebra.coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis`: the
  coefficient of `qⁿ` in the `(i, j)` entry of the graded Cartan matrix is the number of
  length-`n` paths `j ⟶ i`.
* `TauCeti.PathAlgebra.coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis_of_neg`:
  negative-degree coefficients vanish.
* `TauCeti.PathAlgebra.one_sub_T_smul_transpose_mul_gradedCartanMatrix_eq_one` and
  `TauCeti.PathAlgebra.gradedCartanMatrix_eq_inv_one_sub_T_smul_transpose`: the graded Cartan
  matrix is `(1 - q Aᵀ)⁻¹`.
* `TauCeti.PathAlgebra.gradedCartanMatrix_map_invert_transpose_mul_one_sub_T_neg_smul_eq_one`:
  its conjugate transpose inverts `1 - q⁻¹ A`.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Section 3, for the Cartan matrix of a path algebra.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Cartan matrix over `ℤ[q,q⁻¹]`.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory LaurentPolynomial
open scoped Matrix

universe u v w

variable (k : Type w) (Q : Type u) [Quiver.{v} Q] [Field k] [Finite Q]
  [FiniteDimensional k (pathAlgebra k Q)]

/-- **The vertex-projective basis of `K₀^gr(proj kQ)`** over `ℤ[q,q⁻¹]`, for a finite acyclic
quiver: its vector at `i` is the class `[kQ eᵢ]` of the graded vertex projective. -/
def gradedVertexProjectiveClassBasis :
    Module.Basis Q (LaurentPolynomial ℤ)
      (LaurentK0.{max u v w}
        (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))) :=
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  gradedIdempotentProjectiveBasis (completeOrthogonalIdempotents_vertexIdempotent k Q)
    (vertexIdempotent_mem_integerGrade_zero k Q) (isHomogeneous_span_vertexIdempotent k Q)
    (fun _ => integerGrade_eq_bot_of_neg k Q)
    (integerGrade_zero_eq_span_range_vertexIdempotent k Q).le vertexIdempotent_ne_zero

/-- The basis vector of `TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis` at `i` is the
class `[kQ eᵢ]`. -/
@[simp]
theorem gradedVertexProjectiveClassBasis_apply (i : Q) :
    gradedVertexProjectiveClassBasis k Q i = gradedVertexProjectiveClass k Q i := by
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  unfold gradedVertexProjectiveClassBasis
  rw [gradedIdempotentProjectiveBasis_apply, gradedVertexProjectiveClass_eq]
  congr 2
  exact (gradedVertexProjective_def k Q i).symm

/-- **The graded Cartan matrix of a path algebra counts paths by length.** In the bases of graded
vertex projectives and graded vertex simples, the coefficient of `qⁿ` in the `(i, j)` entry is
the number of paths of length `n` from `j` to `i`. -/
theorem coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis [Fintype Q] (i j : Q) (n : ℕ) :
    (gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q) i j).coeff n =
      Nat.card (PathBetween Q n j i) := by
  rw [gradedCartanMatrix_apply, gradedVertexSimpleClassBasis_repr_apply,
    gradedVertexProjectiveClassBasis_apply, coeff_gradedCartanMap_gradedVertexProjectiveClass]

/-- The entries of the graded Cartan matrix of a path algebra have no negative powers of `q`. -/
theorem coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis_of_neg [Fintype Q] (i j : Q)
    (d : ℤ) (hd : d < 0) :
    (gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q) i j).coeff d = 0 := by
  rw [gradedCartanMatrix_apply, gradedVertexSimpleClassBasis_repr_apply,
    gradedVertexProjectiveClassBasis_apply,
    coeff_gradedCartanMap_gradedVertexProjectiveClass_of_neg k Q i j d hd]

/-- **The graded Cartan matrix of a path algebra inverts `1 - q Aᵀ`**, where the `(i, j)` entry
of `A` counts arrows `i ⟶ j`, in the bases of graded vertex projectives and graded vertex
simples. On coefficients of `qⁿ` this is the last-arrow recursion for path counts: the paths of
length `n + 1` from `j` to `i` are the paths of length `n` from `j` to some `l` followed by an
arrow `l ⟶ i`, and the only path of length zero is the trivial path. -/
theorem one_sub_T_smul_transpose_mul_gradedCartanMatrix_eq_one [Fintype Q] [DecidableEq Q] :
    (1 - (T 1 : LaurentPolynomial ℤ) •
        (Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : LaurentPolynomial ℤ))ᵀ) *
      gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q) = 1 := by
  have : ∀ i j : Q, Finite (i ⟶ j) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  -- Compare the coefficients of `qⁿ` entrywise, separately for `n < 0`, `n = 0` and `n = m + 1`.
  refine Matrix.ext fun i j => ?_
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply]
  ext n
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_T_mul,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Matrix.transpose_apply, Matrix.of_apply,
    coeff_natCast_mul, Matrix.one_apply]
  rcases lt_or_ge n 0 with hn | hn
  · simp only [coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis_of_neg k Q _ j n hn,
      coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis_of_neg k Q _ j (n - 1)
        (by omega), mul_zero, Finset.sum_const_zero, sub_zero]
    split_ifs <;> simp [hn.ne]
  · lift n to ℕ using hn
    cases n with
    | zero =>
      simp only [Nat.cast_zero, zero_sub,
        coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis_of_neg k Q _ j (-1)
          (by norm_num), mul_zero, Finset.sum_const_zero, sub_zero]
      have h0 := coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis k Q i j 0
      rw [Nat.cast_zero] at h0
      rw [h0, card_pathBetween_zero]
      by_cases h : i = j
      · subst h
        simp
      · simp [h, Ne.symm h]
    | succ m =>
      have hs := coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis k Q i j (m + 1)
      rw [Nat.cast_succ] at hs
      rw [Nat.cast_succ, add_sub_cancel_right, hs]
      simp only [coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis k Q _ j m,
        ← card_pathBetween_mul_card_arrow_eq, Nat.cast_sum, Nat.cast_mul, mul_comm, sub_self]
      have hm : (m : ℤ) + 1 ≠ 0 := by omega
      split_ifs <;> simp [hm]

/-- **The graded Cartan matrix of a path algebra is `(1 - q Aᵀ)⁻¹`**, where the `(i, j)` entry
of `A` counts arrows `i ⟶ j`, in the bases of graded vertex projectives and graded vertex
simples. -/
theorem gradedCartanMatrix_eq_inv_one_sub_T_smul_transpose [Fintype Q] [DecidableEq Q] :
    gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q) =
      (1 - (T 1 : LaurentPolynomial ℤ) •
        (Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : LaurentPolynomial ℤ))ᵀ)⁻¹ :=
  (Matrix.inv_eq_right_inv (one_sub_T_smul_transpose_mul_gradedCartanMatrix_eq_one k Q)).symm

/-- **The conjugate-transposed graded Cartan matrix of a path algebra inverts `1 - q⁻¹ A`**,
where the `(i, j)` entry of `A` counts arrows `i ⟶ j`. This is the conjugate transpose of
`TauCeti.PathAlgebra.one_sub_T_smul_transpose_mul_gradedCartanMatrix_eq_one`. The matrix
`1 - q⁻¹ A` is the graded Ringel matrix, the q-Euler matrix of the graded vertex simples
(`TauCeti.PathAlgebra.gradedExtEulerForm_basis`). -/
theorem gradedCartanMatrix_map_invert_transpose_mul_one_sub_T_neg_smul_eq_one [Fintype Q]
    [DecidableEq Q] :
    ((gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q)).map (invert (R := ℤ)))ᵀ *
      (1 - (T (-1) : LaurentPolynomial ℤ) •
        Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : LaurentPolynomial ℤ)) = 1 := by
  have hA : ((invert (R := ℤ)).mapMatrix (1 - (T 1 : LaurentPolynomial ℤ) •
      (Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : LaurentPolynomial ℤ))ᵀ))ᵀ =
      1 - (T (-1) : LaurentPolynomial ℤ) •
        Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : LaurentPolynomial ℤ) := by
    ext i j
    by_cases h : i = j <;> simp [h, Ne.symm]
  have h := congrArg (fun M => ((invert (R := ℤ)).mapMatrix M)ᵀ)
    (one_sub_T_smul_transpose_mul_gradedCartanMatrix_eq_one k Q)
  rwa [map_mul, map_one, Matrix.transpose_mul, Matrix.transpose_one, hA,
    AlgEquiv.mapMatrix_apply] at h

end TauCeti.PathAlgebra
