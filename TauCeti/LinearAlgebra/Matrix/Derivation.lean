/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Derivations of a matrix algebra are inner

Every linear endomorphism of a matrix algebra satisfying the associative Leibniz rule is
commutation with a matrix. This holds over any commutative ring, including in positive
characteristic, and identifies the infinitesimal algebra automorphisms of a matrix algebra.

## References

* N. Jacobson, *Basic Algebra II*, the innerness of derivations of matrix algebras.
-/

public section

open Matrix

namespace LinearMap

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- Every associative derivation of a matrix algebra is inner, over any commutative ring.
No nonemptiness assumption on the matrix index type is needed. -/
theorem exists_matrix_eq_mulLeft_sub_mulRight_of_leibniz
    (D : Matrix ι ι R →ₗ[R] Matrix ι ι R)
    (hD : ∀ A B, D (A * B) = D A * B + A * D B) :
    ∃ X : Matrix ι ι R, D = LinearMap.mulLeft R X - LinearMap.mulRight R X := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    exact ⟨0, Subsingleton.elim _ _⟩
  | inr h =>
    let r : ι := Classical.choice h
    let X : Matrix ι ι R := of fun a b => D (Matrix.single b r 1) a r
    refine ⟨X, (stdBasis R ι ι).ext fun ij => ?_⟩
    rcases ij with ⟨i, j⟩
    rw [stdBasis_eq_single]
    rw [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    ext a b
    have hab := congrArg (fun M : Matrix ι ι R => M a r)
      (hD (Matrix.single i j 1) (Matrix.single b r 1))
    have hprod : Matrix.single i j (1 : R) * Matrix.single b r 1 =
        if j = b then Matrix.single i r 1 else 0 := by
      by_cases h : j = b
      · subst b
        simp
      · simp [single_mul_single_of_ne _ _ _ _ h, h]
    rw [hprod] at hab
    simp only [apply_ite D, map_zero, Matrix.add_apply, mul_single_apply_same, mul_one] at hab
    simp only [Matrix.sub_apply]
    by_cases hjb : j = b
    · subst b
      by_cases hai : a = i
      · subst a
        simp only [ite_true, single_mul_apply_same, one_mul,
          mul_single_apply_same, mul_one] at hab ⊢
        dsimp only [X, of_apply]
        exact eq_sub_of_add_eq hab.symm
      · simp [hai] at hab ⊢
        simpa only [X, of_apply] using hab.symm
    · by_cases hai : a = i
      · subst a
        simp [hjb, Ne.symm hjb] at hab ⊢
        simpa only [X, of_apply] using eq_neg_of_add_eq_zero_left hab.symm
      · simp [hjb, Ne.symm hjb, hai] at hab ⊢
        simpa only [X, of_apply] using hab.symm

end LinearMap
