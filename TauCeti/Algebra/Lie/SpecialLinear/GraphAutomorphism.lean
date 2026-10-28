/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
public import Mathlib.Algebra.Lie.Classical

/-!
# The pinned type-A Lie graph automorphism

Conjugating negative transpose by the existing signed reversal matrix
`TauCeti.typeAGraphConjugator` gives the pinned type-A Lie graph automorphism over any
commutative ring.

The Tau Ceti PR #4951 by mccorvie-agent constructed the same map using
a separate diagonal matrix. Here the conjugator is the one already used by the group
graph automorphism.
-/

public section

open Matrix

namespace TauCeti

variable (r : ℕ) (A : Type*) [CommRing A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The pinned type-A Lie graph automorphism on all matrices. -/
def typeAGraphLieEquiv :
    Matrix (Fin (r + 1)) (Fin (r + 1)) A ≃ₗ⁅A⁆
      Matrix (Fin (r + 1)) (Fin (r + 1)) A :=
  (negTransposeLieEquiv (Fin (r + 1)) A).trans
    (lieConj (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
      (typeAGraphConjugator r A).invertible)

/-- The Lie graph automorphism is signed conjugate transpose. -/
theorem typeAGraphLieEquiv_apply (X : Matrix (Fin (r + 1)) (Fin (r + 1)) A) :
    typeAGraphLieEquiv r A X =
      -((typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) * Xᵀ *
        ((typeAGraphConjugator r A)⁻¹ : Matrix (Fin (r + 1)) (Fin (r + 1)) A)) := by
  simp only [typeAGraphLieEquiv, LieEquiv.trans_apply, negTransposeLieEquiv_apply,
    lieConj_apply, mul_neg, neg_mul]

/-- The graph automorphism reverses both indices and applies the alternating signs. -/
@[simp]
theorem typeAGraphLieEquiv_apply_apply
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) A) (i j : Fin (r + 1)) :
    typeAGraphLieEquiv r A X i j =
      -((-1 : A) ^ i.val * X j.rev i.rev * (-1 : A) ^ j.val) := by
  rw [typeAGraphLieEquiv_apply, typeAGraphConjugator_inv_eq_transpose]
  simp [Matrix.mul_apply, typeAGraphConjugator_apply]

/-- The pinned matrix Lie graph automorphism has order dividing two. -/
@[simp]
theorem typeAGraphLieEquiv_typeAGraphLieEquiv
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) A) :
    typeAGraphLieEquiv r A (typeAGraphLieEquiv r A X) = X := by
  let Q : Matrix (Fin (r + 1)) (Fin (r + 1)) A := typeAGraphConjugator r A
  have hQQ : Q * Q = Matrix.scalar (Fin (r + 1)) ((-1 : A) ^ r) := by
    simpa only [Q, Units.val_mul, GeneralLinearGroup.coe_scalar,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using
      congrArg Units.val (typeAGraphConjugator_mul_self (A := A) r)
  calc
    _ = (Q * Q) * X * (Q * Q)ᵀ := by
      simp only [typeAGraphLieEquiv_apply, typeAGraphConjugator_inv_eq_transpose,
        transpose_neg, transpose_mul, transpose_transpose, mul_neg, neg_mul, neg_neg,
        mul_assoc, Q]
    _ = X := by
      rw [hQQ]
      simp only [Matrix.scalar_apply]
      rw [diagonal_transpose]
      ext i j
      simp only [mul_diagonal, diagonal_mul]
      rw [mul_assoc, mul_comm (X i j), ← mul_assoc, ← mul_pow]
      simp

/-- Signed reverse transpose negates the trace. -/
@[simp]
theorem trace_typeAGraphLieEquiv
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) A) :
    trace (typeAGraphLieEquiv r A X) = -trace X := by
  let := (typeAGraphConjugator r A).invertible
  rw [typeAGraphLieEquiv_apply, trace_neg, trace_mul_comm]
  simp [← mul_assoc]

/-- The graph automorphism reverses matrix units, with their root-dependent sign. -/
@[simp]
theorem typeAGraphLieEquiv_single (i j : Fin (r + 1)) (a : A) :
    typeAGraphLieEquiv r A (single i j a) =
      single j.rev i.rev ((-1 : A) ^ ((i : ℕ) + (j : ℕ) + 1) * a) := by
  have hmod : ((j.rev : ℕ) + (i.rev : ℕ) + 1) % 2 =
      ((i : ℕ) + (j : ℕ) + 1) % 2 := by
    simp only [Fin.val_rev]
    omega
  have hsign : -((-1 : A) ^ (j.rev : ℕ) * a * (-1 : A) ^ (i.rev : ℕ)) =
      (-1 : A) ^ ((i : ℕ) + (j : ℕ) + 1) * a := by
    calc
      _ = (-1 : A) ^ ((j.rev : ℕ) + (i.rev : ℕ) + 1) * a := by
        rw [pow_add, pow_add, pow_one]
        ring
      _ = _ := by
        rw [neg_one_pow_eq_pow_mod_two ((j.rev : ℕ) + (i.rev : ℕ) + 1),
          neg_one_pow_eq_pow_mod_two ((i : ℕ) + (j : ℕ) + 1), hmod]
  ext k l
  by_cases hk : k = j.rev
  · subst k
    by_cases hl : l = i.rev
    · subst l
      simpa only [typeAGraphLieEquiv_apply_apply, Fin.rev_rev, single_apply,
        and_self, ite_true] using hsign
    · have hl' : i ≠ l.rev := by
        intro h
        apply hl
        simpa only [Fin.rev_rev] using (congrArg Fin.rev h).symm
      simp [hl, hl', eq_comm]
  · have hk' : j ≠ k.rev := by
      intro h
      apply hk
      simpa only [Fin.rev_rev] using (congrArg Fin.rev h).symm
    simp [hk, hk', eq_comm]

/-- The inverse of the matrix Lie graph automorphism is itself. -/
@[simp]
theorem typeAGraphLieEquiv_symm :
    (typeAGraphLieEquiv r A).symm = typeAGraphLieEquiv r A := by
  ext X : 1
  apply (typeAGraphLieEquiv r A).injective
  simp

/-- Fixed matrices are skew-adjoint for the inverse signed reversal matrix. -/
theorem typeAGraphLieEquiv_eq_self_iff
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) A) :
    typeAGraphLieEquiv r A X = X ↔
      (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹.IsSkewAdjoint X := by
  let Q : Matrix (Fin (r + 1)) (Fin (r + 1)) A := typeAGraphConjugator r A
  let : Invertible Q := (typeAGraphConjugator r A).invertible
  -- Unfold only the native adjoint relation into its matrix equation.
  change typeAGraphLieEquiv r A X = X ↔ Xᵀ * Q⁻¹ = Q⁻¹ * (-X)
  rw [typeAGraphLieEquiv_apply]
  constructor
  · intro h
    have := congrArg (fun Y ↦ -(Q⁻¹ * Y)) h
    simpa [Q, ← mul_assoc] using this
  · intro h
    have := congrArg (fun Y ↦ -(Q * Y)) h
    simpa [Q, mul_assoc] using this

end TauCeti

namespace TauCeti

open Matrix LieAlgebra.SpecialLinear

variable (r : ℕ) (A : Type*) [CommRing A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The pinned type-A graph automorphism on the native trace-zero matrix Lie algebra. -/
def typeASpecialLinearGraphAutomorphism :
    sl (Fin (r + 1)) A ≃ₗ⁅A⁆ sl (Fin (r + 1)) A :=
  (typeAGraphLieEquiv r A).ofSubalgebras _ _ <| by
    ext X
    simp only [LieSubalgebra.mem_map_submodule, Submodule.mem_map_equiv]
    -- Membership in the native special linear algebra is exactly the trace-zero condition.
    change trace ((typeAGraphLieEquiv r A).symm X) = 0 ↔ trace X = 0
    rw [typeAGraphLieEquiv_symm, trace_typeAGraphLieEquiv, neg_eq_zero]

/-- The trace-zero automorphism is the restriction of the matrix automorphism. -/
@[simp]
theorem coe_typeASpecialLinearGraphAutomorphism (X : sl (Fin (r + 1)) A) :
    (typeASpecialLinearGraphAutomorphism r A X : Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
      typeAGraphLieEquiv r A X :=
  (rfl)

/-- The pinned special linear graph automorphism has order dividing two. -/
@[simp]
theorem typeASpecialLinearGraphAutomorphism_typeASpecialLinearGraphAutomorphism
    (X : sl (Fin (r + 1)) A) :
    typeASpecialLinearGraphAutomorphism r A (typeASpecialLinearGraphAutomorphism r A X) = X := by
  apply Subtype.ext
  simp

/-- On off-diagonal matrix units, the trace-zero automorphism has the same root sign. -/
@[simp]
theorem typeASpecialLinearGraphAutomorphism_single (i j : Fin (r + 1)) (hij : i ≠ j) (a : A) :
    typeASpecialLinearGraphAutomorphism r A (single i j hij a) =
      single j.rev i.rev (Fin.rev_injective.ne hij.symm)
        ((-1 : A) ^ ((i : ℕ) + (j : ℕ) + 1) * a) := by
  apply Subtype.ext
  simp only [coe_typeASpecialLinearGraphAutomorphism, val_single, typeAGraphLieEquiv_single]

/-- Positive simple-root vectors are carried to the reversed node, with unchanged parameter. -/
theorem typeASpecialLinearGraphAutomorphism_single_upper (i : Fin r) (a : A) :
    typeASpecialLinearGraphAutomorphism r A
        (single i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne a) =
      single i.rev.castSucc i.rev.succ (Fin.castSucc_lt_succ (i := i.rev)).ne a := by
  have hsign : (-1 : A) ^ ((i.castSucc : ℕ) + ((i.succ : Fin (r + 1)) : ℕ) + 1) = 1 :=
    Even.neg_one_pow ⟨(i : ℕ) + 1, by simp only [Fin.val_castSucc, Fin.val_succ]; omega⟩
  simpa only [Fin.rev_succ, Fin.rev_castSucc, hsign, one_mul] using
    typeASpecialLinearGraphAutomorphism_single r A i.castSucc i.succ
      (Fin.castSucc_lt_succ (i := i)).ne a

/-- Negative simple-root vectors are carried to the reversed node, with unchanged parameter. -/
theorem typeASpecialLinearGraphAutomorphism_single_lower (i : Fin r) (a : A) :
    typeASpecialLinearGraphAutomorphism r A
        (single i.succ i.castSucc (Fin.castSucc_lt_succ (i := i)).ne' a) =
      single i.rev.succ i.rev.castSucc (Fin.castSucc_lt_succ (i := i.rev)).ne' a := by
  have hsign : (-1 : A) ^ (((i.succ : Fin (r + 1)) : ℕ) + (i.castSucc : ℕ) + 1) = 1 :=
    Even.neg_one_pow ⟨(i : ℕ) + 1, by simp only [Fin.val_castSucc, Fin.val_succ]; omega⟩
  simpa only [Fin.rev_castSucc, Fin.rev_succ, hsign, one_mul] using
    typeASpecialLinearGraphAutomorphism_single r A i.succ i.castSucc
      (Fin.castSucc_lt_succ (i := i)).ne' a

/-- The automorphism reverses the two indices of a trace-zero diagonal difference. -/
@[simp]
theorem typeASpecialLinearGraphAutomorphism_singleSubSingle (i j : Fin (r + 1)) (a : A) :
    typeASpecialLinearGraphAutomorphism r A (singleSubSingle i j a) =
      singleSubSingle j.rev i.rev a := by
  have hsign (k : Fin (r + 1)) : (-1 : A) ^ ((k : ℕ) + (k : ℕ) + 1) = -1 :=
    Odd.neg_one_pow ⟨(k : ℕ), by omega⟩
  apply Subtype.ext
  simp only [coe_typeASpecialLinearGraphAutomorphism, val_singleSubSingle, map_sub,
    typeAGraphLieEquiv_single, hsign, neg_one_mul, ← Matrix.single_neg]
  abel

/-- The simple coroot vector is carried to the reversed Dynkin node. -/
theorem typeASpecialLinearGraphAutomorphism_coroot (i : Fin r) (a : A) :
    typeASpecialLinearGraphAutomorphism r A (singleSubSingle i.castSucc i.succ a) =
      singleSubSingle i.rev.castSucc i.rev.succ a := by
  simp only [typeASpecialLinearGraphAutomorphism_singleSubSingle, Fin.rev_succ, Fin.rev_castSucc]

/-- Fixed trace-zero matrices are precisely the matrices skew-adjoint for the inverse conjugator. -/
theorem typeASpecialLinearGraphAutomorphism_eq_self_iff (X : sl (Fin (r + 1)) A) :
    typeASpecialLinearGraphAutomorphism r A X = X ↔
      (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹.IsSkewAdjoint X := by
  rw [Subtype.ext_iff, coe_typeASpecialLinearGraphAutomorphism, typeAGraphLieEquiv_eq_self_iff]

end TauCeti
