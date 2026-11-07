/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.GraphAutomorphism.Coordinates
import TauCeti.Algebra.CharP.Invertible
import TauCeti.Algebra.Lie.Orthogonal.Basic

/-!
# Restriction and extension for the type-D graph involution

Compression to the invariant coordinates sends native type-D matrices to native
type-B matrices. Extension by zero on the anti-invariant line is a Lie
homomorphism, and restriction is its linear left inverse. These maps use the
norm-two coordinate of the native odd orthogonal form.
-/

public section

open Matrix LieAlgebra.Orthogonal

namespace TauCeti

variable {I : Type*} [DecidableEq I] [Fintype I] (c : I)
  (A : Type*) [CommRing A] [Invertible (2 : A)]

private theorem typeDGraphInclusion_transpose_mul_form :
    (typeDGraphInclusion c A)ᵀ * JD I A =
      JB {i : I // i ≠ c} A * typeDGraphProjection c A := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, isSymm_JD.eq, isSymm_JB.eq] using
    congrArg Matrix.transpose (typeDGraphInclusion_form_transport c A)

private theorem typeDGraphRestriction_mem (X : typeD I A) :
    typeDGraphProjection c A * (X : Matrix (I ⊕ I) (I ⊕ I) A) *
      typeDGraphInclusion c A ∈ typeB {i : I // i ≠ c} A := by
  have hX := X.property
  simp only [typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hX
  simp only [typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  calc
    _ = (typeDGraphInclusion c A)ᵀ * (X : Matrix (I ⊕ I) (I ⊕ I) A)ᵀ *
        ((typeDGraphProjection c A)ᵀ * JB {i : I // i ≠ c} A) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (typeDGraphInclusion c A)ᵀ *
        ((X : Matrix (I ⊕ I) (I ⊕ I) A)ᵀ * JD I A) * typeDGraphInclusion c A := by
      rw [← typeDGraphInclusion_form_transport]
      simp only [Matrix.mul_assoc]
    _ = (typeDGraphInclusion c A)ᵀ *
        (JD I A * (-(X : Matrix (I ⊕ I) (I ⊕ I) A))) * typeDGraphInclusion c A := by
      rw [hX]
    _ = _ := by
      simp only [← Matrix.mul_assoc, typeDGraphInclusion_transpose_mul_form,
        Matrix.mul_neg, Matrix.neg_mul]

private theorem typeDGraphExtension_mem (Y : typeB {i : I // i ≠ c} A) :
    typeDGraphInclusion c A * Y.val * typeDGraphProjection c A ∈ typeD I A := by
  have hY := Y.property
  simp only [typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hY
  simp only [typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  calc
    _ = (typeDGraphProjection c A)ᵀ *
        ((Y : Matrix _ _ A)ᵀ * JB {i : I // i ≠ c} A) * typeDGraphProjection c A := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc,
        typeDGraphInclusion_transpose_mul_form]
    _ = (typeDGraphProjection c A)ᵀ *
        (JB {i : I // i ≠ c} A * (-(Y : Matrix _ _ A))) * typeDGraphProjection c A := by
      rw [hY]
    _ = _ := by
      simp only [← Matrix.mul_assoc, ← typeDGraphInclusion_form_transport,
        Matrix.mul_neg, Matrix.neg_mul]

private theorem typeDGraphExtension_mul
    (Y Z : Matrix (Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c})
      (Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) A) :
    (typeDGraphInclusion c A * Y * typeDGraphProjection c A) *
      (typeDGraphInclusion c A * Z * typeDGraphProjection c A) =
        typeDGraphInclusion c A * (Y * Z) * typeDGraphProjection c A := by
  calc
    _ = typeDGraphInclusion c A * Y *
        (typeDGraphProjection c A * typeDGraphInclusion c A) * Z *
          typeDGraphProjection c A := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [typeDGraphProjection_mul_inclusion, Matrix.mul_one]
      simp only [Matrix.mul_assoc]

/-- Restrict a native even orthogonal operator to the graph-invariant coordinates. -/
def typeDGraphRestriction : typeD I A →ₗ[A] typeB {i : I // i ≠ c} A where
  toFun X := ⟨typeDGraphProjection c A * X.val * typeDGraphInclusion c A,
    by exact typeDGraphRestriction_mem c A X⟩
  map_add' X Y := by
    apply Subtype.ext
    simp only [AddMemClass.coe_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by
    apply Subtype.ext
    simp only [SetLike.val_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- Extend a native odd orthogonal operator by zero on the anti-invariant line. -/
def typeDGraphExtension : typeB {i : I // i ≠ c} A →ₗ⁅A⁆ typeD I A where
  toFun Y := ⟨typeDGraphInclusion c A * Y.val * typeDGraphProjection c A,
    by exact typeDGraphExtension_mem c A Y⟩
  map_add' X Y := by
    apply Subtype.ext
    simp only [AddMemClass.coe_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by
    apply Subtype.ext
    simp only [SetLike.val_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
  map_lie' {X Y} := by
    apply Subtype.ext
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def]
    rw [typeDGraphExtension_mul, typeDGraphExtension_mul, Matrix.mul_sub, Matrix.sub_mul]

/-- The underlying matrix of restriction is compression by projection and inclusion. -/
@[simp]
theorem typeDGraphRestriction_apply_val (X : typeD I A) :
    (typeDGraphRestriction c A X : Matrix
      (Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c})
      (Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) A) =
      typeDGraphProjection c A * X.val * typeDGraphInclusion c A :=
  (rfl)

/-- The underlying matrix of extension uses inclusion and projection. -/
@[simp]
theorem typeDGraphExtension_apply_val (Y : typeB {i : I // i ≠ c} A) :
    (typeDGraphExtension c A Y : Matrix (I ⊕ I) (I ⊕ I) A) =
      typeDGraphInclusion c A * Y.val * typeDGraphProjection c A :=
  (rfl)

/-- Restriction recovers an extended odd orthogonal operator. -/
@[simp]
theorem typeDGraphRestriction_extension (Y : typeB {i : I // i ≠ c} A) :
    typeDGraphRestriction c A (typeDGraphExtension c A Y) = Y := by
  apply Subtype.ext
  simp only [typeDGraphRestriction_apply_val, typeDGraphExtension_apply_val]
  calc
    _ = (typeDGraphProjection c A * typeDGraphInclusion c A) * (Y : Matrix _ _ A) *
        (typeDGraphProjection c A * typeDGraphInclusion c A) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [typeDGraphProjection_mul_inclusion, Matrix.one_mul, Matrix.mul_one]

/-- Extended odd orthogonal operators are fixed by the chosen-pair involution. -/
@[simp]
theorem typeDGraphLieEquiv_extension (Y : typeB {i : I // i ≠ c} A) :
    typeDGraphLieEquiv c A (typeDGraphExtension c A Y) = typeDGraphExtension c A Y := by
  apply Subtype.ext
  simp only [typeDGraphLieEquiv_apply_val, typeDGraphExtension_apply_val]
  calc
    _ = (typeDGraphMatrix c A * typeDGraphInclusion c A) * (Y : Matrix _ _ A) *
        (typeDGraphProjection c A * typeDGraphMatrix c A) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [typeDGraphMatrix_mul_inclusion, typeDGraphProjection_mul_graphMatrix]

private theorem typeDGraphProjection_mul_fixed_mul_antiInclusion (X : typeD I A)
    (hX : typeDGraphLieEquiv c A X = X) :
    typeDGraphProjection c A * X.val * typeDGraphAntiInclusion c A = 0 := by
  have hcomm := (typeDGraphLieEquiv_eq_self_iff c A X).mp hX
  apply eq_zero_of_eq_neg_of_invertible_two (R := A)
  calc
    _ = (typeDGraphProjection c A * typeDGraphMatrix c A) * X.val *
        typeDGraphAntiInclusion c A := by rw [typeDGraphProjection_mul_graphMatrix]
    _ = typeDGraphProjection c A * (typeDGraphMatrix c A * X.val) *
        typeDGraphAntiInclusion c A := by simp only [Matrix.mul_assoc]
    _ = typeDGraphProjection c A * (X.val * typeDGraphMatrix c A) *
        typeDGraphAntiInclusion c A := by rw [hcomm]
    _ = typeDGraphProjection c A * X.val *
        (typeDGraphMatrix c A * typeDGraphAntiInclusion c A) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [typeDGraphMatrix_mul_antiInclusion, Matrix.mul_neg]

private theorem typeDGraphAntiProjection_mul_fixed_mul_inclusion (X : typeD I A)
    (hX : typeDGraphLieEquiv c A X = X) :
    typeDGraphAntiProjection c A * X.val * typeDGraphInclusion c A = 0 := by
  have hcomm := (typeDGraphLieEquiv_eq_self_iff c A X).mp hX
  apply eq_zero_of_eq_neg_of_invertible_two (R := A)
  calc
    _ = typeDGraphAntiProjection c A * X.val *
        (typeDGraphMatrix c A * typeDGraphInclusion c A) := by
      rw [typeDGraphMatrix_mul_inclusion]
    _ = typeDGraphAntiProjection c A * (X.val * typeDGraphMatrix c A) *
        typeDGraphInclusion c A := by simp only [Matrix.mul_assoc]
    _ = typeDGraphAntiProjection c A * (typeDGraphMatrix c A * X.val) *
        typeDGraphInclusion c A := by rw [← hcomm]
    _ = (typeDGraphAntiProjection c A * typeDGraphMatrix c A) * X.val *
        typeDGraphInclusion c A := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [typeDGraphAntiProjection_mul_graphMatrix, Matrix.neg_mul, Matrix.neg_mul]

/-- A fixed native even orthogonal operator vanishes on the anti-invariant line. -/
theorem typeDGraphFixed_mul_antiInclusion (X : typeD I A)
    (hX : typeDGraphLieEquiv c A X = X) :
    X.val * typeDGraphAntiInclusion c A = 0 := by
  let a := typeDGraphAntiProjection c A * X.val * typeDGraphAntiInclusion c A
  have hsplit : X.val * typeDGraphAntiInclusion c A = typeDGraphAntiInclusion c A * a := by
    calc
      _ = typeDGraphInclusion c A *
          (typeDGraphProjection c A * X.val * typeDGraphAntiInclusion c A) +
            typeDGraphAntiInclusion c A * a := by
        simpa only [a, Matrix.mul_assoc] using
          (typeDGraphInclusion_mul_projection_mul_add c A
            (X.val * typeDGraphAntiInclusion c A)).symm
      _ = _ := by
        rw [typeDGraphProjection_mul_fixed_mul_antiInclusion c A X hX,
          Matrix.mul_zero, zero_add]
  have hskew := X.property
  simp only [typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hskew
  have hsandwich := congrArg (fun M : Matrix (I ⊕ I) (I ⊕ I) A =>
    (typeDGraphAntiInclusion c A)ᵀ * M * typeDGraphAntiInclusion c A) hskew
  have ha : aᵀ * ((typeDGraphAntiInclusion c A)ᵀ * JD I A *
      typeDGraphAntiInclusion c A) =
      -(((typeDGraphAntiInclusion c A)ᵀ * JD I A * typeDGraphAntiInclusion c A) * a) := by
    have h : (X.val * typeDGraphAntiInclusion c A)ᵀ * JD I A *
        typeDGraphAntiInclusion c A =
        -((typeDGraphAntiInclusion c A)ᵀ * JD I A *
          (X.val * typeDGraphAntiInclusion c A)) := by
      simpa only [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_neg,
        Matrix.neg_mul] using hsandwich
    rw [hsplit] at h
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using h
  have hat : aᵀ = a := by ext i j; cases i; cases j; rfl
  rw [hat, typeDGraphAntiInclusion_gram] at ha
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at ha
  have ha0 : a = 0 :=
    (isUnit_of_invertible (2 : A)).neg.smul_eq_zero.mp
      (eq_zero_of_eq_neg_of_invertible_two (R := A) ha)
  rw [hsplit, ha0, Matrix.mul_zero]

/-- Extension recovers every fixed native even orthogonal operator from its restriction. -/
theorem typeDGraphExtension_restriction (X : typeD I A)
    (hX : typeDGraphLieEquiv c A X = X) :
    typeDGraphExtension c A (typeDGraphRestriction c A X) = X := by
  have hanti := typeDGraphFixed_mul_antiInclusion c A X hX
  have hplus : X.val * typeDGraphInclusion c A =
      typeDGraphInclusion c A * typeDGraphProjection c A * X.val *
        typeDGraphInclusion c A := by
    calc
      _ = typeDGraphInclusion c A *
          (typeDGraphProjection c A * X.val * typeDGraphInclusion c A) +
            typeDGraphAntiInclusion c A *
              (typeDGraphAntiProjection c A * X.val * typeDGraphInclusion c A) := by
        simpa only [Matrix.mul_assoc] using
          (typeDGraphInclusion_mul_projection_mul_add c A
            (X.val * typeDGraphInclusion c A)).symm
      _ = _ := by
        rw [typeDGraphAntiProjection_mul_fixed_mul_inclusion c A X hX,
          Matrix.mul_zero, add_zero]
        simp only [Matrix.mul_assoc]
  apply Subtype.ext
  simp only [typeDGraphExtension_apply_val, typeDGraphRestriction_apply_val]
  calc
    _ = (typeDGraphInclusion c A * typeDGraphProjection c A * X.val *
        typeDGraphInclusion c A) * typeDGraphProjection c A := by
      simp only [Matrix.mul_assoc]
    _ = X.val * (typeDGraphInclusion c A * typeDGraphProjection c A) := by
      rw [← hplus]
      simp only [Matrix.mul_assoc]
    _ = X.val * (typeDGraphInclusion c A * typeDGraphProjection c A +
        typeDGraphAntiInclusion c A * typeDGraphAntiProjection c A) := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc X.val (typeDGraphAntiInclusion c A),
        hanti, Matrix.zero_mul, add_zero]
    _ = X.val := by rw [typeDGraphInclusion_mul_projection_add, Matrix.mul_one]

/-- Restriction preserves the bracket of two operators fixed by the graph involution. -/
theorem typeDGraphRestriction_lie_of_fixed (X Y : typeD I A)
    (hX : typeDGraphLieEquiv c A X = X) (hY : typeDGraphLieEquiv c A Y = Y) :
    typeDGraphRestriction c A ⁅X, Y⁆ =
      ⁅typeDGraphRestriction c A X, typeDGraphRestriction c A Y⁆ := by
  have hinj : Function.Injective (typeDGraphExtension c A) :=
    Function.LeftInverse.injective (typeDGraphRestriction_extension c A)
  apply hinj
  rw [(typeDGraphExtension c A).map_lie, typeDGraphExtension_restriction c A X hX,
    typeDGraphExtension_restriction c A Y hY]
  apply typeDGraphExtension_restriction
  rw [(typeDGraphLieEquiv c A).map_lie, hX, hY]

end TauCeti
