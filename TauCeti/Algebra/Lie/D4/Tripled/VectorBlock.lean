/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Generators

/-!
# The vector block of the tripled type-D4 representation

The first eight coordinates of the tripled type-`D₄` representation form its natural vector
summand. This file compares that block with the standard split orthogonal representation on
coordinates `Fin 4 ⊕ Fin 4`.

The positive isotropic coordinates occur in their standard order. The negative coordinates occur
in reverse order, as required by the natural weights
`ε₁, ε₂, ε₃, ε₄, -ε₄, -ε₃, -ε₂, -ε₁`. The standard split orthogonal matrices
have negative entries on one half of each root operator, whereas the minuscule tripled matrices
use coefficient `1` on every weight step. Multiplying the reversed negative-coordinate basis by
the alternating signs `-1, 1, -1, 1` reconciles these conventions.

The three final equations are the entrywise intertwining identities for the positive, negative,
and Cartan Chevalley generators. They fix both the Bourbaki node numbering and every basis sign.

## Main declarations

* `TauCeti.D4Tripled.vectorIndex`: their inclusion into the natural block of the tripled table.
* `TauCeti.D4Tripled.vectorBasisSign`: the basis normalization on the standard coordinates.
* `TauCeti.D4Tripled.raisingMatrix_vectorIndex`,
  `TauCeti.D4Tripled.loweringMatrix_vectorIndex`, and
  `TauCeti.D4Tripled.cartanGeneratorMatrix_vectorIndex`: the signed generator comparisons.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

/-! ## Coordinates and signs -/

/-- The standard vector coordinates included into the natural block of the tripled weight table. -/
@[expose]
public def vectorIndex : Fin 4 ⊕ Fin 4 → Fin 24
  | .inl i => ⟨i, by omega⟩
  | .inr i => ⟨7 - i, by omega⟩

/-- A positive standard coordinate has the same numerical index in the tripled table. -/
@[simp]
public theorem vectorIndex_inl_val (i : Fin 4) : (vectorIndex (.inl i) : ℕ) = i := by
  rfl

/-- A negative standard coordinate has the complementary index in the natural block. -/
@[simp]
public theorem vectorIndex_inr_val (i : Fin 4) : (vectorIndex (.inr i) : ℕ) = 7 - i := by
  rfl

/-- Distinct standard vector coordinates have distinct positions in the tripled table. -/
public theorem vectorIndex_injective : Function.Injective vectorIndex := by
  intro a b
  unfold vectorIndex
  rcases a with a | a <;> rcases b with b | b
  all_goals fin_cases a <;> fin_cases b <;> decide +kernel

/-- Every standard vector coordinate lands in the natural summand of the tripled table. -/
private theorem d4TripledSummand_vectorIndex_aux (a : Fin 4 ⊕ Fin 4) :
    d4TripledSummand (vectorIndex a) = 0 := by
  rcases a with i | i <;> fin_cases i <;> decide +kernel

@[simp]
public theorem d4TripledSummand_vectorIndex (a : Fin 4 ⊕ Fin 4) :
    d4TripledSummand (vectorIndex a) = 0 :=
  d4TripledSummand_vectorIndex_aux a

private theorem range_vectorIndex_aux :
    Set.range vectorIndex = {a : Fin 24 | d4TripledSummand a = 0} := by
  ext a
  fin_cases a <;> decide +kernel +revert

/-- The standard vector coordinates exhaust exactly the natural block of the tripled table. -/
public theorem range_vectorIndex :
    Set.range vectorIndex = {a : Fin 24 | d4TripledSummand a = 0} :=
  range_vectorIndex_aux

/-- The sign change which makes the standard orthogonal basis agree with the unsigned tripled
minuscule basis. It is `1` on the positive coordinates and alternates on the negative ones. -/
@[expose]
public def vectorBasisSign : Fin 4 ⊕ Fin 4 → ℤ
  | .inl _ => 1
  | .inr i => (-1) ^ (i.val + 1)

/-- The vector-basis sign is trivial on the positive coordinates. -/
@[simp]
public theorem vectorBasisSign_inl (i : Fin 4) : vectorBasisSign (.inl i) = 1 :=
  rfl

/-- The vector-basis sign alternates on the negative coordinates. -/
@[simp]
public theorem vectorBasisSign_inr (i : Fin 4) :
    vectorBasisSign (.inr i) = (-1) ^ (i.val + 1) :=
  rfl

/-- Every vector-basis sign is its own inverse. -/
@[simp]
public theorem vectorBasisSign_mul_self (a : Fin 4 ⊕ Fin 4) :
    vectorBasisSign a * vectorBasisSign a = 1 := by
  unfold vectorBasisSign
  rcases a with i | i
  · simp
  · fin_cases i <;> decide

/-! ## Chevalley-generator comparison -/

private theorem vectorIndex_eq_d4TripledReflection_iff
    (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    vectorIndex a = d4TripledReflection i (vectorIndex b) ↔
      d4TripledWeight (vectorIndex a) =
        d4TripledWeight (vectorIndex b) -
          d4TripledWeight (vectorIndex b) i • CartanMatrix.D 4 i := by
  rw [← d4TripledWeight_reflection]
  exact (Function.Injective.eq_iff d4TripledWeight_injective).symm

private theorem raisingMatrix_vectorIndex_inl_inl (i a b : Fin 4) :
    raisingMatrix i (vectorIndex (.inl a)) (vectorIndex (.inl b)) =
      TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i (.inl a) (.inl b) := by
  rw [D4Tripled.raisingMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, d4TripledWeight, CartanMatrix.D_four, Matrix.vecHead, Matrix.vecTail,
      Matrix.single_apply, Fin.ext_iff]

private theorem raisingMatrix_vectorIndex_inl_inr (i a b : Fin 4) :
    raisingMatrix i (vectorIndex (.inl a)) (vectorIndex (.inr b)) * vectorBasisSign (.inr b) =
      TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i (.inl a) (.inr b) := by
  rw [D4Tripled.raisingMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, vectorBasisSign, d4TripledWeight, CartanMatrix.D_four, Matrix.vecHead,
      Matrix.vecTail, Matrix.single_apply, Fin.ext_iff]

private theorem raisingMatrix_vectorIndex_inr_inl (i a b : Fin 4) :
    raisingMatrix i (vectorIndex (.inr a)) (vectorIndex (.inl b)) =
      vectorBasisSign (.inr a) *
        TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i (.inr a) (.inl b) := by
  rw [D4Tripled.raisingMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, vectorBasisSign, d4TripledWeight, CartanMatrix.D_four, Matrix.vecHead,
      Matrix.vecTail]

private theorem raisingMatrix_vectorIndex_inr_inr (i a b : Fin 4) :
    raisingMatrix i (vectorIndex (.inr a)) (vectorIndex (.inr b)) *
        vectorBasisSign (.inr b) =
      vectorBasisSign (.inr a) *
        TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i (.inr a) (.inr b) := by
  rw [D4Tripled.raisingMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, vectorBasisSign, d4TripledWeight, CartanMatrix.D_four, Matrix.vecHead,
      Matrix.vecTail, Matrix.single_apply, Fin.ext_iff]

private theorem raisingMatrix_vectorIndex_aux (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    raisingMatrix i (vectorIndex a) (vectorIndex b) * vectorBasisSign b =
      vectorBasisSign a * TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i a b := by
  rcases a with a | a <;> rcases b with b | b
  · simpa only [vectorBasisSign_inl, mul_one, one_mul] using
      raisingMatrix_vectorIndex_inl_inl i a b
  · simpa only [vectorBasisSign_inl, one_mul] using
      raisingMatrix_vectorIndex_inl_inr i a b
  · simpa only [vectorBasisSign_inl, mul_one] using
      raisingMatrix_vectorIndex_inr_inl i a b
  · exact raisingMatrix_vectorIndex_inr_inr i a b

/-- The natural block of a tripled raising matrix is the standard vector raising matrix after the
alternating basis normalization. This is the coefficient form of `B e = e A`. -/
public theorem raisingMatrix_vectorIndex (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    raisingMatrix i (vectorIndex a) (vectorIndex b) * vectorBasisSign b =
      vectorBasisSign a * TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i a b :=
  raisingMatrix_vectorIndex_aux i a b

private theorem loweringMatrix_vectorIndex_inl_inl (i a b : Fin 4) :
    loweringMatrix i (vectorIndex (.inl a)) (vectorIndex (.inl b)) =
      TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i (.inl a) (.inl b) := by
  rw [D4Tripled.loweringMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, d4TripledWeight, CartanMatrix.D_four, Matrix.vecHead, Matrix.vecTail,
      Matrix.single_apply, Fin.ext_iff]

private theorem loweringMatrix_vectorIndex_inl_inr (i a b : Fin 4) :
    loweringMatrix i (vectorIndex (.inl a)) (vectorIndex (.inr b)) * vectorBasisSign (.inr b) =
      TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i (.inl a) (.inr b) := by
  rw [D4Tripled.loweringMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, vectorBasisSign, d4TripledWeight, CartanMatrix.D_four, Matrix.vecHead,
      Matrix.vecTail]

private theorem loweringMatrix_vectorIndex_inr_inl (i a b : Fin 4) :
    loweringMatrix i (vectorIndex (.inr a)) (vectorIndex (.inl b)) =
      vectorBasisSign (.inr a) *
        TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i (.inr a) (.inl b) := by
  rw [D4Tripled.loweringMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, vectorBasisSign, d4TripledWeight, CartanMatrix.D_four, Matrix.vecHead,
      Matrix.vecTail, Matrix.single_apply, Fin.ext_iff]

private theorem loweringMatrix_vectorIndex_inr_inr (i a b : Fin 4) :
    loweringMatrix i (vectorIndex (.inr a)) (vectorIndex (.inr b)) *
        vectorBasisSign (.inr b) =
      vectorBasisSign (.inr a) *
        TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i (.inr a) (.inr b) := by
  rw [D4Tripled.loweringMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, vectorBasisSign, d4TripledWeight, CartanMatrix.D_four, Matrix.vecHead,
      Matrix.vecTail, Matrix.single_apply, Fin.ext_iff]

private theorem loweringMatrix_vectorIndex_aux (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    loweringMatrix i (vectorIndex a) (vectorIndex b) * vectorBasisSign b =
      vectorBasisSign a * TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i a b := by
  rcases a with a | a <;> rcases b with b | b
  · simpa only [vectorBasisSign_inl, mul_one, one_mul] using
      loweringMatrix_vectorIndex_inl_inl i a b
  · simpa only [vectorBasisSign_inl, one_mul] using
      loweringMatrix_vectorIndex_inl_inr i a b
  · simpa only [vectorBasisSign_inl, mul_one] using
      loweringMatrix_vectorIndex_inr_inl i a b
  · exact loweringMatrix_vectorIndex_inr_inr i a b

/-- The natural block of a tripled lowering matrix is the standard vector lowering matrix after
the same alternating basis normalization. -/
public theorem loweringMatrix_vectorIndex (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    loweringMatrix i (vectorIndex a) (vectorIndex b) * vectorBasisSign b =
      vectorBasisSign a * TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i a b :=
  loweringMatrix_vectorIndex_aux i a b

private theorem cartanGeneratorMatrix_vectorIndex_aux
    (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    cartanGeneratorMatrix i (vectorIndex a) (vectorIndex b) * vectorBasisSign b =
      vectorBasisSign a *
        ((TypeDStd.cartanGenerator (K := ℤ) 4 (by omega) i :
          LieAlgebra.Orthogonal.typeD (Fin 4) ℤ) :
            Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) a b := by
  rcases a with a | a <;> rcases b with b | b
  all_goals fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [D4Tripled.cartanGeneratorMatrix_apply, TypeDStd.val_cartanGenerator,
      vectorIndex, vectorBasisSign, d4TripledWeight]

/-- The natural block of a tripled Cartan-generator matrix is the standard vector Cartan matrix
after the alternating basis normalization. -/
public theorem cartanGeneratorMatrix_vectorIndex (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    cartanGeneratorMatrix i (vectorIndex a) (vectorIndex b) * vectorBasisSign b =
      vectorBasisSign a *
        ((TypeDStd.cartanGenerator (K := ℤ) 4 (by omega) i :
          LieAlgebra.Orthogonal.typeD (Fin 4) ℤ) :
            Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) a b :=
  cartanGeneratorMatrix_vectorIndex_aux i a b

end TauCeti.D4Tripled
