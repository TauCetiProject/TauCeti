/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.BlockIntertwiners
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
the sign `(-1)^(i+1)` on coordinate `.inr i` reconciles these conventions; in standard coordinate
order `i = 0, …, 3`, these signs are `-1, 1, -1, 1`.

The final entrywise and matrix equations are the intertwining identities for the positive,
negative, and Cartan Chevalley generators. They fix both the Bourbaki node numbering and every
basis sign.

## Main declarations

* `TauCeti.D4Tripled.vectorIndex`: the inclusion of the standard coordinates `Fin 4 ⊕ Fin 4`
  into the natural block of the tripled table.
* `TauCeti.D4Tripled.vectorBasisSign`: the basis normalization on the standard coordinates.
* `TauCeti.D4Tripled.raisingMatrix_vectorIndex`,
  `TauCeti.D4Tripled.loweringMatrix_vectorIndex`, and
  `TauCeti.D4Tripled.cartanGeneratorMatrix_vectorIndex`: the signed generator comparisons.
* `TauCeti.D4Tripled.vectorBlockEquiv`: the signed linear equivalence from the standard
  vector module to the natural block.
* `TauCeti.D4Tripled.vectorBlockEquiv_raising_mulVec` and its lowering and Cartan analogues:
  the corresponding generator-action intertwiners.
* `TauCeti.D4Tripled.raisingMatrix_vectorIndex_mul_diagonal` and its lowering and Cartan
  counterparts: the same comparisons as matrix intertwining identities.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

/-! ## Coordinates and signs -/

/-- The standard vector coordinates included into the natural block of the tripled weight table. -/
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
@[simp]
public theorem d4TripledSummand_vectorIndex (a : Fin 4 ⊕ Fin 4) :
    d4TripledSummand (vectorIndex a) = 0 := by
  rw [d4TripledSummand_eq_zero_iff]
  rcases a with i | i <;> fin_cases i <;> decide +kernel

/-- The standard vector coordinates exhaust exactly the natural block of the tripled table. -/
public theorem range_vectorIndex :
    Set.range vectorIndex = {a : Fin 24 | d4TripledSummand a = 0} := by
  ext a
  rw [Set.mem_range, Set.mem_ofPred_eq, d4TripledSummand_eq_zero_iff]
  fin_cases a <;> decide +kernel +revert

/-- The sign change which makes the standard orthogonal basis agree with the unsigned tripled
minuscule basis. It is `1` on the positive coordinates and alternates on the negative ones. -/
public def vectorBasisSign : Fin 4 ⊕ Fin 4 → ℤ
  | .inl _ => 1
  | .inr i => (-1) ^ (i.val + 1)

/-- The vector-basis sign is trivial on the positive coordinates. -/
@[simp]
public theorem vectorBasisSign_inl (i : Fin 4) : vectorBasisSign (.inl i) = 1 :=
  vectorBasisSign.eq_1 i

/-- The vector-basis sign alternates on the negative coordinates. -/
@[simp]
public theorem vectorBasisSign_inr (i : Fin 4) :
    vectorBasisSign (.inr i) = (-1) ^ (i.val + 1) :=
  vectorBasisSign.eq_2 i

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

private theorem piSingle_zero_one_eq_vector :
    (Pi.single 0 1 : Fin 4 → ℤ) = ![1, 0, 0, 0] := by
  decide

/-- The natural block of the tripled table consists of the standard vector weights: the weight at
a coordinate is the corresponding entry of the standard type-`D₄` Cartan diagonal. -/
public theorem d4TripledWeight_vectorIndex (a : Fin 4 ⊕ Fin 4) (i : Fin 4) :
    d4TripledWeight (vectorIndex a) i =
      typeDDiagonalValue (typeDSimpleRoot 4 (by omega) i) a := by
  rcases a with a | a <;> fin_cases a <;> fin_cases i <;>
    simp [vectorIndex, typeDSimpleRoot_of_add_one_lt, typeDSimpleRoot_of_not_add_one_lt]

/-- The natural block of a tripled raising matrix is the standard vector raising matrix after the
alternating basis normalization. With `D` the diagonal matrix of `vectorBasisSign`, the restricted
tripled matrix `B` and standard matrix `A` satisfy `B * D = D * A` entrywise. -/
public theorem raisingMatrix_vectorIndex (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    raisingMatrix i (vectorIndex a) (vectorIndex b) * vectorBasisSign b =
      vectorBasisSign a * TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i a b := by
  rw [D4Tripled.raisingMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  rcases a with a | a <;> rcases b with b | b
  all_goals fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, vectorBasisSign, piSingle_zero_one_eq_vector,
      CartanMatrix.D_four, Matrix.vecHead, Matrix.vecTail, Matrix.single_apply, Fin.ext_iff]

/-- The natural block of a tripled lowering matrix is the standard vector lowering matrix after
the same alternating basis normalization. -/
public theorem loweringMatrix_vectorIndex (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    loweringMatrix i (vectorIndex a) (vectorIndex b) * vectorBasisSign b =
      vectorBasisSign a * TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i a b := by
  rw [D4Tripled.loweringMatrix_apply]
  simp only [vectorIndex_eq_d4TripledReflection_iff]
  rcases a with a | a <;> rcases b with b | b
  all_goals fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [vectorIndex, vectorBasisSign, piSingle_zero_one_eq_vector,
      CartanMatrix.D_four, Matrix.vecHead, Matrix.vecTail, Matrix.single_apply, Fin.ext_iff]

/-- The natural block of a tripled Cartan-generator matrix is the standard vector Cartan matrix
after the alternating basis normalization. -/
public theorem cartanGeneratorMatrix_vectorIndex (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    cartanGeneratorMatrix i (vectorIndex a) (vectorIndex b) * vectorBasisSign b =
      vectorBasisSign a *
        ((TypeDStd.cartanGenerator (K := ℤ) 4 (by omega) i :
          LieAlgebra.Orthogonal.typeD (Fin 4) ℤ) :
            Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) a b := by
  rw [D4Tripled.cartanGeneratorMatrix_apply, TypeDStd.val_cartanGenerator,
    typeDDiagonalMatrix_apply]
  simp only [vectorIndex_injective.eq_iff]
  by_cases h : a = b
  · subst b
    simp [d4TripledWeight_vectorIndex, mul_comm]
  · simp [h]

/-- The restricted tripled raising matrix intertwines the alternating diagonal basis change with
the standard vector raising matrix. -/
public theorem raisingMatrix_vectorIndex_mul_diagonal (i : Fin 4) :
    (raisingMatrix i).submatrix vectorIndex vectorIndex * Matrix.diagonal vectorBasisSign =
      Matrix.diagonal vectorBasisSign * TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i := by
  ext a b
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply] using
    raisingMatrix_vectorIndex i a b

/-- The restricted tripled lowering matrix intertwines the alternating diagonal basis change with
the standard vector lowering matrix. -/
public theorem loweringMatrix_vectorIndex_mul_diagonal (i : Fin 4) :
    (loweringMatrix i).submatrix vectorIndex vectorIndex * Matrix.diagonal vectorBasisSign =
      Matrix.diagonal vectorBasisSign * TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i := by
  ext a b
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply] using
    loweringMatrix_vectorIndex i a b

/-- The restricted tripled Cartan-generator matrix intertwines the alternating diagonal basis
change with the standard vector Cartan matrix. -/
public theorem cartanGeneratorMatrix_vectorIndex_mul_diagonal (i : Fin 4) :
    (cartanGeneratorMatrix i).submatrix vectorIndex vectorIndex *
        Matrix.diagonal vectorBasisSign =
      Matrix.diagonal vectorBasisSign *
        ((TypeDStd.cartanGenerator (K := ℤ) 4 (by omega) i :
          LieAlgebra.Orthogonal.typeD (Fin 4) ℤ) :
            Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) := by
  ext a b
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply] using
    cartanGeneratorMatrix_vectorIndex i a b

public section

/-! ## The signed vector-block equivalence -/

/-- The standard split vector coordinates, identified with the natural block of the tripled
type-`D₄` table. -/
noncomputable def vectorBlockIndexEquiv : (Fin 4 ⊕ Fin 4) ≃ Block 0 :=
  Equiv.ofBijective
    (fun a => ⟨vectorIndex a, d4TripledSummand_vectorIndex a⟩)
    ⟨fun _ _ h => vectorIndex_injective (congrArg Subtype.val h), fun a => by
      have ha : a.1 ∈ Set.range vectorIndex := by
        rw [range_vectorIndex]
        exact a.2
      obtain ⟨x, hx⟩ := ha
      exact ⟨x, Subtype.ext hx⟩⟩

/-- The underlying table coordinate of `vectorBlockIndexEquiv` is `vectorIndex`. -/
@[simp]
theorem coe_vectorBlockIndexEquiv (a : Fin 4 ⊕ Fin 4) :
    (vectorBlockIndexEquiv a).1 = vectorIndex a := by
  exact congrArg Subtype.val (Equiv.ofBijective_apply _ _ a)

private noncomputable def vectorSignEquiv :
    (Fin 4 ⊕ Fin 4 → ℚ) ≃ₗ[ℚ] (Fin 4 ⊕ Fin 4 → ℚ) where
  toFun v a := vectorBasisSign a * v a
  invFun v a := vectorBasisSign a * v a
  left_inv v := by
    funext a
    dsimp
    rw [← mul_assoc, ← Int.cast_mul, vectorBasisSign_mul_self]
    simp
  right_inv v := by
    funext a
    dsimp
    rw [← mul_assoc, ← Int.cast_mul, vectorBasisSign_mul_self]
    simp
  map_add' x y := by
    funext a
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The standard split vector module, written in the signed coordinates of the natural block of
the tripled type-`D₄` table. -/
noncomputable def vectorBlockEquiv :
    (Fin 4 ⊕ Fin 4 → ℚ) ≃ₗ[ℚ] (Block 0 → ℚ) :=
  vectorSignEquiv.trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) vectorBlockIndexEquiv)

/-- Evaluation of the vector-block equivalence on a standard coordinate. -/
@[simp]
theorem vectorBlockEquiv_apply_apply (v : Fin 4 ⊕ Fin 4 → ℚ)
    (a : Fin 4 ⊕ Fin 4) :
    vectorBlockEquiv v (vectorBlockIndexEquiv a) = vectorBasisSign a * v a := by
  simp [vectorBlockEquiv, vectorSignEquiv]

private theorem cast_typeDStd_raisingMatrix (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    (TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i a b : ℚ) =
      TypeDStd.raisingMatrix (K := ℚ) 4 (by omega) i a b := by
  by_cases hi : (i : ℕ) + 1 < 4
  · rw [TypeDStd.raisingMatrix_of_chain 4 (by omega) hi,
      TypeDStd.raisingMatrix_of_chain 4 (by omega) hi]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.fromBlocks, Matrix.single_apply]
  · rw [TypeDStd.raisingMatrix_of_fork 4 (by omega) hi,
      TypeDStd.raisingMatrix_of_fork 4 (by omega) hi]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.fromBlocks, Matrix.single_apply]

private theorem cast_typeDStd_loweringMatrix (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    (TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i a b : ℚ) =
      TypeDStd.loweringMatrix (K := ℚ) 4 (by omega) i a b := by
  by_cases hi : (i : ℕ) + 1 < 4
  · rw [TypeDStd.loweringMatrix_of_chain 4 (by omega) hi,
      TypeDStd.loweringMatrix_of_chain 4 (by omega) hi]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.fromBlocks, Matrix.single_apply]
  · rw [TypeDStd.loweringMatrix_of_fork 4 (by omega) hi,
      TypeDStd.loweringMatrix_of_fork 4 (by omega) hi]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.fromBlocks, Matrix.single_apply]

private theorem cast_typeDStd_cartanGenerator (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    (((TypeDStd.cartanGenerator (K := ℤ) 4 (by omega) i :
        LieAlgebra.Orthogonal.typeD (Fin 4) ℤ) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) a b : ℚ) =
      ((TypeDStd.cartanGenerator (K := ℚ) 4 (by omega) i :
        LieAlgebra.Orthogonal.typeD (Fin 4) ℚ) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℚ) a b := by
  rw [TypeDStd.val_cartanGenerator, TypeDStd.val_cartanGenerator]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [typeDDiagonalMatrix_apply]

private theorem vectorBlockEquiv_mulVec
    (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℚ)
    (B : Matrix (Block 0) (Block 0) ℚ)
    (h : ∀ a b, (vectorBasisSign a : ℚ) * A a b =
      B (vectorBlockIndexEquiv a) (vectorBlockIndexEquiv b) * vectorBasisSign b)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    vectorBlockEquiv (A *ᵥ v) = B *ᵥ vectorBlockEquiv v := by
  funext a
  obtain ⟨a, rfl⟩ := vectorBlockIndexEquiv.surjective a
  simp only [vectorBlockEquiv_apply_apply, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv vectorBlockIndexEquiv (fun b =>
    (vectorBasisSign a : ℚ) * (A a b * v b))
    (fun b => B (vectorBlockIndexEquiv a) b * vectorBlockEquiv v b) ?_
  intro b
  rw [vectorBlockEquiv_apply_apply]
  calc
    (vectorBasisSign a : ℚ) * (A a b * v b) =
        ((vectorBasisSign a : ℚ) * A a b) * v b := by ring
    _ = (B (vectorBlockIndexEquiv a) (vectorBlockIndexEquiv b) *
          (vectorBasisSign b : ℚ)) * v b := by rw [h]
    _ = _ := by ring

/-- The signed vector-block equivalence intertwines every positive simple-root operator with the
raising matrix on the natural block. -/
@[simp]
theorem vectorBlockEquiv_raising_mulVec (i : Fin 4) (v : Fin 4 ⊕ Fin 4 → ℚ) :
    vectorBlockEquiv (TypeDStd.raisingMatrix (K := ℚ) 4 (by omega) i *ᵥ v) =
      blockRaisingMatrix ℚ 0 i *ᵥ vectorBlockEquiv v := by
  apply vectorBlockEquiv_mulVec
  intro a b
  simp only [blockRaisingMatrix_apply, coe_vectorBlockIndexEquiv]
  have h := congrArg (Int.castRingHom ℚ) (raisingMatrix_vectorIndex i a b)
  simp only [map_mul] at h
  -- The public comparison is integral, so expose its entrywise cast before rewriting over ℚ.
  change (raisingMatrix i (vectorIndex a) (vectorIndex b) : ℚ) *
      (vectorBasisSign b : ℚ) =
    (vectorBasisSign a : ℚ) *
      (TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i a b : ℚ) at h
  rw [cast_typeDStd_raisingMatrix] at h
  exact h.symm

/-- The signed vector-block equivalence intertwines every negative simple-root operator with the
lowering matrix on the natural block. -/
@[simp]
theorem vectorBlockEquiv_lowering_mulVec (i : Fin 4) (v : Fin 4 ⊕ Fin 4 → ℚ) :
    vectorBlockEquiv (TypeDStd.loweringMatrix (K := ℚ) 4 (by omega) i *ᵥ v) =
      blockLoweringMatrix ℚ 0 i *ᵥ vectorBlockEquiv v := by
  apply vectorBlockEquiv_mulVec
  intro a b
  simp only [blockLoweringMatrix_apply, coe_vectorBlockIndexEquiv]
  have h := congrArg (Int.castRingHom ℚ) (loweringMatrix_vectorIndex i a b)
  simp only [map_mul] at h
  -- The public comparison is integral, so expose its entrywise cast before rewriting over ℚ.
  change (loweringMatrix i (vectorIndex a) (vectorIndex b) : ℚ) *
      (vectorBasisSign b : ℚ) =
    (vectorBasisSign a : ℚ) *
      (TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i a b : ℚ) at h
  rw [cast_typeDStd_loweringMatrix] at h
  exact h.symm

/-- The signed vector-block equivalence intertwines every Cartan generator with the diagonal
weight matrix on the natural block. -/
@[simp]
theorem vectorBlockEquiv_cartanGenerator_mulVec (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    vectorBlockEquiv
        (typeDDiagonalMatrix (fun j =>
          (typeDSimpleRoot 4 (by omega) i j : ℚ)) *ᵥ v) =
      blockCartanGeneratorMatrix ℚ 0 i *ᵥ vectorBlockEquiv v := by
  apply vectorBlockEquiv_mulVec
  intro a b
  simp only [blockCartanGeneratorMatrix_apply, coe_vectorBlockIndexEquiv]
  have h := congrArg (Int.castRingHom ℚ) (cartanGeneratorMatrix_vectorIndex i a b)
  simp only [map_mul] at h
  -- The public comparison is integral, so expose its entrywise cast before rewriting over ℚ.
  change (cartanGeneratorMatrix i (vectorIndex a) (vectorIndex b) : ℚ) *
      (vectorBasisSign b : ℚ) =
    (vectorBasisSign a : ℚ) *
      ((((TypeDStd.cartanGenerator (K := ℤ) 4 (by omega) i :
        LieAlgebra.Orthogonal.typeD (Fin 4) ℤ) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) a b : ℚ)) at h
  rw [cast_typeDStd_cartanGenerator] at h
  rw [TypeDStd.val_cartanGenerator] at h
  exact h.symm

end

end TauCeti.D4Tripled
