/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import TauCeti.LinearAlgebra.Eigenspace.Diagonal

/-!
# Root spaces of the split even orthogonal Lie algebra

This file computes the root spaces of `LieAlgebra.Orthogonal.typeD ι K` relative to its diagonal
Cartan subalgebra. The two copies of `ι` in the hyperbolic basis have coordinate weights `εᵢ` and
`-εᵢ`. Hence a matrix entry in position `(a, b)` has weight equal to the difference of those two
signed coordinate weights.

Over a reduced ring, generalized root spaces are honest simultaneous eigenspaces because each Cartan
element acts diagonally on the ambient matrix units. This gives an entrywise support criterion
that reduces the calculation of a concrete root space to the positions having its requested signed
weight; the converse support characterization uses the stronger hypothesis that the coefficient
ring is a domain.

## Main results

* `TauCeti.rootSpace_typeDDiagonalCartan_eq_weightSpace`: generalized root spaces are honest
  simultaneous eigenspaces.
* `TauCeti.mem_rootSpace_typeDDiagonalCartan_iff`: over a domain, membership is equivalent to
  entrywise support on positions of the requested weight.

The reduced-ring diagonal-eigenspace step reuses the generic helper in
`TauCeti.LinearAlgebra.Eigenspace.Diagonal`, factored from the analogous
`TauCeti.Algebra.Lie.GeneralLinear.RootSpace` development.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8, 12.
-/

public section

namespace TauCeti

open _root_.Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-! ## Signed coordinate weights -/

/-- The weight of a hyperbolic coordinate: `εᵢ` on the first summand and `-εᵢ` on the second. -/
noncomputable def typeDCoordinateWeight (a : ι ⊕ ι) :
    Module.Dual K (typeDDiagonalCartan K ι) :=
  match a with
  | .inl i => typeDEpsilon i
  | .inr i => -typeDEpsilon i

/-- The weight of the matrix entry `(a, b)`, namely the difference of its signed coordinate
weights. -/
noncomputable def typeDMatrixWeight (a b : ι ⊕ ι) :
    Module.Dual K (typeDDiagonalCartan K ι) :=
  typeDCoordinateWeight a - typeDCoordinateWeight b

/-- The signed coordinate weight evaluates through the corresponding diagonal entry. -/
@[simp]
theorem typeDCoordinateWeight_apply (a : ι ⊕ ι) (A : typeDDiagonalCartan K ι) :
    typeDCoordinateWeight a A =
      typeDDiagonalValue ((typeDDiagonalEquiv (K := K) (ι := ι)).symm A) a := by
  cases a with
  | inl i => simp [typeDCoordinateWeight]
  | inr i => simp [typeDCoordinateWeight]

/-- The matrix-entry weight evaluates as the difference of the two signed diagonal coordinates. -/
@[simp]
theorem typeDMatrixWeight_apply (a b : ι ⊕ ι) (A : typeDDiagonalCartan K ι) :
    typeDMatrixWeight a b A =
      typeDDiagonalValue ((typeDDiagonalEquiv (K := K) (ι := ι)).symm A) a -
        typeDDiagonalValue ((typeDDiagonalEquiv (K := K) (ι := ι)).symm A) b := by
  simp [typeDMatrixWeight]

/-- The difference-root weight `εᵢ - εⱼ` on the split diagonal Cartan. -/
noncomputable def typeDWeightSub (i j : ι) : Module.Dual K (typeDDiagonalCartan K ι) :=
  typeDEpsilon i - typeDEpsilon j

/-- The sum-root weight `εᵢ + εⱼ` on the split diagonal Cartan. -/
noncomputable def typeDWeightAdd (i j : ι) : Module.Dual K (typeDDiagonalCartan K ι) :=
  typeDEpsilon i + typeDEpsilon j

/-- The difference-root weight evaluates as the difference of the corresponding diagonal entries. -/
@[simp]
theorem typeDWeightSub_apply (i j : ι) (A : typeDDiagonalCartan K ι) :
    typeDWeightSub i j A =
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i) -
        (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl j) (.inl j) := by
  simp [typeDWeightSub]

/-- The sum-root weight evaluates as the sum of the corresponding diagonal entries. -/
@[simp]
theorem typeDWeightAdd_apply (i j : ι) (A : typeDDiagonalCartan K ι) :
    typeDWeightAdd i j A =
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i) +
        (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl j) (.inl j) := by
  simp [typeDWeightAdd]

/-- A difference-root weight vanishes when its two coordinates agree. -/
@[simp]
theorem typeDWeightSub_self (i : ι) : typeDWeightSub (K := K) i i = 0 := by
  ext A
  simp [typeDWeightSub]

/-- The matrix-entry weight on a diagonal entry is the zero functional. -/
@[simp]
theorem typeDMatrixWeight_self (a : ι ⊕ ι) :
    typeDMatrixWeight (K := K) a a = 0 := by
  simp [typeDMatrixWeight]

/-- The `(inl i, inl j)` matrix-entry weight is the difference-root weight `εᵢ - εⱼ`. -/
@[simp]
theorem typeDMatrixWeight_inl_inl (i j : ι) :
    typeDMatrixWeight (K := K) (.inl i) (.inl j) = typeDWeightSub i j := by
  simp [typeDMatrixWeight, typeDCoordinateWeight, typeDWeightSub]

/-- The `(inl i, inr j)` matrix-entry weight is the sum-root weight `εᵢ + εⱼ`. -/
@[simp]
theorem typeDMatrixWeight_inl_inr (i j : ι) :
    typeDMatrixWeight (K := K) (.inl i) (.inr j) = typeDWeightAdd i j := by
  simp [typeDMatrixWeight, typeDCoordinateWeight, typeDWeightAdd]

/-- The `(inr i, inl j)` matrix-entry weight is the negative sum-root weight. -/
@[simp]
theorem typeDMatrixWeight_inr_inl (i j : ι) :
    typeDMatrixWeight (K := K) (.inr i) (.inl j) = -typeDWeightAdd i j := by
  simp [typeDMatrixWeight, typeDCoordinateWeight, typeDWeightAdd]
  abel

/-- The `(inr i, inr j)` matrix-entry weight is the reversed difference-root weight. -/
@[simp]
theorem typeDMatrixWeight_inr_inr (i j : ι) :
    typeDMatrixWeight (K := K) (.inr i) (.inr j) = typeDWeightSub j i := by
  simp [typeDMatrixWeight, typeDCoordinateWeight, typeDWeightSub]
  abel

/-! ## Honest weight spaces and entrywise support -/

/-- The adjoint action of an element of the split diagonal Cartan is diagonal in the ambient
matrix-unit basis. -/
theorem toEnd_typeDDiagonalCartan_matrix_eq_toLin_diagonal (A : typeDDiagonalCartan K ι) :
    LieModule.toEnd K (typeDDiagonalCartan K ι) (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A =
      Matrix.toLin (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι))
        (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι))
        (Matrix.diagonal fun p : (ι ⊕ ι) × (ι ⊕ ι) => typeDMatrixWeight p.1 p.2 A) := by
  refine (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι)).ext fun p => ?_
  rw [LieModule.toEnd_apply_apply, Matrix.toLin_self,
    Finset.sum_eq_single p (fun q _ hq => by rw [Matrix.diagonal_apply_ne _ hq, zero_smul])
      (by simp),
    Matrix.diagonal_apply_eq, Matrix.stdBasis_eq_single]
  ext a b
  rw [typeDMatrixWeight_apply]
  have hA := coe_typeDDiagonalEquiv_apply
    ((typeDDiagonalEquiv (K := K) (ι := ι)).symm A)
  rw [LinearEquiv.apply_symm_apply] at hA
  have hAval : A.val.val =
      typeDDiagonalMatrix ((typeDDiagonalEquiv (K := K) (ι := ι)).symm A) :=
    congrArg Subtype.val hA
  -- The bracket is evaluated in the ambient matrix representation; this explicit coercion
  -- exposes the matrix unit to `typeDDiagonalMatrix_lie_apply` below.
  change (⁅A.val.val, Matrix.single p.1 p.2 1⁆ : Matrix _ _ K) a b = _
  rw [hAval, typeDDiagonalMatrix_lie_apply, Matrix.smul_apply]
  by_cases h : p.1 = a ∧ p.2 = b
  · rcases h with ⟨rfl, rfl⟩
    simp
  · simp [h]

/-- Over a reduced ring, the root spaces for the split diagonal Cartan are honest simultaneous
eigenspaces rather than merely generalized eigenspaces. -/
theorem rootSpace_typeDDiagonalCartan_eq_weightSpace
    [IsReduced K]
    (χ : Module.Dual K (typeDDiagonalCartan K ι)) :
    LieAlgebra.rootSpace (typeDDiagonalCartan K ι) χ =
      LieModule.weightSpace (LieAlgebra.Orthogonal.typeD ι K)
        (χ : typeDDiagonalCartan K ι → K) := by
  refine le_antisymm (fun X hX => ?_) (LieModule.weightSpace_le_genWeightSpace _ _)
  rw [LieModule.mem_weightSpace]
  intro A
  let inc := ((LieAlgebra.Orthogonal.typeD ι K).incl').restrictLie
    (typeDDiagonalCartan K ι)
  have hambient : (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈
      LieModule.genWeightSpace (Matrix (ι ⊕ ι) (ι ⊕ ι) K) χ := by
    exact LieModule.map_genWeightSpace_le inc ⟨X, hX, rfl⟩
  have hA : (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈ Module.End.maxGenEigenspace
      (LieModule.toEnd K (typeDDiagonalCartan K ι)
        (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A) (χ A) := by
    have := LieModule.genWeightSpace_le_genWeightSpaceOf
      (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A _ hambient
    rwa [LieModule.mem_genWeightSpaceOf, ← Module.End.mem_maxGenEigenspace] at this
  rw [toEnd_typeDDiagonalCartan_matrix_eq_toLin_diagonal,
    maxGenEigenspace_toLin_diagonal_eq_eigenspace_of_isReduced,
    Module.End.mem_eigenspace_iff, ← toEnd_typeDDiagonalCartan_matrix_eq_toLin_diagonal,
    LieModule.toEnd_apply_apply] at hA
  exact Subtype.ext hA

/-- The diagonal Cartan acts on each ambient matrix entry through its signed coordinate-difference
weight. The matrix need not itself lie in the type-`D` subalgebra. -/
@[simp]
theorem typeDDiagonalCartan_lie_apply (A : typeDDiagonalCartan K ι)
    (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (a b : ι ⊕ ι) :
    ⁅(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K),
        X⁆ a b = typeDMatrixWeight a b A * X a b := by
  rw [← (typeDDiagonalEquiv (K := K) (ι := ι)).apply_symm_apply A,
    coe_typeDDiagonalEquiv_apply, typeDDiagonalMatrix_lie_apply, typeDMatrixWeight_apply]
  simp only [LinearEquiv.symm_apply_apply]

/-- A type-`D` matrix supported on entries of weight `χ` belongs to the `χ` root space. -/
theorem mem_rootSpace_typeDDiagonalCartan_of_forall
    {χ : Module.Dual K (typeDDiagonalCartan K ι)}
    {X : LieAlgebra.Orthogonal.typeD ι K}
    (h : ∀ a b, typeDMatrixWeight a b ≠ χ →
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0) :
    X ∈ LieAlgebra.rootSpace (typeDDiagonalCartan K ι) χ := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  apply Subtype.ext
  ext a b
  rw [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul]
  simp only [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket]
  rw [typeDDiagonalCartan_lie_apply]
  by_cases hab : typeDMatrixWeight a b = χ
  · rw [congrArg (fun f : Module.Dual K (typeDDiagonalCartan K ι) => f A) hab]
  · rw [h a b hab, mul_zero, mul_zero]

/-- Over a domain, a matrix in the split type-`D` Lie algebra belongs to the root space of `χ`
exactly when all entries whose signed coordinate difference is not `χ` vanish. -/
@[simp]
theorem mem_rootSpace_typeDDiagonalCartan_iff
    [IsDomain K]
    (χ : Module.Dual K (typeDDiagonalCartan K ι))
    (X : LieAlgebra.Orthogonal.typeD ι K) :
    X ∈ LieAlgebra.rootSpace (typeDDiagonalCartan K ι) χ ↔
      ∀ a b, typeDMatrixWeight a b ≠ χ →
        (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0 := by
  refine ⟨fun hX a b hab => ?_, mem_rootSpace_typeDDiagonalCartan_of_forall⟩
  obtain ⟨k, hk⟩ : ∃ k, typeDMatrixWeight a b
      (typeDDiagonalCartanBasis (K := K) (ι := ι) k) ≠
        χ (typeDDiagonalCartanBasis (K := K) (ι := ι) k) := by
    by_contra hcon
    push Not at hcon
    exact hab ((typeDDiagonalCartanBasis (K := K) (ι := ι)).ext hcon)
  rw [rootSpace_typeDDiagonalCartan_eq_weightSpace, LieModule.mem_weightSpace] at hX
  let A := typeDDiagonalCartanBasis (K := K) (ι := ι) k
  have hEq := congrArg Subtype.val (hX A)
  have hentry := congrFun (congrFun hEq a) b
  rw [SetLike.val_smul, Matrix.smul_apply] at hentry
  simp only [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket] at hentry
  rw [typeDDiagonalCartan_lie_apply] at hentry
  exact (mul_eq_zero.mp (by linear_combination hentry)).resolve_left (sub_ne_zero.mpr hk)

end TauCeti
