/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SumRootGenerators
import TauCeti.Algebra.Lie.GeneralLinear.RootSpace

/-!
# Root-space coordinates for the split odd orthogonal Lie algebra

The standard coordinates of the split type-B module have weights `0`, `εᵢ`, and `-εᵢ`.
An ambient matrix entry therefore has weight equal to its row weight minus its column weight.
This file characterizes generalized root-space membership by those entry weights and locates
all five standard root-generator families in their root spaces. These computations are the
coordinate input for classifying the roots and matching them to the abstract type-B root datum.

Generalized root spaces are honest simultaneous eigenspaces over a reduced ring. Over a domain,
a root vector is supported exactly on entries of the requested weight. Neither statement
requires characteristic zero or invertibility of two. Root-generator membership holds over any
commutative ring; the assertions do not claim that the displayed generators exhaust each space.

The diagonal-operator argument follows the existing type-D construction in
`TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Space`, reusing the ambient diagonal action from
`TauCeti.Algebra.Lie.GeneralLinear.RootSpace`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8, 12.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-- The coordinate weight in the split odd orthogonal module: zero in the middle, followed by
`εᵢ` and `-εᵢ` on the paired isotropic summands. -/
noncomputable def typeBCoordinateWeight (a : Unit ⊕ ι ⊕ ι) :
    Module.Dual K (typeBDiagonalCartan K ι) :=
  match a with
  | .inl _ => 0
  | .inr (.inl i) => typeBEpsilon i
  | .inr (.inr i) => -typeBEpsilon i

/-- The middle coordinate has zero weight. -/
@[simp] theorem typeBCoordinateWeight_inl (i : Unit) :
    typeBCoordinateWeight (K := K) (ι := ι) (.inl i) = 0 := (rfl)

/-- The first isotropic summand has coordinate weights `εᵢ`. -/
@[simp] theorem typeBCoordinateWeight_inr_inl (i : ι) :
    typeBCoordinateWeight (K := K) (.inr (.inl i)) = typeBEpsilon i := (rfl)

/-- The second isotropic summand has coordinate weights `-εᵢ`. -/
@[simp] theorem typeBCoordinateWeight_inr_inr (i : ι) :
    typeBCoordinateWeight (K := K) (.inr (.inr i)) = -typeBEpsilon i := (rfl)

/-- Coordinate weights evaluate as the corresponding diagonal entries. -/
@[simp] theorem typeBCoordinateWeight_apply (a : Unit ⊕ ι ⊕ ι)
    (A : typeBDiagonalCartan K ι) :
    typeBCoordinateWeight a A =
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a a := by
  obtain ⟨d, hd⟩ := mem_typeBDiagonalCartan_iff.mp A.property
  rcases a with a | (a | a) <;>
    simp [typeBCoordinateWeight, typeBEpsilon_apply, hd]

/-- The weight of a matrix entry is its row weight minus its column weight. -/
noncomputable def typeBMatrixWeight (a b : Unit ⊕ ι ⊕ ι) :
    Module.Dual K (typeBDiagonalCartan K ι) :=
  typeBCoordinateWeight a - typeBCoordinateWeight b

/-- The defining equation of a matrix-entry weight. -/
theorem typeBMatrixWeight_def (a b : Unit ⊕ ι ⊕ ι) :
    typeBMatrixWeight (K := K) a b = typeBCoordinateWeight a - typeBCoordinateWeight b := (rfl)

/-- Matrix-entry weights evaluate as differences of diagonal entries. -/
@[simp] theorem typeBMatrixWeight_apply (a b : Unit ⊕ ι ⊕ ι)
    (A : typeBDiagonalCartan K ι) :
    typeBMatrixWeight a b A =
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a a -
        (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) b b := by
  simp [typeBMatrixWeight]

/-- Diagonal entries have zero weight. -/
@[simp] theorem typeBMatrixWeight_self (a : Unit ⊕ ι ⊕ ι) :
    typeBMatrixWeight (K := K) a a = 0 := by
  simp [typeBMatrixWeight]

/-- The adjoint action of an element of the split diagonal Cartan is diagonal in the ambient
matrix-unit basis. -/
theorem toEnd_typeBDiagonalCartan_matrix_eq_toLin_diagonal (A : typeBDiagonalCartan K ι) :
    LieModule.toEnd K (typeBDiagonalCartan K ι) (Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) A =
      Matrix.toLin (Matrix.stdBasis K (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι))
        (Matrix.stdBasis K (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι))
        (Matrix.diagonal fun p : (Unit ⊕ ι ⊕ ι) × (Unit ⊕ ι ⊕ ι) =>
          typeBMatrixWeight p.1 p.2 A) := by
  obtain ⟨d, hd⟩ := mem_typeBDiagonalCartan_iff.mp A.property
  let D : diagonalCartan K (Unit ⊕ ι ⊕ ι) :=
    ⟨typeBDiagonalMatrix d, typeBDiagonalMatrix_mem_diagonalCartan d⟩
  -- Both restrictions act by the same ambient commutator; identify the acting endomorphism.
  have h : LieModule.toEnd K (typeBDiagonalCartan K ι)
      (Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) A =
      LieModule.toEnd K (diagonalCartan K (Unit ⊕ ι ⊕ ι))
        (Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) D := by
    ext X a b
    simp only [LieModule.toEnd_apply_apply, LieSubalgebra.coe_bracket_of_module]
    rw [hd]
  rw [h, toEnd_diagonalCartan_eq_toLin_diagonal]
  congr 2
  funext p
  rw [typeBMatrixWeight_apply, hd]

/-- Over a reduced ring, the root spaces for the split diagonal Cartan are honest simultaneous
eigenspaces rather than merely generalized eigenspaces. -/
theorem rootSpace_typeBDiagonalCartan_eq_weightSpace
    [IsReduced K]
    (χ : Module.Dual K (typeBDiagonalCartan K ι)) :
    LieAlgebra.rootSpace (typeBDiagonalCartan K ι) χ =
      LieModule.weightSpace (LieAlgebra.Orthogonal.typeB ι K)
        (χ : typeBDiagonalCartan K ι → K) := by
  refine le_antisymm (fun X hX => ?_) (LieModule.weightSpace_le_genWeightSpace _ _)
  rw [LieModule.mem_weightSpace]
  intro A
  let inc := ((LieAlgebra.Orthogonal.typeB ι K).incl').restrictLie
    (typeBDiagonalCartan K ι)
  have hambient : (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) ∈
      LieModule.genWeightSpace (Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) χ := by
    exact LieModule.map_genWeightSpace_le inc ⟨X, hX, rfl⟩
  have hA : (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) ∈ Module.End.maxGenEigenspace
      (LieModule.toEnd K (typeBDiagonalCartan K ι)
        (Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) A) (χ A) := by
    have := LieModule.genWeightSpace_le_genWeightSpaceOf
      (Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) A _ hambient
    rwa [LieModule.mem_genWeightSpaceOf, ← Module.End.mem_maxGenEigenspace] at this
  rw [toEnd_typeBDiagonalCartan_matrix_eq_toLin_diagonal,
    maxGenEigenspace_toLin_diagonal_eq_eigenspace_of_isReduced,
    Module.End.mem_eigenspace_iff, ← toEnd_typeBDiagonalCartan_matrix_eq_toLin_diagonal,
    LieModule.toEnd_apply_apply] at hA
  exact Subtype.ext hA

/-- The diagonal Cartan acts on each ambient matrix entry through its signed coordinate-difference
weight. The matrix need not itself lie in the type-`B` subalgebra. -/
@[simp]
theorem typeBDiagonalCartan_lie_apply (A : typeBDiagonalCartan K ι)
    (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (a b : Unit ⊕ ι ⊕ ι) :
    ⁅(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K),
        X⁆ a b = typeBMatrixWeight a b A * X a b := by
  have hA : (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) ∈ diagonalCartan K (Unit ⊕ ι ⊕ ι) := by
    rw [mem_diagonalCartan_iff_isDiag]
    obtain ⟨d, hd⟩ := mem_typeBDiagonalCartan_iff.mp A.property
    rw [hd]
    exact mem_diagonalCartan_iff_isDiag.mp (typeBDiagonalMatrix_mem_diagonalCartan d)
  rw [lie_apply_of_mem_diagonalCartan hA, typeBMatrixWeight_apply]

/-- A type-`B` matrix supported on entries of weight `χ` belongs to the `χ` root space. -/
theorem mem_rootSpace_typeBDiagonalCartan_of_forall
    {χ : Module.Dual K (typeBDiagonalCartan K ι)}
    {X : LieAlgebra.Orthogonal.typeB ι K}
    (h : ∀ a b, typeBMatrixWeight a b ≠ χ →
      (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a b = 0) :
    X ∈ LieAlgebra.rootSpace (typeBDiagonalCartan K ι) χ := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  apply Subtype.ext
  ext a b
  rw [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul]
  simp only [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket]
  rw [typeBDiagonalCartan_lie_apply]
  by_cases hab : typeBMatrixWeight a b = χ
  · rw [congrArg (fun f : Module.Dual K (typeBDiagonalCartan K ι) => f A) hab]
  · rw [h a b hab, mul_zero, mul_zero]

/-- Over a domain, a matrix in the split type-`B` Lie algebra belongs to the root space of `χ`
exactly when all entries whose signed coordinate difference is not `χ` vanish. -/
@[simp]
theorem mem_rootSpace_typeBDiagonalCartan_iff
    [IsDomain K]
    (χ : Module.Dual K (typeBDiagonalCartan K ι))
    (X : LieAlgebra.Orthogonal.typeB ι K) :
    X ∈ LieAlgebra.rootSpace (typeBDiagonalCartan K ι) χ ↔
      ∀ a b, typeBMatrixWeight a b ≠ χ →
        (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a b = 0 := by
  refine ⟨fun hX a b hab => ?_, mem_rootSpace_typeBDiagonalCartan_of_forall⟩
  obtain ⟨k, hk⟩ : ∃ k, typeBMatrixWeight a b
      (typeBDiagonalCartanBasis (K := K) (ι := ι) k) ≠
        χ (typeBDiagonalCartanBasis (K := K) (ι := ι) k) := by
    by_contra hcon
    push Not at hcon
    exact hab ((typeBDiagonalCartanBasis (K := K) (ι := ι)).ext hcon)
  rw [rootSpace_typeBDiagonalCartan_eq_weightSpace, LieModule.mem_weightSpace] at hX
  let A := typeBDiagonalCartanBasis (K := K) (ι := ι) k
  have hEq := congrArg Subtype.val (hX A)
  have hentry := congrFun (congrFun hEq a) b
  rw [SetLike.val_smul, Matrix.smul_apply] at hentry
  simp only [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket] at hentry
  rw [typeBDiagonalCartan_lie_apply] at hentry
  exact (mul_eq_zero.mp (by linear_combination hentry)).resolve_left (sub_ne_zero.mpr hk)

/-- The standard positive short-root generator belongs to its coordinate root space. -/
theorem typeBShortRootGenerator_mem_rootSpace (i : ι) :
    typeBShortRootGenerator (K := K) i ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι) (typeBEpsilon i) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_shortRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

/-- The standard negative short-root generator belongs to its coordinate root space. -/
theorem typeBShortNegativeRootGenerator_mem_rootSpace (i : ι) :
    typeBShortNegativeRootGenerator (K := K) i ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι) (-typeBEpsilon i) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_shortNegativeRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

/-- The standard difference-root generator belongs to its coordinate root space. -/
theorem typeBDifferenceRootGenerator_mem_rootSpace (i : ι) (j : ι) (hij : i ≠ j) :
    typeBDifferenceRootGenerator (K := K) i j hij ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι)
        (typeBEpsilon (K := K) i - typeBEpsilon (K := K) j) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_differenceRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

/-- The standard positive sum-root generator belongs to its coordinate root space. -/
theorem typeBSumRootGenerator_mem_rootSpace (i : ι) (j : ι) :
    typeBSumRootGenerator (K := K) i j ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι)
        (typeBEpsilon (K := K) i + typeBEpsilon (K := K) j) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_sumRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

/-- The standard negative sum-root generator belongs to its coordinate root space. -/
theorem typeBSumNegativeRootGenerator_mem_rootSpace (i : ι) (j : ι) :
    typeBSumNegativeRootGenerator (K := K) i j ∈
      LieAlgebra.rootSpace (typeBDiagonalCartan K ι)
        (-(typeBEpsilon (K := K) i + typeBEpsilon (K := K) j)) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K)).surjective A
  simp only [LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply]
  rw [typeBDiagonalMatrix_lie_sumNegativeRootGenerator]
  simp [coe_typeBDiagonalEquiv_apply]

end TauCeti
