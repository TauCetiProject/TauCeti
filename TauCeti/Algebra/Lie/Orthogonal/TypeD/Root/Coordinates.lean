/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.AllGenerators
public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.LinearAlgebra.Matrix.Alternating

/-!
# Native matrix coordinates for the split even orthogonal Lie algebra

A matrix in the split even orthogonal Lie algebra has blocks `[[A, B], [C, -Aᵀ]]`,
where `B` and `C` are skew-symmetric. When doubling has trivial kernel, their diagonals vanish.
The entries of `A` and the strict upper triangles of `B` and `-C` give coordinates, without
dividing by two. The corresponding basis consists of the existing difference-root generators,
positive sum-root generators, and reversed negative sum-root generators.

The diagonal basis members are the individual hyperbolic diagonal matrices. For `ι = Fin n`
with `4 ≤ n`, the simple coroots instead span the even-sum sublattice over `ℤ`, of index two
in the full diagonal lattice.
-/

public section

namespace TauCeti.TypeDStd

variable {R ι : Type*} [CommRing R] [LinearOrder ι]

/-- The full upper-left block and the two strict upper triangles index the native matrix basis. -/
abbrev RootEntryIndex (ι : Type*) [LT ι] :=
  (ι × ι) ⊕ ({p : ι × ι // p.1 < p.2} ⊕ {p : ι × ι // p.1 < p.2})

variable [Fintype ι]

/-- Entry coordinates on the split even orthogonal Lie algebra when doubling has trivial kernel.

The negative-root coordinates are the negatives of the lower-left upper entries. For
`ι = Fin n` with `4 ≤ n`, this makes the basis member at `(n - 2, n - 1)` agree with
the numbered lowering generator at the fork. -/
def rootEntryEquiv (h2 : ∀ x : R, x + x = 0 → x = 0) :
    LieAlgebra.Orthogonal.typeD ι R ≃ₗ[R] (RootEntryIndex ι → R) where
  toFun X
    | .inl p => X.val (.inl p.1) (.inl p.2)
    | .inr (.inl p) => X.val (.inl p.val.1) (.inr p.val.2)
    | .inr (.inr p) => -X.val (.inr p.val.1) (.inl p.val.2)
  invFun a := ⟨Matrix.fromBlocks (fun i j => a (.inl (i, j)))
    (Matrix.ofStrictUpper fun p => a (.inr (.inl p)))
    (Matrix.ofStrictUpper fun p => -a (.inr (.inr p)))
    (-Matrix.transpose (fun i j => a (.inl (i, j)))),
    Matrix.fromBlocks_mem_typeD _ _ _
      (Matrix.transpose_ofStrictUpper _) (Matrix.transpose_ofStrictUpper _)⟩
  left_inv X := by
    have hB : Matrix.transpose (fun i j => X.val (.inl i) (.inr j)) =
        -(fun i j => X.val (.inl i) (.inr j) : Matrix ι ι R) := by
      ext i j
      exact LieAlgebra.Orthogonal.typeD.apply_inl_inr X j i
    have hC : Matrix.transpose (fun i j => X.val (.inr i) (.inl j)) =
        -(fun i j => X.val (.inr i) (.inl j) : Matrix ι ι R) := by
      ext i j
      exact LieAlgebra.Orthogonal.typeD.apply_inr_inl X j i
    apply Subtype.ext
    ext (i | i) (j | j)
    · exact Matrix.fromBlocks_apply₁₁ _ _ _ _ _ _
    · refine (Matrix.fromBlocks_apply₁₂ _ _ _ _ _ _).trans ?_
      exact
        congrFun (congrFun (Matrix.ofStrictUpper_eq_of_transpose_eq_neg h2 _ hB) i) j
    · refine (Matrix.fromBlocks_apply₂₁ _ _ _ _ _ _).trans ?_
      simpa only [neg_neg] using
        congrFun (congrFun (Matrix.ofStrictUpper_eq_of_transpose_eq_neg h2 _ hC) i) j
    · exact (Matrix.fromBlocks_apply₂₂ _ _ _ _ _ _).trans
        (LieAlgebra.Orthogonal.typeD.apply_inr_inr X i j).symm
  right_inv a := by
    funext p
    rcases p with p | (p | p)
    · exact Matrix.fromBlocks_apply₁₁ _ _ _ _ _ _
    · exact (Matrix.fromBlocks_apply₁₂ _ _ _ _ _ _).trans
        (Matrix.ofStrictUpper_apply_of_lt _ p)
    · refine (congrArg Neg.neg (Matrix.fromBlocks_apply₂₁ _ _ _ _ _ _)).trans ?_
      simpa only [neg_neg] using
        congrArg Neg.neg (Matrix.ofStrictUpper_apply_of_lt (fun p => -a (.inr (.inr p))) p)
  map_add' X Y := by
    funext p
    rcases p with p | (p | p) <;>
      simp only [AddMemClass.coe_add, Matrix.add_apply, Pi.add_apply, neg_add]
  map_smul' a X := by
    funext p
    rcases p with p | (p | p) <;>
      simp only [SetLike.val_smul, Matrix.smul_apply, Pi.smul_apply, smul_neg, RingHom.id_apply]

/-- Inverse native coordinates complete the upper-right entries and the negatives of the
lower-left coordinates to skew blocks. -/
@[simp]
theorem val_rootEntryEquiv_symm (h2 : ∀ x : R, x + x = 0 → x = 0)
    (a : RootEntryIndex ι → R) :
    ((rootEntryEquiv h2).symm a).val =
      Matrix.fromBlocks (fun i j => a (.inl (i, j)))
        (Matrix.ofStrictUpper fun p => a (.inr (.inl p)))
        (Matrix.ofStrictUpper fun p => -a (.inr (.inr p)))
        (-Matrix.transpose (fun i j => a (.inl (i, j)))) := by
  rfl

/-- Difference-root coordinates read the entire upper-left block. -/
@[simp]
theorem rootEntryEquiv_apply_inl (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) (p : ι × ι) :
    rootEntryEquiv h2 X (.inl p) = X.val (.inl p.1) (.inl p.2) := by
  rfl

/-- Positive sum-root coordinates read the strict upper triangle of the upper-right block. -/
@[simp]
theorem rootEntryEquiv_apply_inr_inl (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryEquiv h2 X (.inr (.inl p)) = X.val (.inl p.val.1) (.inr p.val.2) := by
  rfl

/-- Negative sum-root coordinates negate the strict upper triangle of the lower-left block. -/
@[simp]
theorem rootEntryEquiv_apply_inr_inr (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryEquiv h2 X (.inr (.inr p)) = -X.val (.inr p.val.1) (.inl p.val.2) := by
  rfl

/-- A native matrix basis, including individual hyperbolic diagonal elements, without division
by two. -/
noncomputable def rootEntryBasis (h2 : ∀ x : R, x + x = 0 → x = 0) :
    Module.Basis (RootEntryIndex ι) R (LieAlgebra.Orthogonal.typeD ι R) :=
  Module.Basis.ofEquivFun (rootEntryEquiv h2)

/-- The matrix basis has the coordinates of `rootEntryEquiv`. -/
@[simp]
theorem rootEntryBasis_repr (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) (p : RootEntryIndex ι) :
    (rootEntryBasis h2).repr X p = rootEntryEquiv h2 X p :=
  Module.Basis.ofEquivFun_repr_apply _ _ _

private theorem rootEntryEquiv_basis (h2 : ∀ x : R, x + x = 0 → x = 0)
    (p : RootEntryIndex ι) :
    rootEntryEquiv h2 (rootEntryBasis h2 p) = Pi.single p 1 := by
  rw [rootEntryBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]

/-- The first basis family consists of all difference-root matrices, including the diagonal. -/
@[simp]
theorem rootEntryBasis_inl (h2 : ∀ x : R, x + x = 0 → x = 0) (p : ι × ι) :
    rootEntryBasis h2 (.inl p) = differenceRootGenerator p.1 p.2 := by
  rcases p with ⟨i, j⟩
  apply (rootEntryEquiv h2).injective
  rw [rootEntryEquiv_basis]
  ext q
  rcases q with ⟨a, b⟩ | (p | p)
  all_goals
    simp [rootEntryEquiv_apply_inl, rootEntryEquiv_apply_inr_inl,
      rootEntryEquiv_apply_inr_inr,
      val_differenceRootGenerator, differenceRootMatrix_def, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.single_apply, Pi.single_apply,
      eq_comm]

/-- The second basis family consists of the positive sum-root matrices above the diagonal. -/
@[simp]
theorem rootEntryBasis_inr_inl (h2 : ∀ x : R, x + x = 0 → x = 0)
    (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryBasis h2 (.inr (.inl p)) = sumRootGenerator p.val.1 p.val.2 := by
  apply (rootEntryEquiv h2).injective
  rw [rootEntryEquiv_basis]
  ext q
  rcases q with ⟨a, b⟩ | (q | q)
  · simp [val_sumRootGenerator, sumRootMatrix_def, Matrix.fromBlocks_apply₁₁]
  · rw [rootEntryEquiv_apply_inr_inl, val_sumRootGenerator, sumRootMatrix_def]
    simpa [Matrix.fromBlocks_apply₁₂, Pi.single_apply, eq_comm] using
      (Matrix.single_sub_single_apply_of_lt p q (1 : R)).symm
  · simp [val_sumRootGenerator, sumRootMatrix_def, Matrix.fromBlocks_apply₂₁]

/-- The third basis family reverses the negative sum-root indices, as at the native fork. -/
@[simp]
theorem rootEntryBasis_inr_inr (h2 : ∀ x : R, x + x = 0 → x = 0)
    (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryBasis h2 (.inr (.inr p)) = negSumRootGenerator p.val.2 p.val.1 := by
  apply (rootEntryEquiv h2).injective
  rw [rootEntryEquiv_basis]
  ext q
  rcases q with ⟨a, b⟩ | (q | q)
  · simp [val_negSumRootGenerator, negSumRootMatrix_def, Matrix.fromBlocks_apply₁₁]
  · simp [val_negSumRootGenerator, negSumRootMatrix_def, Matrix.fromBlocks_apply₁₂]
  · rw [rootEntryEquiv_apply_inr_inr, val_negSumRootGenerator, negSumRootMatrix_def]
    simpa [Matrix.fromBlocks_apply₂₁, Matrix.sub_apply, Pi.single_apply, neg_sub, eq_comm] using
      (Matrix.single_sub_single_apply_of_lt p q (1 : R)).symm

/-- Every split even orthogonal matrix expands in the three native root-matrix families.
Only strict upper pairs occur in the sum-root families, so no coefficient is divided by two. -/
theorem eq_sum_rootEntryBasis (h2 : ∀ x : R, x + x = 0 → x = 0)
    (X : LieAlgebra.Orthogonal.typeD ι R) :
    X =
      (∑ p : ι × ι, X.val (.inl p.1) (.inl p.2) • differenceRootGenerator p.1 p.2) +
      (∑ p : {p : ι × ι // p.1 < p.2},
        X.val (.inl p.val.1) (.inr p.val.2) • sumRootGenerator p.val.1 p.val.2) +
      (∑ p : {p : ι × ι // p.1 < p.2},
        (-X.val (.inr p.val.1) (.inl p.val.2)) • negSumRootGenerator p.val.2 p.val.1) := by
  simpa only [Fintype.sum_sum_type, rootEntryBasis_repr, rootEntryEquiv_apply_inl,
    rootEntryEquiv_apply_inr_inl, rootEntryEquiv_apply_inr_inr, rootEntryBasis_inl,
    rootEntryBasis_inr_inl, rootEntryBasis_inr_inr, add_assoc] using
    ((rootEntryBasis h2).sum_repr X).symm

end TauCeti.TypeDStd
