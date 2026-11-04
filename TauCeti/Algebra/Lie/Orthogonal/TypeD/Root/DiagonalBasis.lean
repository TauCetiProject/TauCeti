/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Coordinates
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Extending a diagonal basis in the even orthogonal Lie algebra

When doubling has trivial kernel, an arbitrary basis of the diagonal coordinates extends to a
basis of the native even orthogonal module by retaining the off-diagonal difference-root
matrices and both sum-root families. Only the diagonal coordinates change. The type-D
specialization to the simple-coroot basis is `TauCeti.TypeDStd.pinnedRootBasis` in
`TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Basis`.

## Main declarations

* `TauCeti.TypeDStd.basisOfDiagonal`: the extended basis.
* `TauCeti.TypeDStd.basisOfDiagonal_diagonal`: its diagonal slots are the diagonal Cartan
  elements `typeDDiagonalEquiv (b i)`.
* `TauCeti.TypeDStd.basisOfDiagonal_inl_of_ne`, `basisOfDiagonal_inr_inl`,
  `basisOfDiagonal_inr_inr`: the off-diagonal slots keep the root generators.
-/

public section

namespace TauCeti.TypeDStd

variable {R ι : Type*} [CommRing R] [LinearOrder ι] [Fintype ι]

private def diagonalChangeEquiv (e : (ι → R) ≃ₗ[R] (ι → R)) :
    (RootEntryIndex ι → R) ≃ₗ[R] (RootEntryIndex ι → R) where
  toFun a
    | .inl (i, j) => if i = j then e (fun k => a (.inl (k, k))) i else a (.inl (i, j))
    | .inr p => a (.inr p)
  invFun a
    | .inl (i, j) =>
      if i = j then e.symm (fun k => a (.inl (k, k))) i else a (.inl (i, j))
    | .inr p => a (.inr p)
  left_inv a := by
    ext p
    rcases p with ⟨i, j⟩ | p
    · by_cases h : i = j
      · subst j
        simp
      · simp [h]
    · rfl
  right_inv a := by
    ext p
    rcases p with ⟨i, j⟩ | p
    · by_cases h : i = j
      · subst j
        simp
      · simp [h]
    · rfl
  map_add' a b := by
    ext p
    rcases p with ⟨i, j⟩ | p
    · by_cases h : i = j <;> simp [h, ← Pi.add_def]
    · rfl
  map_smul' a b := by
    ext p
    rcases p with ⟨i, j⟩ | p
    · by_cases h : i = j
      · subst j
        simpa only [ite_true, Pi.smul_def, smul_eq_mul, RingHom.id_apply] using
          congrFun (map_smul e a (fun k => b (.inl (k, k)))) i
      · simp [h]
    · rfl

omit [Fintype ι] in
private theorem diagonalChangeEquiv_apply_inl (e : (ι → R) ≃ₗ[R] (ι → R))
    (a : RootEntryIndex ι → R) (i j : ι) :
    diagonalChangeEquiv e a (.inl (i, j)) =
      if i = j then e (fun k => a (.inl (k, k))) i else a (.inl (i, j)) := rfl

omit [Fintype ι] in
private theorem diagonalChangeEquiv_apply_inr (e : (ι → R) ≃ₗ[R] (ι → R))
    (a : RootEntryIndex ι → R) (p : {p : ι × ι // p.1 < p.2} ⊕ {p : ι × ι // p.1 < p.2}) :
    diagonalChangeEquiv e a (.inr p) = a (.inr p) := rfl

omit [Fintype ι] in
private theorem diagonalChangeEquiv_symm_apply_inl (e : (ι → R) ≃ₗ[R] (ι → R))
    (a : RootEntryIndex ι → R) (i j : ι) :
    (diagonalChangeEquiv e).symm a (.inl (i, j)) =
      if i = j then e.symm (fun k => a (.inl (k, k))) i else a (.inl (i, j)) := rfl

omit [Fintype ι] in
private theorem diagonalChangeEquiv_symm_apply_inr (e : (ι → R) ≃ₗ[R] (ι → R))
    (a : RootEntryIndex ι → R) (p : {p : ι × ι // p.1 < p.2} ⊕ {p : ι × ι // p.1 < p.2}) :
    (diagonalChangeEquiv e).symm a (.inr p) = a (.inr p) := rfl

/-- Extend a basis of diagonal coordinates to the full even orthogonal module, retaining
the off-diagonal difference-root matrices and both sum-root families. -/
noncomputable def basisOfDiagonal (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) :
    Module.Basis (RootEntryIndex ι) R (LieAlgebra.Orthogonal.typeD ι R) :=
  Module.Basis.ofEquivFun ((rootEntryEquiv h2).trans (diagonalChangeEquiv b.equivFun))

private theorem basisOfDiagonal_repr (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (X : LieAlgebra.Orthogonal.typeD ι R)
    (p : RootEntryIndex ι) :
    (basisOfDiagonal h2 b).repr X p =
      diagonalChangeEquiv b.equivFun (rootEntryEquiv h2 X) p := by
  rw [basisOfDiagonal, Module.Basis.ofEquivFun_repr_apply, LinearEquiv.trans_apply]

/-- The diagonal coefficients are the coefficients of the upper-left diagonal in `b`. -/
@[simp]
theorem basisOfDiagonal_repr_diagonal (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (X : LieAlgebra.Orthogonal.typeD ι R) (i : ι) :
    (basisOfDiagonal h2 b).repr X (.inl (i, i)) =
      b.repr (fun k => X.val (.inl k) (.inl k)) i := by
  rw [basisOfDiagonal_repr, diagonalChangeEquiv_apply_inl, ite_eq_left rfl,
    Module.Basis.equivFun_apply]
  simp only [rootEntryEquiv_apply_inl]

/-- The off-diagonal difference-root coefficients remain upper-left matrix entries. -/
@[simp]
theorem basisOfDiagonal_repr_inl_of_ne (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (X : LieAlgebra.Orthogonal.typeD ι R)
    {i j : ι} (h : i ≠ j) :
    (basisOfDiagonal h2 b).repr X (.inl (i, j)) = X.val (.inl i) (.inl j) := by
  rw [basisOfDiagonal_repr, diagonalChangeEquiv_apply_inl, ite_eq_right h, rootEntryEquiv_apply_inl]

/-- Positive sum-root coefficients remain strict upper entries of the upper-right block. -/
@[simp]
theorem basisOfDiagonal_repr_inr_inl (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (X : LieAlgebra.Orthogonal.typeD ι R)
    (p : {p : ι × ι // p.1 < p.2}) :
    (basisOfDiagonal h2 b).repr X (.inr (.inl p)) =
      X.val (.inl p.val.1) (.inr p.val.2) := by
  rw [basisOfDiagonal_repr, diagonalChangeEquiv_apply_inr, rootEntryEquiv_apply_inr_inl]

/-- Negative sum-root coefficients remain negatives of strict upper entries of the
lower-left block. -/
@[simp]
theorem basisOfDiagonal_repr_inr_inr (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (X : LieAlgebra.Orthogonal.typeD ι R)
    (p : {p : ι × ι // p.1 < p.2}) :
    (basisOfDiagonal h2 b).repr X (.inr (.inr p)) =
      -X.val (.inr p.val.1) (.inl p.val.2) := by
  rw [basisOfDiagonal_repr, diagonalChangeEquiv_apply_inr, rootEntryEquiv_apply_inr_inr]

private theorem basisOfDiagonal_apply (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (p : RootEntryIndex ι) :
    basisOfDiagonal h2 b p =
      (rootEntryEquiv h2).symm ((diagonalChangeEquiv b.equivFun).symm (Pi.single p 1)) := by
  simp only [basisOfDiagonal, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_trans_apply]

omit [Fintype ι] in
private theorem diagonalChangeEquiv_symm_single (e : (ι → R) ≃ₗ[R] (ι → R))
    (p : RootEntryIndex ι) (h : ∀ i, p ≠ .inl (i, i)) :
    (diagonalChangeEquiv e).symm (Pi.single p 1) = Pi.single p 1 := by
  have hd : (fun i => (Pi.single p (1 : R) : RootEntryIndex ι → R) (.inl (i, i))) = 0 :=
    funext fun i => Pi.single_eq_of_ne (Ne.symm (h i)) 1
  ext q
  rcases q with ⟨i, j⟩ | q
  · by_cases hij : i = j
    · subst j
      rw [diagonalChangeEquiv_symm_apply_inl, ite_eq_left rfl, hd, map_zero, Pi.zero_apply,
        Pi.single_eq_of_ne (Ne.symm (h i))]
    · rw [diagonalChangeEquiv_symm_apply_inl, ite_eq_right hij]
  · rw [diagonalChangeEquiv_symm_apply_inr]

private theorem basisOfDiagonal_eq_rootEntryBasis
    (h2 : ∀ x : R, x + x = 0 → x = 0) (b : Module.Basis ι R (ι → R))
    (p : RootEntryIndex ι) (h : ∀ i, p ≠ .inl (i, i)) :
    basisOfDiagonal h2 b p = rootEntryBasis h2 p := by
  rw [basisOfDiagonal_apply, diagonalChangeEquiv_symm_single _ _ h, rootEntryBasis_apply]

omit [Fintype ι] in
private theorem inl_ne_inl_diagonal {i j : ι} (h : i ≠ j) (k : ι) :
    (.inl (i, j) : RootEntryIndex ι) ≠ .inl (k, k) := by
  rintro ⟨⟩
  exact h rfl

/-- Off-diagonal basis vectors are the original difference-root matrices. -/
@[simp]
theorem basisOfDiagonal_inl_of_ne (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) {i j : ι} (h : i ≠ j) :
    basisOfDiagonal h2 b (.inl (i, j)) = differenceRootGenerator i j := by
  rw [basisOfDiagonal_eq_rootEntryBasis _ _ _ (inl_ne_inl_diagonal h), rootEntryBasis_inl]

/-- Positive sum-root basis vectors are unchanged by the diagonal substitution. -/
@[simp]
theorem basisOfDiagonal_inr_inl (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (p : {p : ι × ι // p.1 < p.2}) :
    basisOfDiagonal h2 b (.inr (.inl p)) = sumRootGenerator p.val.1 p.val.2 := by
  rw [basisOfDiagonal_eq_rootEntryBasis _ _ _ fun _ => Sum.inr_ne_inl, rootEntryBasis_inr_inl]

/-- Negative sum-root basis vectors retain the reversed indices of the native entry basis. -/
@[simp]
theorem basisOfDiagonal_inr_inr (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (p : {p : ι × ι // p.1 < p.2}) :
    basisOfDiagonal h2 b (.inr (.inr p)) = negSumRootGenerator p.val.2 p.val.1 := by
  rw [basisOfDiagonal_eq_rootEntryBasis _ _ _ fun _ => Sum.inr_ne_inl, rootEntryBasis_inr_inr]

/-- The matrix of a diagonal basis vector is `diag(b i, -(b i))`. -/
theorem val_basisOfDiagonal_diagonal (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (i : ι) :
    (basisOfDiagonal h2 b (.inl (i, i))).val = typeDDiagonalMatrix (b i) := by
  have hd : (fun k => (Pi.single (.inl (i, i)) (1 : R) : RootEntryIndex ι → R)
      (.inl (k, k))) = Pi.single i 1 := by
    ext k
    simp [Pi.single_apply, eq_comm]
  have hA : (fun j k => (diagonalChangeEquiv b.equivFun).symm
      (Pi.single (.inl (i, i)) (1 : R) : RootEntryIndex ι → R) (.inl (j, k))) =
        Matrix.diagonal (b i) := by
    ext j k
    rw [diagonalChangeEquiv_symm_apply_inl, hd, Basis.equivFun_symm_single]
    by_cases h : j = k
    · subst k
      rw [ite_eq_left rfl, Matrix.diagonal_apply_eq]
    · rw [ite_eq_right h, Matrix.diagonal_apply_ne _ h,
        Pi.single_eq_of_ne (inl_ne_inl_diagonal h i)]
  have hz : ∀ q, (diagonalChangeEquiv b.equivFun).symm
      (Pi.single (.inl (i, i)) (1 : R) : RootEntryIndex ι → R) (.inr q) = 0 := fun q => by
    rw [diagonalChangeEquiv_symm_apply_inr, Pi.single_eq_of_ne Sum.inr_ne_inl]
  have hB : (fun p : {p : ι × ι // p.1 < p.2} => (diagonalChangeEquiv b.equivFun).symm
      (Pi.single (.inl (i, i)) (1 : R) : RootEntryIndex ι → R) (.inr (.inl p))) = 0 :=
    funext fun p => hz _
  have hC : (fun p : {p : ι × ι // p.1 < p.2} => -(diagonalChangeEquiv b.equivFun).symm
      (Pi.single (.inl (i, i)) (1 : R) : RootEntryIndex ι → R) (.inr (.inr p))) = 0 :=
    funext fun p => by rw [hz, neg_zero, Pi.zero_apply]
  rw [basisOfDiagonal_apply, val_rootEntryEquiv_symm, hA, hB, hC, Matrix.ofStrictUpper_zero,
    Matrix.diagonal_transpose, typeDDiagonalMatrix_eq_fromBlocks]

/-- A diagonal basis vector is the diagonal Cartan element with upper diagonal `b i`. -/
@[simp]
theorem basisOfDiagonal_diagonal (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (i : ι) :
    basisOfDiagonal h2 b (.inl (i, i)) =
      (typeDDiagonalEquiv (K := R) (ι := ι) (b i) : LieAlgebra.Orthogonal.typeD ι R) :=
  Subtype.ext ((val_basisOfDiagonal_diagonal h2 b i).trans
    (congrArg Subtype.val (coe_typeDDiagonalEquiv_apply (b i))).symm)

end TauCeti.TypeDStd
