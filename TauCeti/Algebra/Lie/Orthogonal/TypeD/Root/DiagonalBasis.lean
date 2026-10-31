/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Coordinates

/-!
# Extending a diagonal basis in the even orthogonal Lie algebra

An arbitrary basis of diagonal coordinates extends to a basis of the native even orthogonal
module by retaining the off-diagonal difference-root matrices and both sum-root families.
Only the diagonal coordinates change. This construction supports the simple-coroot bases
for native types D and B without repeating the coordinate substitution.
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
private theorem diagonalChangeEquiv_symm_apply_inl (e : (ι → R) ≃ₗ[R] (ι → R))
    (a : RootEntryIndex ι → R) (i j : ι) :
    (diagonalChangeEquiv e).symm a (.inl (i, j)) =
      if i = j then e.symm (fun k => a (.inl (k, k))) i else a (.inl (i, j)) := rfl

private noncomputable def diagonalCoordsEquiv (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) :
    LieAlgebra.Orthogonal.typeD ι R ≃ₗ[R] (RootEntryIndex ι → R) :=
  (rootEntryEquiv h2).trans (diagonalChangeEquiv b.equivFun)

/-- Extend a basis of diagonal coordinates to the full even orthogonal module, retaining
the off-diagonal difference-root matrices and both sum-root families. -/
noncomputable def basisOfDiagonal (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) :
    Module.Basis (RootEntryIndex ι) R (LieAlgebra.Orthogonal.typeD ι R) :=
  Module.Basis.ofEquivFun (diagonalCoordsEquiv h2 b)

/-- The diagonal coefficients are the coefficients of the upper-left diagonal in `b`. -/
@[simp]
theorem basisOfDiagonal_repr_diagonal (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (X : LieAlgebra.Orthogonal.typeD ι R) (i : ι) :
    (basisOfDiagonal h2 b).repr X (.inl (i, i)) =
      b.repr (fun k => X.val (.inl k) (.inl k)) i := by
  simp [basisOfDiagonal, diagonalCoordsEquiv, diagonalChangeEquiv]

/-- The off-diagonal difference-root coefficients remain upper-left matrix entries. -/
@[simp]
theorem basisOfDiagonal_repr_of_ne (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (X : LieAlgebra.Orthogonal.typeD ι R)
    {i j : ι} (h : i ≠ j) :
    (basisOfDiagonal h2 b).repr X (.inl (i, j)) = X.val (.inl i) (.inl j) := by
  simp [basisOfDiagonal, diagonalCoordsEquiv, diagonalChangeEquiv, h]

/-- Positive sum-root coefficients remain strict upper entries of the upper-right block. -/
@[simp]
theorem basisOfDiagonal_repr_sumRoot (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (X : LieAlgebra.Orthogonal.typeD ι R)
    (p : {p : ι × ι // p.1 < p.2}) :
    (basisOfDiagonal h2 b).repr X (.inr (.inl p)) =
      X.val (.inl p.val.1) (.inr p.val.2) := by
  simp [basisOfDiagonal, diagonalCoordsEquiv, diagonalChangeEquiv]

/-- Negative sum-root coefficients remain negatives of strict upper entries of the
lower-left block. -/
@[simp]
theorem basisOfDiagonal_repr_negSumRoot (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (X : LieAlgebra.Orthogonal.typeD ι R)
    (p : {p : ι × ι // p.1 < p.2}) :
    (basisOfDiagonal h2 b).repr X (.inr (.inr p)) =
      -X.val (.inr p.val.1) (.inl p.val.2) := by
  simp [basisOfDiagonal, diagonalCoordsEquiv, diagonalChangeEquiv]

private theorem basisOfDiagonal_apply (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (p : RootEntryIndex ι) :
    basisOfDiagonal h2 b p =
      (rootEntryEquiv h2).symm ((diagonalChangeEquiv b.equivFun).symm (Pi.single p 1)) := by
  rw [basisOfDiagonal, Module.Basis.coe_ofEquivFun]
  rfl

omit [Fintype ι] in
private theorem diagonalChangeEquiv_symm_single (e : (ι → R) ≃ₗ[R] (ι → R))
    (p : RootEntryIndex ι) (h : ∀ i, p ≠ .inl (i, i)) :
    (diagonalChangeEquiv e).symm (Pi.single p 1) = Pi.single p 1 := by
  have hd : (fun i => (Pi.single p (1 : R) : RootEntryIndex ι → R) (.inl (i, i))) = 0 := by
    ext i
    simp [Ne.symm (h i)]
  ext q
  rcases q with ⟨i, j⟩ | q
  · by_cases hij : i = j
    · subst j
      rw [diagonalChangeEquiv_symm_apply_inl, ite_eq_left rfl, hd, map_zero]
      simp [Ne.symm (h i)]
    · simp [diagonalChangeEquiv_symm_apply_inl, hij]
  · rfl

private theorem basisOfDiagonal_eq_rootEntryBasis
    (h2 : ∀ x : R, x + x = 0 → x = 0) (b : Module.Basis ι R (ι → R))
    (p : RootEntryIndex ι) (h : ∀ i, p ≠ .inl (i, i)) :
    basisOfDiagonal h2 b p = rootEntryBasis h2 p := by
  apply (rootEntryEquiv h2).injective
  rw [basisOfDiagonal_apply, diagonalChangeEquiv_symm_single _ _ h,
    LinearEquiv.apply_symm_apply]
  ext q
  rw [← rootEntryBasis_repr, Module.Basis.repr_self]
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- Off-diagonal basis vectors are the original difference-root matrices. -/
@[simp]
theorem basisOfDiagonal_of_ne (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) {i j : ι} (h : i ≠ j) :
    basisOfDiagonal h2 b (.inl (i, j)) = differenceRootGenerator i j := by
  rw [basisOfDiagonal_eq_rootEntryBasis, rootEntryBasis_inl]
  intro k hk
  have hp := Sum.inl.inj hk
  exact h ((congrArg Prod.fst hp).trans (congrArg Prod.snd hp).symm)

/-- Positive sum-root basis vectors are unchanged by the diagonal substitution. -/
@[simp]
theorem basisOfDiagonal_sumRoot (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (p : {p : ι × ι // p.1 < p.2}) :
    basisOfDiagonal h2 b (.inr (.inl p)) = sumRootGenerator p.val.1 p.val.2 := by
  rw [basisOfDiagonal_eq_rootEntryBasis, rootEntryBasis_inr_inl]
  intro i
  exact Sum.inr_ne_inl

/-- Negative sum-root basis vectors retain the reversed indices of the native entry basis. -/
@[simp]
theorem basisOfDiagonal_negSumRoot (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (p : {p : ι × ι // p.1 < p.2}) :
    basisOfDiagonal h2 b (.inr (.inr p)) = negSumRootGenerator p.val.2 p.val.1 := by
  rw [basisOfDiagonal_eq_rootEntryBasis, rootEntryBasis_inr_inr]
  intro i
  exact Sum.inr_ne_inl

/-- A diagonal basis vector has upper diagonal `b i` and the opposite lower diagonal. -/
@[simp]
theorem val_basisOfDiagonal_diagonal (h2 : ∀ x : R, x + x = 0 → x = 0)
    (b : Module.Basis ι R (ι → R)) (i : ι) :
    (basisOfDiagonal h2 b (.inl (i, i))).val =
      Matrix.fromBlocks (Matrix.diagonal (b i)) 0 0 (-Matrix.diagonal (b i)) := by
  have hd : (fun k => (Pi.single (.inl (i, i)) (1 : R) : RootEntryIndex ι → R)
      (.inl (k, k))) = Pi.single i 1 := by
    ext k
    simp [Pi.single_apply, eq_comm]
  have hb : b.equivFun.symm (Pi.single i 1) = b i := by
    simp [Module.Basis.equivFun_symm_apply]
  have hA : (fun j k =>
      (diagonalChangeEquiv b.equivFun).symm (Pi.single (.inl (i, i)) 1) (.inl (j, k))) =
        Matrix.diagonal (b i) := by
    ext j k
    rw [diagonalChangeEquiv_symm_apply_inl, hd, hb]
    by_cases h : j = k
    · simp [h]
    · suffices j = i → k = i → (1 : R) = 0 by
        simpa [h, Pi.single_apply] using this
      intro hj hk
      exact (h (hj.trans hk.symm)).elim
  rw [basisOfDiagonal_apply, val_rootEntryEquiv_symm, hA]
  have hz : Matrix.ofStrictUpper (fun _ : {p : ι × ι // p.1 < p.2} => (0 : R)) = 0 :=
    Matrix.ofStrictUpper_zero
  simp [diagonalChangeEquiv, hz]

end TauCeti.TypeDStd
