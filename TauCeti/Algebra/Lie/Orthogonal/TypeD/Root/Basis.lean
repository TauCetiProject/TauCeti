/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.DiagonalBasis

/-!
# A native type-D basis with the numbered simple coroots

When two is invertible, the Bourbaki simple coroots replace the elementary diagonal
vectors in the native even orthogonal basis. The off-diagonal difference-root vectors
and the two sum-root families are retained, including the reversed indices in the
negative family. Thus the numbered Cartan, raising and lowering generators are literal
basis members. The diagonal coordinates are the prefix-sum and half-total formulas
of the simple-root basis.
-/

public section

namespace TauCeti.TypeDStd

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The native even orthogonal basis whose diagonal slots are the numbered simple coroots. -/
noncomputable def pinnedRootBasis (n : ℕ) (hn : 4 ≤ n) :
    Module.Basis (RootEntryIndex (Fin n)) R (LieAlgebra.Orthogonal.typeD (Fin n) R) :=
  basisOfDiagonal (isUnit_of_invertible (2 : R)).eq_zero_of_add_self_eq_zero
    (DynkinType.typeDSimpleRootBasis R n hn)

/-- Diagonal slots are exactly the numbered Cartan generators. -/
@[simp]
theorem pinnedRootBasis_diagonal (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    pinnedRootBasis (R := R) n hn (.inl (i, i)) = cartanGenerator n hn i := by
  apply Subtype.ext
  rw [pinnedRootBasis, val_basisOfDiagonal_diagonal, DynkinType.typeDSimpleRootBasis_apply,
    cartanGenerator_eq_typeDDiagonalEquiv, coe_typeDDiagonalEquiv_apply]
  ext (j | j) (k | k) <;> by_cases h : j = k <;>
    simp [h, Matrix.fromBlocks, Matrix.diagonal, typeDDiagonalMatrix_apply]

/-- The simple-coroot coefficients are prefix sums along the chain and half-total
expressions at the fork. -/
theorem pinnedRootBasis_repr_diagonal (n : ℕ) (hn : 4 ≤ n)
    (X : LieAlgebra.Orthogonal.typeD (Fin n) R) (k : Fin n) :
    (pinnedRootBasis (R := R) n hn).repr X (.inl (k, k)) =
      if (k : ℕ) + 2 < n then ∑ j ∈ Finset.Iic k, X.val (.inl j) (.inl j)
      else if (k : ℕ) + 1 < n then
        ⅟ (2 : R) * (∑ j, X.val (.inl j) (.inl j)) -
          X.val (.inl ⟨n - 1, by omega⟩) (.inl ⟨n - 1, by omega⟩)
      else ⅟ (2 : R) * (∑ j, X.val (.inl j) (.inl j)) := by
  rw [pinnedRootBasis, basisOfDiagonal_repr_diagonal]
  exact DynkinType.typeDSimpleRootBasis_repr_apply R hn _ k

/-- Off-diagonal slots retain their difference-root vectors. -/
@[simp]
theorem pinnedRootBasis_inl_of_ne (n : ℕ) (hn : 4 ≤ n) {i j : Fin n} (h : i ≠ j) :
    pinnedRootBasis (R := R) n hn (.inl (i, j)) = differenceRootGenerator i j := by
  exact basisOfDiagonal_of_ne _ _ h

/-- Positive sum-root slots retain the original upper-right block vectors. -/
@[simp]
theorem pinnedRootBasis_inr_inl (n : ℕ) (hn : 4 ≤ n)
    (p : {p : Fin n × Fin n // p.1 < p.2}) :
    pinnedRootBasis (R := R) n hn (.inr (.inl p)) =
      sumRootGenerator p.val.1 p.val.2 := by
  exact basisOfDiagonal_sumRoot _ _ p

/-- Negative sum-root slots retain the reversed native lower-left block vectors. -/
@[simp]
theorem pinnedRootBasis_inr_inr (n : ℕ) (hn : 4 ≤ n)
    (p : {p : Fin n × Fin n // p.1 < p.2}) :
    pinnedRootBasis (R := R) n hn (.inr (.inr p)) =
      negSumRootGenerator p.val.2 p.val.1 := by
  exact basisOfDiagonal_negSumRoot _ _ p

/-- Off-diagonal difference-root coefficients are upper-left matrix entries. -/
@[simp]
theorem pinnedRootBasis_repr_inl_of_ne (n : ℕ) (hn : 4 ≤ n)
    (X : LieAlgebra.Orthogonal.typeD (Fin n) R) {i j : Fin n} (h : i ≠ j) :
    (pinnedRootBasis (R := R) n hn).repr X (.inl (i, j)) =
      X.val (.inl i) (.inl j) := by
  exact basisOfDiagonal_repr_of_ne _ _ X h

/-- Positive sum-root coefficients are strict upper entries of the upper-right block. -/
@[simp]
theorem pinnedRootBasis_repr_inr_inl (n : ℕ) (hn : 4 ≤ n)
    (X : LieAlgebra.Orthogonal.typeD (Fin n) R)
    (p : {p : Fin n × Fin n // p.1 < p.2}) :
    (pinnedRootBasis (R := R) n hn).repr X (.inr (.inl p)) =
      X.val (.inl p.val.1) (.inr p.val.2) := by
  exact basisOfDiagonal_repr_sumRoot _ _ X p

/-- Negative sum-root coefficients include the sign of the reversed native generator. -/
@[simp]
theorem pinnedRootBasis_repr_inr_inr (n : ℕ) (hn : 4 ≤ n)
    (X : LieAlgebra.Orthogonal.typeD (Fin n) R)
    (p : {p : Fin n × Fin n // p.1 < p.2}) :
    (pinnedRootBasis (R := R) n hn).repr X (.inr (.inr p)) =
      -X.val (.inr p.val.1) (.inl p.val.2) := by
  exact basisOfDiagonal_repr_negSumRoot _ _ X p

/-- A chain raising generator occupies the forward adjacent difference-root slot. -/
theorem pinnedRootBasis_chain_inl (n : ℕ) (hn : 4 ≤ n)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    pinnedRootBasis (R := R) n hn (.inl (i, chainNext n i hi)) =
      rootGenerator n hn (.inl i) := by
  rw [pinnedRootBasis_inl_of_ne n hn (ne_chainNext n i hi),
    differenceRootGenerator_chain_eq_rootGenerator]

/-- A chain lowering generator occupies the reversed adjacent difference-root slot. -/
theorem pinnedRootBasis_chain_inr (n : ℕ) (hn : 4 ≤ n)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    pinnedRootBasis (R := R) n hn (.inl (chainNext n i hi, i)) =
      rootGenerator n hn (.inr i) := by
  rw [pinnedRootBasis_inl_of_ne n hn (ne_chainNext n i hi).symm,
    differenceRootGenerator_reverse_chain_eq_rootGenerator]

/-- The fork raising generator occupies the positive sum-root slot. -/
theorem pinnedRootBasis_fork_inl (n : ℕ) (hn : 4 ≤ n) :
    pinnedRootBasis (R := R) n hn (.inr (.inl
      ⟨(forkLeft n hn, forkRight n hn), by
        simp only [Fin.lt_def, forkLeft_val, forkRight_val]
        omega⟩)) = rootGenerator n hn (.inl (forkRight n hn)) := by
  rw [pinnedRootBasis_inr_inl, sumRootGenerator_fork_eq_rootGenerator]

/-- The fork lowering generator occupies the reversed negative sum-root slot. -/
theorem pinnedRootBasis_fork_inr (n : ℕ) (hn : 4 ≤ n) :
    pinnedRootBasis (R := R) n hn (.inr (.inr
      ⟨(forkLeft n hn, forkRight n hn), by
        simp only [Fin.lt_def, forkLeft_val, forkRight_val]
        omega⟩)) = rootGenerator n hn (.inr (forkRight n hn)) := by
  rw [pinnedRootBasis_inr_inr, negSumRootGenerator_reverse_fork_eq_rootGenerator]

/-- The numbered Cartan generators have unit coordinate vectors. -/
@[simp]
theorem pinnedRootBasis_repr_cartanGenerator (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    (pinnedRootBasis (R := R) n hn).repr (cartanGenerator n hn i) =
      Finsupp.single (.inl (i, i)) 1 := by
  rw [← pinnedRootBasis_diagonal n hn i, Module.Basis.repr_self]

/-- The chain raising generators have unit forward-slot coordinate vectors. -/
@[simp]
theorem pinnedRootBasis_repr_chain_inl (n : ℕ) (hn : 4 ≤ n)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (pinnedRootBasis (R := R) n hn).repr (rootGenerator n hn (.inl i)) =
      Finsupp.single (.inl (i, chainNext n i hi)) 1 := by
  rw [← pinnedRootBasis_chain_inl n hn i hi, Module.Basis.repr_self]

/-- The chain lowering generators have unit reversed-slot coordinate vectors. -/
@[simp]
theorem pinnedRootBasis_repr_chain_inr (n : ℕ) (hn : 4 ≤ n)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (pinnedRootBasis (R := R) n hn).repr (rootGenerator n hn (.inr i)) =
      Finsupp.single (.inl (chainNext n i hi, i)) 1 := by
  rw [← pinnedRootBasis_chain_inr n hn i hi, Module.Basis.repr_self]

/-- The fork raising generator has a unit positive sum-root coordinate vector. -/
@[simp]
theorem pinnedRootBasis_repr_fork_inl (n : ℕ) (hn : 4 ≤ n) :
    (pinnedRootBasis (R := R) n hn).repr
      (rootGenerator n hn (.inl (forkRight n hn))) =
      Finsupp.single (.inr (.inl ⟨(forkLeft n hn, forkRight n hn), by
        simp only [Fin.lt_def, forkLeft_val, forkRight_val]
        omega⟩)) 1 := by
  rw [← pinnedRootBasis_fork_inl n hn, Module.Basis.repr_self]

/-- The fork lowering generator has a unit negative sum-root coordinate vector. -/
@[simp]
theorem pinnedRootBasis_repr_fork_inr (n : ℕ) (hn : 4 ≤ n) :
    (pinnedRootBasis (R := R) n hn).repr
      (rootGenerator n hn (.inr (forkRight n hn))) =
      Finsupp.single (.inr (.inr ⟨(forkLeft n hn, forkRight n hn), by
        simp only [Fin.lt_def, forkLeft_val, forkRight_val]
        omega⟩)) 1 := by
  rw [← pinnedRootBasis_fork_inr n hn, Module.Basis.repr_self]

end TauCeti.TypeDStd
