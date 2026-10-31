/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Generators
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# The native type-D graph involution

Swapping the two coordinates of a chosen hyperbolic pair preserves the split bilinear form.
Conjugation by this swap gives an involution of its native skew-adjoint matrix Lie algebra
over every commutative ring, including in characteristic two.

For the last pair in the standard positive system, this is the type-D diagram involution.
It exchanges the raising and lowering generators at the two terminal nodes and fixes the
other generators. The result supplies the native Lie automorphism needed to twist the two
half-spin representations; it does not construct an intertwiner between them.
-/

public section

open Matrix LieAlgebra.Orthogonal

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I : Type*} [DecidableEq I] (c : I) (A : Type*) [CommRing A]

/-- Exchange the two coordinates of one hyperbolic pair. -/
def typeDGraphIndex : Equiv.Perm (I ⊕ I) := Equiv.swap (.inl c) (.inr c)

/-- The positive coordinate of the chosen pair is sent to its negative coordinate. -/
@[simp]
theorem typeDGraphIndex_inl_self : typeDGraphIndex c (.inl c) = .inr c := by
  simp [typeDGraphIndex]

/-- The negative coordinate of the chosen pair is sent to its positive coordinate. -/
@[simp]
theorem typeDGraphIndex_inr_self : typeDGraphIndex c (.inr c) = .inl c := by
  simp [typeDGraphIndex]

/-- A positive coordinate outside the chosen pair is fixed. -/
@[simp]
theorem typeDGraphIndex_inl_of_ne {i : I} (hi : i ≠ c) :
    typeDGraphIndex c (.inl i) = .inl i := by
  exact Equiv.swap_apply_of_ne_of_ne (by simpa using hi) (by simp)

/-- A negative coordinate outside the chosen pair is fixed. -/
@[simp]
theorem typeDGraphIndex_inr_of_ne {i : I} (hi : i ≠ c) :
    typeDGraphIndex c (.inr i) = .inr i := by
  exact Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hi)

/-- The hyperbolic-pair index swap is its own inverse. -/
@[simp]
theorem typeDGraphIndex_symm : (typeDGraphIndex c).symm = typeDGraphIndex c := by
  simp [typeDGraphIndex]

/-- The permutation matrix exchanging one hyperbolic pair. -/
def typeDGraphMatrix : Matrix (I ⊕ I) (I ⊕ I) A :=
  (typeDGraphIndex c).permMatrix A

/-- The swap matrix has one entry in the column selected by the index permutation. -/
theorem typeDGraphMatrix_apply (s t : I ⊕ I) :
    typeDGraphMatrix c A s t = if typeDGraphIndex c s = t then 1 else 0 := by
  simp [typeDGraphMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

/-- The hyperbolic-pair swap matrix is symmetric. -/
@[simp]
theorem typeDGraphMatrix_transpose : (typeDGraphMatrix c A)ᵀ = typeDGraphMatrix c A := by
  simp [typeDGraphMatrix, typeDGraphIndex]

variable [Fintype I]

/-- The hyperbolic-pair swap matrix squares to the identity. -/
@[simp]
theorem typeDGraphMatrix_mul_self : typeDGraphMatrix c A * typeDGraphMatrix c A = 1 := by
  simp [typeDGraphMatrix, ← Matrix.permMatrix_mul, typeDGraphIndex]

private theorem typeDGraphMatrix_conj (X : Matrix (I ⊕ I) (I ⊕ I) A) :
    typeDGraphMatrix c A * X * typeDGraphMatrix c A =
      Matrix.reindexAlgEquiv A A (typeDGraphIndex c) X := by
  simp only [typeDGraphMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    typeDGraphIndex_symm, Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]

private theorem typeDGraphIndex_form :
    Matrix.reindexAlgEquiv A A (typeDGraphIndex c) (JD I A) = JD I A := by
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  ext (i | i) (j | j) <;> by_cases hi : i = c <;> by_cases hj : j = c <;>
    simp_all [Matrix.submatrix_apply, JD, Matrix.fromBlocks, Matrix.one_apply, eq_comm]

/-- Exchanging a hyperbolic pair preserves the native split orthogonal form. -/
theorem typeDGraphMatrix_orthogonal :
    (typeDGraphMatrix c A)ᵀ * JD I A * typeDGraphMatrix c A = JD I A := by
  rw [typeDGraphMatrix_transpose, typeDGraphMatrix_conj, typeDGraphIndex_form]

/-- Swap the chosen hyperbolic pair in the native skew-adjoint Lie algebra. -/
def typeDGraphLieEquiv : typeD I A ≃ₗ⁅A⁆ typeD I A :=
  (LieEquiv.ofEq (typeD I A) (skewAdjointMatricesLieSubalgebra (JD I A))
    (by simp only [typeD])).trans
    ((skewAdjointMatricesLieSubalgebraEquivTranspose (JD I A)
      (Matrix.reindexAlgEquiv A A (typeDGraphIndex c))
      (fun X => by
        simpa only [Matrix.coe_reindexAlgEquiv] using
          Matrix.transpose_reindex (typeDGraphIndex c) (typeDGraphIndex c) X)).trans
      (LieEquiv.ofEq _ (typeD I A) (by rw [typeDGraphIndex_form]; simp only [typeD])))

/-- The chosen-pair involution acts by conjugation with the hyperbolic-pair swap. -/
theorem typeDGraphLieEquiv_apply_val (X : typeD I A) :
    (typeDGraphLieEquiv c A X : Matrix (I ⊕ I) (I ⊕ I) A) =
      typeDGraphMatrix c A * X * typeDGraphMatrix c A := by
  rw [typeDGraphMatrix_conj, typeDGraphLieEquiv, LieEquiv.trans_apply, LieEquiv.trans_apply,
    LieEquiv.ofEq_apply, skewAdjointMatricesLieSubalgebraEquivTranspose_apply]
  -- Apply the carrier identity on matrices under the reindexing map.
  exact congrArg (reindexAlgEquiv A A (typeDGraphIndex c))
    (LieEquiv.ofEq_apply (typeD I A) (skewAdjointMatricesLieSubalgebra (JD I A)) _ X)

/-- The chosen-pair involution permutes both matrix indices by the chosen pair swap. -/
theorem typeDGraphLieEquiv_apply_apply (X : typeD I A) (s t : I ⊕ I) :
    (typeDGraphLieEquiv c A X : Matrix (I ⊕ I) (I ⊕ I) A) s t =
      (X : Matrix (I ⊕ I) (I ⊕ I) A) (typeDGraphIndex c s) (typeDGraphIndex c t) := by
  rw [typeDGraphLieEquiv_apply_val, typeDGraphMatrix_conj]
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    typeDGraphIndex_symm]

/-- Applying the chosen-pair involution twice returns the original matrix. -/
@[simp]
theorem typeDGraphLieEquiv_typeDGraphLieEquiv (X : typeD I A) :
    typeDGraphLieEquiv c A (typeDGraphLieEquiv c A X) = X := by
  apply Subtype.ext
  simp only [typeDGraphLieEquiv_apply_val]
  simp only [← mul_assoc, typeDGraphMatrix_mul_self, one_mul]
  rw [mul_assoc, typeDGraphMatrix_mul_self, mul_one]

/-- The chosen-pair Lie involution is its own inverse. -/
@[simp]
theorem typeDGraphLieEquiv_symm :
    (typeDGraphLieEquiv c A).symm = typeDGraphLieEquiv c A := by
  ext X : 1
  apply (typeDGraphLieEquiv c A).injective
  simp

/-- Fixed matrices are precisely those commuting with the hyperbolic-pair swap. -/
theorem typeDGraphLieEquiv_eq_self_iff (X : typeD I A) :
    typeDGraphLieEquiv c A X = X ↔
      typeDGraphMatrix c A * (X : Matrix (I ⊕ I) (I ⊕ I) A) = X * typeDGraphMatrix c A := by
  rw [Subtype.ext_iff, typeDGraphLieEquiv_apply_val]
  constructor
  · intro h
    have := congrArg (fun Y => Y * typeDGraphMatrix c A) h
    simpa [mul_assoc] using this
  · intro h
    rw [h, mul_assoc, typeDGraphMatrix_mul_self, mul_one]

private theorem typeDGraphReindex_single (s t : I ⊕ I) (a : A) :
    Matrix.reindexAlgEquiv A A (typeDGraphIndex c) (Matrix.single s t a) =
      Matrix.single (typeDGraphIndex c s) (typeDGraphIndex c t) a := by
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  simp only [Matrix.submatrix_single_equiv, Equiv.symm_symm]

open TypeDStd

variable (n : ℕ) (hn : 4 ≤ n)

private theorem typeDGraphReindex_raising (i : Fin n) :
    Matrix.reindexAlgEquiv A A (typeDGraphIndex (forkRight n hn))
        (raisingMatrix n hn i) =
      raisingMatrix n hn (graphPermD n (by omega) i) := by
  have hac := forkLeft_ne_forkRight n hn
  have hchain : (forkLeft n hn : ℕ) + 1 < n := by simp; omega
  have hfr_not : ¬(forkRight n hn : ℕ) + 1 < n := by simp; omega
  by_cases hi : i = forkLeft n hn ∨ i = forkRight n hn
  · rcases hi with rfl | rfl <;>
      simp only [graphPermD_forkLeft, graphPermD_forkRight] <;>
      rw [raisingMatrix_eq_single_sub_single_of_chain n hn hchain,
        raisingMatrix_eq_single_sub_single_of_fork n hn (i := forkRight n hn) hfr_not] <;>
      rw [map_sub, typeDGraphReindex_single, typeDGraphReindex_single] <;>
      simp [hac]
  obtain ⟨hi, hi'⟩ := not_or.mp hi
  have hiv : (i : ℕ) ≠ n - 2 := by simpa [Fin.ext_iff] using hi
  have hiv' : (i : ℕ) ≠ n - 1 := by simpa [Fin.ext_iff] using hi'
  have hic : (i : ℕ) + 1 < n := by omega
  have hinc : chainNext n i hic ≠ forkRight n hn := by
    intro h
    have := congrArg Fin.val h
    simp only [chainNext_val, forkRight_val] at this
    omega
  rw [graphPermD_apply_of_ne_of_ne n (by omega) i hiv hiv',
    raisingMatrix_eq_single_sub_single_of_chain n hn hic]
  rw [map_sub, typeDGraphReindex_single, typeDGraphReindex_single]
  simp [hi', hinc]

/-- At the last hyperbolic pair, the diagram involution exchanges the raising and lowering
generators at the two terminal nodes and fixes the other root generators. -/
@[simp]
theorem typeDGraphLieEquiv_rootGenerator (k : Fin n ⊕ Fin n) :
    typeDGraphLieEquiv (forkRight n hn) A (rootGenerator n hn k) =
      rootGenerator n hn (Sum.map (graphPermD n (by omega)) (graphPermD n (by omega)) k) := by
  apply Subtype.ext
  rw [typeDGraphLieEquiv_apply_val, typeDGraphMatrix_conj]
  rcases k with i | i
  · simpa only [val_rootGenerator_inl, Sum.map_inl] using typeDGraphReindex_raising A n hn i
  · simp only [Sum.map_inr, val_rootGenerator_inr, loweringMatrix_eq_transpose]
    simpa only [Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex] using
      congrArg Matrix.transpose (typeDGraphReindex_raising A n hn i)

/-- The native graph involution acts on the Cartan generators by the same diagram permutation. -/
@[simp]
theorem typeDGraphLieEquiv_cartanGenerator (i : Fin n) :
    typeDGraphLieEquiv (forkRight n hn) A (cartanGenerator n hn i) =
      cartanGenerator n hn (graphPermD n (by omega) i) := by
  have hi : ⁅rootGenerator (K := A) n hn (.inl i), rootGenerator (K := A) n hn (.inr i)⁆ =
      cartanGenerator (K := A) n hn i := by simp
  rw [← hi, LieEquiv.map_lie, typeDGraphLieEquiv_rootGenerator, typeDGraphLieEquiv_rootGenerator]
  simp

end TauCeti
