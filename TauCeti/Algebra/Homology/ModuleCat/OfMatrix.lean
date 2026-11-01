/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Chain complexes of coordinate spaces given by matrices

Let `R` be a commutative ring, `n : α → ℕ` a family of ranks and `M i` a matrix with `n i` rows
and `n (i + 1)` columns, such that consecutive products `M i * M (i + 1)` vanish. Then
`ChainComplex.ofMatrix M hM` is the chain complex of coordinate spaces `Fin (n i) → R` whose
differential `Rⁿ⁽ⁱ⁺¹⁾ → Rⁿ⁽ⁱ⁾` is multiplication by `M i`. Its standard bases
(`ChainComplex.ofMatrixBasis`) make it a based complex whose differentials have the matrices
`M i` (`ChainComplex.toMatrix_ofMatrix_d`).

This is the usual way to write down a based finite free complex explicitly. For instance, the
matrices of the differentials of a based complex over `R`, mapped along a ring homomorphism
`R →+* S`, define in this way its scalar extension to `S`.
-/

public section

noncomputable section

open CategoryTheory Module Matrix

namespace ChainComplex

variable {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]
  {R : Type*} [CommRing R] {n : α → ℕ} (M : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) R)
  (hM : ∀ i, M i * M (i + 1) = 0)

/-- The chain complex of coordinate spaces `Fin (n i) → R` whose differential `Rⁿ⁽ⁱ⁺¹⁾ → Rⁿ⁽ⁱ⁾`
is multiplication by the matrix `M i`, given that consecutive products `M i * M (i + 1)` vanish. -/
@[expose] def ofMatrix : ChainComplex (ModuleCat R) α :=
  ChainComplex.of (fun i ↦ ModuleCat.of R (Fin (n i) → R))
    (fun i ↦ ModuleCat.ofHom (Matrix.toLin' (M i)))
    fun i ↦ by
      ext1
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ← Matrix.toLin'_mul, hM]
      simp

theorem ofMatrix_X (i : α) : (ofMatrix M hM).X i = ModuleCat.of R (Fin (n i) → R) :=
  rfl

theorem ofMatrix_d (i : α) :
    (ofMatrix M hM).d (i + 1) i = ModuleCat.ofHom (Matrix.toLin' (M i)) := by
  simp [ofMatrix]

@[simp]
theorem ofMatrix_d_apply (i : α) (x : (ofMatrix M hM).X (i + 1)) :
    ((ofMatrix M hM).d (i + 1) i).hom x = M i *ᵥ x := by
  rw [ofMatrix_d]
  rfl

/-- The standard basis of the coordinate space `Fin (n i) → R` in degree `i` of
`ChainComplex.ofMatrix M hM`. -/
def ofMatrixBasis (i : α) : Basis (Fin (n i)) R ((ofMatrix M hM).X i) :=
  Pi.basisFun R (Fin (n i))

@[simp]
theorem ofMatrixBasis_apply (i : α) (k : Fin (n i)) : ofMatrixBasis M hM i k = Pi.single k 1 :=
  Pi.basisFun_apply R (Fin (n i)) k

@[simp]
theorem ofMatrixBasis_repr (i : α) (x : (ofMatrix M hM).X i) (k : Fin (n i)) :
    (ofMatrixBasis M hM i).repr x k = x k :=
  Pi.basisFun_repr R (Fin (n i)) x k

/-- The matrix of the differential `Rⁿ⁽ⁱ⁺¹⁾ → Rⁿ⁽ⁱ⁾` of `ChainComplex.ofMatrix M hM` in the standard
bases is `M i`. -/
@[simp]
theorem toMatrix_ofMatrix_d (i : α) :
    LinearMap.toMatrix (ofMatrixBasis M hM (i + 1)) (ofMatrixBasis M hM i)
      ((ofMatrix M hM).d (i + 1) i).hom = M i := by
  rw [ofMatrix_d]
  exact LinearMap.toMatrix'_toLin' _

end ChainComplex
