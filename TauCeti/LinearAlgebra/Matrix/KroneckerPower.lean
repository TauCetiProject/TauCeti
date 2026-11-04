/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Kronecker powers of matrices

For a matrix `A` with rows indexed by `m`, columns indexed by `n` and a finite type `κ`, the
Kronecker power `Matrix.kroneckerPower κ A` is the matrix with rows indexed by `κ → m` and columns
indexed by `κ → n` whose `(v, u)` entry is `∏ i, A (v i) (u i)`. It is the matrix of `A` acting in
every factor of the `κ`-indexed tensor power, in the monomial bases.

The Kronecker power is multiplicative and commutes with transposition, so if `Aᵀ * A = 1` then
the Kronecker power satisfies the same identity. The Kronecker power of a diagonal matrix is
diagonal, and that of the matrix of an equivalence `f` is the matrix of the equivalence
`v ↦ f ∘ v` of index functions.

## Main definitions

* `Matrix.kroneckerPower`: the `κ`-indexed Kronecker power of a matrix.

## Main results

* `Matrix.kroneckerPower_mul`, `Matrix.kroneckerPower_one`, `Matrix.transpose_kroneckerPower`:
  the Kronecker power is multiplicative, sends `1` to `1` and commutes with transposition.
* `Matrix.transpose_kroneckerPower_mul_self`: the Kronecker power of a matrix with `Aᵀ * A = 1`
  satisfies the same identity.
* `Matrix.toMatrix_piTensorProductMap_mulVecLin`: the Kronecker power is the matrix of `A` acting
  in every factor of the tensor power, in the monomial basis.
* `Matrix.apply_comp_mul_prod_of_commute_kroneckerPower`: a matrix commuting with the Kronecker
  power of a monomial matrix is invariant under the relabelling of its indices, up to the weights.
* `Matrix.kroneckerPower_diagonal` and `Matrix.kroneckerPower_toMatrix_toPEquiv`: the Kronecker
  powers of diagonal and permutation-type matrices.
-/

public section

namespace Matrix

variable {R : Type*} {l m n : Type*} (κ : Type*)

/-- The **Kronecker power** of a matrix `A : Matrix m n R`: the matrix with rows indexed by
`κ → m` and columns indexed by `κ → n` whose `(v, u)` entry is `∏ i, A (v i) (u i)`, the matrix of
`A` acting in every factor of the `κ`-indexed tensor power. -/
def kroneckerPower [CommMonoid R] [Fintype κ] (A : Matrix m n R) : Matrix (κ → m) (κ → n) R :=
  Matrix.of fun v u => ∏ i, A (v i) (u i)

@[simp]
theorem kroneckerPower_apply [CommMonoid R] [Fintype κ] (A : Matrix m n R) (v : κ → m)
    (u : κ → n) :
    A.kroneckerPower κ v u = ∏ i, A (v i) (u i) :=
  (rfl)

variable {κ}

/-- The Kronecker power commutes with transposition. -/
@[simp]
theorem transpose_kroneckerPower [CommMonoid R] [Fintype κ] (A : Matrix m n R) :
    (A.kroneckerPower κ)ᵀ = Aᵀ.kroneckerPower κ :=
  (rfl)

/-- The Kronecker power of the identity matrix is the identity matrix. -/
@[simp]
theorem kroneckerPower_one [CommMonoidWithZero R] [DecidableEq n] [Fintype κ] :
    (1 : Matrix n n R).kroneckerPower κ = 1 := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]

/-- The Kronecker power is multiplicative: the `(v, u)` entry of `A^{⊗κ} * B^{⊗κ}` expands, by
distributing the product over the sums, into the product of the entries of `A * B`. -/
theorem kroneckerPower_mul [CommSemiring R] [Fintype m] [Fintype κ] [DecidableEq κ]
    (A : Matrix l m R) (B : Matrix m n R) :
    (A * B).kroneckerPower κ = A.kroneckerPower κ * B.kroneckerPower κ := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.mul_apply, Fintype.prod_sum, ← Finset.prod_mul_distrib]

/-- The Kronecker power of a matrix `A` with `Aᵀ * A = 1` satisfies the same identity. -/
theorem transpose_kroneckerPower_mul_self [CommSemiring R] [Fintype n] [DecidableEq n]
    [Fintype κ] [DecidableEq κ] {A : Matrix n n R} (hA : Aᵀ * A = 1) :
    (A.kroneckerPower κ)ᵀ * A.kroneckerPower κ = 1 := by
  rw [transpose_kroneckerPower, ← kroneckerPower_mul, hA, kroneckerPower_one]

/-- **The Kronecker power is the matrix of the tensor power.** The matrix of `A` acting in every
factor of the `κ`-indexed tensor power of `m → R`, in the monomial basis built from the standard
bases, is the Kronecker power of `A`. -/
theorem toMatrix_piTensorProductMap_mulVecLin [CommSemiring R] [Fintype m] [DecidableEq m]
    [Fintype κ] [DecidableEq κ] (A : Matrix m m R) :
    LinearMap.toMatrix (Basis.piTensorProduct fun _ : κ => Pi.basisFun R m)
        (Basis.piTensorProduct fun _ : κ => Pi.basisFun R m)
        (PiTensorProduct.map fun _ : κ => A.mulVecLin) =
      A.kroneckerPower κ := by
  ext v u
  simp [LinearMap.toMatrix_apply]

/-- **Commuting with the Kronecker power of a monomial matrix.** Let `A` be the monomial matrix
sending the `y`-th basis vector to `d y` times the `π y`-th one, so `A x y = d y` when `x = π y`
and `0` otherwise. If `M` commutes with the Kronecker power of `A`, then relabelling both indices
of an entry of `M` by `π` satisfies the cross-multiplied identity
`M (π ∘ v) (π ∘ u) * ∏ i, d (u i) = (∏ i, d (v i)) * M v u`,
with the column weight `∏ i, d (u i)` on the left and the row weight `∏ i, d (v i)` on the right.
When the column weight is invertible, the relabelled entry is therefore the original entry
multiplied by the row weight and divided by the column weight. -/
theorem apply_comp_mul_prod_of_commute_kroneckerPower [CommSemiring R] [Fintype m]
    [DecidableEq m] [Fintype κ] [DecidableEq κ] {M : Matrix (κ → m) (κ → m) R}
    (π : Equiv.Perm m) (d : m → R)
    (hM : Commute M ((Matrix.of fun x y => if x = π y then d y else 0).kroneckerPower κ))
    (v u : κ → m) :
    M (π ∘ v) (π ∘ u) * ∏ i, d (u i) = (∏ i, d (v i)) * M v u := by
  have hK (w x : κ → m) :
      (Matrix.of fun x y => if x = π y then d y else 0).kroneckerPower κ w x =
        if w = π ∘ x then ∏ i, d (x i) else 0 := by
    simp [Finset.prod_ite_zero, funext_iff]
  have h := congrFun (congrFun hM.eq (π ∘ v)) u
  have hinj (w : κ → m) : (π ∘ v = π ∘ w) ↔ v = w := π.injective.comp_left.eq_iff
  simp only [Matrix.mul_apply, hK, mul_ite, mul_zero, ite_mul, zero_mul, hinj] at h
  simpa using h
/-- The Kronecker power of a diagonal matrix is the diagonal matrix with entry `∏ i, d (v i)` at
the index function `v`. -/
@[simp]
theorem kroneckerPower_diagonal [CommMonoidWithZero R] [DecidableEq n] [Fintype κ] (d : n → R) :
    (diagonal d).kroneckerPower κ = diagonal fun v : κ → n => ∏ i, d (v i) := by
  ext v u
  simp [diagonal_apply, Finset.prod_ite_zero, funext_iff]

/-- The Kronecker power of the matrix of an equivalence `f : m ≃ n` is the matrix of the
equivalence `v ↦ f ∘ v` it induces on the index functions. -/
@[simp]
theorem kroneckerPower_toMatrix_toPEquiv [CommMonoidWithZero R] [DecidableEq n] [Fintype κ]
    (f : m ≃ n) :
    (f.toPEquiv.toMatrix : Matrix m n R).kroneckerPower κ =
      (Equiv.piCongrRight fun _ : κ => f).toPEquiv.toMatrix := by
  ext v u
  simp [Fintype.prod_boole, funext_iff]

end Matrix
