/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Matrices and determinants in tower bases

Let `A` be an `R`-algebra with an `R`-basis `bA`, and let `M` be an `A`-module with an `A`-basis
`c`. The vectors `bA a • c k` form the `R`-basis `bA.smulTower' c` of `M`, indexed by pairs
`(k, a)`.

* `LinearMap.toMatrix_restrictScalars`: the matrix in tower bases of an `A`-linear map
  `f : M → M'`, viewed as an `R`-linear map, is the block matrix whose `(k, l)` block is the matrix
  `Algebra.leftMulMatrix bA x` of multiplication by the entry `x` of the matrix of `f` in the
  `A`-bases. This generalizes `LinearMap.restrictScalars_toMatrix` from endomorphisms to maps
  between two modules.
* `Module.Basis.det_smulTower'`: over commutative rings, the determinant in the basis
  `bA.smulTower' c` of the family `bA a • v k` is the norm `Algebra.norm R (c.det v)` of the
  determinant of `v` in the basis `c`.

The second statement is the form in which determinants over a finite extension are compared with
determinants over the base, for instance for the torsion of a based chain complex after
restricting its scalars.
-/

public section

open Module

section Semiring

variable {R A M M' ι ι' κ : Type*} [Fintype ι] [Finite ι'] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (bA : Basis ι R A) (c : Basis κ A M) (c' : Basis ι' A M')

/-- The matrix in tower bases of an `A`-linear map `f`, viewed as an `R`-linear map, is the block
matrix obtained by replacing each entry `x` of the matrix of `f` by the matrix of multiplication
by `x` in the basis `bA`. -/
theorem LinearMap.toMatrix_restrictScalars (f : M →ₗ[A] M') :
    (f.restrictScalars R).toMatrix (bA.smulTower' c) (bA.smulTower' c') =
      Matrix.comp ι' κ ι ι R ((f.toMatrix c c').map (Algebra.leftMulMatrix bA)) := by
  ext ⟨k, a⟩ ⟨l, b⟩
  simp [LinearMap.toMatrix_apply, Algebra.leftMulMatrix_apply, Basis.smulTower'_repr,
    Basis.smulTower'_apply, mul_comm]

end Semiring

section CommRing

variable {R A M ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M] [Module A M]
  [IsScalarTower R A M]

/-- The determinant, in the tower basis `bA.smulTower' c`, of the family of vectors `bA a • v k` is
the norm of the determinant of the family `v` in the basis `c`. -/
theorem Module.Basis.det_smulTower' (bA : Basis ι R A) (c : Basis κ A M) (v : κ → M) :
    (bA.smulTower' c).det (fun x ↦ bA x.2 • v x.1) = Algebra.norm R (c.det v) := by
  have : Module.Free R A := .of_basis bA
  have : Module.Free A M := .of_basis c
  -- Both determinants are determinants of the `A`-linear map sending `c k` to `v k`.
  set g : M →ₗ[A] M := c.constr ℕ v
  have hg : (bA.smulTower' c).toMatrix (fun x ↦ bA x.2 • v x.1) =
      LinearMap.toMatrix (bA.smulTower' c) (bA.smulTower' c) (g.restrictScalars R) := by
    ext i j
    simp [Basis.toMatrix_apply, LinearMap.toMatrix_apply, Basis.smulTower'_apply, g]
  rw [Basis.det_apply, hg, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, Basis.det_apply,
    Basis.toMatrix_eq_toMatrix_constr, LinearMap.det_toMatrix]

end CommRing
