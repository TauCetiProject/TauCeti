/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Model
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Classical coordinates on the pinned type `Cₙ` lattices

The pinned type `Cₙ` datum `TauCeti.DynkinType.typeCSimplyConnectedRootDatum` writes its character
lattice in the fundamental-weight basis and its cocharacter lattice in the simple-coroot basis.
Both lattices are also the classical lattice `ℤ ^ n` with standard basis `e₀, …, e_{n-1}`, because
the simple coroots `eᵢ - eᵢ₊₁` and `e_{n-1}` of `Cₙ` form a basis of it. This file makes that
identification explicit, in the form a concrete group with diagonal torus `𝔾ₘⁿ` consumes.

The change of coordinates on characters sends `λ` to its pairings `(⟨λ, e_a⟩)_a` with the
classical basis, and the one on cocharacters sends `μ` to `(⟨e_a, μ⟩)_a`. They send the families
`TauCeti.DynkinType.TypeC.weight` and `TauCeti.DynkinType.TypeC.coweight` to the standard basis
vectors and carry the pinned dot-product pairing to the classical one. Both are integral with
integral inverse, since the matrices of the two families are inverse transposes of one another by
`TauCeti.DynkinType.TypeC.weight_dotProduct_coweight`.

## Main definitions

* `TauCeti.DynkinType.TypeC.classicalWeightEquiv`: classical coordinates on the character lattice.
* `TauCeti.DynkinType.TypeC.classicalCoweightEquiv`: classical coordinates on the cocharacter
  lattice.

## Main results

* `TauCeti.DynkinType.TypeC.classicalWeightEquiv_weight` and
  `TauCeti.DynkinType.TypeC.classicalCoweightEquiv_coweight`: `e_a` has classical coordinates the
  `a`-th standard basis vector in both lattices.
* `TauCeti.DynkinType.TypeC.classicalWeightEquiv_dotProduct_classicalCoweightEquiv`: the change of
  coordinates preserves the pairing.

## References

N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
-/

public section

namespace TauCeti

namespace DynkinType

namespace TypeC

open Matrix

variable {n : ℕ}

/-- The matrix whose `a`-th row is `weight n a`. -/
private def weightMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a => weight n a

/-- The matrix whose `a`-th row is `coweight n a`. -/
private def coweightMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a => coweight n a

/-- The matrix form of `weight_dotProduct_coweight`. -/
private lemma weightMatrix_mul_transpose_coweightMatrix :
    weightMatrix n * (coweightMatrix n)ᵀ = 1 := by
  ext a c
  rw [mul_apply, one_apply]
  simpa [weightMatrix, coweightMatrix, dotProduct, Fin.ext_iff] using
    weight_dotProduct_coweight (n := n) (a := (a : ℕ)) (c := (c : ℕ)) a.isLt

private lemma coweightMatrix_mul_transpose_weightMatrix :
    coweightMatrix n * (weightMatrix n)ᵀ = 1 := by
  rw [← transpose_transpose (coweightMatrix n), ← transpose_mul,
    weightMatrix_mul_transpose_coweightMatrix, transpose_one]

/-- **Classical coordinates on the pinned type `Cₙ` character lattice.** A character `λ`, written
in the fundamental-weight basis, is sent to its pairings `(⟨λ, e_a⟩)_a` with the classical basis. -/
noncomputable def classicalWeightEquiv (n : ℕ) : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  LinearEquiv.ofLinearMap (coweightMatrix n).mulVecLin (weightMatrix n)ᵀ.mulVecLin
    (by rw [← mulVecLin_mul, coweightMatrix_mul_transpose_weightMatrix, mulVecLin_one])
    (by
      rw [← mulVecLin_mul, mul_eq_one_comm.mp coweightMatrix_mul_transpose_weightMatrix,
        mulVecLin_one])

/-- **Classical coordinates on the pinned type `Cₙ` cocharacter lattice.** A cocharacter `μ`,
written in the simple-coroot basis, is sent to its pairings `(⟨e_a, μ⟩)_a` with the classical
basis. -/
noncomputable def classicalCoweightEquiv (n : ℕ) : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  LinearEquiv.ofLinearMap (weightMatrix n).mulVecLin (coweightMatrix n)ᵀ.mulVecLin
    (by rw [← mulVecLin_mul, weightMatrix_mul_transpose_coweightMatrix, mulVecLin_one])
    (by
      rw [← mulVecLin_mul, mul_eq_one_comm.mp weightMatrix_mul_transpose_coweightMatrix,
        mulVecLin_one])

/-- The `a`-th classical coordinate of a character is its pairing with `e_a`. -/
@[simp]
theorem classicalWeightEquiv_apply (x : Fin n → ℤ) (a : Fin n) :
    classicalWeightEquiv n x a = x ⬝ᵥ coweight n a := by
  simp [classicalWeightEquiv, coweightMatrix, mulVec, dotProduct_comm, -coweight_apply]

/-- The `a`-th classical coordinate of a cocharacter is the pairing of `e_a` with it. -/
@[simp]
theorem classicalCoweightEquiv_apply (y : Fin n → ℤ) (a : Fin n) :
    classicalCoweightEquiv n y a = weight n a ⬝ᵥ y := by
  simp [classicalCoweightEquiv, weightMatrix, mulVec, -weight_apply]

/-- The character `e_a` has the `a`-th standard basis vector as classical coordinates. -/
@[simp]
theorem classicalWeightEquiv_weight (a : Fin n) :
    classicalWeightEquiv n (weight n a) = Pi.single a 1 := by
  ext c
  rw [classicalWeightEquiv_apply, weight_dotProduct_coweight a.isLt, Pi.single_apply]
  simp [Fin.ext_iff, eq_comm]

/-- The cocharacter `e_a` has the `a`-th standard basis vector as classical coordinates. -/
@[simp]
theorem classicalCoweightEquiv_coweight (a : Fin n) :
    classicalCoweightEquiv n (coweight n a) = Pi.single a 1 := by
  ext c
  rw [classicalCoweightEquiv_apply, weight_dotProduct_coweight c.isLt, Pi.single_apply]
  simp [Fin.ext_iff]

/-- **The classical coordinates preserve the pairing.** The pinned dot product of a character and
a cocharacter is the dot product of their classical coordinates. -/
@[simp]
theorem classicalWeightEquiv_dotProduct_classicalCoweightEquiv (x y : Fin n → ℤ) :
    classicalWeightEquiv n x ⬝ᵥ classicalCoweightEquiv n y = x ⬝ᵥ y := by
  have hx : classicalWeightEquiv n x = (coweightMatrix n) *ᵥ x := by
    rw [classicalWeightEquiv, LinearEquiv.coe_ofLinearMap, mulVecLin_apply]
  have hy : classicalCoweightEquiv n y = (weightMatrix n) *ᵥ y := by
    rw [classicalCoweightEquiv, LinearEquiv.coe_ofLinearMap, mulVecLin_apply]
  rw [hx, hy, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul,
    mul_eq_one_comm.mp weightMatrix_mul_transpose_coweightMatrix, vecMul_one]

end TypeC

end DynkinType

end TauCeti
