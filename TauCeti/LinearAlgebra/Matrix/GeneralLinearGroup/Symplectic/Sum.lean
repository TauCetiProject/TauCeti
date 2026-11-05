/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.Realify

/-!
# Direct sums of symplectic matrices

The standard symplectic form `Matrix.J` on coordinates indexed by `l ⊕ l` pairs the coordinate
`inl i` with `inr i`. For two index types `n` and `m`, the coordinates `(n ⊕ m) ⊕ (n ⊕ m)` of
`R^{2(n + m)}` regroup, by `Equiv.sumSumSumComm`, into the coordinates `(n ⊕ n) ⊕ (m ⊕ m)` of
`R^{2n} × R^{2m}`, and through this regrouping `J (n ⊕ m)` is the block-diagonal matrix with
blocks `J n` and `J m` (`Matrix.symplecticSum_J`).

The **symplectic direct sum** `Matrix.symplecticSum A B` of a matrix `A` indexed by `n ⊕ n` and a
matrix `B` indexed by `m ⊕ m` is the block-diagonal matrix with blocks `A` and `B`, read in the
coordinates `(n ⊕ m) ⊕ (n ⊕ m)`. It is multiplicative and compatible with transposes, so it
carries symplectic matrices to symplectic matrices, orthogonal or unitary matrices to unitary
matrices and positive semidefinite matrices to positive semidefinite matrices. It induces the
group morphism `TauCeti.GLSymplectic.sum : Sp(2n, R) × Sp(2m, R) →* Sp(2(n + m), R)`. Realifying a
block-diagonal complex matrix gives the symplectic direct sum of the realifications
(`Matrix.realify_fromBlocks_zero`), which identifies the direct sum on the realified unitary
groups with the block sum `U(n) × U(m) → U(n + m)`.

This is the operation in the direct-sum axiom of the Maslov index of loops of symplectic
matrices.

## Main definitions

* `Matrix.symplecticSum`: the direct sum of matrices indexed by `n ⊕ n` and by `m ⊕ m`.
* `TauCeti.GLSymplectic.sum`: the direct sum `Sp(2n, R) × Sp(2m, R) →* Sp(2(n + m), R)`.

## Main results

* `Matrix.symplecticSum_J`: the standard symplectic form is the direct sum of standard forms.
* `Matrix.symplecticSum_mem_symplecticGroup`, `Matrix.symplecticSum_mem_unitaryGroup` and
  `Matrix.PosSemidef.symplecticSum`: the direct sum preserves symplectic, unitary and positive
  semidefinite matrices.
* `Matrix.realify_fromBlocks_zero`: realification turns block-diagonal complex matrices into
  symplectic direct sums.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2 (the direct sum of
  symplectic matrices in Theorem 2.2.12).
-/

public section

namespace Matrix

variable {n m R : Type*}

/-- The **symplectic direct sum** of a matrix `A` on the coordinates `n ⊕ n` and a matrix `B` on
the coordinates `m ⊕ m`: the block-diagonal matrix with blocks `A` and `B`, read in the coordinates
`(n ⊕ m) ⊕ (n ⊕ m)` through `Equiv.sumSumSumComm`, which pairs `inl i` with `inr i` in both
summands. -/
def symplecticSum [Zero R] (A : Matrix (n ⊕ n) (n ⊕ n) R) (B : Matrix (m ⊕ m) (m ⊕ m) R) :
    Matrix ((n ⊕ m) ⊕ (n ⊕ m)) ((n ⊕ m) ⊕ (n ⊕ m)) R :=
  (fromBlocks A 0 0 B).submatrix (Equiv.sumSumSumComm n m n m) (Equiv.sumSumSumComm n m n m)

/-- The symplectic direct sum is the regrouped block-diagonal matrix. -/
theorem symplecticSum_def [Zero R] (A : Matrix (n ⊕ n) (n ⊕ n) R)
    (B : Matrix (m ⊕ m) (m ⊕ m) R) :
    symplecticSum A B =
      (fromBlocks A 0 0 B).submatrix (Equiv.sumSumSumComm n m n m) (Equiv.sumSumSumComm n m n m) :=
  (rfl)

/-- The symplectic direct sum is multiplicative. -/
@[simp]
theorem symplecticSum_mul [Fintype n] [Fintype m] [NonUnitalNonAssocSemiring R]
    (A A' : Matrix (n ⊕ n) (n ⊕ n) R) (B B' : Matrix (m ⊕ m) (m ⊕ m) R) :
    symplecticSum (A * A') (B * B') = symplecticSum A B * symplecticSum A' B' := by
  rw [symplecticSum, symplecticSum, symplecticSum, submatrix_mul_equiv, fromBlocks_multiply]
  simp

/-- The direct sum of identity matrices is the identity. -/
@[simp]
theorem symplecticSum_one [DecidableEq n] [DecidableEq m] [Zero R] [One R] :
    symplecticSum (1 : Matrix (n ⊕ n) (n ⊕ n) R) (1 : Matrix (m ⊕ m) (m ⊕ m) R) = 1 := by
  rw [symplecticSum, fromBlocks_one, submatrix_one_equiv]

/-- The transpose of a direct sum is the direct sum of the transposes. -/
@[simp]
theorem symplecticSum_transpose [Zero R] (A : Matrix (n ⊕ n) (n ⊕ n) R)
    (B : Matrix (m ⊕ m) (m ⊕ m) R) : (symplecticSum A B)ᵀ = symplecticSum Aᵀ Bᵀ := by
  simp only [symplecticSum, transpose_submatrix, fromBlocks_transpose, transpose_zero]

/-- The conjugate transpose of a direct sum is the direct sum of the conjugate transposes. -/
@[simp]
theorem symplecticSum_conjTranspose [AddMonoid R] [StarAddMonoid R]
    (A : Matrix (n ⊕ n) (n ⊕ n) R) (B : Matrix (m ⊕ m) (m ⊕ m) R) :
    (symplecticSum A B)ᴴ = symplecticSum Aᴴ Bᴴ := by
  simp only [symplecticSum, conjTranspose_submatrix, fromBlocks_conjTranspose, conjTranspose_zero]

/-- The standard symplectic form on `R^{2(n + m)}` is the direct sum of the standard symplectic
forms on `R^{2n}` and `R^{2m}`. -/
theorem symplecticSum_J [DecidableEq n] [DecidableEq m] [CommRing R] :
    symplecticSum (J n R) (J m R) = J (n ⊕ m) R := by
  ext i j
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
    simp [symplecticSum, J, Equiv.sumSumSumComm, ← fromBlocks_one]

/-- The direct sum of two symplectic matrices is symplectic. -/
theorem symplecticSum_mem_symplecticGroup [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    [CommRing R] {A : Matrix (n ⊕ n) (n ⊕ n) R} {B : Matrix (m ⊕ m) (m ⊕ m) R}
    (hA : A ∈ symplecticGroup n R) (hB : B ∈ symplecticGroup m R) :
    symplecticSum A B ∈ symplecticGroup (n ⊕ m) R := by
  rw [SymplecticGroup.mem_iff] at hA hB ⊢
  rw [← symplecticSum_J, symplecticSum_transpose, ← symplecticSum_mul, ← symplecticSum_mul, hA,
    hB]

/-- The direct sum of two unitary matrices is unitary. -/
theorem symplecticSum_mem_unitaryGroup [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    [CommRing R] [StarRing R] {A : Matrix (n ⊕ n) (n ⊕ n) R} {B : Matrix (m ⊕ m) (m ⊕ m) R}
    (hA : A ∈ unitaryGroup (n ⊕ n) R) (hB : B ∈ unitaryGroup (m ⊕ m) R) :
    symplecticSum A B ∈ unitaryGroup ((n ⊕ m) ⊕ (n ⊕ m)) R := by
  rw [mem_unitaryGroup_iff] at hA hB ⊢
  rw [star_eq_conjTranspose, symplecticSum_conjTranspose, ← symplecticSum_mul,
    ← star_eq_conjTranspose, ← star_eq_conjTranspose, hA, hB, symplecticSum_one]

/-- The direct sum of two positive semidefinite matrices is positive semidefinite. -/
theorem PosSemidef.symplecticSum [Finite n] [Finite m] [CommRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] {A : Matrix (n ⊕ n) (n ⊕ n) R}
    {B : Matrix (m ⊕ m) (m ⊕ m) R} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.symplecticSum A B).PosSemidef := by
  have := Fintype.ofFinite n
  have := Fintype.ofFinite m
  rw [Matrix.symplecticSum, posSemidef_submatrix_equiv]
  rw [posSemidef_iff_dotProduct_mulVec] at hA hB ⊢
  refine ⟨hA.1.fromBlocks (by simp) hB.1, fun x ↦ ?_⟩
  rw [← Sum.elim_comp_inl_inr x, fromBlocks_mulVec, Function.star_sumElim,
    sumElim_dotProduct_sumElim]
  simpa using add_nonneg (hA.2 (x ∘ Sum.inl)) (hB.2 (x ∘ Sum.inr))

/-- Realification turns a block-diagonal complex matrix into the symplectic direct sum of the
realifications of its blocks. -/
theorem realify_fromBlocks_zero {𝕜 : Type*} [RCLike 𝕜] (U : Matrix n n 𝕜) (V : Matrix m m 𝕜) :
    (fromBlocks U 0 0 V).realify = symplecticSum U.realify V.realify := by
  ext i j
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
    simp [symplecticSum, Equiv.sumSumSumComm]

end Matrix

namespace TauCeti.GLSymplectic

open Matrix

variable {n m R : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [CommRing R]

/-- The direct sum `Sp(2n, R) × Sp(2m, R) →* Sp(2(n + m), R)` of symplectic matrices, by
`Matrix.symplecticSum`. -/
def sum : GLSymplectic n R × GLSymplectic m R →* GLSymplectic (n ⊕ m) R where
  toFun p :=
    ⟨⟨symplecticSum (p.1 : GL (n ⊕ n) R) (p.2 : GL (m ⊕ m) R),
      symplecticSum ((p.1 : GL (n ⊕ n) R)⁻¹ : GL (n ⊕ n) R) ((p.2 : GL (m ⊕ m) R)⁻¹ : GL _ R),
      by rw [← symplecticSum_mul, Units.mul_inv, Units.mul_inv, symplecticSum_one],
      by rw [← symplecticSum_mul, Units.inv_mul, Units.inv_mul, symplecticSum_one]⟩,
      mem_iff_mem_symplecticGroup.2 (symplecticSum_mem_symplecticGroup
        (mem_iff_mem_symplecticGroup.1 p.1.2) (mem_iff_mem_symplecticGroup.1 p.2.2))⟩
  map_one' := Subtype.ext (Units.ext (by simp))
  map_mul' p q := Subtype.ext (Units.ext (by simp))

/-- The direct sum of symplectic matrices is their symplectic direct sum as matrices. -/
@[simp]
theorem coe_sum (A : GLSymplectic n R) (B : GLSymplectic m R) :
    ((sum (A, B) : GL ((n ⊕ m) ⊕ (n ⊕ m)) R) : Matrix ((n ⊕ m) ⊕ (n ⊕ m)) _ R) =
      symplecticSum (A : GL (n ⊕ n) R) (B : GL (m ⊕ m) R) :=
  (rfl)

end TauCeti.GLSymplectic
