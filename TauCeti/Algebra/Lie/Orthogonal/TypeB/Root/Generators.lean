/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.DiagonalCartan
public import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Simple-root generators for the split orthogonal Lie algebra of type B

This file constructs integral matrices for both signs of the Bourbaki simple roots in the standard
split model `LieAlgebra.Orthogonal.typeB ι K`, together with the auxiliary difference-root family
`εᵢ - εⱼ`. For a difference root, the matrices are the usual paired matrix units. For a short
root `εᵢ`, the normalization forced by Mathlib's form matrix `diag(2, J)` is

```text
eᵢ = 2 Eᵢ₀ - E₀,-ᵢ,       fᵢ = E₀,ᵢ - 2 E-ᵢ,₀.
```

Thus `[eᵢ, fᵢ]` is `2(Eᵢᵢ - E-ᵢ,-ᵢ)`, the coroot of the short root `εᵢ`. Unlike a difference-root
operator, `eᵢ` is not square-zero over `ℤ`: its square is twice an integral matrix and its cube
vanishes. The corresponding
divided square is made explicit below. These integral divided powers are the data needed to
exponentiate the root operators over `ℤ` in the type-`B` Chevalley construction.

## Main definitions

* `TauCeti.typeBDifferenceRootGenerator`: the root vector for `εᵢ - εⱼ`.
* `TauCeti.typeBDifferenceCorootGenerator`: its diagonal coroot.
* `TauCeti.typeBShortRootGenerator`: the root vector for `εᵢ`.
* `TauCeti.typeBShortCorootGenerator`: its diagonal coroot.
* `TauCeti.typeBShortRootDividedSquare`: the integral divided square `eᵢ² / 2`.
* `TauCeti.typeBSimpleRootGenerator`: the Bourbaki-indexed simple-root vectors of `Bₙ₊₁`.
* `TauCeti.typeBSimpleRootGeneratorFamily`: those vectors and their opposites as one family
  indexed by `Fin (n + 1) ⊕ Fin (n + 1)`.

## References

The matrix realization and Bourbaki numbering follow Bourbaki, *Groupes et algèbres de Lie*,
Chapters 4--6, Planche II. The integral normalization of the short-root operators is the standard
one used in Carter, *Simple Groups of Lie Type*, Section 4.2. The ambient split form is Mathlib's
`LieAlgebra.Orthogonal.JB`.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {K : Type u}
variable {ι : Type*} [DecidableEq ι]

/-! ### Difference roots `εᵢ - εⱼ` -/

section AddGroupWithOne

variable [AddGroupWithOne K]

/-- The ambient root matrix for the long type-`B` root `εᵢ - εⱼ`; the inequality witness
excludes the degenerate zero-weight case. -/
def typeBDifferenceRootMatrix (i j : ι) (_hij : i ≠ j) :
    Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  single (.inr (.inl i)) (.inr (.inl j)) 1 -
    single (.inr (.inr j)) (.inr (.inr i)) 1

/-- The difference-root matrix as a difference of two matrix units. -/
theorem typeBDifferenceRootMatrix_def (i j : ι) (hij : i ≠ j) :
    typeBDifferenceRootMatrix (K := K) i j hij =
      single (.inr (.inl i)) (.inr (.inl j)) 1 -
        single (.inr (.inr j)) (.inr (.inr i)) 1 :=
  (rfl)

end AddGroupWithOne

section Ring

variable [Ring K] [Fintype ι]

/-- Two difference-root matrices bracket to zero when their directed index pairs cannot
concatenate in either order. -/
theorem typeBDifferenceRootMatrix_lie_differenceRootMatrix_of_ne (i j k l : ι)
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) :
    ⁅typeBDifferenceRootMatrix (K := K) i j hij,
      typeBDifferenceRootMatrix (K := K) k l hkl⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBDifferenceRootMatrix_def, mul_sub, sub_mul, Matrix.single_mul_single_of_ne,
    hjk, hjk.symm, hil, hil.symm]

/-- The bracket of two concatenated difference-root matrices is the difference-root matrix for
the concatenated index pair. -/
theorem typeBDifferenceRootMatrix_lie_differenceRootMatrix_chain (i j k l : ι)
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j = k) (hil : i ≠ l) :
    ⁅typeBDifferenceRootMatrix (K := K) i j hij, typeBDifferenceRootMatrix (K := K) k l hkl⁆ =
      typeBDifferenceRootMatrix (K := K) i l hil := by
  subst k
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBDifferenceRootMatrix_def, mul_sub, sub_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, hil, hil.symm]

end Ring

variable [CommRing K] [Fintype ι]

/-- The difference-root matrix sends the basis vector at `+j` to the one at `+i` and the basis
vector at `-i` to minus the one at `-j`, and kills every other basis vector. -/
theorem toLinAlgEquiv_typeBDifferenceRootMatrix_apply_basis {M : Type*} [AddCommGroup M]
    [Module K M]
    (bas : Module.Basis (Unit ⊕ ι ⊕ ι) K M) (i j : ι) (hij : i ≠ j)
    (c : Unit ⊕ ι ⊕ ι) :
    Matrix.toLinAlgEquiv bas (typeBDifferenceRootMatrix i j hij) (bas c) =
      (if .inr (.inl j) = c then bas (.inr (.inl i)) else 0) -
        if .inr (.inr i) = c then bas (.inr (.inr j)) else 0 := by
  rw [typeBDifferenceRootMatrix, map_sub, LinearMap.sub_apply,
    toLinAlgEquiv_single_apply_basis, toLinAlgEquiv_single_apply_basis]
  simp

/-- The difference-root matrix is skew-adjoint for the split odd orthogonal form. -/
theorem typeBDifferenceRootMatrix_mem_typeB (i j : ι) (hij : i ≠ j) :
    typeBDifferenceRootMatrix (K := K) i j hij ∈ LieAlgebra.Orthogonal.typeB ι K := by
  rw [LieAlgebra.Orthogonal.typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- Unfold subtype membership to expose the ambient skew-adjoint matrix equation.
  change (typeBDifferenceRootMatrix (K := K) i j hij)ᵀ * LieAlgebra.Orthogonal.JB ι K =
    LieAlgebra.Orthogonal.JB ι K * (-typeBDifferenceRootMatrix (K := K) i j hij)
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [typeBDifferenceRootMatrix, LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD,
      Matrix.mul_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]
  all_goals
    by_cases hia : i = a <;> by_cases hja : j = a <;>
      by_cases hib : i = b <;> by_cases hjb : j = b <;> simp_all <;> aesop

/-- The root vector `e_{εᵢ-εⱼ}` in the split type-`B` Lie algebra. -/
def typeBDifferenceRootGenerator (i j : ι) (hij : i ≠ j) :
    LieAlgebra.Orthogonal.typeB ι K :=
  ⟨typeBDifferenceRootMatrix i j hij, typeBDifferenceRootMatrix_mem_typeB i j hij⟩

/-- The underlying matrix of `typeBDifferenceRootGenerator`. -/
@[simp]
theorem coe_typeBDifferenceRootGenerator (i j : ι) (hij : i ≠ j) :
    (typeBDifferenceRootGenerator (K := K) i j hij :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBDifferenceRootMatrix i j hij :=
  (rfl)

/-- The diagonal coroot matrix paired with the long root `εᵢ - εⱼ`; the inequality witness
excludes the degenerate zero-weight case. -/
def typeBDifferenceCorootMatrix (i j : ι) (_hij : i ≠ j) :
    Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  typeBDiagonalMatrix (Pi.single i 1 - Pi.single j 1)

/-- The coroot `h_{εᵢ-εⱼ}` of the long root `εᵢ - εⱼ` in the split type-`B` Lie algebra. -/
def typeBDifferenceCorootGenerator (i j : ι) (hij : i ≠ j) : LieAlgebra.Orthogonal.typeB ι K :=
  ⟨typeBDifferenceCorootMatrix i j hij, typeBDiagonalMatrix_mem_typeB _⟩

/-- The underlying matrix of `typeBDifferenceCorootGenerator`. -/
@[simp]
theorem coe_typeBDifferenceCorootGenerator (i j : ι) (hij : i ≠ j) :
    (typeBDifferenceCorootGenerator (K := K) i j hij :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBDifferenceCorootMatrix i j hij :=
  (rfl)

/-- The coroot of the long root `εᵢ - εⱼ` has coordinate vector `εᵢ - εⱼ` in the split diagonal
Cartan. -/
theorem typeBDifferenceCorootGenerator_eq_diagonal (i j : ι) (hij : i ≠ j) :
    typeBDifferenceCorootGenerator (K := K) i j hij =
      ((typeBDiagonalEquiv (K := K) (ι := ι) (Pi.single i 1 - Pi.single j 1) :
        typeBDiagonalCartan K ι) : LieAlgebra.Orthogonal.typeB ι K) := by
  apply Subtype.ext
  rw [coe_typeBDiagonalEquiv_apply]
  rfl

/-- Opposite difference-root vectors bracket to their diagonal coroot. -/
@[simp]
theorem typeBDifferenceRootGenerator_lie_swap (i j : ι) (hij : i ≠ j) :
    ⁅typeBDifferenceRootGenerator (K := K) i j hij,
      typeBDifferenceRootGenerator (K := K) j i hij.symm⁆ =
      typeBDifferenceCorootGenerator i j hij := by
  apply Subtype.ext
  -- The subtype bracket reduces definitionally to the ambient matrix commutator.
  change typeBDifferenceRootMatrix (K := K) i j hij * typeBDifferenceRootMatrix j i hij.symm -
      typeBDifferenceRootMatrix j i hij.symm * typeBDifferenceRootMatrix i j hij =
        typeBDifferenceCorootMatrix i j hij
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [typeBDifferenceRootMatrix, typeBDifferenceCorootMatrix, typeBDiagonalMatrix_apply,
      mul_sub, sub_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
      Matrix.single_apply, Pi.single_apply]
  all_goals aesop

/-- Every difference-root matrix is square-zero. -/
theorem typeBDifferenceRootMatrix_mul_self (i j : ι) (hij : i ≠ j) :
    typeBDifferenceRootMatrix (K := K) i j hij * typeBDifferenceRootMatrix i j hij = 0 := by
  simp [typeBDifferenceRootMatrix, mul_sub, sub_mul, Matrix.single_mul_single_of_ne, hij,
    hij.symm]

/-! ### Short roots -/

/-- The ambient root matrix for the short type-`B` root `εᵢ`, with the integral Chevalley
normalization adapted to the middle coefficient `2` in `LieAlgebra.Orthogonal.JB`. -/
def typeBShortRootMatrix (i : ι) : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  single (.inr (.inl i)) (.inl ()) 2 - single (.inl ()) (.inr (.inr i)) 1

omit [Fintype ι] in
/-- The positive short type-`B` root matrix as `2 Eᵢ₀ - E₀,₋ᵢ`. -/
theorem typeBShortRootMatrix_def (i : ι) :
    typeBShortRootMatrix (K := K) i =
      single (.inr (.inl i)) (.inl ()) 2 - single (.inl ()) (.inr (.inr i)) 1 :=
  (rfl)

/-- The ambient root matrix for the opposite short root `-εᵢ`. -/
def typeBShortNegativeRootMatrix (i : ι) :
    Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  single (.inl ()) (.inr (.inl i)) 1 - single (.inr (.inr i)) (.inl ()) 2

omit [Fintype ι] in
/-- The negative short type-`B` root matrix as `E₀ᵢ - 2 E₋ᵢ,₀`. -/
theorem typeBShortNegativeRootMatrix_def (i : ι) :
    typeBShortNegativeRootMatrix (K := K) i =
      single (.inl ()) (.inr (.inl i)) 1 - single (.inr (.inr i)) (.inl ()) 2 :=
  (rfl)

/-- The positive short-root matrix acts on the coordinate basis only through the middle and
negative summands. -/
theorem toLinAlgEquiv_typeBShortRootMatrix_apply_basis {M : Type*} [AddCommGroup M] [Module K M]
    (bas : Module.Basis (Unit ⊕ ι ⊕ ι) K M) (i : ι) (c : Unit ⊕ ι ⊕ ι) :
    Matrix.toLinAlgEquiv bas (typeBShortRootMatrix i) (bas c) =
      (if .inl () = c then (2 : K) • bas (.inr (.inl i)) else 0) -
        if .inr (.inr i) = c then bas (.inl ()) else 0 := by
  rw [typeBShortRootMatrix, map_sub, LinearMap.sub_apply,
    toLinAlgEquiv_single_apply_basis, toLinAlgEquiv_single_apply_basis]
  simp

/-- The negative short-root matrix acts on the coordinate basis only through the positive and
middle summands. -/
theorem toLinAlgEquiv_typeBShortNegativeRootMatrix_apply_basis {M : Type*} [AddCommGroup M]
    [Module K M] (bas : Module.Basis (Unit ⊕ ι ⊕ ι) K M) (i : ι)
    (c : Unit ⊕ ι ⊕ ι) :
    Matrix.toLinAlgEquiv bas (typeBShortNegativeRootMatrix i) (bas c) =
      (if .inr (.inl i) = c then bas (.inl ()) else 0) -
        if .inl () = c then (2 : K) • bas (.inr (.inr i)) else 0 := by
  rw [typeBShortNegativeRootMatrix, map_sub, LinearMap.sub_apply,
    toLinAlgEquiv_single_apply_basis, toLinAlgEquiv_single_apply_basis]
  simp

/-- The bracket of a positive short type-`B` root matrix with a difference-root matrix. -/
theorem typeBShortRootMatrix_lie_differenceRootMatrix (i k l : ι) (hkl : k ≠ l) :
    ⁅typeBShortRootMatrix (K := K) i, typeBDifferenceRootMatrix (K := K) k l hkl⁆ =
      -(if i = l then typeBShortRootMatrix (K := K) k else 0) := by
  rw [LieRing.of_associative_ring_bracket]
  split_ifs with hil
  · subst l
    simp [typeBShortRootMatrix_def, typeBDifferenceRootMatrix_def, mul_sub, sub_mul,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]
  · simp [typeBShortRootMatrix_def, typeBDifferenceRootMatrix_def, mul_sub, sub_mul,
      Matrix.single_mul_single_of_ne, hil, Ne.symm hil]

/-- The bracket of a negative short type-`B` root matrix with a difference-root matrix. -/
theorem typeBShortNegativeRootMatrix_lie_differenceRootMatrix (i k l : ι) (hkl : k ≠ l) :
    ⁅typeBShortNegativeRootMatrix (K := K) i, typeBDifferenceRootMatrix (K := K) k l hkl⁆ =
      if i = k then typeBShortNegativeRootMatrix (K := K) l else 0 := by
  rw [LieRing.of_associative_ring_bracket]
  split_ifs with hik
  · subst k
    simp [typeBShortNegativeRootMatrix_def, typeBDifferenceRootMatrix_def, mul_sub, sub_mul,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]
  · simp [typeBShortNegativeRootMatrix_def, typeBDifferenceRootMatrix_def, mul_sub, sub_mul,
      Matrix.single_mul_single_of_ne, hik, Ne.symm hik]

/-- The positive short-root matrix is skew-adjoint for the split odd orthogonal form. -/
theorem typeBShortRootMatrix_mem_typeB (i : ι) :
    typeBShortRootMatrix (K := K) i ∈ LieAlgebra.Orthogonal.typeB ι K := by
  rw [LieAlgebra.Orthogonal.typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- Unfold subtype membership to expose the ambient skew-adjoint matrix equation.
  change (typeBShortRootMatrix (K := K) i)ᵀ * LieAlgebra.Orthogonal.JB ι K =
    LieAlgebra.Orthogonal.JB ι K * (-typeBShortRootMatrix (K := K) i)
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [typeBShortRootMatrix, LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD,
      Matrix.mul_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- The negative short-root matrix is skew-adjoint for the split odd orthogonal form. -/
theorem typeBShortNegativeRootMatrix_mem_typeB (i : ι) :
    typeBShortNegativeRootMatrix (K := K) i ∈ LieAlgebra.Orthogonal.typeB ι K := by
  rw [LieAlgebra.Orthogonal.typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- Unfold subtype membership to expose the ambient skew-adjoint matrix equation.
  change (typeBShortNegativeRootMatrix (K := K) i)ᵀ * LieAlgebra.Orthogonal.JB ι K =
    LieAlgebra.Orthogonal.JB ι K * (-typeBShortNegativeRootMatrix (K := K) i)
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [typeBShortNegativeRootMatrix, LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD,
      Matrix.mul_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- The short-root vector `e_{εᵢ}` in the split type-`B` Lie algebra. -/
def typeBShortRootGenerator (i : ι) : LieAlgebra.Orthogonal.typeB ι K :=
  ⟨typeBShortRootMatrix i, typeBShortRootMatrix_mem_typeB i⟩

/-- The opposite short-root vector `f_{εᵢ} = e_{-εᵢ}`. -/
def typeBShortNegativeRootGenerator (i : ι) : LieAlgebra.Orthogonal.typeB ι K :=
  ⟨typeBShortNegativeRootMatrix i, typeBShortNegativeRootMatrix_mem_typeB i⟩

/-- The underlying matrix of `typeBShortRootGenerator`. -/
@[simp]
theorem coe_typeBShortRootGenerator (i : ι) :
    (typeBShortRootGenerator (K := K) i :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBShortRootMatrix i :=
  (rfl)

/-- The underlying matrix of `typeBShortNegativeRootGenerator`. -/
@[simp]
theorem coe_typeBShortNegativeRootGenerator (i : ι) :
    (typeBShortNegativeRootGenerator (K := K) i :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBShortNegativeRootMatrix i :=
  (rfl)

/-! ### Diagonal action on root generators -/

/-- A split diagonal element acts on the root vector of weight `εᵢ - εⱼ` by that
weight. -/
@[simp]
theorem typeBDiagonalMatrix_lie_differenceRootGenerator (d : ι → K) (i j : ι) (hij : i ≠ j) :
    ⁅(⟨typeBDiagonalMatrix d, typeBDiagonalMatrix_mem_typeB d⟩ :
        LieAlgebra.Orthogonal.typeB ι K), typeBDifferenceRootGenerator (K := K) i j hij⁆ =
      (d i - d j) • typeBDifferenceRootGenerator i j hij := by
  have hd := typeBDiagonalMatrix_mem_diagonalCartan (K := K) d
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, coe_typeBDifferenceRootGenerator,
    typeBDifferenceRootMatrix_def, lie_sub, lie_single_of_mem_diagonalCartan hd,
    lie_single_of_mem_diagonalCartan hd, smul_sub]
  simp [sub_eq_add_neg, add_comm]

/-- A split diagonal element acts on the positive short-root vector of weight `εᵢ`. -/
@[simp]
theorem typeBDiagonalMatrix_lie_shortRootGenerator (d : ι → K) (i : ι) :
    ⁅(⟨typeBDiagonalMatrix d, typeBDiagonalMatrix_mem_typeB d⟩ :
        LieAlgebra.Orthogonal.typeB ι K), typeBShortRootGenerator (K := K) i⁆ =
      d i • typeBShortRootGenerator i := by
  have hd := typeBDiagonalMatrix_mem_diagonalCartan (K := K) d
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, coe_typeBShortRootGenerator,
    typeBShortRootMatrix_def, lie_sub, lie_single_of_mem_diagonalCartan hd,
    lie_single_of_mem_diagonalCartan hd, smul_sub]
  simp

/-- A split diagonal element acts on the negative short-root vector of weight `-εᵢ`. -/
@[simp]
theorem typeBDiagonalMatrix_lie_shortNegativeRootGenerator (d : ι → K) (i : ι) :
    ⁅(⟨typeBDiagonalMatrix d, typeBDiagonalMatrix_mem_typeB d⟩ :
        LieAlgebra.Orthogonal.typeB ι K), typeBShortNegativeRootGenerator (K := K) i⁆ =
      -(d i) • typeBShortNegativeRootGenerator i := by
  have hd := typeBDiagonalMatrix_mem_diagonalCartan (K := K) d
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, coe_typeBShortNegativeRootGenerator,
    typeBShortNegativeRootMatrix_def, lie_sub, lie_single_of_mem_diagonalCartan hd,
    lie_single_of_mem_diagonalCartan hd, smul_sub]
  simp

/-- The diagonal coroot `2εᵢ` of the short root `εᵢ`, in the standard type-`B` coordinates. -/
def typeBShortCorootMatrix (i : ι) : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  typeBDiagonalMatrix (2 • Pi.single i 1)

/-- The coroot `h_{εᵢ}` of the short root `εᵢ` in the split type-`B` Lie algebra. -/
def typeBShortCorootGenerator (i : ι) : LieAlgebra.Orthogonal.typeB ι K :=
  ⟨typeBShortCorootMatrix i, typeBDiagonalMatrix_mem_typeB _⟩

/-- The underlying matrix of `typeBShortCorootGenerator`. -/
@[simp]
theorem coe_typeBShortCorootGenerator (i : ι) :
    (typeBShortCorootGenerator (K := K) i :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBShortCorootMatrix i :=
  (rfl)

/-- The coroot of the short root `εᵢ` has coordinate vector `2εᵢ` in the split diagonal Cartan. -/
theorem typeBShortCorootGenerator_eq_diagonal (i : ι) :
    typeBShortCorootGenerator (K := K) i =
      ((typeBDiagonalEquiv (K := K) (ι := ι) (2 • Pi.single i 1) :
        typeBDiagonalCartan K ι) : LieAlgebra.Orthogonal.typeB ι K) := by
  apply Subtype.ext
  rw [coe_typeBDiagonalEquiv_apply]
  rfl

/-- The positive and negative short-root vectors bracket to the coroot of `εᵢ`. -/
@[simp]
theorem typeBShortRootGenerator_lie_negative (i : ι) :
    ⁅typeBShortRootGenerator (K := K) i, typeBShortNegativeRootGenerator (K := K) i⁆ =
      typeBShortCorootGenerator i := by
  apply Subtype.ext
  -- The subtype bracket reduces definitionally to the ambient matrix commutator.
  change typeBShortRootMatrix (K := K) i * typeBShortNegativeRootMatrix i -
      typeBShortNegativeRootMatrix i * typeBShortRootMatrix i = typeBShortCorootMatrix i
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [typeBShortRootMatrix, typeBShortNegativeRootMatrix, typeBShortCorootMatrix,
      typeBDiagonalMatrix_apply, mul_sub, sub_mul, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne, Matrix.single_apply, Pi.single_apply]
  all_goals aesop

/-- The integral divided square `e_{εᵢ}^{(2)}` of a positive short-root vector. -/
def typeBShortRootDividedSquare (i : ι) :
    Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  -single (.inr (.inl i)) (.inr (.inr i)) 1

/-- The square of a positive short-root vector is twice its integral divided square. -/
theorem typeBShortRootMatrix_mul_self (i : ι) :
    typeBShortRootMatrix (K := K) i * typeBShortRootMatrix i =
      2 • typeBShortRootDividedSquare i := by
  simp [typeBShortRootMatrix, typeBShortRootDividedSquare, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]

/-- Positive short-root vectors have nilpotence degree at most three. -/
theorem typeBShortRootMatrix_cube (i : ι) :
    typeBShortRootMatrix (K := K) i * typeBShortRootMatrix i * typeBShortRootMatrix i = 0 := by
  rw [typeBShortRootMatrix_mul_self, Matrix.smul_mul]
  simp [typeBShortRootMatrix, typeBShortRootDividedSquare, mul_sub,
    Matrix.single_mul_single_of_ne]

/-- The integral divided square `f_{εᵢ}^{(2)}` of a negative short-root vector. -/
def typeBShortNegativeRootDividedSquare (i : ι) :
    Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  -single (.inr (.inr i)) (.inr (.inl i)) 1

/-- The square of a negative short-root vector is twice its integral divided square. -/
theorem typeBShortNegativeRootMatrix_mul_self (i : ι) :
    typeBShortNegativeRootMatrix (K := K) i * typeBShortNegativeRootMatrix i =
      2 • typeBShortNegativeRootDividedSquare i := by
  simp [typeBShortNegativeRootMatrix, typeBShortNegativeRootDividedSquare, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]

/-- Negative short-root vectors have nilpotence degree at most three. -/
theorem typeBShortNegativeRootMatrix_cube (i : ι) :
    typeBShortNegativeRootMatrix (K := K) i * typeBShortNegativeRootMatrix i *
      typeBShortNegativeRootMatrix i = 0 := by
  rw [typeBShortNegativeRootMatrix_mul_self, Matrix.smul_mul]
  simp [typeBShortNegativeRootMatrix, typeBShortNegativeRootDividedSquare, mul_sub,
    Matrix.single_mul_single_of_ne]

/-! ### The Bourbaki simple system -/

variable {n : ℕ}

/-- The positive simple-root matrices of `Bₙ₊₁` in Bourbaki order. The first `n` nodes are
the long roots `εⱼ - εⱼ₊₁`, and the last node is the short root `εₙ`. -/
def typeBSimpleRootMatrix (i : Fin (n + 1)) :
    Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K :=
  Fin.lastCases (typeBShortRootMatrix (Fin.last n))
    (fun j => typeBDifferenceRootMatrix j.castSucc j.succ (ne_of_lt j.castSucc_lt_succ)) i

/-- The negative simple-root matrices of `Bₙ₊₁` in Bourbaki order. -/
def typeBSimpleNegativeRootMatrix (i : Fin (n + 1)) :
    Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K :=
  Fin.lastCases (typeBShortNegativeRootMatrix (Fin.last n))
    (fun j => typeBDifferenceRootMatrix j.succ j.castSucc (ne_of_gt j.castSucc_lt_succ)) i

/-- The simple coroot matrices of `Bₙ₊₁` in Bourbaki order. -/
def typeBSimpleCorootMatrix (i : Fin (n + 1)) :
    Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K :=
  Fin.lastCases (typeBShortCorootMatrix (Fin.last n))
    (fun j => typeBDifferenceCorootMatrix j.castSucc j.succ (ne_of_lt j.castSucc_lt_succ)) i

@[simp]
theorem typeBSimpleRootMatrix_last :
    typeBSimpleRootMatrix (K := K) (Fin.last n) =
      typeBShortRootMatrix (Fin.last n) := by
  simp [typeBSimpleRootMatrix]

@[simp]
theorem typeBSimpleRootMatrix_castSucc (j : Fin n) :
    typeBSimpleRootMatrix (K := K) j.castSucc =
      typeBDifferenceRootMatrix j.castSucc j.succ (ne_of_lt j.castSucc_lt_succ) := by
  simp [typeBSimpleRootMatrix]

@[simp]
theorem typeBSimpleNegativeRootMatrix_last :
    typeBSimpleNegativeRootMatrix (K := K) (Fin.last n) =
      typeBShortNegativeRootMatrix (Fin.last n) := by
  simp [typeBSimpleNegativeRootMatrix]

@[simp]
theorem typeBSimpleNegativeRootMatrix_castSucc (j : Fin n) :
    typeBSimpleNegativeRootMatrix (K := K) j.castSucc =
      typeBDifferenceRootMatrix j.succ j.castSucc (ne_of_gt j.castSucc_lt_succ) := by
  simp [typeBSimpleNegativeRootMatrix]

@[simp]
theorem typeBSimpleCorootMatrix_last :
    typeBSimpleCorootMatrix (K := K) (Fin.last n) =
      typeBShortCorootMatrix (Fin.last n) := by
  simp [typeBSimpleCorootMatrix]

@[simp]
theorem typeBSimpleCorootMatrix_castSucc (j : Fin n) :
    typeBSimpleCorootMatrix (K := K) j.castSucc =
      typeBDifferenceCorootMatrix j.castSucc j.succ (ne_of_lt j.castSucc_lt_succ) := by
  simp [typeBSimpleCorootMatrix]

/-- Every Bourbaki simple-root matrix belongs to the split type-`B` Lie algebra. -/
theorem typeBSimpleRootMatrix_mem_typeB (i : Fin (n + 1)) :
    typeBSimpleRootMatrix (K := K) i ∈ LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [typeBSimpleRootMatrix_last]
    exact typeBShortRootMatrix_mem_typeB (K := K) _
  · rw [typeBSimpleRootMatrix_castSucc]
    exact typeBDifferenceRootMatrix_mem_typeB (K := K) j.castSucc j.succ
      (ne_of_lt j.castSucc_lt_succ)

/-- Every negative Bourbaki simple-root matrix belongs to the split type-`B` Lie algebra. -/
theorem typeBSimpleNegativeRootMatrix_mem_typeB (i : Fin (n + 1)) :
    typeBSimpleNegativeRootMatrix (K := K) i ∈
      LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [typeBSimpleNegativeRootMatrix_last]
    exact typeBShortNegativeRootMatrix_mem_typeB (K := K) _
  · rw [typeBSimpleNegativeRootMatrix_castSucc]
    exact typeBDifferenceRootMatrix_mem_typeB (K := K) j.succ j.castSucc
      (ne_of_gt j.castSucc_lt_succ)

/-- The positive simple-root vector `eᵢ` for the Bourbaki pinning of `Bₙ₊₁`. -/
def typeBSimpleRootGenerator (i : Fin (n + 1)) :
    LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K :=
  ⟨typeBSimpleRootMatrix i, typeBSimpleRootMatrix_mem_typeB i⟩

/-- The negative simple-root vector `fᵢ` for the Bourbaki pinning of `Bₙ₊₁`. -/
def typeBSimpleNegativeRootGenerator (i : Fin (n + 1)) :
    LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K :=
  ⟨typeBSimpleNegativeRootMatrix i, typeBSimpleNegativeRootMatrix_mem_typeB i⟩

/-- The simple coroot `hᵢ` for the Bourbaki pinning of `Bₙ₊₁`. -/
def typeBSimpleCorootGenerator (i : Fin (n + 1)) :
    LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K :=
  Fin.lastCases (typeBShortCorootGenerator (Fin.last n))
    (fun j => typeBDifferenceCorootGenerator j.castSucc j.succ (ne_of_lt j.castSucc_lt_succ)) i

@[simp]
theorem typeBSimpleRootGenerator_last :
    typeBSimpleRootGenerator (K := K) (Fin.last n) =
      typeBShortRootGenerator (Fin.last n) := by
  apply Subtype.ext
  simp [typeBSimpleRootGenerator]

@[simp]
theorem typeBSimpleRootGenerator_castSucc (j : Fin n) :
    typeBSimpleRootGenerator (K := K) j.castSucc =
      typeBDifferenceRootGenerator j.castSucc j.succ (ne_of_lt j.castSucc_lt_succ) := by
  apply Subtype.ext
  simp [typeBSimpleRootGenerator]

@[simp]
theorem typeBSimpleNegativeRootGenerator_last :
    typeBSimpleNegativeRootGenerator (K := K) (Fin.last n) =
      typeBShortNegativeRootGenerator (Fin.last n) := by
  apply Subtype.ext
  simp [typeBSimpleNegativeRootGenerator]

@[simp]
theorem typeBSimpleNegativeRootGenerator_castSucc (j : Fin n) :
    typeBSimpleNegativeRootGenerator (K := K) j.castSucc =
      typeBDifferenceRootGenerator j.succ j.castSucc (ne_of_gt j.castSucc_lt_succ) := by
  apply Subtype.ext
  simp [typeBSimpleNegativeRootGenerator]

@[simp]
theorem typeBSimpleCorootGenerator_last :
    typeBSimpleCorootGenerator (K := K) (Fin.last n) =
      typeBShortCorootGenerator (Fin.last n) := by
  simp [typeBSimpleCorootGenerator]

@[simp]
theorem typeBSimpleCorootGenerator_castSucc (j : Fin n) :
    typeBSimpleCorootGenerator (K := K) j.castSucc =
      typeBDifferenceCorootGenerator j.castSucc j.succ (ne_of_lt j.castSucc_lt_succ) := by
  simp [typeBSimpleCorootGenerator]

@[simp]
theorem coe_typeBSimpleRootGenerator (i : Fin (n + 1)) :
    (typeBSimpleRootGenerator (K := K) i :
      Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K) =
      typeBSimpleRootMatrix i := by
  simp [typeBSimpleRootGenerator]

@[simp]
theorem coe_typeBSimpleNegativeRootGenerator (i : Fin (n + 1)) :
    (typeBSimpleNegativeRootGenerator (K := K) i :
      Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K) =
      typeBSimpleNegativeRootMatrix i := by
  simp [typeBSimpleNegativeRootGenerator]

@[simp]
theorem coe_typeBSimpleCorootGenerator (i : Fin (n + 1)) :
    (typeBSimpleCorootGenerator (K := K) i :
      Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K) =
      typeBSimpleCorootMatrix i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [typeBSimpleCorootGenerator, typeBSimpleCorootMatrix]

/-- Every numbered simple coroot belongs to the split diagonal Cartan. -/
theorem typeBSimpleCorootGenerator_mem_typeBDiagonalCartan (i : Fin (n + 1)) :
    typeBSimpleCorootGenerator (K := K) i ∈ typeBDiagonalCartan K (Fin (n + 1)) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [typeBSimpleCorootGenerator_last, typeBShortCorootGenerator_eq_diagonal]
    exact (typeBDiagonalEquiv _).property
  · rw [typeBSimpleCorootGenerator_castSucc, typeBDifferenceCorootGenerator_eq_diagonal]
    exact (typeBDiagonalEquiv _).property

/-- The positive and negative Bourbaki-numbered simple-root vectors of `Bₙ₊₁`, combined into the
single family indexed by `Fin (n + 1) ⊕ Fin (n + 1)` that the Chevalley constructions consume. -/
def typeBSimpleRootGeneratorFamily (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K :=
  Sum.elim (typeBSimpleRootGenerator (K := K))
    (typeBSimpleNegativeRootGenerator (K := K)) k

@[simp]
theorem typeBSimpleRootGeneratorFamily_inl (i : Fin (n + 1)) :
    typeBSimpleRootGeneratorFamily (K := K) (.inl i) = typeBSimpleRootGenerator i :=
  (rfl)

@[simp]
theorem typeBSimpleRootGeneratorFamily_inr (i : Fin (n + 1)) :
    typeBSimpleRootGeneratorFamily (K := K) (.inr i) = typeBSimpleNegativeRootGenerator i :=
  (rfl)

/-- Each positive and negative Bourbaki simple-root pair brackets to its simple coroot. -/
@[simp]
theorem typeBSimpleRootGenerator_lie_negative (i : Fin (n + 1)) :
    ⁅typeBSimpleRootGenerator (K := K) i, typeBSimpleNegativeRootGenerator (K := K) i⁆ =
      typeBSimpleCorootGenerator i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [typeBSimpleRootGenerator_last, typeBSimpleNegativeRootGenerator_last,
      typeBSimpleCorootGenerator_last] using
      (typeBShortRootGenerator_lie_negative (K := K) (Fin.last n))
  · simpa only [typeBSimpleRootGenerator_castSucc,
      typeBSimpleNegativeRootGenerator_castSucc, typeBSimpleCorootGenerator_castSucc] using
      (typeBDifferenceRootGenerator_lie_swap (K := K) j.castSucc j.succ
        (ne_of_lt j.castSucc_lt_succ))

/-- The divided square of a Bourbaki simple-root matrix. It vanishes at long nodes and is the
integral short-root divided square at the terminal node. -/
def typeBSimpleRootDividedSquare (i : Fin (n + 1)) :
    Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K :=
  Fin.lastCases (typeBShortRootDividedSquare (Fin.last n)) (fun _ => 0) i

@[simp]
theorem typeBSimpleRootDividedSquare_last :
    typeBSimpleRootDividedSquare (K := K) (Fin.last n) =
      typeBShortRootDividedSquare (Fin.last n) := by
  simp [typeBSimpleRootDividedSquare]

@[simp]
theorem typeBSimpleRootDividedSquare_castSucc (j : Fin n) :
    typeBSimpleRootDividedSquare (K := K) j.castSucc = 0 := by
  simp [typeBSimpleRootDividedSquare]

/-- A simple-root matrix squares to twice its integral divided square. -/
theorem typeBSimpleRootMatrix_mul_self (i : Fin (n + 1)) :
    typeBSimpleRootMatrix (K := K) i * typeBSimpleRootMatrix i =
      2 • typeBSimpleRootDividedSquare i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [typeBSimpleRootDividedSquare] using
      (typeBShortRootMatrix_mul_self (K := K) (Fin.last n))
  · simp [typeBSimpleRootDividedSquare,
      typeBDifferenceRootMatrix_mul_self (K := K) j.castSucc j.succ (ne_of_lt j.castSucc_lt_succ)]

/-- Every Bourbaki simple-root matrix has nilpotence degree at most three. -/
theorem typeBSimpleRootMatrix_cube (i : Fin (n + 1)) :
    typeBSimpleRootMatrix (K := K) i * typeBSimpleRootMatrix i * typeBSimpleRootMatrix i = 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using typeBShortRootMatrix_cube (K := K) (Fin.last n)
  · simp [typeBDifferenceRootMatrix_mul_self (K := K) j.castSucc j.succ
      (ne_of_lt j.castSucc_lt_succ)]

/-- The divided square of a negative Bourbaki simple-root matrix. It vanishes at long nodes and
is the integral negative short-root divided square at the terminal node. -/
def typeBSimpleNegativeRootDividedSquare (i : Fin (n + 1)) :
    Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K :=
  Fin.lastCases (typeBShortNegativeRootDividedSquare (Fin.last n)) (fun _ => 0) i

@[simp]
theorem typeBSimpleNegativeRootDividedSquare_last :
    typeBSimpleNegativeRootDividedSquare (K := K) (Fin.last n) =
      typeBShortNegativeRootDividedSquare (Fin.last n) := by
  simp [typeBSimpleNegativeRootDividedSquare]

@[simp]
theorem typeBSimpleNegativeRootDividedSquare_castSucc (j : Fin n) :
    typeBSimpleNegativeRootDividedSquare (K := K) j.castSucc = 0 := by
  simp [typeBSimpleNegativeRootDividedSquare]

/-- A negative simple-root matrix squares to twice its integral divided square. -/
theorem typeBSimpleNegativeRootMatrix_mul_self (i : Fin (n + 1)) :
    typeBSimpleNegativeRootMatrix (K := K) i * typeBSimpleNegativeRootMatrix i =
      2 • typeBSimpleNegativeRootDividedSquare i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [typeBSimpleNegativeRootDividedSquare] using
      (typeBShortNegativeRootMatrix_mul_self (K := K) (Fin.last n))
  · simp [typeBSimpleNegativeRootDividedSquare,
      typeBDifferenceRootMatrix_mul_self (K := K) j.succ j.castSucc (ne_of_gt j.castSucc_lt_succ)]

/-- Every negative Bourbaki simple-root matrix has nilpotence degree at most three. -/
theorem typeBSimpleNegativeRootMatrix_cube (i : Fin (n + 1)) :
    typeBSimpleNegativeRootMatrix (K := K) i * typeBSimpleNegativeRootMatrix i *
      typeBSimpleNegativeRootMatrix i = 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using typeBShortNegativeRootMatrix_cube (K := K) (Fin.last n)
  · simp [typeBDifferenceRootMatrix_mul_self (K := K) j.succ j.castSucc
      (ne_of_gt j.castSucc_lt_succ)]

end TauCeti
