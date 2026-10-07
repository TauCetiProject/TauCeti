/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.RootGenerators

/-!
# Sum-root generators for the split orthogonal Lie algebra of type B

Relative to the split diagonal Cartan of `LieAlgebra.Orthogonal.typeB ι K`, the roots are the
short roots `±εᵢ` and the long roots `±εᵢ ± εⱼ` for `i ≠ j`. The companion file
`TauCeti/Algebra/Lie/Orthogonal/TypeB/RootGenerators.lean` builds the short roots and the
difference long roots `εᵢ - εⱼ`. This file supplies the remaining two families, the *sum* long
roots

```text
εᵢ + εⱼ    and    -εᵢ - εⱼ,
```

whose matrices are the skew pairs

```text
e_{εᵢ+εⱼ} = Eᵢ,₋ⱼ - Eⱼ,₋ᵢ,       e_{-εᵢ-εⱼ} = E₋ᵢ,ⱼ - E₋ⱼ,ᵢ.
```

Each pair is antisymmetric, and that is what makes it skew-adjoint for Mathlib's form matrix
`diag(2, J)`. A sum-root matrix has no entry in the anisotropic coordinate, so unlike a
short-root matrix it carries no coefficient `2`.

Two features of these vectors are what a Chevalley construction over `ℤ` asks of them. They are
square-zero -- indeed any product of two positive, or of two negative, sum-root matrices
vanishes -- so their exponentials are `1 + t X` and no divided power is involved. And a
sum-root vector is not the bracket of two short-root vectors: the Chevalley structure constant
of a pair of short roots whose sum is long has absolute value `2`, and in the normalization
below `⁅e_{εᵢ}, e_{εⱼ}⁆ = -2 e_{εᵢ+εⱼ}`, so the integral vector itself has to be written down.
Once it is, bracketing it with a difference-root vector moves one of its coordinates,
bracketing it with an opposite sum-root vector sharing one coordinate returns a difference-root
vector, and bracketing it with an opposite short-root vector returns a short-root vector, so the
four families interact by the expected relations.

Both displayed matrices are antisymmetric in `i` and `j`, so swapping the coordinates negates
them. In particular the two families are not Chevalley partners at matching indices: the vector
`f` with `⁅e_{εᵢ+εⱼ}, f⁆ = h_{εᵢ+εⱼ}` is `e_{-εⱼ-εᵢ} = -e_{-εᵢ-εⱼ}`, so the sl₂-triple of the
root `εᵢ + εⱼ` pairs `typeBSumRootGenerator i j` with `typeBSumNegativeRootGenerator j i`.

## Main definitions

* `TauCeti.typeBSumRootGenerator`: the root vector `e_{εᵢ+εⱼ}`.
* `TauCeti.typeBSumNegativeRootGenerator`: the opposite root vector `e_{-εᵢ-εⱼ}`; the Chevalley
  partner `f_{εᵢ+εⱼ}` of `e_{εᵢ+εⱼ}` is its index-swapped instance
  `typeBSumNegativeRootGenerator j i`.
* `TauCeti.typeBSumCorootGenerator`: the paired coroot `h_{εᵢ+εⱼ}`, of coordinate vector
  `εᵢ + εⱼ`.

## Main results

* `TauCeti.typeBSumRootMatrix_mem_typeB` and
  `TauCeti.typeBSumNegativeRootMatrix_mem_typeB`: both matrices are skew-adjoint for the split
  odd orthogonal form.
* `TauCeti.typeBSumRootMatrix_mul_sumRootMatrix` and its negative counterpart: products within
  one family vanish, so each sum-root vector is square-zero and any two of them commute.
* `TauCeti.typeBDiagonalMatrix_lie_sumRootGenerator` and
  `TauCeti.typeBDiagonalMatrix_lie_sumNegativeRootGenerator`: the split diagonal Cartan acts by
  the weights `εᵢ + εⱼ` and `-εᵢ - εⱼ`.
* `TauCeti.typeBSumRootGenerator_lie_negative`: `e_{εᵢ+εⱼ}` brackets with the index-swapped
  opposite vector `e_{-εⱼ-εᵢ}` to the coroot `h_{εᵢ+εⱼ}`.
* `TauCeti.typeBShortRootMatrix_lie_shortRootMatrix` (with structure constant `-2`),
  `TauCeti.typeBDifferenceRootMatrix_lie_sumRootMatrix`,
  `TauCeti.typeBSumRootMatrix_lie_sumNegativeRootMatrix`,
  `TauCeti.typeBSumRootMatrix_lie_shortNegativeRootMatrix` and their lowering-side
  counterparts: the Chevalley relations linking the sum-root family to the short and
  difference-root families.
* `TauCeti.typeBShortRootMatrix_lie_sumRootMatrix`,
  `TauCeti.typeBDifferenceRootMatrix_lie_sumRootMatrix_of_ne`,
  `TauCeti.typeBSumRootMatrix_lie_sumNegativeRootMatrix_of_ne`,
  `TauCeti.typeBSumRootMatrix_lie_shortNegativeRootMatrix_of_ne` and their counterparts: the
  configurations in which the sum of the two roots is not a root, so the bracket vanishes.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Planche II, for the root system and
  its Bourbaki numbering.
* R. W. Carter, *Simple Groups of Lie Type*, Section 4.2, for the integral normalization of the
  root vectors and the structure constants of a non-simply-laced system.

The declaration order and proof layout follow the difference-root and short-root sections of
`TauCeti.Algebra.Lie.Orthogonal.TypeB.RootGenerators`, and the corresponding type-`D` family in
`TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.AllGenerators`.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {K : Type u} [CommRing K]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The ambient root matrix for the long type-`B` root `εᵢ + εⱼ`. -/
def typeBSumRootMatrix (i j : ι) : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  single (.inr (.inl i)) (.inr (.inr j)) 1 -
    single (.inr (.inl j)) (.inr (.inr i)) 1

omit [Fintype ι] in
/-- The positive sum-root matrix as `Eᵢ,₋ⱼ - Eⱼ,₋ᵢ`. -/
theorem typeBSumRootMatrix_def (i j : ι) :
    typeBSumRootMatrix (K := K) i j =
      single (.inr (.inl i)) (.inr (.inr j)) 1 -
        single (.inr (.inl j)) (.inr (.inr i)) 1 :=
  (rfl)

/-- The ambient root matrix for the long type-`B` root `-εᵢ - εⱼ`. -/
def typeBSumNegativeRootMatrix (i j : ι) : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  single (.inr (.inr i)) (.inr (.inl j)) 1 -
    single (.inr (.inr j)) (.inr (.inl i)) 1

omit [Fintype ι] in
/-- The negative sum-root matrix as `E₋ᵢ,ⱼ - E₋ⱼ,ᵢ`. -/
theorem typeBSumNegativeRootMatrix_def (i j : ι) :
    typeBSumNegativeRootMatrix (K := K) i j =
      single (.inr (.inr i)) (.inr (.inl j)) 1 -
        single (.inr (.inr j)) (.inr (.inl i)) 1 :=
  (rfl)

/-- The positive sum-root matrix is skew-adjoint for the split odd orthogonal form. -/
theorem typeBSumRootMatrix_mem_typeB (i j : ι) :
    typeBSumRootMatrix (K := K) i j ∈ LieAlgebra.Orthogonal.typeB ι K := by
  rw [LieAlgebra.Orthogonal.typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- Unfold subtype membership to expose the ambient skew-adjoint matrix equation.
  change (typeBSumRootMatrix (K := K) i j)ᵀ * LieAlgebra.Orthogonal.JB ι K =
    LieAlgebra.Orthogonal.JB ι K * (-typeBSumRootMatrix (K := K) i j)
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [typeBSumRootMatrix, LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD,
      Matrix.mul_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- The negative sum-root matrix is skew-adjoint for the split odd orthogonal form. -/
theorem typeBSumNegativeRootMatrix_mem_typeB (i j : ι) :
    typeBSumNegativeRootMatrix (K := K) i j ∈ LieAlgebra.Orthogonal.typeB ι K := by
  rw [LieAlgebra.Orthogonal.typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- Unfold subtype membership to expose the ambient skew-adjoint matrix equation.
  change (typeBSumNegativeRootMatrix (K := K) i j)ᵀ * LieAlgebra.Orthogonal.JB ι K =
    LieAlgebra.Orthogonal.JB ι K * (-typeBSumNegativeRootMatrix (K := K) i j)
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [typeBSumNegativeRootMatrix, LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD,
      Matrix.mul_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

omit [Fintype ι] in
/-- Swapping the coordinates negates the positive sum-root matrix. -/
theorem typeBSumRootMatrix_swap (i j : ι) :
    typeBSumRootMatrix (K := K) j i = -typeBSumRootMatrix i j := by
  rw [typeBSumRootMatrix_def, typeBSumRootMatrix_def, neg_sub]

omit [Fintype ι] in
/-- Swapping the coordinates negates the negative sum-root matrix. -/
theorem typeBSumNegativeRootMatrix_swap (i j : ι) :
    typeBSumNegativeRootMatrix (K := K) j i = -typeBSumNegativeRootMatrix i j := by
  rw [typeBSumNegativeRootMatrix_def, typeBSumNegativeRootMatrix_def, neg_sub]

omit [Fintype ι] in
/-- The positive sum-root matrix vanishes on the diagonal, where `εᵢ + εⱼ` is not a root. -/
@[simp]
theorem typeBSumRootMatrix_self (i : ι) : typeBSumRootMatrix (K := K) i i = 0 := by
  rw [typeBSumRootMatrix_def, sub_self]

omit [Fintype ι] in
/-- The negative sum-root matrix vanishes on the diagonal. -/
@[simp]
theorem typeBSumNegativeRootMatrix_self (i : ι) :
    typeBSumNegativeRootMatrix (K := K) i i = 0 := by
  rw [typeBSumNegativeRootMatrix_def, sub_self]

/-- Any product of two positive sum-root matrices vanishes; in particular each one is
square-zero in the standard representation. -/
@[simp]
theorem typeBSumRootMatrix_mul_sumRootMatrix (i j k l : ι) :
    typeBSumRootMatrix (K := K) i j * typeBSumRootMatrix k l = 0 := by
  -- Every row index is in the first copy of `ι` and every column index in the second, so no
  -- column of the left factor meets a row of the right one.
  simp [typeBSumRootMatrix_def, mul_sub, sub_mul, Matrix.single_mul_single_of_ne]

/-- Any product of two negative sum-root matrices vanishes; in particular each one is
square-zero in the standard representation. -/
@[simp]
theorem typeBSumNegativeRootMatrix_mul_sumNegativeRootMatrix (i j k l : ι) :
    typeBSumNegativeRootMatrix (K := K) i j * typeBSumNegativeRootMatrix k l = 0 := by
  simp [typeBSumNegativeRootMatrix_def, mul_sub, sub_mul, Matrix.single_mul_single_of_ne]

/-- Positive sum-root vectors commute: the sum of two of their roots is never a root. -/
@[simp]
theorem typeBSumRootMatrix_lie_sumRootMatrix (i j k l : ι) :
    ⁅typeBSumRootMatrix (K := K) i j, typeBSumRootMatrix (K := K) k l⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]
  simp

/-- Negative sum-root vectors commute. -/
@[simp]
theorem typeBSumNegativeRootMatrix_lie_sumNegativeRootMatrix (i j k l : ι) :
    ⁅typeBSumNegativeRootMatrix (K := K) i j,
      typeBSumNegativeRootMatrix (K := K) k l⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]
  simp

/-! ### Bundled generators -/

/-- The sum-root vector `e_{εᵢ+εⱼ}` in the split type-`B` Lie algebra. -/
def typeBSumRootGenerator (i j : ι) : LieAlgebra.Orthogonal.typeB ι K :=
  ⟨typeBSumRootMatrix i j, typeBSumRootMatrix_mem_typeB i j⟩

/-- The opposite sum-root vector `e_{-εᵢ-εⱼ}`, of weight `-εᵢ - εⱼ`.

It is antisymmetric in `i` and `j`, so it is the Chevalley `f_{εᵢ+εⱼ}` only up to sign: the
partner of `typeBSumRootGenerator i j` in the sl₂-triple is the index-swapped instance
`typeBSumNegativeRootGenerator j i`, as `typeBSumRootGenerator_lie_negative` records. -/
def typeBSumNegativeRootGenerator (i j : ι) : LieAlgebra.Orthogonal.typeB ι K :=
  ⟨typeBSumNegativeRootMatrix i j, typeBSumNegativeRootMatrix_mem_typeB i j⟩

@[simp]
theorem coe_typeBSumRootGenerator (i j : ι) :
    (typeBSumRootGenerator (K := K) i j :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBSumRootMatrix i j :=
  (rfl)

@[simp]
theorem coe_typeBSumNegativeRootGenerator (i j : ι) :
    (typeBSumNegativeRootGenerator (K := K) i j :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBSumNegativeRootMatrix i j :=
  (rfl)

/-- Swapping the coordinates negates the positive sum-root vector. -/
theorem typeBSumRootGenerator_swap (i j : ι) :
    typeBSumRootGenerator (K := K) j i = -typeBSumRootGenerator i j := by
  apply Subtype.ext
  simpa using typeBSumRootMatrix_swap (K := K) i j

/-- Swapping the coordinates negates the negative sum-root vector. -/
theorem typeBSumNegativeRootGenerator_swap (i j : ι) :
    typeBSumNegativeRootGenerator (K := K) j i = -typeBSumNegativeRootGenerator i j := by
  apply Subtype.ext
  simpa using typeBSumNegativeRootMatrix_swap (K := K) i j

/-- The positive sum-root vector vanishes on the diagonal, where `εᵢ + εⱼ` is not a root. -/
@[simp]
theorem typeBSumRootGenerator_self (i : ι) : typeBSumRootGenerator (K := K) i i = 0 := by
  apply Subtype.ext
  simp

/-- The negative sum-root vector vanishes on the diagonal. -/
@[simp]
theorem typeBSumNegativeRootGenerator_self (i : ι) :
    typeBSumNegativeRootGenerator (K := K) i i = 0 := by
  apply Subtype.ext
  simp

/-- A positive sum-root vector at distinct coordinates is nonzero. -/
theorem typeBSumRootGenerator_ne_zero [Nontrivial K] (i j : ι) (hij : i ≠ j) :
    typeBSumRootGenerator (K := K) i j ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun (congrArg Subtype.val h) (.inr (.inl i)))
    (.inr (.inr j))
  simp [typeBSumRootMatrix_def, hij] at hentry

/-- A negative sum-root vector at distinct coordinates is nonzero. -/
theorem typeBSumNegativeRootGenerator_ne_zero [Nontrivial K] (i j : ι) (hij : i ≠ j) :
    typeBSumNegativeRootGenerator (K := K) i j ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun (congrArg Subtype.val h) (.inr (.inr i)))
    (.inr (.inl j))
  simp [typeBSumNegativeRootMatrix_def, hij] at hentry

/-! ### The paired coroot -/

/-- The diagonal coroot matrix paired with the long root `εᵢ + εⱼ`. -/
def typeBSumCorootMatrix (i j : ι) : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  typeBDiagonalMatrix (Pi.single i 1 + Pi.single j 1)

omit [Fintype ι] in
/-- The sum coroot matrix as the split diagonal matrix of coordinate vector `εᵢ + εⱼ`. -/
theorem typeBSumCorootMatrix_def (i j : ι) :
    typeBSumCorootMatrix (K := K) i j =
      typeBDiagonalMatrix (Pi.single i 1 + Pi.single j 1) :=
  (rfl)

/-- The coroot `h_{εᵢ+εⱼ}` in the split type-`B` Lie algebra. -/
def typeBSumCorootGenerator (i j : ι) : LieAlgebra.Orthogonal.typeB ι K :=
  ⟨typeBSumCorootMatrix i j, typeBDiagonalMatrix_mem_typeB _⟩

@[simp]
theorem coe_typeBSumCorootGenerator (i j : ι) :
    (typeBSumCorootGenerator (K := K) i j :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBSumCorootMatrix i j :=
  (rfl)

/-- The sum coroot has coordinate vector `εᵢ + εⱼ` in the split diagonal Cartan. -/
theorem typeBSumCorootGenerator_eq_diagonal (i j : ι) :
    typeBSumCorootGenerator (K := K) i j =
      ((typeBDiagonalEquiv (K := K) (ι := ι) (Pi.single i 1 + Pi.single j 1) :
        typeBDiagonalCartan K ι) : LieAlgebra.Orthogonal.typeB ι K) := by
  apply Subtype.ext
  rw [coe_typeBDiagonalEquiv_apply]
  rfl

/-! ### Diagonal action on the sum-root generators -/

/-- A split diagonal element acts on the sum-root vector of weight `εᵢ + εⱼ` by that weight. -/
@[simp]
theorem typeBDiagonalMatrix_lie_sumRootGenerator (d : ι → K) (i j : ι) :
    ⁅(⟨typeBDiagonalMatrix d, typeBDiagonalMatrix_mem_typeB d⟩ :
        LieAlgebra.Orthogonal.typeB ι K), typeBSumRootGenerator (K := K) i j⁆ =
      (d i + d j) • typeBSumRootGenerator i j := by
  have hd := typeBDiagonalMatrix_mem_diagonalCartan (K := K) d
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, coe_typeBSumRootGenerator,
    typeBSumRootMatrix_def, lie_sub, lie_single_of_mem_diagonalCartan hd,
    lie_single_of_mem_diagonalCartan hd, smul_sub]
  simp [add_comm]

/-- A split diagonal element acts on the sum-root vector of weight `-εᵢ - εⱼ`. -/
@[simp]
theorem typeBDiagonalMatrix_lie_sumNegativeRootGenerator (d : ι → K) (i j : ι) :
    ⁅(⟨typeBDiagonalMatrix d, typeBDiagonalMatrix_mem_typeB d⟩ :
        LieAlgebra.Orthogonal.typeB ι K), typeBSumNegativeRootGenerator (K := K) i j⁆ =
      -(d i + d j) • typeBSumNegativeRootGenerator i j := by
  have hd := typeBDiagonalMatrix_mem_diagonalCartan (K := K) d
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, coe_typeBSumNegativeRootGenerator,
    typeBSumNegativeRootMatrix_def, lie_sub, lie_single_of_mem_diagonalCartan hd,
    lie_single_of_mem_diagonalCartan hd, smul_sub]
  simp [sub_eq_add_neg, add_comm]

/-! ### Chevalley relations with the long and short families -/

/-- Two positive short-root vectors bracket to minus twice a sum-root vector:
`⁅e_{εᵢ}, e_{εⱼ}⁆ = -2 e_{εᵢ+εⱼ}`. A structure constant of absolute value `2` is the Chevalley
one for a pair of short type-`B` roots whose sum is long. -/
theorem typeBShortRootMatrix_lie_shortRootMatrix (i j : ι) :
    ⁅typeBShortRootMatrix (K := K) i, typeBShortRootMatrix (K := K) j⁆ =
      -(2 • typeBSumRootMatrix (K := K) i j) := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBShortRootMatrix_def, typeBSumRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, smul_sub,
    Matrix.smul_single]
  abel

/-- Two negative short-root vectors bracket to minus twice a negative sum-root vector:
`⁅f_{εᵢ}, f_{εⱼ}⁆ = -2 e_{-εᵢ-εⱼ}`. -/
theorem typeBShortNegativeRootMatrix_lie_shortNegativeRootMatrix (i j : ι) :
    ⁅typeBShortNegativeRootMatrix (K := K) i, typeBShortNegativeRootMatrix (K := K) j⁆ =
      -(2 • typeBSumNegativeRootMatrix (K := K) i j) := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBShortNegativeRootMatrix_def, typeBSumNegativeRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, smul_sub,
    Matrix.smul_single]
  abel

/-- A short-root vector commutes with a positive sum-root vector: `εᵢ + ε_k + ε_l` is never a
root, so this bracket vanishes for all index choices. -/
@[simp]
theorem typeBShortRootMatrix_lie_sumRootMatrix (i k l : ι) :
    ⁅typeBShortRootMatrix (K := K) i, typeBSumRootMatrix (K := K) k l⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBShortRootMatrix_def, typeBSumRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_of_ne]

/-- A negative short-root vector commutes with a negative sum-root vector. -/
@[simp]
theorem typeBShortNegativeRootMatrix_lie_sumNegativeRootMatrix (i k l : ι) :
    ⁅typeBShortNegativeRootMatrix (K := K) i, typeBSumNegativeRootMatrix (K := K) k l⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBShortNegativeRootMatrix_def, typeBSumNegativeRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_of_ne]

/-- Bracketing a long difference-root vector with a sum-root vector moves the sum-root
vector's first coordinate: `⁅e_{εᵢ-εⱼ}, e_{εⱼ+ε_k}⁆ = e_{εᵢ+ε_k}`. -/
theorem typeBDifferenceRootMatrix_lie_sumRootMatrix (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) :
    ⁅typeBDifferenceRootMatrix (K := K) i j hij, typeBSumRootMatrix (K := K) j k⁆ =
      typeBSumRootMatrix (K := K) i k := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBDifferenceRootMatrix_def, typeBSumRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hjk, hjk.symm]

/-- A difference-root vector commutes with a positive sum-root vector whose coordinates avoid the
lowered one: `εᵢ - εⱼ + ε_k + ε_l` is then not a root. -/
@[simp]
theorem typeBDifferenceRootMatrix_lie_sumRootMatrix_of_ne (i j k l : ι) (hij : i ≠ j) (hjk : j ≠ k)
    (hjl : j ≠ l) :
    ⁅typeBDifferenceRootMatrix (K := K) i j hij, typeBSumRootMatrix (K := K) k l⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBDifferenceRootMatrix_def, typeBSumRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_of_ne, hjk, hjk.symm, hjl, hjl.symm]

/-- Bracketing a long difference-root vector with a negative sum-root vector moves the latter's
first coordinate, with a sign: `⁅e_{εᵢ-εⱼ}, e_{-εᵢ-ε_l}⁆ = -e_{-εⱼ-ε_l}`. -/
theorem typeBDifferenceRootMatrix_lie_sumNegativeRootMatrix (i j l : ι) (hij : i ≠ j)
    (hil : i ≠ l) :
    ⁅typeBDifferenceRootMatrix (K := K) i j hij, typeBSumNegativeRootMatrix (K := K) i l⁆ =
      -typeBSumNegativeRootMatrix (K := K) j l := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBDifferenceRootMatrix_def, typeBSumNegativeRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hil, hil.symm]
  abel

/-- A difference-root vector commutes with a negative sum-root vector whose coordinates avoid the
raised one. -/
@[simp]
theorem typeBDifferenceRootMatrix_lie_sumNegativeRootMatrix_of_ne (i j k l : ι) (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) :
    ⁅typeBDifferenceRootMatrix (K := K) i j hij, typeBSumNegativeRootMatrix (K := K) k l⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBDifferenceRootMatrix_def, typeBSumNegativeRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_of_ne, hik, hik.symm, hil, hil.symm]

/-- A positive and a negative sum-root vector commute when their index pairs are disjoint: the
sum of their roots is then not a root. -/
@[simp]
theorem typeBSumRootMatrix_lie_sumNegativeRootMatrix_of_ne (i j k l : ι) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅typeBSumRootMatrix (K := K) i j, typeBSumNegativeRootMatrix (K := K) k l⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_of_ne, hik, hik.symm, hil, hil.symm, hjk, hjk.symm, hjl, hjl.symm]

/-- Bracketing a sum-root vector with an opposite sum-root vector that shares one coordinate
gives the difference-root vector of the remaining pair: `⁅e_{εᵢ+εⱼ}, e_{-εⱼ-ε_k}⁆ = e_{εᵢ-ε_k}`.
This is the bracket that returns from the sum-root family to the difference-root family. -/
theorem typeBSumRootMatrix_lie_sumNegativeRootMatrix (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    ⁅typeBSumRootMatrix (K := K) i j, typeBSumNegativeRootMatrix (K := K) j k⁆ =
      typeBDifferenceRootMatrix (K := K) i k hik := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, typeBDifferenceRootMatrix_def,
    mul_sub, sub_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
    hij, hij.symm, hjk, hjk.symm, hik, hik.symm]

/-- Lowering a sum-root vector by a negative short-root vector gives minus a positive short-root
vector: `⁅e_{εᵢ+εⱼ}, f_{εⱼ}⁆ = -e_{εᵢ}`. -/
theorem typeBSumRootMatrix_lie_shortNegativeRootMatrix (i j : ι) (hij : i ≠ j) :
    ⁅typeBSumRootMatrix (K := K) i j, typeBShortNegativeRootMatrix (K := K) j⁆ =
      -typeBShortRootMatrix (K := K) i := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBSumRootMatrix_def, typeBShortNegativeRootMatrix_def, typeBShortRootMatrix_def,
    mul_sub, sub_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
    hij, hij.symm]
  abel

/-- A positive sum-root vector commutes with a negative short-root vector at a third coordinate:
`εᵢ + εⱼ - ε_k` is then not a root. -/
@[simp]
theorem typeBSumRootMatrix_lie_shortNegativeRootMatrix_of_ne (i j k : ι) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ⁅typeBSumRootMatrix (K := K) i j, typeBShortNegativeRootMatrix (K := K) k⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBSumRootMatrix_def, typeBShortNegativeRootMatrix_def, mul_sub, sub_mul,
    Matrix.single_mul_single_of_ne, hik, hik.symm, hjk, hjk.symm]

/-- Raising a negative sum-root vector by a positive short-root vector gives minus a negative
short-root vector: `⁅e_{-εᵢ-εⱼ}, e_{εⱼ}⁆ = -f_{εᵢ}`. -/
theorem typeBSumNegativeRootMatrix_lie_shortRootMatrix (i j : ι) (hij : i ≠ j) :
    ⁅typeBSumNegativeRootMatrix (K := K) i j, typeBShortRootMatrix (K := K) j⁆ =
      -typeBShortNegativeRootMatrix (K := K) i := by
  rw [LieRing.of_associative_ring_bracket]
  simp [typeBSumNegativeRootMatrix_def, typeBShortRootMatrix_def,
    typeBShortNegativeRootMatrix_def, mul_sub, sub_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, hij, hij.symm]

/-- A sum-root vector and the index-swapped opposite sum-root vector bracket to the diagonal
coroot: `⁅e_{εᵢ+εⱼ}, e_{-εⱼ-εᵢ}⁆ = h_{εᵢ+εⱼ}`. Since swapping the coordinates negates the
opposite vector, the matching-index bracket is `-h_{εᵢ+εⱼ}`. -/
@[simp]
theorem typeBSumRootGenerator_lie_negative (i j : ι) (hij : i ≠ j) :
    ⁅typeBSumRootGenerator (K := K) i j, typeBSumNegativeRootGenerator (K := K) j i⁆ =
      typeBSumCorootGenerator i j := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, coe_typeBSumRootGenerator,
    coe_typeBSumNegativeRootGenerator, coe_typeBSumCorootGenerator,
    LieRing.of_associative_ring_bracket]
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [typeBSumRootMatrix, typeBSumNegativeRootMatrix, typeBSumCorootMatrix,
      typeBDiagonalMatrix_apply, mul_sub, sub_mul, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne, Matrix.single_apply, Pi.single_apply, hij, hij.symm]
  all_goals aesop

end TauCeti
