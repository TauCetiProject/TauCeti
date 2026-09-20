/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.LinearAlgebra.Matrix.Step
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight

/-!
# The integral short-root representation of type F4

This file realizes the Chevalley generators of type `F₄` on the twenty-six-element weight
diagram `TauCeti.DynkinType.f4ShortRootWeight`, whose weights are the twenty-four short roots
and the zero weight taken twice. On the coordinate vector belonging to the `b`th weight, the
Cartan generator `H_i` acts by the simple-coroot coordinate of that weight, and each raising
generator `E_i` and lowering generator `F_i` carries the coordinate vector to an integer
multiple of a single coordinate vector, read from explicit target and coefficient tables. Every
generator is therefore a *step matrix*, a matrix each of whose columns has at most one nonzero
entry, and products of step matrices are again step matrices.

The resulting integer matrices satisfy the Chevalley--Serre relations for the transpose of the
Bourbaki Cartan matrix of type `F₄`, which is the convention under which `⁅H_i, E_j⁆` is the
pairing of the `j`th simple root with the `i`th simple coroot times `E_j`. The universal
property of the Serre presentation gives the explicit integral twenty-six-dimensional
representation. The two long simple raising and lowering generators square to zero. The two
short ones do not: their squares are twice an integral matrix, the divided square, and their
cubes vanish. Those divided squares are what an admissible lattice built on this weight basis
must be stable under.

The two zero-weight coordinate vectors are the images of the two short simple lowering
generators applied to the coordinate vectors of the corresponding simple roots, and the tables
record how each short simple raising generator returns them: the one from its own root with
coefficient two, the other with coefficient one.

No identification with the abstract irreducible highest-weight module is asserted here, and the
zero-weight basis is the explicitly tabulated one rather than one characterized by a generation
property. The construction is explicit: every matrix entry is read from the weight, target and
coefficient tables.

## Main definitions

* `TauCeti.F4ShortRoot.cartanMatrix`, `raisingMatrix`, and `loweringMatrix`: the integral
  Cartan, raising, and lowering matrices.
* `TauCeti.F4ShortRoot.raisingDividedSquareMatrix` and `loweringDividedSquareMatrix`: the
  divided squares of the raising and lowering matrices.
* `TauCeti.F4ShortRoot.isSerreSystem`: the Chevalley--Serre relations between them over `ℤ`.
* `TauCeti.F4ShortRoot.serreRepresentation`: the induced representation of the type-`F₄` Serre
  Lie algebra.

## Main results

* `TauCeti.F4ShortRoot.raisingMatrix_mul_self` and `loweringMatrix_mul_self`: each square is
  twice the divided square.
* `TauCeti.F4ShortRoot.raisingMatrix_mul_raisingDividedSquareMatrix` and its three siblings: each
  generator annihilates its own divided square on either side, so each generator cubes to zero.
* `TauCeti.F4ShortRoot.raisingMatrix_mul_self_of_lt_two` and `loweringMatrix_mul_self_of_lt_two`:
  the two long simple generators square to zero.

## References

The numbering follows Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII. The
admissible lattice generated from a highest weight vector by divided-power lowering operators is
the one of B. Kostant, *Groups over `ℤ`*, and R. Steinberg, *Lectures on Chevalley Groups*,
§12. The construction of the twenty-six-dimensional module from its weight diagram and the
Serre presentation follows J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §§18 and 27.
-/

public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

open LieAlgebra TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Step matrices -/

/-- The matrix whose `b`th column is `c b` times the `t b`th coordinate vector. -/
private def stepMatrix (t : Fin 26 → Fin 26) (c : Fin 26 → ℤ) : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.of fun a b => if a = t b then c b else 0

/-- The entrywise formula for a step matrix. -/
@[simp]
private theorem stepMatrix_apply (t : Fin 26 → Fin 26) (c : Fin 26 → ℤ) (a b : Fin 26) :
    stepMatrix t c a b = if a = t b then c b else 0 := by
  rw [stepMatrix, Matrix.of_apply]

/-- A matrix built from target and coefficient tables has those tables as step data. -/
private theorem isStep_stepMatrix (t : Fin 26 → Fin 26) (c : Fin 26 → ℤ) :
    (stepMatrix t c).IsStep t c :=
  Matrix.isStep_of_apply (stepMatrix_apply t c)

/-- The product of two step matrices is the step matrix of the composite targets and the
product of the coefficients along the way. -/
private theorem stepMatrix_mul_stepMatrix (t t' : Fin 26 → Fin 26) (c c' : Fin 26 → ℤ) :
    stepMatrix t c * stepMatrix t' c' = stepMatrix (t ∘ t') fun b => c (t' b) * c' b := by
  ext a b
  rw [((isStep_stepMatrix t c).mul (isStep_stepMatrix t' c')).apply a b, stepMatrix_apply]

/-- A diagonal matrix times a step matrix rescales each column by the diagonal entry at its
target. -/
private theorem diagonal_mul_stepMatrix (d : Fin 26 → ℤ) (t : Fin 26 → Fin 26) (c : Fin 26 → ℤ) :
    Matrix.diagonal d * stepMatrix t c = stepMatrix t fun b => d (t b) * c b := by
  ext a b
  rw [((Matrix.isStep_diagonal d).mul (isStep_stepMatrix t c)).apply a b, stepMatrix_apply]
  rfl

/-- A step matrix times a diagonal matrix rescales each column by the diagonal entry at its
index. -/
private theorem stepMatrix_mul_diagonal (t : Fin 26 → Fin 26) (c : Fin 26 → ℤ) (d : Fin 26 → ℤ) :
    stepMatrix t c * Matrix.diagonal d = stepMatrix t fun b => c b * d b := by
  ext a b
  rw [((isStep_stepMatrix t c).mul (Matrix.isStep_diagonal d)).apply a b, stepMatrix_apply]
  rfl

/-! ## The tables -/

/-- The target index of each coordinate vector under the `i`th raising generator; a column with
coefficient zero has itself as its target. -/
@[expose] def raisingTarget : Fin 4 → Fin 26 → Fin 26 := ![
  ![0, 1, 2, 3, 3, 5, 5, 7, 8, 7, 10, 11, 12, 13, 14, 15, 16, 17, 16, 19, 19, 21, 21, 23, 24, 25],
  ![0, 1, 2, 2, 4, 5, 6, 7, 6, 9, 10, 9, 12, 13, 14, 15, 14, 17, 18, 17, 20, 21, 22, 22, 24, 25],
  ![0, 1, 1, 3, 4, 3, 4, 7, 8, 9, 8, 11, 11, 11, 12, 15, 16, 15, 18, 19, 20, 19, 20, 23, 23, 25],
  ![0, 0, 2, 3, 4, 5, 6, 5, 8, 6, 10, 8, 10, 10, 14, 13, 16, 14, 18, 16, 18, 21, 22, 23, 24, 24]]

/-- The coefficient of each coordinate vector under the `i`th raising generator. -/
@[expose] def raisingCoeff : Fin 4 → Fin 26 → ℤ := ![
  ![0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0],
  ![0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 2, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0],
  ![0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1]]

/-- The target index of each coordinate vector under the `i`th lowering generator; a column
with coefficient zero has itself as its target. -/
@[expose] def loweringTarget : Fin 4 → Fin 26 → Fin 26 := ![
  ![0, 1, 2, 4, 4, 6, 6, 9, 8, 9, 10, 11, 12, 13, 14, 15, 18, 17, 18, 20, 20, 22, 22, 23, 24, 25],
  ![0, 1, 3, 3, 4, 5, 8, 7, 8, 11, 10, 11, 12, 13, 16, 15, 16, 19, 18, 19, 20, 21, 23, 23, 24, 25],
  ![0, 2, 2, 5, 6, 5, 6, 7, 10, 9, 10, 12, 14, 14, 14, 17, 16, 17, 18, 21, 22, 21, 22, 24, 24, 25],
  ![1, 1, 2, 3, 4, 7, 9, 7, 11, 9, 13, 11, 15, 15, 17, 15, 19, 17, 20, 19, 20, 21, 22, 23, 25, 25]]

/-- The coefficient of each coordinate vector under the `i`th lowering generator. -/
@[expose] def loweringCoeff : Fin 4 → Fin 26 → ℤ := ![
  ![0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0],
  ![1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0]]

/-- The target index of each coordinate vector under the divided square of the `i`th raising
generator. Only the two short simple roots contribute, each moving the coordinate vector of the
negative of its root to that of the root itself. -/
@[expose] def raisingDividedSquareTarget : Fin 4 → Fin 26 → Fin 26 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 11, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 10, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]

/-- The coefficient of each coordinate vector under the divided square of the `i`th raising
generator. -/
@[expose] def raisingDividedSquareCoeff : Fin 4 → Fin 26 → ℤ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The target index of each coordinate vector under the divided square of the `i`th lowering
generator. -/
@[expose] def loweringDividedSquareTarget : Fin 4 → Fin 26 → Fin 26 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 14, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]

/-- The coefficient of each coordinate vector under the divided square of the `i`th lowering
generator. -/
@[expose] def loweringDividedSquareCoeff : Fin 4 → Fin 26 → ℤ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-! ## The integral generator matrices -/

/-- The Cartan generator `H_i` in the short-root weight basis. -/
def cartanMatrix (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.diagonal fun a => f4ShortRootWeight a i

/-- The raising generator `E_i` in the short-root weight basis. -/
def raisingMatrix (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  stepMatrix (raisingTarget i) (raisingCoeff i)

/-- The lowering generator `F_i` in the short-root weight basis. -/
def loweringMatrix (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  stepMatrix (loweringTarget i) (loweringCoeff i)

/-- The divided square `E_i^(2) = E_i² / 2` of the raising generator, an integral matrix. -/
def raisingDividedSquareMatrix (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  stepMatrix (raisingDividedSquareTarget i) (raisingDividedSquareCoeff i)

/-- The divided square `F_i^(2) = F_i² / 2` of the lowering generator, an integral matrix. -/
def loweringDividedSquareMatrix (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  stepMatrix (loweringDividedSquareTarget i) (loweringDividedSquareCoeff i)

/-- The entrywise formula for the diagonal Cartan generator matrix. -/
@[simp]
theorem cartanMatrix_apply (i : Fin 4) (a b : Fin 26) :
    cartanMatrix i a b = if a = b then f4ShortRootWeight a i else 0 := by
  rw [cartanMatrix, Matrix.diagonal_apply]

/-- The entrywise formula for the raising generator matrix. -/
@[simp]
theorem raisingMatrix_apply (i : Fin 4) (a b : Fin 26) :
    raisingMatrix i a b = if a = raisingTarget i b then raisingCoeff i b else 0 := by
  rw [raisingMatrix, stepMatrix_apply]

/-- The entrywise formula for the lowering generator matrix. -/
@[simp]
theorem loweringMatrix_apply (i : Fin 4) (a b : Fin 26) :
    loweringMatrix i a b = if a = loweringTarget i b then loweringCoeff i b else 0 := by
  rw [loweringMatrix, stepMatrix_apply]

/-- The entrywise formula for the divided square of the raising generator. -/
@[simp]
theorem raisingDividedSquareMatrix_apply (i : Fin 4) (a b : Fin 26) :
    raisingDividedSquareMatrix i a b =
      if a = raisingDividedSquareTarget i b then raisingDividedSquareCoeff i b else 0 := by
  rw [raisingDividedSquareMatrix, stepMatrix_apply]

/-- The entrywise formula for the divided square of the lowering generator. -/
@[simp]
theorem loweringDividedSquareMatrix_apply (i : Fin 4) (a b : Fin 26) :
    loweringDividedSquareMatrix i a b =
      if a = loweringDividedSquareTarget i b then loweringDividedSquareCoeff i b else 0 := by
  rw [loweringDividedSquareMatrix, stepMatrix_apply]

/-! ## Chevalley--Serre relations -/

private theorem cartanMatrix_lie_H (i j : Fin 4) :
    ⁅cartanMatrix i, cartanMatrix j⁆ = 0 := by
  simp [Ring.lie_def, cartanMatrix, Matrix.diagonal_mul_diagonal, mul_comm]

private theorem raisingMatrix_lie_F_self (i : Fin 4) :
    ⁅raisingMatrix i, loweringMatrix i⁆ = cartanMatrix i := by
  rw [Ring.lie_def, raisingMatrix, loweringMatrix, cartanMatrix, stepMatrix_mul_stepMatrix,
    stepMatrix_mul_stepMatrix]
  ext a b
  rw [Matrix.sub_apply, stepMatrix_apply, stepMatrix_apply, Matrix.diagonal_apply]
  revert a b i
  decide +kernel

private theorem raisingMatrix_lie_F_of_ne (i j : Fin 4) (hij : i ≠ j) :
    ⁅raisingMatrix i, loweringMatrix j⁆ = 0 := by
  rw [Ring.lie_def, raisingMatrix, loweringMatrix, stepMatrix_mul_stepMatrix,
    stepMatrix_mul_stepMatrix]
  ext a b
  rw [Matrix.sub_apply, stepMatrix_apply, stepMatrix_apply, Matrix.zero_apply]
  revert a b i j
  decide +kernel

private theorem cartanMatrix_lie_E (i j : Fin 4) :
    ⁅cartanMatrix i, raisingMatrix j⁆ = CartanMatrix.F₄ᵀ i j • raisingMatrix j := by
  rw [Ring.lie_def, cartanMatrix, raisingMatrix, diagonal_mul_stepMatrix, stepMatrix_mul_diagonal,
    Matrix.transpose_apply]
  ext a b
  rw [Matrix.sub_apply, Matrix.smul_apply, stepMatrix_apply, stepMatrix_apply, stepMatrix_apply,
    smul_eq_mul]
  revert a b i j
  decide +kernel

private theorem cartanMatrix_lie_F (i j : Fin 4) :
    ⁅cartanMatrix i, loweringMatrix j⁆ = -(CartanMatrix.F₄ᵀ i j • loweringMatrix j) := by
  rw [Ring.lie_def, cartanMatrix, loweringMatrix, diagonal_mul_stepMatrix,
    stepMatrix_mul_diagonal, Matrix.transpose_apply]
  ext a b
  rw [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, stepMatrix_apply, stepMatrix_apply,
    stepMatrix_apply, smul_eq_mul]
  revert a b i j
  decide +kernel

/-- The exponents `(-(F₄ᵀ i j)).toNat` of the Serre relations, tabulated. -/
private theorem toNat_neg_cartan (i j : Fin 4) :
    (-(CartanMatrix.F₄ᵀ i j)).toNat =
      ![![0, 1, 0, 0], ![1, 0, 1, 0], ![0, 2, 0, 1], ![0, 0, 1, 0]] i j := by
  revert i j
  decide +kernel

private theorem raisingMatrix_lie_E_lie_E (i j : Fin 4) :
    (ad ℤ _ (raisingMatrix i) ^ (-(CartanMatrix.F₄ᵀ i j)).toNat)
      ⁅raisingMatrix i, raisingMatrix j⁆ = 0 := by
  rw [toNat_neg_cartan]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, pow_zero, pow_succ, Module.End.mul_apply,
      Module.End.one_apply, ad_apply, Ring.lie_def, raisingMatrix, mul_sub, sub_mul,
      stepMatrix_mul_stepMatrix, ← mul_assoc] <;>
    ext a b <;>
    simp only [Matrix.sub_apply, stepMatrix_apply, Matrix.zero_apply, Function.comp_apply] <;>
    revert a b <;>
    decide +kernel

private theorem loweringMatrix_lie_F_lie_F (i j : Fin 4) :
    (ad ℤ _ (loweringMatrix i) ^ (-(CartanMatrix.F₄ᵀ i j)).toNat)
      ⁅loweringMatrix i, loweringMatrix j⁆ = 0 := by
  rw [toNat_neg_cartan]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, pow_zero, pow_succ, Module.End.mul_apply,
      Module.End.one_apply, ad_apply, Ring.lie_def, loweringMatrix, mul_sub, sub_mul,
      stepMatrix_mul_stepMatrix, ← mul_assoc] <;>
    ext a b <;>
    simp only [Matrix.sub_apply, stepMatrix_apply, Matrix.zero_apply, Function.comp_apply] <;>
    revert a b <;>
    decide +kernel

/-- The integral short-root generator matrices satisfy the Chevalley--Serre relations of type
`F₄`, for the transpose of the Bourbaki Cartan matrix, in Bourbaki numbering. -/
theorem isSerreSystem :
    IsSerreSystem ℤ CartanMatrix.F₄ᵀ cartanMatrix raisingMatrix loweringMatrix where
  lie_H_H := cartanMatrix_lie_H
  lie_E_F_self := raisingMatrix_lie_F_self
  lie_E_F_of_ne := raisingMatrix_lie_F_of_ne
  lie_H_E := cartanMatrix_lie_E
  lie_H_F := cartanMatrix_lie_F
  ad_pow_lie_E_E := raisingMatrix_lie_E_lie_E
  ad_pow_lie_F_F := loweringMatrix_lie_F_lie_F

/-- The explicit integral twenty-six-dimensional representation of the type-`F₄` Serre Lie
algebra. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ CartanMatrix.F₄ᵀ →ₗ⁅ℤ⁆ Matrix (Fin 26) (Fin 26) ℤ :=
  serreLift isSerreSystem

/-- The integral Serre representation sends `H_i` to the Cartan generator matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 4) :
    serreRepresentation (serreH ℤ CartanMatrix.F₄ᵀ i) = cartanMatrix i :=
  serreLift_serreH isSerreSystem i

/-- The integral Serre representation sends `E_i` to the raising generator matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 4) :
    serreRepresentation (serreE ℤ CartanMatrix.F₄ᵀ i) = raisingMatrix i :=
  serreLift_serreE isSerreSystem i

/-- The integral Serre representation sends `F_i` to the lowering generator matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 4) :
    serreRepresentation (serreF ℤ CartanMatrix.F₄ᵀ i) = loweringMatrix i :=
  serreLift_serreF isSerreSystem i

/-! ## Squares and cubes of the generators -/

/-- The square of a raising generator is twice its divided square. -/
theorem raisingMatrix_mul_self (i : Fin 4) :
    raisingMatrix i * raisingMatrix i = (2 : ℤ) • raisingDividedSquareMatrix i := by
  rw [raisingMatrix, raisingDividedSquareMatrix, stepMatrix_mul_stepMatrix]
  ext a b
  rw [Matrix.smul_apply, stepMatrix_apply, stepMatrix_apply, smul_eq_mul]
  revert a b i
  decide +kernel

/-- The square of a lowering generator is twice its divided square. -/
theorem loweringMatrix_mul_self (i : Fin 4) :
    loweringMatrix i * loweringMatrix i = (2 : ℤ) • loweringDividedSquareMatrix i := by
  rw [loweringMatrix, loweringDividedSquareMatrix, stepMatrix_mul_stepMatrix]
  ext a b
  rw [Matrix.smul_apply, stepMatrix_apply, stepMatrix_apply, smul_eq_mul]
  revert a b i
  decide +kernel

/-- A raising generator annihilates its divided square on the left. -/
@[simp]
theorem raisingMatrix_mul_raisingDividedSquareMatrix (i : Fin 4) :
    raisingMatrix i * raisingDividedSquareMatrix i = 0 := by
  rw [raisingMatrix, raisingDividedSquareMatrix, stepMatrix_mul_stepMatrix]
  ext a b
  rw [stepMatrix_apply, Matrix.zero_apply]
  revert a b i
  decide +kernel

/-- A raising generator annihilates its divided square on the right. -/
@[simp]
theorem raisingDividedSquareMatrix_mul_raisingMatrix (i : Fin 4) :
    raisingDividedSquareMatrix i * raisingMatrix i = 0 := by
  rw [raisingMatrix, raisingDividedSquareMatrix, stepMatrix_mul_stepMatrix]
  ext a b
  rw [stepMatrix_apply, Matrix.zero_apply]
  revert a b i
  decide +kernel

/-- A lowering generator annihilates its divided square on the left. -/
@[simp]
theorem loweringMatrix_mul_loweringDividedSquareMatrix (i : Fin 4) :
    loweringMatrix i * loweringDividedSquareMatrix i = 0 := by
  rw [loweringMatrix, loweringDividedSquareMatrix, stepMatrix_mul_stepMatrix]
  ext a b
  rw [stepMatrix_apply, Matrix.zero_apply]
  revert a b i
  decide +kernel

/-- A lowering generator annihilates its divided square on the right. -/
@[simp]
theorem loweringDividedSquareMatrix_mul_loweringMatrix (i : Fin 4) :
    loweringDividedSquareMatrix i * loweringMatrix i = 0 := by
  rw [loweringMatrix, loweringDividedSquareMatrix, stepMatrix_mul_stepMatrix]
  ext a b
  rw [stepMatrix_apply, Matrix.zero_apply]
  revert a b i
  decide +kernel

/-- Every raising generator cubes to zero. -/
@[simp]
theorem raisingMatrix_pow_three (i : Fin 4) : raisingMatrix i ^ 3 = 0 := by
  rw [pow_succ, pow_two, raisingMatrix_mul_self, smul_mul_assoc,
    raisingDividedSquareMatrix_mul_raisingMatrix, smul_zero]

/-- Every lowering generator cubes to zero. -/
@[simp]
theorem loweringMatrix_pow_three (i : Fin 4) : loweringMatrix i ^ 3 = 0 := by
  rw [pow_succ, pow_two, loweringMatrix_mul_self, smul_mul_assoc,
    loweringDividedSquareMatrix_mul_loweringMatrix, smul_zero]

/-- The divided square of a long simple raising generator vanishes. -/
theorem raisingDividedSquareMatrix_eq_zero_of_lt_two (i : Fin 4) (hi : (i : ℕ) < 2) :
    raisingDividedSquareMatrix i = 0 := by
  fin_cases i
  · ext a b
    rw [raisingDividedSquareMatrix_apply, Matrix.zero_apply]
    revert a b
    decide +kernel
  · ext a b
    rw [raisingDividedSquareMatrix_apply, Matrix.zero_apply]
    revert a b
    decide +kernel
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)

/-- The divided square of a long simple lowering generator vanishes. -/
theorem loweringDividedSquareMatrix_eq_zero_of_lt_two (i : Fin 4) (hi : (i : ℕ) < 2) :
    loweringDividedSquareMatrix i = 0 := by
  fin_cases i
  · ext a b
    rw [loweringDividedSquareMatrix_apply, Matrix.zero_apply]
    revert a b
    decide +kernel
  · ext a b
    rw [loweringDividedSquareMatrix_apply, Matrix.zero_apply]
    revert a b
    decide +kernel
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)

/-- The long simple raising generators square to zero. -/
@[simp]
theorem raisingMatrix_mul_self_of_lt_two (i : Fin 4) (hi : (i : ℕ) < 2) :
    raisingMatrix i * raisingMatrix i = 0 := by
  rw [raisingMatrix_mul_self, raisingDividedSquareMatrix_eq_zero_of_lt_two i hi, smul_zero]

/-- The long simple lowering generators square to zero. -/
@[simp]
theorem loweringMatrix_mul_self_of_lt_two (i : Fin 4) (hi : (i : ℕ) < 2) :
    loweringMatrix i * loweringMatrix i = 0 := by
  rw [loweringMatrix_mul_self, loweringDividedSquareMatrix_eq_zero_of_lt_two i hi, smul_zero]

end TauCeti.F4ShortRoot
