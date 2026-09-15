/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.AdmissibleLattice
public import TauCeti.LinearAlgebra.Matrix.IntCast
public import TauCeti.LinearAlgebra.Matrix.Step
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The numbered simple root matrices of type F4 and their divided-power exponentials

`TauCeti.F4ShortRoot.rootMatrix` and `TauCeti.F4ShortRoot.rootDividedSquareMatrix` are the
integral matrices of the eight numbered simple root generators of the twenty-six-dimensional
short-root representation of type `F₄` and of their divided squares. This file records the two
properties of those matrices that every later construction on them uses, independently of what
that construction is: each has at most one nonzero entry in each column, tabulated by a target
and a coefficient table, and the four products that can be formed from a generator and its
divided square are the expected multiples of one another.

The step structure is what makes entrywise identities between products of these matrices finite
computations rather than sums over the twenty-six indices, and the product relations are the
input to every expansion of a divided-power exponential in its parameter.

Those exponentials are the numbered simple root elements `1 + u X + u² X⁽²⁾` themselves, over an
arbitrary commutative ring. The product relations make them a homomorphism from the additive
group of the value ring, so they are invertible with inverse the element of the negated parameter;
in characteristic two the negation is trivial and each element is an involution.

## Main definitions

* `TauCeti.F4ShortRoot.rootElementMatrix` and `TauCeti.F4ShortRoot.rootElementUnit`: the matrix
  `1 + u X + u² X⁽²⁾` of a numbered simple root element, and that matrix as an element of the
  general linear group.
* `TauCeti.F4ShortRoot.rootStepTarget` and `TauCeti.F4ShortRoot.rootStepCoeff`: the target and
  coefficient tables of a numbered simple root matrix, with
  `TauCeti.F4ShortRoot.rootDividedSquareStepTarget` and
  `TauCeti.F4ShortRoot.rootDividedSquareStepCoeff` those of its divided square.

## Main results

* `TauCeti.F4ShortRoot.isStep_rootMatrix` and
  `TauCeti.F4ShortRoot.isStep_rootDividedSquareMatrix`: the step structure.
* `TauCeti.F4ShortRoot.rootMatrix_mul_self`: a numbered simple root matrix squares to twice its
  divided square, with `TauCeti.F4ShortRoot.rootMatrix_mul_mul_self` its cube zero.
* `TauCeti.F4ShortRoot.rootMatrix_mul_rootDividedSquareMatrix`,
  `TauCeti.F4ShortRoot.rootDividedSquareMatrix_mul_rootMatrix` and
  `TauCeti.F4ShortRoot.rootDividedSquareMatrix_mul_self`: the remaining products vanish.
* `TauCeti.F4ShortRoot.rootElementMatrix_zero` and `TauCeti.F4ShortRoot.rootElementMatrix_add`,
  with `TauCeti.F4ShortRoot.rootElementUnit_zero` and `TauCeti.F4ShortRoot.rootElementUnit_add`:
  the numbered simple root elements are the image of the additive group of the value ring.
* `TauCeti.F4ShortRoot.rootElementMatrix_mul_self`: in characteristic two each element is an
  involution, with `TauCeti.F4ShortRoot.rootElementMatrix_map_pow_two` squaring its parameter.

## References

The numbering follows N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII. The
divided-power generators are those of R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R]

/-! ## Step structure of the numbered simple root matrices -/

/-- The target table of the numbered simple root generator matrix. -/
@[expose] def rootStepTarget : Fin 4 ⊕ Fin 4 → Fin 26 → Fin 26 :=
  Sum.elim raisingTarget loweringTarget

/-- The coefficient table of the numbered simple root generator matrix. -/
@[expose] def rootStepCoeff : Fin 4 ⊕ Fin 4 → Fin 26 → ℤ :=
  Sum.elim raisingCoeff loweringCoeff

/-- The target table of the divided square of a numbered simple root generator matrix. -/
@[expose] def rootDividedSquareStepTarget : Fin 4 ⊕ Fin 4 → Fin 26 → Fin 26 :=
  Sum.elim raisingDividedSquareTarget loweringDividedSquareTarget

/-- The coefficient table of the divided square of a numbered simple root generator matrix. -/
@[expose] def rootDividedSquareStepCoeff : Fin 4 ⊕ Fin 4 → Fin 26 → ℤ :=
  Sum.elim raisingDividedSquareCoeff loweringDividedSquareCoeff

/-- The matrix of a numbered simple root generator is a step matrix. -/
theorem isStep_rootMatrix (k : Fin 4 ⊕ Fin 4) :
    (rootMatrix k).IsStep (rootStepTarget k) (rootStepCoeff k) := by
  refine Matrix.isStep_of_apply fun a b => ?_
  cases k with
  | inl i =>
      rw [rootMatrix_inl]
      exact raisingMatrix_apply i a b
  | inr i =>
      rw [rootMatrix_inr]
      exact loweringMatrix_apply i a b

/-- The divided square of a numbered simple root generator matrix is a step matrix. -/
theorem isStep_rootDividedSquareMatrix (k : Fin 4 ⊕ Fin 4) :
    (rootDividedSquareMatrix k).IsStep (rootDividedSquareStepTarget k)
      (rootDividedSquareStepCoeff k) := by
  refine Matrix.isStep_of_apply fun a b => ?_
  cases k with
  | inl i =>
      rw [rootDividedSquareMatrix_inl]
      exact raisingDividedSquareMatrix_apply i a b
  | inr i =>
      rw [rootDividedSquareMatrix_inr]
      exact loweringDividedSquareMatrix_apply i a b

/-! ## Products of the numbered simple root matrices -/

/-- The square of a numbered simple root matrix is twice its divided square. -/
theorem rootMatrix_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootMatrix k * rootMatrix k = (2 : ℤ) • rootDividedSquareMatrix k := by
  cases k with
  | inl i => rw [rootMatrix_inl, rootDividedSquareMatrix_inl, raisingMatrix_mul_self]
  | inr i => rw [rootMatrix_inr, rootDividedSquareMatrix_inr, loweringMatrix_mul_self]

/-- A numbered simple root matrix annihilates its divided square on the left. -/
@[simp]
theorem rootMatrix_mul_rootDividedSquareMatrix (k : Fin 4 ⊕ Fin 4) :
    rootMatrix k * rootDividedSquareMatrix k = 0 := by
  cases k with
  | inl i =>
      rw [rootMatrix_inl, rootDividedSquareMatrix_inl,
        raisingMatrix_mul_raisingDividedSquareMatrix]
  | inr i =>
      rw [rootMatrix_inr, rootDividedSquareMatrix_inr,
        loweringMatrix_mul_loweringDividedSquareMatrix]

/-- A numbered simple root matrix annihilates its divided square on the right. -/
@[simp]
theorem rootDividedSquareMatrix_mul_rootMatrix (k : Fin 4 ⊕ Fin 4) :
    rootDividedSquareMatrix k * rootMatrix k = 0 := by
  cases k with
  | inl i =>
      rw [rootMatrix_inl, rootDividedSquareMatrix_inl,
        raisingDividedSquareMatrix_mul_raisingMatrix]
  | inr i =>
      rw [rootMatrix_inr, rootDividedSquareMatrix_inr,
        loweringDividedSquareMatrix_mul_loweringMatrix]

/-- A numbered simple root matrix cubes to zero. -/
theorem rootMatrix_mul_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootMatrix k * rootMatrix k * rootMatrix k = 0 := by
  rw [rootMatrix_mul_self, smul_mul_assoc, rootDividedSquareMatrix_mul_rootMatrix, smul_zero]

/-- The divided square of a numbered simple root matrix squares to zero. -/
@[simp]
theorem rootDividedSquareMatrix_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootDividedSquareMatrix k * rootDividedSquareMatrix k = 0 := by
  have h2 : ((2 : ℤ) • rootDividedSquareMatrix k) * ((2 : ℤ) • rootDividedSquareMatrix k) =
      (4 : ℤ) • (rootDividedSquareMatrix k * rootDividedSquareMatrix k) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num
  have h : (4 : ℤ) • (rootDividedSquareMatrix k * rootDividedSquareMatrix k) = 0 := by
    rw [← h2, ← rootMatrix_mul_self, ← mul_assoc, rootMatrix_mul_mul_self, zero_mul]
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)
/-! ## The numbered simple root elements -/

/-- The matrix `1 + u X + u² X⁽²⁾` of the numbered simple root element of parameter `u`, with
`X` the integral matrix of the generator and `X⁽²⁾` that of its divided square. -/
def rootElementMatrix (k : Fin 4 ⊕ Fin 4) (u : R) : Matrix (Fin 26) (Fin 26) R :=
  1 + u • (rootMatrix k).map (Int.cast : ℤ → R) +
    u ^ 2 • (rootDividedSquareMatrix k).map (Int.cast : ℤ → R)

/-- The defining equation of the numbered simple root element matrix. -/
theorem rootElementMatrix_def (k : Fin 4 ⊕ Fin 4) (u : R) :
    rootElementMatrix k u =
      1 + u • (rootMatrix k).map (Int.cast : ℤ → R) +
        u ^ 2 • (rootDividedSquareMatrix k).map (Int.cast : ℤ → R) := by
  rw [rootElementMatrix]

/-- **The numbered simple root element at parameter zero is the identity.** -/
@[simp]
theorem rootElementMatrix_zero (k : Fin 4 ⊕ Fin 4) : rootElementMatrix k (0 : R) = 1 := by
  rw [rootElementMatrix_def, zero_smul, add_zero, zero_pow two_ne_zero, zero_smul, add_zero]

/-- **The numbered simple root elements add their parameters**: the divided-power exponential of a
cube-zero generator is a homomorphism from the additive group. -/
theorem rootElementMatrix_add (k : Fin 4 ⊕ Fin 4) (u v : R) :
    rootElementMatrix k (u + v) = rootElementMatrix k u * rootElementMatrix k v := by
  rw [rootElementMatrix_def, rootElementMatrix_def, rootElementMatrix_def]
  set X := (rootMatrix k).map (Int.cast : ℤ → R) with hXdef
  set Y := (rootDividedSquareMatrix k).map (Int.cast : ℤ → R) with hYdef
  have hX : X * X = (2 : R) • Y := by
    rw [hXdef, hYdef, ← Matrix.map_intCast_mul, rootMatrix_mul_self]
    ext a b
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      Int.cast_mul, Matrix.map_apply]
    norm_num
  have hXY : X * Y = 0 := by
    rw [hXdef, hYdef, ← Matrix.map_intCast_mul, rootMatrix_mul_rootDividedSquareMatrix,
      Matrix.map_zero _ Int.cast_zero]
  have hYX : Y * X = 0 := by
    rw [hXdef, hYdef, ← Matrix.map_intCast_mul, rootDividedSquareMatrix_mul_rootMatrix,
      Matrix.map_zero _ Int.cast_zero]
  have hY : Y * Y = 0 := by
    rw [hYdef, ← Matrix.map_intCast_mul, rootDividedSquareMatrix_mul_self,
      Matrix.map_zero _ Int.cast_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hX, hXY, hYX, hY,
    smul_zero, add_zero, smul_smul]
  module

/-- **A numbered simple root element is an involution in characteristic two**: adding the
parameter to itself gives zero, and the element at parameter zero is the identity. -/
theorem rootElementMatrix_mul_self [CharP R 2] (k : Fin 4 ⊕ Fin 4) (u : R) :
    rootElementMatrix k u * rootElementMatrix k u = 1 := by
  rw [← rootElementMatrix_add, CharTwo.add_self_eq_zero, rootElementMatrix_zero]

/-- The numbered simple root element of parameter `u`, as an element of the general linear group:
its inverse is the element of parameter `-u`. -/
def rootElementUnit (k : Fin 4 ⊕ Fin 4) (u : R) : GeneralLinearGroup (Fin 26) R :=
  ⟨rootElementMatrix k u, rootElementMatrix k (-u),
    by rw [← rootElementMatrix_add, add_neg_cancel, rootElementMatrix_zero],
    by rw [← rootElementMatrix_add, neg_add_cancel, rootElementMatrix_zero]⟩

/-- The matrix of a numbered simple root element of the general linear group. -/
@[simp]
theorem coe_rootElementUnit (k : Fin 4 ⊕ Fin 4) (u : R) :
    ((rootElementUnit k u : GeneralLinearGroup (Fin 26) R) : Matrix (Fin 26) (Fin 26) R) =
      rootElementMatrix k u := by
  rw [rootElementUnit]

/-- **The numbered simple root element of the general linear group at parameter zero is the
identity.** -/
@[simp]
theorem rootElementUnit_zero (k : Fin 4 ⊕ Fin 4) : rootElementUnit k (0 : R) = 1 :=
  Units.ext (by rw [coe_rootElementUnit, rootElementMatrix_zero, Units.val_one])

/-- **The numbered simple root elements of the general linear group add their parameters.** -/
theorem rootElementUnit_add (k : Fin 4 ⊕ Fin 4) (u v : R) :
    rootElementUnit k (u + v) = rootElementUnit k u * rootElementUnit k v :=
  Units.ext (by
    rw [coe_rootElementUnit, Units.val_mul, coe_rootElementUnit, coe_rootElementUnit,
      rootElementMatrix_add])

/-- The matrix of the inverse of a numbered simple root element is the element of the negated
parameter. This is not a `simp` lemma because the simp normal form of its left-hand side is the
matrix inverse of `TauCeti.F4ShortRoot.rootElementMatrix`. -/
theorem coe_inv_rootElementUnit (k : Fin 4 ⊕ Fin 4) (u : R) :
    (((rootElementUnit k u)⁻¹ : GeneralLinearGroup (Fin 26) R) :
        Matrix (Fin 26) (Fin 26) R) = rootElementMatrix k (-u) := by
  rw [rootElementUnit]
  rfl

/-- In characteristic two a numbered simple root element is its own inverse. -/
theorem coe_inv_rootElementUnit_of_charP [CharP R 2] (k : Fin 4 ⊕ Fin 4) (u : R) :
    (((rootElementUnit k u)⁻¹ : GeneralLinearGroup (Fin 26) R) :
        Matrix (Fin 26) (Fin 26) R) = rootElementMatrix k u := by
  rw [coe_inv_rootElementUnit, CharTwo.neg_eq]

/-- **Squaring the entries of a numbered simple root element squares its parameter**, which in
characteristic two is the Frobenius on it. -/
theorem rootElementMatrix_map_pow_two [CharP R 2] (k : Fin 4 ⊕ Fin 4) (u : R) :
    (rootElementMatrix k u).map (· ^ 2) = rootElementMatrix k (u ^ 2) := by
  ext a b
  rw [Matrix.map_apply, rootElementMatrix_def, rootElementMatrix_def]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply]
  have hsq : ∀ z : ℤ, ((z : R)) ^ 2 = (z : R) := fun z =>
    (frobenius_def (R := R) 2 (z : R)).symm.trans (map_intCast (frobenius R 2) z)
  rw [CharTwo.add_sq, CharTwo.add_sq, mul_pow, mul_pow, hsq, hsq]
  split_ifs
  · rw [one_pow]
  · rw [zero_pow two_ne_zero]

end TauCeti.F4ShortRoot
