/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic
public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Unitriangular
public import Mathlib.Algebra.Group.Commutator

/-!
# The triple-bond commutator on the short-root G₂ module

Compute the commutator of the two positive numbered simple-root subgroups on the integral
seven-dimensional module. The formula retains the mixed terms of degrees two through five,
including the quadratic divided-power contribution of the short root. It supplies an explicit
matrix identity in the six-parameter normal form `TauCeti.G2ShortRoot.crossUnipotentMatrix`
for collecting these root elements without inverting two or three.

All identities hold over arbitrary commutative rings, including nonreduced rings. The integral
toral closure is not identified here with the pinned simply connected group scheme of type G₂;
transfer to that group requires such an identification.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The normalization uses the matrices in `TauCeti.Algebra.Lie.G2.ShortRoot.Basic` and the
root-subgroup formulas in `TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`.
-/

public section

open scoped Matrix commutatorElement
open Multiplicative

namespace TauCeti.G2ShortRoot.IntegralToralClosure

universe v

/-- The positive short simple-root point `x_{α₁}(t)` is the normal form with parameters
`(t, 0, 0, 0, 0, 0)`. -/
theorem coe_rootSubgroupPoints_inl_zero_eq_crossUnipotentMatrix
    {A : Type v} [CommRing A] (t : A) :
    ((rootSubgroupPoints (.inl 0) A (ofAdd t) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = crossUnipotentMatrix t 0 0 0 0 0 := by
  rw [coe_rootSubgroupPoints_inl_zero, crossUnipotentMatrix_def]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The positive long simple-root point `x_{α₂}(t)` is the normal form with parameters
`(0, t, 0, 0, 0, 0)`. -/
theorem coe_rootSubgroupPoints_inl_one_eq_crossUnipotentMatrix
    {A : Type v} [CommRing A] (t : A) :
    ((rootSubgroupPoints (.inl 1) A (ofAdd t) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = crossUnipotentMatrix 0 t 0 0 0 0 := by
  rw [coe_rootSubgroupPoints_inl_one, crossUnipotentMatrix_def]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The exact normal form of `[x_{α₁}(a), x_{α₂}(b)]`, with `α₁` short and `α₂` long in
Bourbaki numbering. No characteristic assumption or division is required. -/
theorem coe_commutatorElement_rootSubgroupPoints_inl_zero_inl_one
    (A : Type v) [CommRing A] (a b : A) :
    (((⁅rootSubgroupPoints (.inl 0) A (ofAdd a),
        rootSubgroupPoints (.inl 1) A (ofAdd b)⁆ : points A) :
        Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      crossUnipotentMatrix 0 0 (a * b) (-a ^ 2 * b) (a ^ 3 * b) (-a ^ 3 * b ^ 2) := by
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_mul]
  rw [Units.mul_inv_eq_iff_eq_mul, Units.mul_inv_eq_iff_eq_mul]
  rw [coe_rootSubgroupPoints_inl_zero_eq_crossUnipotentMatrix,
    coe_rootSubgroupPoints_inl_one_eq_crossUnipotentMatrix]
  simp only [crossUnipotentMatrix_mul_crossUnipotentMatrix]
  congr 1 <;> ring

end TauCeti.G2ShortRoot.IntegralToralClosure
