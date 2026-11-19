/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RootRelations.TripleBond

/-!
# The triple-bond commutator in the characteristic-three G₂ carrier

Transfer the integral positive-simple-root commutator formula to the closed subgroup of GL₇
generated over 𝔽₃. The result holds over every commutative 𝔽₃-algebra, including nonreduced
algebras, and retains the nonlinear terms in the two root parameters.

The transfer uses the proved equality of the root matrices. It does not identify the carrier
with the specialization of the integral toral closure, or with an independently pinned simply
connected group scheme.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The calculation is the one in
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RootRelations.TripleBond`.
-/

public section

open scoped Matrix commutatorElement
open Multiplicative

namespace TauCeti.G2ShortRoot.PrimeField

universe v

/-- The positive short simple-root point `x_{α₁}(t)` is the normal form with parameters
`(t, 0, 0, 0, 0, 0)`. -/
theorem coe_rootSubgroupPoints_inl_zero_eq_crossUnipotentMatrix
    {A : Type v} [CommRing A] [Algebra (ZMod 3) A] (t : A) :
    ((rootSubgroupPoints (.inl 0) A (ofAdd t) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = crossUnipotentMatrix t 0 0 0 0 0 := by
  rw [coe_rootSubgroupPoints]
  exact IntegralToralClosure.coe_rootSubgroupPoints_inl_zero_eq_crossUnipotentMatrix t

/-- The positive long simple-root point `x_{α₂}(t)` is the normal form with parameters
`(0, t, 0, 0, 0, 0)`. -/
theorem coe_rootSubgroupPoints_inl_one_eq_crossUnipotentMatrix
    {A : Type v} [CommRing A] [Algebra (ZMod 3) A] (t : A) :
    ((rootSubgroupPoints (.inl 1) A (ofAdd t) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = crossUnipotentMatrix 0 t 0 0 0 0 := by
  rw [coe_rootSubgroupPoints]
  exact IntegralToralClosure.coe_rootSubgroupPoints_inl_one_eq_crossUnipotentMatrix t

/-- The normal form of the positive-simple-root commutator in the short-root G₂ carrier generated
over 𝔽₃. The parameters and signs are those of the integral numbered root subgroups. -/
theorem coe_commutatorElement_rootSubgroupPoints_inl_zero_inl_one
    (A : Type v) [CommRing A] [Algebra (ZMod 3) A] (a b : A) :
    (((⁅rootSubgroupPoints (.inl 0) A (ofAdd a),
        rootSubgroupPoints (.inl 1) A (ofAdd b)⁆ : points A) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      crossUnipotentMatrix 0 0 (a * b) (-a ^ 2 * b) (a ^ 3 * b) (-a ^ 3 * b ^ 2) := by
  have h := IntegralToralClosure.coe_commutatorElement_rootSubgroupPoints_inl_zero_inl_one
    A a b
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_rootSubgroupPoints] using h

end TauCeti.G2ShortRoot.PrimeField
