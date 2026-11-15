/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Category.ModuleCat.MatlisDual

/-!
# Scalar duals as right modules

The scalar dual of a left module `M` over a `k`-algebra `A` is the right module
`ModuleCat.matlisDualObj k k M`, the Matlis dual with values in the field `k`, with action
`(a • φ)(x) = φ(a.unop • x)`. Evaluation identifies a finite-dimensional module with the scalar dual
of this right module. This pairing is used to form `Tr D`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section I.3.
-/

public section

namespace ModuleCat

universe u v w

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A]

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

/-- The right scalar dual of a finite-dimensional module is finite-dimensional. -/
instance (M : ModuleCat.{w} A) [Module.Finite k M] : Module.Finite k (matlisDualObj k k M) :=
  Module.Finite.equiv (matlisDualObjLinearEquiv k k M).symm

/-- Evaluation pairs a finite-dimensional left module with its right scalar dual. -/
noncomputable def scalarDualEvalEquiv (M : ModuleCat.{w} A) [Module.Finite k M] :
    M ≃ₗ[k] Module.Dual k (matlisDualObj k k M) :=
  (Module.evalEquiv k M).trans (matlisDualObjLinearEquiv k k M).dualMap

/-- Evaluation on the right scalar dual is application of the underlying functional. -/
@[simp]
theorem scalarDualEvalEquiv_apply (M : ModuleCat.{w} A) [Module.Finite k M] (x : M)
    (φ : matlisDualObj k k M) :
    scalarDualEvalEquiv k M x φ = matlisDualObjLinearEquiv k k M φ x := by
  simp [scalarDualEvalEquiv, LinearEquiv.dualMap_apply]

/-- Evaluation respects the left action and its dual right action. -/
theorem scalarDualEvalEquiv_smul (M : ModuleCat.{w} A) [Module.Finite k M] (a : A) (x : M)
    (φ : matlisDualObj k k M) :
    scalarDualEvalEquiv k M (a • x) φ = scalarDualEvalEquiv k M x (MulOpposite.op a • φ) := by
  simp

end ModuleCat
