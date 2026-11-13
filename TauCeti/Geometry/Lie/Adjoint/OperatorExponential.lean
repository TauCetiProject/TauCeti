/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Analysis.Normed.Operator.Mul
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Exponentiating the commutator operator

In a real Banach algebra, exponentiating the continuous commutator operator
`y ↦ x * y - y * x` gives conjugation by `exp x`. This is the Banach-algebra shadow of the Lie-group
identity `Ad (lieExp X) = exp (ad X)`. The underlying linear map of the bounded commutator is
Mathlib's `LieAlgebra.ad` for the associative-ring Lie bracket. The commutator itself works in
compatible nonunital seminormed algebras over any nontrivially normed field; the identification
with `LieAlgebra.ad` uses a unital seminormed algebra. Neither requires completeness. The proof of
the conjugation identity uses the exponentials of bounded left and right multiplication,
`TauCeti.exp_mulLeft_apply` and `TauCeti.exp_mulRight_apply`, which are proved with the other
multiplication-operator identities in `TauCeti/Analysis/Normed/Operator/Mul.lean`.

## Main definitions

* `TauCeti.Lie.continuousCommutator`: the continuous commutator operator associated to an algebra
  element.

## Main results

* `TauCeti.Lie.exp_continuousCommutator_apply`: its operator exponential acts by conjugation.
* `TauCeti.Lie.exp_continuousCommutator`: the corresponding equality of bounded operators.
* `TauCeti.Lie.continuousCommutator_toLinearMap`: its underlying linear map is Mathlib's
  `LieAlgebra.ad`.
-/

public section

noncomputable section

namespace TauCeti.Lie

open NormedSpace

section NonUnital

variable (𝕜 : Type*) {R : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalSeminormedRing R] [NormedSpace 𝕜 R]
  [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

/-- The continuous-linear family of endomorphisms `y ↦ x * y - y * x`. -/
def continuousCommutator : R →L[𝕜] R →L[𝕜] R :=
  ContinuousLinearMap.mul 𝕜 R - (ContinuousLinearMap.mul 𝕜 R).flip

@[simp]
theorem continuousCommutator_apply (x y : R) :
    continuousCommutator 𝕜 x y = x * y - y * x := by
  simp [continuousCommutator]

end NonUnital

section AlgebraicAdjoint

variable (𝕜 : Type*) {R : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedRing R] [NormedAlgebra 𝕜 R]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The continuous commutator is the bounded realization of Mathlib's algebraic adjoint map for
the ring-commutator bracket supplied by `LieRing.ofAssociativeRing`. Callers who restate the
right-hand side should enable that instance locally. -/
theorem continuousCommutator_toLinearMap (x : R) :
    (continuousCommutator 𝕜 x).toLinearMap = LieAlgebra.ad 𝕜 R x := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  ext y
  simp [continuousCommutator]

end AlgebraicAdjoint

section Complete

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- Exponentiating the continuous commutator operator gives conjugation by the algebra
exponential. -/
@[simp]
theorem exp_continuousCommutator_apply (x y : R) :
    exp (continuousCommutator ℝ x) y = exp x * y * exp (-x) := by
  let L := ContinuousLinearMap.mul ℝ R x
  let R' := (ContinuousLinearMap.mul ℝ R).flip x
  have hcomm : Commute L R' := by
    ext z
    simp only [L, R', mul_apply_eq_comp, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.flip_apply, mul_assoc]
  have hcommutator : continuousCommutator ℝ x = L - R' := by
    rw [continuousCommutator, sub_apply]
  rw [hcommutator, sub_eq_add_neg, exp_add_of_commute hcomm.neg_right,
    mul_apply_eq_comp]
  have hneg : -R' = (ContinuousLinearMap.mul ℝ R).flip (-x) := by
    simpa only [R'] using (map_neg (ContinuousLinearMap.mul ℝ R).flip x).symm
  rw [hneg, exp_mulRight_apply, exp_mulLeft_apply, mul_assoc]

/-- Exponentiating the continuous commutator gives the bounded conjugation operator. -/
theorem exp_continuousCommutator (x : R) :
    exp (continuousCommutator ℝ x) =
      ContinuousLinearMap.mulLeftRight ℝ R (exp x) (exp (-x)) := by
  ext y
  simp

end Complete

end TauCeti.Lie
