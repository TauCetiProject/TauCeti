/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Geometry.Lie.Exponential.Unitary
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility
public import TauCeti.Geometry.Lie.Functor

/-!
# Exponential lines and unitary skew-adjointness of smooth unit-group representations

For a smooth homomorphism `φ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ` from a finite-dimensional
real Lie group `G` into the unit group of a finite-dimensional real normed algebra `R`, the
ambient-algebra element `unitsLieAlgebraEquiv (lieMap φ X)` generates the image of the Lie-group
exponential ray `t ↦ (φ (lieExp (t • X)) : R)` under the Banach-algebra exponential and gives its
time-zero real derivative. When `R` is a real normed star algebra with continuous star and every
`(φ g : R)` lies in `unitary R`, the differentiated elements are skew-adjoint (`star x = -x`).

## Main results

* `ContMDiffMonoidMorphism.exp_smul_unitsLieAlgebraEquiv_lieMap`: `NormedSpace.exp` of `t` times
  `unitsLieAlgebraEquiv (lieMap φ X)` equals `(φ (lieExp (t • X)) : R)`.
* `ContMDiffMonoidMorphism.hasDerivAt_coe_lieExp_smul_zero`: differentiating
  `t ↦ (φ (lieExp (t • X)) : R)` at `0` recovers `unitsLieAlgebraEquiv (lieMap φ X)`.
* `ContMDiffMonoidMorphism.star_unitsLieAlgebraEquiv_lieMap`: unitary-valued smooth unit-group
  homomorphisms differentiate to skew-adjoint elements.
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace ContMDiffMonoidMorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- Completeness of the finite-dimensional real normed algebra `R`. -/
local instance : CompleteSpace R := FiniteDimensional.completeSpace ℝ R

/-- Along a smooth homomorphism into the unit group of a finite-dimensional real normed algebra,
exponentiating a real multiple of the differentiated generator in `R` evaluates the group
homomorphism on the Lie-group exponential line. -/
theorem exp_smul_unitsLieAlgebraEquiv_lieMap
    (φ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ) (t : ℝ)
    (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    NormedSpace.exp (t • unitsLieAlgebraEquiv (lieMap φ X)) = (φ (lieExp (t • X)) : R) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  simpa only [map_smul, lieExp_eq_expUnit, TauCeti.expUnit_coe] using
    (congrArg Units.val (map_lieExp φ (t • X))).symm

/-- Differentiating a smooth unit-group representation along a Lie-group exponential ray at `t = 0`
yields the generator `unitsLieAlgebraEquiv (lieMap φ X)` in the ambient algebra `R`. -/
theorem hasDerivAt_coe_lieExp_smul_zero
    (φ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ) (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    HasDerivAt (fun t : ℝ ↦ (φ (lieExp (t • X)) : R))
      (unitsLieAlgebraEquiv (lieMap φ X)) 0 := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  simpa only [← φ.exp_smul_unitsLieAlgebraEquiv_lieMap, zero_smul, NormedSpace.exp_zero,
    mul_one] using hasDerivAt_exp_smul_const' (unitsLieAlgebraEquiv (lieMap φ X)) (0 : ℝ)

/-- A smooth homomorphism into the unit group of a finite-dimensional real normed star algebra
whose values lie in `unitary R` differentiates to skew-adjoint elements `star x = -x`. -/
theorem star_unitsLieAlgebraEquiv_lieMap [StarRing R] [ContinuousStar R]
    (φ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ)
    (hφ : ∀ g : G, (φ g : R) ∈ unitary R) (X : LeftInvariantDerivation I G) :
    star (unitsLieAlgebraEquiv (lieMap φ X)) = -unitsLieAlgebraEquiv (lieMap φ X) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  rw [← skewAdjoint.mem_iff, ← TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint]
  intro t
  rw [φ.exp_smul_unitsLieAlgebraEquiv_lieMap]
  exact hφ (lieExp (t • X))

end ContMDiffMonoidMorphism
