/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Topological star modules and self-adjoint inclusions

This file supplements `Mathlib.Topology.Algebra.Module.Star` with the continuous linear inclusion
`selfAdjoint.subtypeL` from `selfAdjoint A` into `A` and the identification
`selfAdjointPartL_eq_realPart` between Mathlib's `selfAdjointPartL ℝ A` and `realPart` (`ℜ`) on a
topological complex star module.

## Main definitions and results

* `selfAdjoint.subtypeL`: the canonical continuous `R`-linear inclusion `selfAdjoint A →L[R] A`.
* `selfAdjoint.subtypeL_apply`: evaluation lemma for `selfAdjoint.subtypeL`.
* `selfAdjointPartL_eq_realPart`: `selfAdjointPartL ℝ A x = ℜ x` on a topological complex star
  module.
-/

public section

namespace selfAdjoint

/-- The canonical inclusion `selfAdjoint A →L[R] A` as a continuous `R`-linear map. Unlike
`(selfAdjoint.submodule R A).subtypeL`, its domain is `selfAdjoint A` with its own
`Module R (selfAdjoint A)` instance rather than `↥(selfAdjoint.submodule R A)` with
`Submodule.module`, avoiding implicit-transparency mismatches when composing or pulling back. -/
def subtypeL (R A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
    [Module R A] [StarAddMonoid A] [StarModule R A] [TopologicalSpace A] :
    selfAdjoint A →L[R] A where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_subtypeVal

/-- Evaluating `selfAdjoint.subtypeL` returns the underlying element of `A`. -/
@[simp]
theorem subtypeL_apply {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
    [Module R A] [StarAddMonoid A] [StarModule R A] [TopologicalSpace A] (a : selfAdjoint A) :
    subtypeL R A a = (a : A) := by
  rfl

end selfAdjoint

section Complex

open scoped ComplexStarModule

/-- On a topological complex star module, Mathlib's continuous self-adjoint projection
`selfAdjointPartL ℝ A` agrees with `realPart` (`ℜ`). -/
@[simp]
theorem selfAdjointPartL_eq_realPart {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A]
    [StarModule ℂ A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousStar A]
    [ContinuousConstSMul ℝ A] (x : A) :
    selfAdjointPartL ℝ A x = ℜ x :=
  rfl

end Complex
