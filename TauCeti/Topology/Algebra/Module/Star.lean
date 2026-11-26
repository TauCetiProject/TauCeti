/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Star

/-!
# Continuous linear inclusion of self-adjoint elements

While `(selfAdjoint.submodule R A).subtypeL` embeds the submodule carrier
`↥(selfAdjoint.submodule R A)` into a topological star module `A`, calculus and operator APIs
stated directly on `selfAdjoint A` need a `ContinuousLinearMap` with syntactic domain
`selfAdjoint A` so that coercions and `simp` lemmas match at `implicit` transparency. This file
provides `selfAdjoint.subtypeL : selfAdjoint A →L[R] A`. Smoothness and Fréchet derivative lemmas
for `Subtype.val : selfAdjoint A → A` live in `TauCeti.Analysis.Calculus.ContDiff.Star` and
`TauCeti.Analysis.Calculus.FDeriv.Star`.
-/

public section

/-- The continuous `R`-linear inclusion `selfAdjoint A →L[R] A` of the self-adjoint elements of a
topological star module `A`, typed directly on `selfAdjoint A`. -/
def selfAdjoint.subtypeL (R A : Type*) [Semiring R] [Star R] [TrivialStar R] [AddCommGroup A]
    [Module R A] [StarAddMonoid A] [StarModule R A] [TopologicalSpace A] :
    selfAdjoint A →L[R] A where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_subtypeVal

/-- Coercing `selfAdjoint.subtypeL R A` to a function yields `Subtype.val`. -/
@[simp]
theorem selfAdjoint.coe_subtypeL (R A : Type*) [Semiring R] [Star R] [TrivialStar R]
    [AddCommGroup A] [Module R A] [StarAddMonoid A] [StarModule R A] [TopologicalSpace A] :
    ⇑(selfAdjoint.subtypeL R A) = (Subtype.val : selfAdjoint A → A) :=
  (rfl)

/-- Applying `selfAdjoint.subtypeL R A` extracts the ambient element. -/
@[simp]
theorem selfAdjoint.subtypeL_apply {R A : Type*} [Semiring R] [Star R] [TrivialStar R]
    [AddCommGroup A] [Module R A] [StarAddMonoid A] [StarModule R A] [TopologicalSpace A]
    (x : selfAdjoint A) :
    selfAdjoint.subtypeL R A x = (x : A) :=
  (rfl)
