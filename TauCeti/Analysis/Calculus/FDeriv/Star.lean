/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import TauCeti.Topology.Algebra.Module.Star
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Fréchet derivatives of the self-adjoint inclusion

Complementing `selfAdjoint.contDiff_subtype_val` in `TauCeti.Analysis.Calculus.ContDiff.Star`,
the inclusion `Subtype.val : selfAdjoint A → A` into a topological star module over a nontrivially
normed field with trivial star has strict and pointwise Fréchet derivative
`selfAdjoint.subtypeL 𝕜 A`.

## Main results

* `selfAdjoint.hasFDerivAtFilter_subtype_val`, `selfAdjoint.hasStrictFDerivAt_subtype_val`,
  `selfAdjoint.hasFDerivAt_subtype_val`, and `selfAdjoint.hasFDerivWithinAt_subtype_val`.
-/

public section

/-- Along any filter, `Subtype.val : selfAdjoint A → A` has Fréchet derivative
`selfAdjoint.subtypeL 𝕜 A` over a scalar field with trivial star. -/
theorem selfAdjoint.hasFDerivAtFilter_subtype_val (𝕜 : Type*) {A : Type*}
    [NontriviallyNormedField 𝕜] [Star 𝕜] [TrivialStar 𝕜]
    [AddCommGroup A] [Module 𝕜 A] [StarAddMonoid A] [StarModule 𝕜 A] [TopologicalSpace A]
    {L : Filter (selfAdjoint A × selfAdjoint A)} :
    HasFDerivAtFilter (Subtype.val : selfAdjoint A → A) (selfAdjoint.subtypeL 𝕜 A) L :=
  selfAdjoint.coe_subtypeL 𝕜 A ▸ (selfAdjoint.subtypeL 𝕜 A).hasFDerivAtFilter

/-- The inclusion `Subtype.val : selfAdjoint A → A` has strict Fréchet derivative
`selfAdjoint.subtypeL 𝕜 A` at every point over a scalar field with trivial star. -/
@[fun_prop]
theorem selfAdjoint.hasStrictFDerivAt_subtype_val (𝕜 : Type*) {A : Type*}
    [NontriviallyNormedField 𝕜] [Star 𝕜] [TrivialStar 𝕜]
    [AddCommGroup A] [Module 𝕜 A] [StarAddMonoid A] [StarModule 𝕜 A] [TopologicalSpace A]
    {x : selfAdjoint A} :
    HasStrictFDerivAt (Subtype.val : selfAdjoint A → A) (selfAdjoint.subtypeL 𝕜 A) x :=
  selfAdjoint.hasFDerivAtFilter_subtype_val 𝕜

/-- The inclusion `Subtype.val : selfAdjoint A → A` has Fréchet derivative
`selfAdjoint.subtypeL 𝕜 A` at every point over a scalar field with trivial star. -/
@[fun_prop]
theorem selfAdjoint.hasFDerivAt_subtype_val (𝕜 : Type*) {A : Type*}
    [NontriviallyNormedField 𝕜] [Star 𝕜] [TrivialStar 𝕜]
    [AddCommGroup A] [Module 𝕜 A] [StarAddMonoid A] [StarModule 𝕜 A] [TopologicalSpace A]
    {x : selfAdjoint A} :
    HasFDerivAt (Subtype.val : selfAdjoint A → A) (selfAdjoint.subtypeL 𝕜 A) x :=
  selfAdjoint.hasFDerivAtFilter_subtype_val 𝕜

/-- Within any set, `Subtype.val : selfAdjoint A → A` has Fréchet derivative
`selfAdjoint.subtypeL 𝕜 A` over a scalar field with trivial star. -/
@[fun_prop]
theorem selfAdjoint.hasFDerivWithinAt_subtype_val (𝕜 : Type*) {A : Type*}
    [NontriviallyNormedField 𝕜] [Star 𝕜] [TrivialStar 𝕜]
    [AddCommGroup A] [Module 𝕜 A] [StarAddMonoid A] [StarModule 𝕜 A] [TopologicalSpace A]
    {s : Set (selfAdjoint A)} {x : selfAdjoint A} :
    HasFDerivWithinAt (Subtype.val : selfAdjoint A → A) (selfAdjoint.subtypeL 𝕜 A) s x :=
  selfAdjoint.hasFDerivAtFilter_subtype_val 𝕜
