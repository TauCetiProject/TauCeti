/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Restrict

/-!
# Coercion lemmas for `SpectrumRestricts.homeomorph`

This file records how Mathlib's `SpectrumRestricts.homeomorph` and its inverse act on the
underlying scalar values in `R` and `S`.

## Main results

* `SpectrumRestricts.coe_homeomorph_apply`: coercing `h.homeomorph x` to `R` applies `f`.
* `SpectrumRestricts.coe_homeomorph_symm_apply`: coercing `h.homeomorph.symm x` to `S` applies
  `algebraMap R S`.
-/

public section

namespace SpectrumRestricts

/-- Coercing `h.homeomorph x` to `R` applies the restriction map `f`. -/
@[simp]
theorem coe_homeomorph_apply {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] {a : A} {f : C(S, R)}
    (h : SpectrumRestricts a f) (x : spectrum S a) :
    ((h.homeomorph x : spectrum R a) : R) = f x :=
  rfl

/-- Coercing `h.homeomorph.symm x` to `S` embeds `x : spectrum R a` via `algebraMap R S`. -/
@[simp]
theorem coe_homeomorph_symm_apply {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] {a : A} {f : C(S, R)}
    (h : SpectrumRestricts a f) (x : spectrum R a) :
    ((h.homeomorph.symm x : spectrum S a) : S) = algebraMap R S x :=
  rfl

end SpectrumRestricts
