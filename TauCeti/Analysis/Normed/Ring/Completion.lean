/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import TauCeti.Topology.Algebra.UniformRing

/-!
# Norms on completions of seminormed rings

The norm of the completion of a seminormed ring extends the norm of the ring by continuity, so
identities and inequalities between continuous functions of the norm pass from the ring to its
completion. This file records that submultiplicativity without a unit, multiplicativity,
`‖x * y‖ = ‖x‖ * ‖y‖`, and power-multiplicativity, `‖x ^ n‖ = ‖x‖ ^ n`, are such properties.
Completing a nonunital seminormed ring, such as an `L¹` convolution algebra on compactly supported
functions, therefore gives a complete nonunital normed ring. Isometry of a star operation passes
to the completion by `UniformSpace.Completion.instNormedStarGroup` in
`TauCeti.Analysis.CStarAlgebra.Completion`. A power-multiplicative norm determines the
power-bounded elements of a normed ring with a topologically nilpotent unit: they are exactly the
elements of norm at most one.

## Main results

* `UniformSpace.Completion.instNonUnitalNormedRing`: the completion of a nonunital seminormed
  ring is a nonunital normed ring.
* `UniformSpace.Completion.instNormMulClass`: the norm of the completion of a seminormed ring
  with a multiplicative norm is multiplicative.
* `UniformSpace.Completion.instNormOneClass`: the completion of a seminormed ring in which `1`
  has norm `1` has the same property.
* `IsPowMul.completion`: the norm of the completion of a seminormed ring with a
  power-multiplicative norm is power-multiplicative.
-/

public section

open UniformSpace

/-- **The completion of a seminormed ring with a power-multiplicative norm has a
power-multiplicative norm.** -/
theorem IsPowMul.completion {R : Type*} [SeminormedRing R] (h : IsPowMul (‖·‖ : R → ℝ)) :
    IsPowMul (‖·‖ : Completion R → ℝ) := by
  intro x n hn
  -- Both sides of `‖x ^ n‖ = ‖x‖ ^ n` are continuous in `x` and agree on the dense image of `R`.
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_pow n).norm (continuous_norm.pow n)
  | ih a =>
    have hcoe : ((a ^ n : R) : Completion R) = (a : Completion R) ^ n :=
      map_pow Completion.coeRingHom a n
    simp only [← hcoe, Completion.norm_coe, h a hn]

/-- **The completion of a seminormed ring with a multiplicative norm has a multiplicative
norm.** -/
instance UniformSpace.Completion.instNormMulClass {R : Type*} [SeminormedRing R] [NormMulClass R] :
    NormMulClass (Completion R) where
  norm_mul x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a b => simp only [← Completion.coe_mul, Completion.norm_coe, norm_mul]

/-- The completion of a seminormed ring in which `1` has norm `1` has the same property. -/
instance UniformSpace.Completion.instNormOneClass {R : Type*} [SeminormedRing R] [NormOneClass R] :
    NormOneClass (Completion R) where
  norm_one := by rw [← Completion.coe_one, Completion.norm_coe, norm_one]

/-- **The completion of a nonunital seminormed ring is a nonunital normed ring.** For a ring with
unit this is the nonunital part of Mathlib's `NormedRing` instance on the completion. -/
noncomputable instance UniformSpace.Completion.instNonUnitalNormedRing {R : Type*}
    [NonUnitalSeminormedRing R] : NonUnitalNormedRing (Completion R) where
  __ : NormedAddCommGroup (Completion R) := inferInstance
  __ : NonUnitalRing (Completion R) := inferInstance
  norm_mul_le x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a b => simpa only [← Completion.coe_mul', Completion.norm_coe] using norm_mul_le a b
