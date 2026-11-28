/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Hom
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
power-bounded elements of a normed ring with a pseudouniformizer: they are exactly the elements
of norm at most one (`TauCeti.Huber.IsPseudoUniformizer.isPowerBounded_iff_norm_le_one`).
Linear norm bounds on continuous nonunital algebra homomorphisms into complete Hausdorff targets
also pass to their extensions on completions (`NonUnitalAlgHom.norm_fromCompletion_le` and
`ContinuousLinearMap.norm_fromCompletion_toNonUnitalAlgHomOfMul_le`).

## Main results

* `IsPowMul.completion`: the norm of the completion of a seminormed ring with a
  power-multiplicative norm is power-multiplicative.
* `UniformSpace.Completion.instNormMulClass`: the norm of the completion of a nonunital
  seminormed ring with a multiplicative norm is multiplicative.
* `UniformSpace.Completion.instNormOneClass`: the completion of a seminormed ring in which `1`
  has norm `1` has the same property.
* `UniformSpace.Completion.instNonUnitalNormedRing`: the completion of a nonunital seminormed
  ring is a nonunital normed ring.
* `UniformSpace.Completion.isBounded_coeRingHom`: the embedding of a seminormed ring into its
  completion is a bounded ring homomorphism.
* `NonUnitalAlgHom.norm_fromCompletion_le`: linear norm bounds on `E` pass to `f.fromCompletion`.
* `ContinuousLinearMap.norm_fromCompletion_toNonUnitalAlgHomOfMul_le`: an operator-norm bound on
  a multiplicative continuous linear map passes to the completion of `toNonUnitalAlgHomOfMul`.
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
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a =>
    have hcoe : ((a ^ n : R) : Completion R) = (a : Completion R) ^ n :=
      map_pow Completion.coeRingHom a n
    simp only [← hcoe, Completion.norm_coe, h a hn]

/-- **The completion of a nonunital seminormed ring with a multiplicative norm has a
multiplicative norm.** -/
instance UniformSpace.Completion.instNormMulClass {R : Type*} [NonUnitalSeminormedRing R]
    [NormMulClass R] : NormMulClass (Completion R) where
  norm_mul x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a b => simp only [← Completion.coe_mul', Completion.norm_coe, norm_mul]

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

/-- The embedding of a seminormed ring into its completion is a bounded ring homomorphism; it
preserves norms. -/
theorem UniformSpace.Completion.isBounded_coeRingHom {R : Type*} [SeminormedRing R] :
    (Completion.coeRingHom : R →+* Completion R).IsBounded :=
  ⟨1, one_pos, fun a => by simp⟩

namespace NonUnitalAlgHom

/-- If a continuous semilinear nonunital algebra homomorphism `f : E →ₛₙₐ[φ] F` into a complete
Hausdorff space satisfies `‖f a‖ ≤ C * ‖a‖` on `E`, then its extension `f.fromCompletion hf`
satisfies the same bound on `UniformSpace.Completion E`. -/
theorem norm_fromCompletion_le {R S E F : Type*} [Monoid R] [Monoid S] {φ : R →* S}
    [NonUnitalSeminormedRing E] [DistribMulAction R E] [UniformContinuousConstSMul R E]
    [NonUnitalSeminormedRing F] [DistribMulAction S F] [ContinuousConstSMul S F]
    [T0Space F] [CompleteSpace F]
    (f : E →ₛₙₐ[φ] F) (hf : Continuous f) {C : ℝ} (hC : ∀ a : E, ‖f a‖ ≤ C * ‖a‖)
    (x : Completion E) :
    ‖f.fromCompletion hf x‖ ≤ C * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp (continuous_fromCompletion f hf))
      (continuous_const.mul continuous_norm)
  | ih a => simpa only [fromCompletion_apply_coe, Completion.norm_coe] using hC a

end NonUnitalAlgHom

namespace ContinuousLinearMap

/-- An operator-norm bound `‖f‖ ≤ C` on a multiplicative continuous linear map into a complete
Hausdorff nonunital seminormed algebra passes to the completion extension of
`f.toNonUnitalAlgHomOfMul`. -/
theorem norm_fromCompletion_toNonUnitalAlgHomOfMul_le
    {R E F : Type*} [NontriviallyNormedField R]
    [NonUnitalSeminormedRing E] [NormedSpace R E]
    [NonUnitalSeminormedRing F] [NormedSpace R F] [T0Space F] [CompleteSpace F]
    (f : E →L[R] F) (hf_mul : ∀ a b : E, f (a * b) = f a * f b)
    {C : ℝ} (hC : ‖f‖ ≤ C) (x : Completion E) :
    ‖(f.toNonUnitalAlgHomOfMul hf_mul).fromCompletion
      (f.continuous_toNonUnitalAlgHomOfMul hf_mul) x‖ ≤ C * ‖x‖ :=
  (f.toNonUnitalAlgHomOfMul hf_mul).norm_fromCompletion_le
    (f.continuous_toNonUnitalAlgHomOfMul hf_mul)
    (fun a => by simpa only [toNonUnitalAlgHomOfMul_apply] using f.le_of_opNorm_le hC a) x

end ContinuousLinearMap
