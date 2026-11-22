/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.Normed.Module.WeakDual
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit.Basic
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Norms and compression of positive functionals on C⋆-algebras

## Pullback along surjective homomorphisms

The norm of a positive functional on a possibly nonunital C⋆-algebra is its limit along any
increasing approximate unit, Mathlib's `PositiveContinuousLinearMap.tendsto_nhds_opNorm`. A
surjective star-algebra homomorphism carries increasing approximate units to increasing
approximate units, so pulling a positive functional back along it does not change the norm,
`PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective`. In particular states pull back
to states along quotient maps; without surjectivity the norm can drop, for instance to `0`.
For the same reason the norm is additive on positive functionals,
`PositiveContinuousLinearMap.opNorm_add`.

The bound `‖ω a‖ ^ 2 ≤ ‖ω‖ ‖ω (star a * a)‖` of Mathlib's
`PositiveContinuousLinearMap.norm_map_sq_le_opNorm_mul` shows that a positive functional vanishes
at every `a` with `ω (star a * a) = 0`
(`PositiveContinuousLinearMap.map_eq_zero_of_map_star_mul_self_eq_zero`).

## Positive functionals in the weak-* dual

For a functional `φ : WeakDual ℂ A` on a C⋆-algebra that is nonnegative on nonnegative elements,
this file records the norm facts about positive functionals in the form used on the weak-* dual.

* `WeakDual.monotone_toStrongDual_of_map_nonneg`: `φ` is monotone.
* `WeakDual.tendsto_approximateUnit_norm_of_map_nonneg`: along the approximate unit, `φ` tends
  to its norm.
* `WeakDual.norm_toStrongDual_eq_map_one_of_map_nonneg`: if `A` is unital, the norm of `φ` is
  `φ 1`.

These are Mathlib's `ContinuousLinearMap.monotone_iff_tendsto_nhds_opNorm` and
`ContinuousLinearMap.monotone_iff_opNorm_eq_map_one`, restated for `WeakDual ℂ A`.

Finally, `WeakDual.ext_nonneg`: a functional on a C⋆-algebra is determined by its values on
nonnegative elements, since these span the algebra.

## Functional compression

Compressing a weak-* dual functional `ω` by `v : A` yields `z ↦ ω (star v * z * v)` as a weak-*
continuous linear map `TauCeti.compressFunctional v : WeakDual 𝕜 A →L[𝕜] WeakDual 𝕜 A`
(`TauCeti.compressFunctional_apply`), with operator norm bound
`TauCeti.norm_toStrongDual_compressFunctional_le` (`‖toStrongDual (compressFunctional v ω)‖ ≤
‖toStrongDual ω‖ * ‖v‖ ^ 2`), preservation of positivity (`TauCeti.map_nonneg_compressFunctional`),
and weak-* closed unit-ball preservation (`TauCeti.compressFunctional_mem_closedBall`).
-/

public section

open Filter
open scoped ComplexOrder Topology

namespace PositiveContinuousLinearMap

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- Pulling a positive functional back along a surjective star-algebra homomorphism of
C⋆-algebras preserves its norm. -/
theorem opNorm_comp_ofClass_of_surjective (ω : B →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f) :
    ‖((ω.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = ‖(ω : B →L[ℂ] ℂ)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  exact Complex.ofReal_injective <| tendsto_nhds_unique
    ((ω.comp (.ofClass f)).tendsto_nhds_opNorm hl)
    (Filter.tendsto_map'_iff.mp (ω.tendsto_nhds_opNorm (hl.map f hf)))

/-- The norm of a sum of positive functionals on a C⋆-algebra is the sum of their norms. -/
theorem opNorm_add (τ σ : A →P[ℂ] ℂ) :
    ‖((τ + σ : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = ‖(τ : A →L[ℂ] ℂ)‖ + ‖(σ : A →L[ℂ] ℂ)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  refine Complex.ofReal_injective <| tendsto_nhds_unique ((τ + σ).tendsto_nhds_opNorm hl) ?_
  push_cast
  exact (τ.tendsto_nhds_opNorm hl).add (σ.tendsto_nhds_opNorm hl)

/-- A positive functional vanishes at every element `a` with `ω (star a * a) = 0`, since
`‖ω a‖ ^ 2 ≤ ‖ω‖ ‖ω (star a * a)‖`. -/
theorem map_eq_zero_of_map_star_mul_self_eq_zero (ω : A →P[ℂ] ℂ) {a : A}
    (ha : ω (star a * a) = 0) : ω a = 0 := by
  simpa [ha] using ω.norm_map_sq_le_opNorm_mul a

end PositiveContinuousLinearMap

namespace WeakDual

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : WeakDual ℂ A}

/-- A functional on a C⋆-algebra is determined by its values on nonnegative elements, since
these span the algebra. In particular two states that agree on nonnegative elements are equal. -/
theorem ext_nonneg {φ ψ : WeakDual ℂ A} (h : ∀ a, 0 ≤ a → φ a = ψ a) : φ = ψ := by
  have := LinearMap.ext_on (CStarAlgebra.span_nonneg (A := A))
    (f := (toStrongDual φ : A →ₗ[ℂ] ℂ)) (g := toStrongDual ψ) fun a ha => h a ha
  exact DFunLike.ext _ _ fun a => by simpa using LinearMap.congr_fun this a

/-- A functional that is nonnegative on nonnegative elements is monotone. -/
theorem monotone_toStrongDual_of_map_nonneg (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    Monotone (toStrongDual φ) :=
  (monotone_iff_map_nonneg _).mpr fun a ha => (hφ a ha).trans_eq (toStrongDual_apply φ a).symm

/-- Along the approximate unit, a functional that is nonnegative on nonnegative elements tends
to its norm. -/
theorem tendsto_approximateUnit_norm_of_map_nonneg (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    Tendsto (fun e => φ e) (CStarAlgebra.approximateUnit A) (𝓝 (‖toStrongDual φ‖ : ℂ)) := by
  simpa using (ContinuousLinearMap.monotone_iff_tendsto_nhds_opNorm
    (CStarAlgebra.increasingApproximateUnit A)).mp (monotone_toStrongDual_of_map_nonneg hφ)

end NonUnital

/-- On a unital C⋆-algebra, the norm of a functional that is nonnegative on nonnegative elements
is its value at `1`. -/
theorem norm_toStrongDual_eq_map_one_of_map_nonneg {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {φ : WeakDual ℂ A} (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    (‖toStrongDual φ‖ : ℂ) = φ 1 := by
  simpa using ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mp
    (monotone_toStrongDual_of_map_nonneg hφ)

end WeakDual

namespace TauCeti

section Compress

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A] [StarRing A]
  [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-- Compress a weak-* dual functional `ω : WeakDual 𝕜 A` by `v : A`, sending `z` to
`ω (star v * z * v)`. -/
noncomputable def compressFunctional (v : A) : WeakDual 𝕜 A →L[𝕜] WeakDual 𝕜 A where
  toFun ω := StrongDual.toWeakDual
    ((WeakDual.toStrongDual ω).comp (ContinuousLinearMap.mulLeftRight 𝕜 A (star v) v))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := WeakDual.continuous_of_continuous_eval fun a => WeakDual.eval_continuous (star v * a * v)

/-- Compressing `ω` by `v` evaluates at `z` as `ω (star v * z * v)`. -/
@[simp]
theorem compressFunctional_apply (v : A) (ω : WeakDual 𝕜 A) (z : A) :
    compressFunctional v ω z = ω (star v * z * v) := by
  unfold compressFunctional
  rfl

/-- The operator norm of `compressFunctional v ω` is at most `‖toStrongDual ω‖ * ‖v‖ ^ 2`. -/
theorem norm_toStrongDual_compressFunctional_le [NormedStarGroup A] (v : A)
    (ω : WeakDual 𝕜 A) :
    ‖WeakDual.toStrongDual (compressFunctional v ω)‖ ≤ ‖WeakDual.toStrongDual ω‖ * ‖v‖ ^ 2 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hmul := ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le 𝕜 A (star v) v
  rw [norm_star v, ← sq] at hmul
  exact mul_le_mul_of_nonneg_left hmul (norm_nonneg _)

/-- Compressing a functional that is nonnegative on nonnegative elements preserves nonnegativity
on nonnegative elements. -/
theorem map_nonneg_compressFunctional [PartialOrder A] [StarOrderedRing A] [PartialOrder 𝕜]
    {v : A} {ω : WeakDual 𝕜 A} (hω : ∀ z : A, 0 ≤ z → 0 ≤ ω z) {z : A} (hz : 0 ≤ z) :
    0 ≤ compressFunctional v ω z := by
  rw [compressFunctional_apply]
  exact hω _ (star_left_conjugate_nonneg hz v)

/-- If `‖toStrongDual ω‖ ≤ 1` and `‖v‖ ≤ 1`, then `compressFunctional v ω` lies in the weak-*
closed unit ball `toStrongDual ⁻¹' Metric.closedBall 0 1`. -/
theorem compressFunctional_mem_closedBall [NormedStarGroup A] {v : A} (hv : ‖v‖ ≤ 1)
    {ω : WeakDual 𝕜 A} (hω : ‖WeakDual.toStrongDual ω‖ ≤ 1) :
    compressFunctional v ω ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1 := by
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  calc ‖WeakDual.toStrongDual (compressFunctional v ω)‖
      ≤ ‖WeakDual.toStrongDual ω‖ * ‖v‖ ^ 2 := norm_toStrongDual_compressFunctional_le v ω
    _ ≤ 1 * 1 ^ 2 := by gcongr
    _ = 1 := by norm_num

end Compress

end TauCeti
