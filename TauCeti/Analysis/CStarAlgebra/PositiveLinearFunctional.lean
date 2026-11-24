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
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Norms of positive functionals on C⋆-algebras

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
(`PositiveContinuousLinearMap.map_eq_zero_of_map_star_mul_self_eq_zero`). More generally, by the
Cauchy–Schwarz inequality a positive linear functional `f` vanishing at `b⋆ b` kills every product
`a b` (`PositiveLinearMap.map_mul_eq_zero_of_map_star_mul_eq_zero`), and one vanishing at `b b⋆`
kills every product `b a` (`PositiveLinearMap.map_mul_eq_zero_of_map_mul_star_eq_zero`).

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

namespace PositiveLinearMap

variable {A F : Type*} [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [Module ℂ A] [SelfAdjointDecompose A] [StarModule ℂ A] [IsScalarTower ℂ A A]
  [FunLike F A ℂ] [LinearMapClass F ℂ A ℂ] [OrderHomClass F A ℂ]

/-- A positive linear functional that vanishes at `b⋆ b` kills every product `a * b`, by the
Cauchy–Schwarz inequality. -/
theorem map_mul_eq_zero_of_map_star_mul_eq_zero (f : F) {b : A} (hb : f (star b * b) = 0)
    (a : A) : f (a * b) = 0 := by
  have h := norm_map_star_mul_le f (star a) b
  simp only [star_star, hb, norm_zero, Real.sqrt_zero, mul_zero, norm_le_zero_iff] at h
  exact h

/-- A positive linear functional that vanishes at `b b⋆` kills every product `b * a`, by the
Cauchy–Schwarz inequality. -/
theorem map_mul_eq_zero_of_map_mul_star_eq_zero (f : F) {b : A} (hb : f (b * star b) = 0)
    (a : A) : f (b * a) = 0 := by
  have h := norm_map_mul_star_le f b (star a)
  simp only [star_star, hb, norm_zero, Real.sqrt_zero, zero_mul, norm_le_zero_iff] at h
  exact h

end PositiveLinearMap

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
