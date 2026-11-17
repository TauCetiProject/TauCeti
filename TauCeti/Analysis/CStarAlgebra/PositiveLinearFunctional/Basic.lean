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
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Norms of positive functionals on C⋆-algebras

## Norm along approximate units

The norm of a positive functional on a possibly nonunital C⋆-algebra is its limit along any
increasing approximate unit, Mathlib's `PositiveContinuousLinearMap.tendsto_nhds_opNorm`. As direct
consequences:

* `PositiveContinuousLinearMap.opNorm_add`: the operator norm is additive on positive functionals,
  `‖ω₁ + ω₂‖ = ‖ω₁‖ + ‖ω₂‖`.
* `PositiveContinuousLinearMap.tendsto_mul_self_nhds_opNorm`: along any increasing approximate unit
  `e`, the squared values `ω (e * e)` also tend to `‖ω‖`.

## Pullback along surjective homomorphisms

* `PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective`: a surjective star-algebra
  homomorphism carries increasing approximate units to increasing approximate units, so pulling a
  positive functional back along it does not change the norm. In particular states pull back to
  states along quotient maps; without surjectivity the norm can drop, for instance to `0`.

## Cauchy–Schwarz vanishing criteria

* `PositiveLinearMap.map_mul_eq_zero_of_map_mul_star_self_eq_zero` and
  `PositiveLinearMap.map_mul_eq_zero_of_map_star_mul_self_eq_zero`: if a positive linear functional
  vanishes on `x * star x` (resp. `star y * y`), it vanishes on `x * y`.
* `PositiveLinearMap.map_eq_zero_of_map_star_mul_self_eq_zero` and
  `PositiveLinearMap.map_eq_zero_of_map_mul_star_self_eq_zero`: on a C⋆-algebra, a positive linear
  functional vanishing on `star x * x` or `x * star x` vanishes on `x`.

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

section Norm

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The operator norm is additive on positive continuous linear functionals. -/
theorem opNorm_add (ω₁ ω₂ : A →P[ℂ] ℂ) :
    ‖((ω₁ + ω₂ : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ =
      ‖(ω₁ : A →L[ℂ] ℂ)‖ + ‖(ω₂ : A →L[ℂ] ℂ)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  exact Complex.ofReal_injective <| tendsto_nhds_unique
    ((ω₁ + ω₂).tendsto_nhds_opNorm hl)
    (by
      simpa [Complex.ofReal_add] using
        (ω₁.tendsto_nhds_opNorm hl).add (ω₂.tendsto_nhds_opNorm hl))

/-- Along any increasing approximate unit `e`, the values `ω (e * e)` of a positive continuous
linear functional tend to `‖ω‖`. -/
theorem tendsto_mul_self_nhds_opNorm (ω : A →P[ℂ] ℂ) {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) :
    Tendsto (fun e => ω (e * e)) l (𝓝 (‖(ω : A →L[ℂ] ℂ)‖ : ℂ)) := by
  by_cases h0 : ‖(ω : A →L[ℂ] ℂ)‖ = 0
  · have hω : (ω : A →L[ℂ] ℂ) = 0 := norm_eq_zero.mp h0
    have hval : ∀ x, ω x = 0 := fun x => by
      simpa using DFunLike.congr_fun hω x
    simpa [h0, hval] using tendsto_const_nhds
  have hpos : 0 < ‖(ω : A →L[ℂ] ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hlim : Tendsto (fun e => ‖ω e‖) l (𝓝 ‖(ω : A →L[ℂ] ℂ)‖) := by
    simpa [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using
      (ω.tendsto_nhds_opNorm hl).norm
  have hnorm : Tendsto (fun e => ‖ω (e * e)‖) l (𝓝 ‖(ω : A →L[ℂ] ℂ)‖) := by
    have hlo : Tendsto (fun e => ‖ω e‖ ^ 2 / ‖(ω : A →L[ℂ] ℂ)‖) l (𝓝 ‖(ω : A →L[ℂ] ℂ)‖) := by
      have h := (hlim.pow 2).div_const ‖(ω : A →L[ℂ] ℂ)‖
      rwa [sq, mul_div_cancel_right₀ _ h0] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hlim ?_ ?_
    · filter_upwards [hl.eventually_nonneg] with e he
      have hsq : star e * e = e * e := by rw [he.isSelfAdjoint.star_eq]
      rw [div_le_iff₀ hpos, mul_comm, ← hsq]
      exact ω.norm_map_sq_le_opNorm_mul e
    · filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
      refine CStarAlgebra.norm_le_norm_of_le_of_nonneg (ω.mono ?_) (ω.map_nonneg ?_)
      · exact CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one he₀ he₁
      · simpa [he₀.isSelfAdjoint.star_eq] using star_mul_self_nonneg e
  refine hnorm.ofReal.congr' ?_
  filter_upwards [hl.eventually_nonneg] with e he₀
  have hsq : 0 ≤ e * e := by simpa [he₀.isSelfAdjoint.star_eq] using star_mul_self_nonneg e
  exact Complex.norm_of_nonneg' (ω.map_nonneg hsq)

end Norm

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

end PositiveContinuousLinearMap

namespace PositiveLinearMap

section StarOrdered

variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [Module ℂ A] [StarRing A]
  [StarOrderedRing A] [SelfAdjointDecompose A] [StarModule ℂ A] [IsScalarTower ℂ A A]
  {F : Type*} [FunLike F A ℂ] [LinearMapClass F ℂ A ℂ] [OrderHomClass F A ℂ]

/-- By Cauchy–Schwarz, if a positive linear functional vanishes on `x * star x`, it vanishes on
`x * y` for every `y`. -/
theorem map_mul_eq_zero_of_map_mul_star_self_eq_zero (f : F) {x : A} (hx : f (x * star x) = 0)
    (y : A) : f (x * y) = 0 := by
  have hcs := norm_map_mul_star_le f x (star y)
  rw [star_star, hx, norm_zero, Real.sqrt_zero, zero_mul] at hcs
  exact norm_eq_zero.mp (le_antisymm hcs (norm_nonneg _))

/-- By Cauchy–Schwarz, if a positive linear functional vanishes on `star y * y`, it vanishes on
`x * y` for every `x`. -/
theorem map_mul_eq_zero_of_map_star_mul_self_eq_zero (f : F) {y : A} (hy : f (star y * y) = 0)
    (x : A) : f (x * y) = 0 := by
  have hcs := norm_map_star_mul_le f (star x) y
  rw [star_star, hy, norm_zero, Real.sqrt_zero, mul_zero] at hcs
  exact norm_eq_zero.mp (le_antisymm hcs (norm_nonneg _))

end StarOrdered

section CStar

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {F : Type*} [FunLike F A ℂ] [LinearMapClass F ℂ A ℂ] [OrderHomClass F A ℂ]

/-- On a C⋆-algebra, if a positive linear functional vanishes on `star x * x`, it vanishes on
`x`. -/
theorem map_eq_zero_of_map_star_mul_self_eq_zero (f : F) {x : A} (hx : f (star x * x) = 0) :
    f x = 0 := by
  have hcs := (PositiveContinuousLinearMap.ofClass (R := ℂ) f).norm_map_le_sqrt_opNorm_mul x
  rw [PositiveContinuousLinearMap.coe_ofClass, hx, norm_zero, Real.sqrt_zero, mul_zero] at hcs
  exact norm_eq_zero.mp (le_antisymm hcs (norm_nonneg _))

/-- On a C⋆-algebra, if a positive linear functional vanishes on `x * star x`, it vanishes on
`x`. -/
theorem map_eq_zero_of_map_mul_star_self_eq_zero (f : F) {x : A} (hx : f (x * star x) = 0) :
    f x = 0 := by
  have h : f (star x) = 0 :=
    map_eq_zero_of_map_star_mul_self_eq_zero f (x := star x) (by rwa [star_star])
  have hstar : star (f x) = 0 := by simpa only [map_star] using h
  exact star_eq_zero.mp hstar

end CStar

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
