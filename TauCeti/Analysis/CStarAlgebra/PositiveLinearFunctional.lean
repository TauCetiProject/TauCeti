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

/-!
# Norms of positive functionals on C⋆-algebras

## Pullback along surjective homomorphisms

The norm of a positive functional on a possibly nonunital C⋆-algebra is its limit along any
increasing approximate unit, Mathlib's `PositiveContinuousLinearMap.tendsto_nhds_opNorm`. A
surjective star-algebra homomorphism carries increasing approximate units to increasing
approximate units, so pulling a positive functional back along it does not change the norm,
`PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective`. In particular states pull back
to states along quotient maps; without surjectivity the norm can drop, for instance to `0`.

## Positive functionals in the weak-* dual

For a functional `φ : WeakDual ℂ A` on a C⋆-algebra that is nonnegative on nonnegative elements,
this file records the norm facts about positive functionals in the form used on the weak-* dual.

* `WeakDual.toPositiveLinearMap`: bundles `φ` as a positive linear map `A →ₚ[ℂ] ℂ`.
* `WeakDual.map_star_of_map_nonneg` and `WeakDual.isSelfAdjoint_apply_of_map_nonneg`: `φ`
  commutes with `star` and takes real values on self-adjoint elements.
* `WeakDual.norm_apply_sq_le_mul_of_map_nonneg`: the Cauchy–Schwarz inequality
  `‖φ a‖ ^ 2 ≤ ‖φ‖ * ‖φ (star a * a)‖`.
* `WeakDual.monotone_toStrongDual_of_map_nonneg`: `φ` is monotone.
* `WeakDual.tendsto_approximateUnit_norm_of_map_nonneg`: along the approximate unit, `φ` tends
  to its norm.
* `WeakDual.norm_toStrongDual_eq_map_one_of_map_nonneg`: if `A` is unital, the norm of `φ` is
  `φ 1`.

These restate Mathlib's `PositiveContinuousLinearMap.norm_map_sq_le_opNorm_mul`,
`ContinuousLinearMap.monotone_iff_tendsto_nhds_opNorm`, and
`ContinuousLinearMap.monotone_iff_opNorm_eq_map_one` for `WeakDual ℂ A`.

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

end PositiveContinuousLinearMap

namespace WeakDual

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : WeakDual ℂ A}

/-- Bundle a weak-* functional that is nonnegative on nonnegative elements as a `PositiveLinearMap`
`A →ₚ[ℂ] ℂ`. -/
noncomputable def toPositiveLinearMap (φ : WeakDual ℂ A) (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    A →ₚ[ℂ] ℂ :=
  .mk₀ (toStrongDual φ : A →ₗ[ℂ] ℂ) hφ

/-- `φ.toPositiveLinearMap hφ` evaluates as `φ`. -/
@[simp]
theorem toPositiveLinearMap_apply (φ : WeakDual ℂ A) (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) (a : A) :
    φ.toPositiveLinearMap hφ a = φ a :=
  (rfl)

/-- The underlying linear map of `φ.toPositiveLinearMap hφ` is `toStrongDual φ`. -/
@[simp]
theorem toLinearMap_toPositiveLinearMap (φ : WeakDual ℂ A) (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    (φ.toPositiveLinearMap hφ).toLinearMap = (toStrongDual φ : A →ₗ[ℂ] ℂ) :=
  (rfl)

/-- Bundling `φ.toPositiveLinearMap hφ` as a continuous positive functional recovers
`toStrongDual φ`. -/
@[simp]
theorem coe_ofClass_toPositiveLinearMap (φ : WeakDual ℂ A) (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    (PositiveContinuousLinearMap.ofClass (φ.toPositiveLinearMap hφ) : A →L[ℂ] ℂ) =
      toStrongDual φ := by
  -- `PositiveLinearMap.mk₀` has no bundled equality lemma; both evaluate as `φ` by definition.
  ext
  rfl

/-- A functional on a C⋆-algebra that is nonnegative on nonnegative elements commutes with
`star`. -/
theorem map_star_of_map_nonneg (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) (a : A) :
    φ (star a) = star (φ a) :=
  map_star (φ.toPositiveLinearMap hφ) a

/-- A functional on a C⋆-algebra that is nonnegative on nonnegative elements maps self-adjoint
elements to self-adjoint (real) scalars. -/
theorem isSelfAdjoint_apply_of_map_nonneg (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) {a : A}
    (ha : IsSelfAdjoint a) : IsSelfAdjoint (φ a) :=
  ha.map (φ.toPositiveLinearMap hφ)

/-- Cauchy–Schwarz inequality for a positive functional in the weak-* dual:
`‖φ a‖ ^ 2 ≤ ‖φ‖ * ‖φ (star a * a)‖`. -/
theorem norm_apply_sq_le_mul_of_map_nonneg (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) (a : A) :
    ‖φ a‖ ^ 2 ≤ ‖toStrongDual φ‖ * ‖φ (star a * a)‖ := by
  simpa using
    (PositiveContinuousLinearMap.ofClass (φ.toPositiveLinearMap hφ)).norm_map_sq_le_opNorm_mul a

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
