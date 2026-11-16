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

## Pullback and descent along star homomorphisms

The norm of a positive functional on a possibly nonunital C⋆-algebra is its limit along any
increasing approximate unit, Mathlib's `PositiveContinuousLinearMap.tendsto_nhds_opNorm`. A
surjective star-algebra homomorphism carries increasing approximate units to increasing
approximate units, so pulling a positive functional back along it does not change the norm,
`PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective`. In particular states pull back
to states along quotient maps; without surjectivity the norm can drop, for instance to `0`.
On unital C⋆-algebras, `‖ω‖ = ω 1`, so pulling back along any star homomorphism that preserves `1`
also preserves the norm (`PositiveContinuousLinearMap.opNorm_comp_ofClass_of_map_one`,
`PositiveContinuousLinearMap.opNorm_comp_ofClass`).

Conversely, any positive functional `ω : A →P[ℂ] ℂ` vanishing on the kernel of a surjective star
homomorphism `f : A → B` descends to a positive continuous linear functional `ω.descend f hf hker`
on `B` of the same operator norm (`PositiveContinuousLinearMap.opNorm_descend`).

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

section NonUnital

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

/-- Descend a positive continuous linear functional `ω : A →P[ℂ] ℂ` along a surjective star
homomorphism `f : A → B` on whose kernel `ω` vanishes. -/
noncomputable def descend (ω : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → ω a = 0) : B →P[ℂ] ℂ :=
  -- Positive linear maps between C⋆-algebras are automatically continuous (`ofClass`).
  let fL : A →ₗ[ℂ] B := LinearMap.ofClass f
  let L : B →ₗ[ℂ] ℂ :=
    (Submodule.liftQ (LinearMap.ker fL) ω.toLinearMap fun a ha => hker a ha).comp
      (fL.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hL (a : A) : L (f a) = ω a := by
    have hmk : (fL.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a :=
      (fL.quotKerEquivOfSurjective hf).symm_apply_eq.mpr rfl
    change (Submodule.liftQ (LinearMap.ker fL) ω.toLinearMap fun x hx => hker x hx)
        ((fL.quotKerEquivOfSurjective hf).symm (f a)) = ω a
    rw [hmk]
    rfl
  have hpos : ∀ b : B, 0 ≤ b → 0 ≤ L b := fun b hb => by
    rw [StarOrderedRing.nonneg_iff] at hb
    refine AddSubmonoid.closure_induction (fun y hy => ?_) (by simp)
      (fun x y _ _ hx hy => by rw [map_add]; exact add_nonneg hx hy) hb
    obtain ⟨c, rfl⟩ := hy
    obtain ⟨a, rfl⟩ := hf c
    dsimp only
    rw [← map_star f, ← map_mul f, hL]
    exact ω.map_nonneg (star_mul_self_nonneg a)
  .ofClass (PositiveLinearMap.mk₀ L hpos)

/-- `ω.descend f hf hker` evaluates at `f a` as `ω a`. -/
@[simp]
theorem descend_apply (ω : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → ω a = 0) (a : A) :
    ω.descend f hf hker (f a) = ω a := by
  let fL : A →ₗ[ℂ] B := LinearMap.ofClass f
  have hmk : (fL.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a :=
    (fL.quotKerEquivOfSurjective hf).symm_apply_eq.mpr rfl
  change (Submodule.liftQ (LinearMap.ker fL) ω.toLinearMap fun x hx => hker x hx)
      ((fL.quotKerEquivOfSurjective hf).symm (f a)) = ω a
  rw [hmk]
  rfl

/-- Pulling `ω.descend f hf hker` back along `f` recovers `ω`. -/
@[simp]
theorem descend_comp_ofClass (ω : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → ω a = 0) :
    (ω.descend f hf hker).comp (.ofClass f) = ω := by
  ext a
  exact ω.descend_apply f hf hker a

/-- Descending a positive functional along a surjective star homomorphism preserves its norm. -/
@[simp]
theorem opNorm_descend (ω : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → ω a = 0) :
    ‖(ω.descend f hf hker : B →L[ℂ] ℂ)‖ = ‖(ω : A →L[ℂ] ℂ)‖ := by
  rw [← opNorm_comp_ofClass_of_surjective (ω.descend f hf hker) f hf, descend_comp_ofClass]

end NonUnital

section Unital

/-- Pulling a positive functional on a unital C⋆-algebra back along a star homomorphism that
preserves `1` preserves its operator norm. -/
theorem opNorm_comp_ofClass_of_map_one {A B F : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (ω : B →P[ℂ] ℂ) (f : F) (hf : f 1 = 1) :
    ‖((ω.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = ‖(ω : B →L[ℂ] ℂ)‖ := by
  apply Complex.ofReal_injective
  rw [(ω.comp (.ofClass f)).ofReal_opNorm_eq_map_one, ω.ofReal_opNorm_eq_map_one]
  simpa using congrArg ω hf

/-- Pulling a positive functional back along a unital star homomorphism between unital
C⋆-algebras preserves its operator norm. -/
theorem opNorm_comp_ofClass {A B F : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]
    (ω : B →P[ℂ] ℂ) (f : F) :
    ‖((ω.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = ‖(ω : B →L[ℂ] ℂ)‖ :=
  opNorm_comp_ofClass_of_map_one ω f (map_one f)

end Unital

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
