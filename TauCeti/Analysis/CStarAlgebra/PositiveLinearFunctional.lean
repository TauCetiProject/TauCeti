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
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Norms and compression of positive functionals on C⋆-algebras

## Pullback and lifting along star homomorphisms

The norm of a positive functional on a possibly nonunital C⋆-algebra is its limit along any
increasing approximate unit, Mathlib's `PositiveContinuousLinearMap.tendsto_nhds_opNorm`. A
surjective star-algebra homomorphism carries increasing approximate units to increasing
approximate units, so pulling a positive functional back along it does not change the norm,
`PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective`. In particular states pull back
to states along quotient maps; without surjectivity the norm can drop, for instance to `0`.
For the same reason the norm is additive on positive functionals,
`PositiveContinuousLinearMap.opNorm_add`.
Positive functionals are closed under scaling by a nonnegative real, so they form an
`ℝ≥0`-module, and scaling multiplies the norm (`PositiveContinuousLinearMap.opNorm_smul`);
Mathlib only provides the `ℕ`-action.
Along a star isomorphism `e`, pulling back along `e` and then along `e.symm` (or the other way
round) recovers the functional,
`PositiveContinuousLinearMap.comp_ofClass_comp_ofClass_symm` and
`PositiveContinuousLinearMap.comp_ofClass_symm_comp_ofClass`. On unital C⋆-algebras,
`‖ω‖ = ω 1`, so pulling back along any star homomorphism that preserves `1` also preserves the
norm (`PositiveContinuousLinearMap.opNorm_comp_ofClass_of_map_one`,
`PositiveContinuousLinearMap.opNorm_comp_ofClass`).

The bound `‖ω a‖ ^ 2 ≤ ‖ω‖ ‖ω (star a * a)‖` of Mathlib's
`PositiveContinuousLinearMap.norm_map_sq_le_opNorm_mul` shows that a positive functional vanishes
at every `a` with `ω (star a * a) = 0`
(`PositiveContinuousLinearMap.map_eq_zero_of_map_star_mul_self_eq_zero`). More generally, by the
Cauchy–Schwarz inequality a positive linear functional `f` vanishing at `b⋆ b` kills every product
`a b` (`PositiveLinearMap.map_mul_eq_zero_of_map_star_mul_eq_zero`), and one vanishing at `b b⋆`
kills every product `b a` (`PositiveLinearMap.map_mul_eq_zero_of_map_mul_star_eq_zero`).

Conversely, any positive functional `ω : A →P[ℂ] ℂ` vanishing on the kernel of a surjective star
homomorphism `f : A → B` lifts uniquely (`PositiveContinuousLinearMap.eq_liftOfSurjective_iff`) to
a positive continuous linear functional `ω.liftOfSurjective f hf hker` on `B` of the same operator
norm (`PositiveContinuousLinearMap.opNorm_liftOfSurjective`).

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
(`TauCeti.compressFunctional_apply`), defined via `WeakDual.precomp`, with composition and
unital identity laws (`TauCeti.compressFunctional_comp`, `TauCeti.compressFunctional_one`), operator
norm bound `TauCeti.norm_toStrongDual_compressFunctional_le`
(`‖toStrongDual (compressFunctional v ω)‖ ≤ ‖toStrongDual ω‖ * ‖v‖ ^ 2`), preservation of
positivity (`TauCeti.map_nonneg_compressFunctional`), and weak-* closed unit-ball preservation
(`TauCeti.compressFunctional_mem_closedBall`).
-/

public section

open Filter
open scoped ComplexOrder NNReal Topology

namespace PositiveContinuousLinearMap

section NNRealSMul

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [TopologicalSpace E]
  [Module ℂ E]

/-- Positive functionals are closed under scaling by a nonnegative real. -/
noncomputable instance instSMulNNReal : SMul ℝ≥0 (E →P[ℂ] ℂ) where
  smul c τ := mk₀ (c • (τ : E →L[ℂ] ℂ)) fun x hx ↦ by
    simpa [NNReal.smul_def] using
      mul_nonneg (Complex.zero_le_real.mpr c.property) (τ.map_nonneg hx)

instance : IsSMulApply ℝ≥0 (E →P[ℂ] ℂ) where

/-- The continuous linear map underlying `c • τ` is `c • τ`. -/
@[simp]
theorem toContinuousLinearMap_smul (c : ℝ≥0) (τ : E →P[ℂ] ℂ) :
    ((c • τ : E →P[ℂ] ℂ) : E →L[ℂ] ℂ) = c • (τ : E →L[ℂ] ℂ) :=
  (rfl)

/-- Positive functionals form a module over the nonnegative reals. -/
noncomputable instance instModuleNNReal : Module ℝ≥0 (E →P[ℂ] ℂ) :=
  fast_instance% FunLike.module

end NNRealSMul

/-- Scaling a positive functional by a nonnegative real `c` multiplies its norm by `c`. -/
theorem opNorm_smul {E : Type*} [SeminormedAddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [NormedSpace ℂ E] (c : ℝ≥0) (τ : E →P[ℂ] ℂ) :
    ‖((c • τ : E →P[ℂ] ℂ) : E →L[ℂ] ℂ)‖ = c * ‖(τ : E →L[ℂ] ℂ)‖ := by
  rw [toContinuousLinearMap_smul, NNReal.smul_def, norm_smul, NNReal.norm_eq]

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- Pulling a positive functional back along a surjective star-algebra homomorphism of
C⋆-algebras preserves its norm. -/
theorem opNorm_comp_ofClass_of_surjective (ω : B →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f) :
    ‖((ω.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = ‖(ω : B →L[ℂ] ℂ)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  exact Complex.ofReal_injective <| tendsto_nhds_unique
    ((ω.comp (.ofClass f)).tendsto_nhds_opNorm hl)
    (Filter.tendsto_map'_iff.mp (ω.tendsto_nhds_opNorm (hl.map f hf)))

/-- Pulling a positive functional back along a star isomorphism and then along its inverse
recovers the functional. -/
@[simp]
theorem comp_ofClass_comp_ofClass_symm (e : A ≃⋆ₐ[ℂ] B) (ω : B →P[ℂ] ℂ) :
    (ω.comp (.ofClass e)).comp (.ofClass e.symm) = ω := by
  ext b
  simp

/-- Pulling a positive functional back along the inverse of a star isomorphism and then along
the isomorphism recovers the functional. -/
@[simp]
theorem comp_ofClass_symm_comp_ofClass (e : A ≃⋆ₐ[ℂ] B) (ω : A →P[ℂ] ℂ) :
    (ω.comp (.ofClass e.symm)).comp (.ofClass e) = ω := by
  ext a
  simp

/-- Lift a positive continuous linear functional `ω : A →P[ℂ] ℂ` along a surjective star
homomorphism `f : A → B` on whose kernel `ω` vanishes. -/
noncomputable def liftOfSurjective (ω : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → ω a = 0) : B →P[ℂ] ℂ :=
  -- Positive linear maps between C⋆-algebras are automatically continuous (`ofClass`).
  let fL : A →ₗ[ℂ] B := LinearMap.ofClass f
  let hkerL : LinearMap.ker fL ≤ LinearMap.ker ω.toLinearMap := fun a ha =>
    LinearMap.mem_ker.mpr (hker a (LinearMap.mem_ker.mp ha))
  let L : B →ₗ[ℂ] ℂ := fL.liftOfSurjective hf ⟨ω.toLinearMap, hkerL⟩
  have hpos : ∀ b : B, 0 ≤ b → 0 ≤ L b := fun b hb => by
    obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
    obtain ⟨a, rfl⟩ := hf c
    have hL : L (f (star a * a)) = ω (star a * a) :=
      LinearMap.equivOfSurjective_apply (f := fL) hf hkerL (m := star a * a)
    rw [← map_star f, ← map_mul f, hL]
    exact ω.map_nonneg (star_mul_self_nonneg a)
  .ofClass (PositiveLinearMap.mk₀ L hpos)

/-- `ω.liftOfSurjective f hf hker` evaluates at `f a` as `ω a`. -/
@[simp]
theorem liftOfSurjective_apply (ω : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → ω a = 0) (a : A) :
    ω.liftOfSurjective f hf hker (f a) = ω a :=
  -- `PositiveContinuousLinearMap.ofClass` and `PositiveLinearMap.mk₀` preserve the underlying
  -- function definitionally.
  LinearMap.equivOfSurjective_apply (f := LinearMap.ofClass f) hf
    (fun x hx => LinearMap.mem_ker.mpr (hker x (LinearMap.mem_ker.mp hx))) (m := a)

/-- Pulling `ω.liftOfSurjective f hf hker` back along `f` recovers `ω`. -/
@[simp]
theorem liftOfSurjective_comp_ofClass (ω : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → ω a = 0) :
    (ω.liftOfSurjective f hf hker).comp (.ofClass f) = ω := by
  ext a
  exact ω.liftOfSurjective_apply f hf hker a

/-- **Uniqueness of `liftOfSurjective`.** A positive continuous linear functional `ψ` on `B` equals
`ω.liftOfSurjective f hf hker` if and only if its pullback along `f` equals `ω`. -/
theorem eq_liftOfSurjective_iff (ω : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → ω a = 0) {ψ : B →P[ℂ] ℂ} :
    ψ = ω.liftOfSurjective f hf hker ↔ ψ.comp (.ofClass f) = ω := by
  refine ⟨fun h => h ▸ ω.liftOfSurjective_comp_ofClass f hf hker, fun h => ?_⟩
  ext b
  obtain ⟨a, rfl⟩ := hf b
  rw [ω.liftOfSurjective_apply f hf hker a, ← h, comp_apply, coe_ofClass]

/-- Lifting a positive functional along a surjective star homomorphism preserves its norm. -/
@[simp]
theorem opNorm_liftOfSurjective (ω : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → ω a = 0) :
    ‖(ω.liftOfSurjective f hf hker : B →L[ℂ] ℂ)‖ = ‖(ω : A →L[ℂ] ℂ)‖ := by
  rw [← opNorm_comp_ofClass_of_surjective (ω.liftOfSurjective f hf hker) f hf,
    liftOfSurjective_comp_ofClass]

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

namespace TauCeti

section Compress

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A] [StarRing A]
  [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-- Compress a weak-* dual functional `ω : WeakDual 𝕜 A` by `v : A`, sending `z` to
`ω (star v * z * v)`. -/
noncomputable def compressFunctional (v : A) : WeakDual 𝕜 A →L[𝕜] WeakDual 𝕜 A :=
  WeakDual.precomp (ContinuousLinearMap.mulLeftRight 𝕜 A (star v) v)

/-- Compressing `ω` by `v` evaluates at `z` as `ω (star v * z * v)`. -/
@[simp]
theorem compressFunctional_apply (v : A) (ω : WeakDual 𝕜 A) (z : A) :
    compressFunctional v ω z = ω (star v * z * v) := by
  simp [compressFunctional]

/-- Compressing by `v` after `w` sends `z ↦ ω (star w * (star v * z * v) * w)`, which is
compressing by `v * w`. -/
@[simp]
theorem compressFunctional_comp (v w : A) :
    (compressFunctional (𝕜 := 𝕜) v).comp (compressFunctional w) =
      compressFunctional (v * w) :=
  ContinuousLinearMap.ext fun ω => DFunLike.ext _ _ fun z => by
    simp [star_mul, mul_assoc]

/-- The operator norm of `compressFunctional v ω` is at most `‖toStrongDual ω‖ * ‖v‖ ^ 2`. -/
theorem norm_toStrongDual_compressFunctional_le [NormedStarGroup A] (v : A)
    (ω : WeakDual 𝕜 A) :
    ‖WeakDual.toStrongDual (compressFunctional v ω)‖ ≤ ‖WeakDual.toStrongDual ω‖ * ‖v‖ ^ 2 := by
  rw [compressFunctional, WeakDual.toStrongDual_precomp]
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

/-- In a unital ring, compressing by `1` is the identity map on `WeakDual 𝕜 A`. -/
@[simp]
theorem compressFunctional_one {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [SeminormedRing A]
    [StarRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] :
    compressFunctional (𝕜 := 𝕜) (1 : A) = ContinuousLinearMap.id 𝕜 (WeakDual 𝕜 A) :=
  ContinuousLinearMap.ext fun ω => DFunLike.ext _ _ fun z => by simp

end TauCeti
