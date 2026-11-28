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
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Norms of positive functionals on C⋆-algebras

## Norm along approximate units

The norm of a positive functional on a possibly nonunital C⋆-algebra is its limit along any
increasing approximate unit, Mathlib's `PositiveContinuousLinearMap.tendsto_nhds_opNorm`. As direct
consequences:

* `PositiveContinuousLinearMap.opNorm_add`: the operator norm is additive on positive functionals,
  `‖ω₁ + ω₂‖ = ‖ω₁‖ + ‖ω₂‖`.
* `PositiveContinuousLinearMap.opNorm_smul`: positive functionals form an `ℝ≥0`-module, and
  scaling by a nonnegative real multiplies the norm.
* `PositiveContinuousLinearMap.tendsto_mul_self_nhds_opNorm`: along any increasing approximate unit
  `e`, the squared values `ω (e * e)` also tend to `‖ω‖`.

## Pullback and lifting along star homomorphisms

* `PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective`: a surjective star-algebra
  homomorphism carries increasing approximate units to increasing approximate units, so pulling a
  positive functional back along it does not change the norm. In particular states pull back to
  states along quotient maps; without surjectivity the norm can drop, for instance to `0`.
  Along a star isomorphism `e`, pulling back along `e` and then along `e.symm` (or the other way
  round) recovers the functional,
  `PositiveContinuousLinearMap.comp_ofClass_comp_ofClass_symm` and
  `PositiveContinuousLinearMap.comp_ofClass_symm_comp_ofClass`. On unital C⋆-algebras,
  `‖ω‖ = ω 1`, so pulling back along any star homomorphism that preserves `1` also preserves the
  norm (`PositiveContinuousLinearMap.opNorm_comp_ofClass_of_map_one`,
  `PositiveContinuousLinearMap.opNorm_comp_ofClass`).

## Cauchy–Schwarz vanishing criteria

* `PositiveContinuousLinearMap.map_eq_zero_of_map_star_mul_self_eq_zero`: a positive continuous
  linear functional vanishing on `star a * a` vanishes on `a`.

* `PositiveLinearMap.map_mul_eq_zero_of_map_star_mul_eq_zero` and
  `PositiveLinearMap.map_mul_eq_zero_of_map_mul_star_eq_zero`: if a positive linear functional
  vanishes on `star b * b` (resp. `b * star b`), it vanishes on `a * b` (resp. `b * a`).
* `PositiveLinearMap.map_eq_zero_of_map_star_mul_self_eq_zero` and
  `PositiveLinearMap.map_eq_zero_of_map_mul_star_self_eq_zero`: on a C⋆-algebra, a positive linear
  functional vanishing on `star x * x` or `x * star x` vanishes on `x`.
* `PositiveLinearMap.map_eq_zero_of_re_eq_zero`: a positive map vanishing in real part on a
  nonnegative element vanishes on that element.

Conversely, any positive functional `ω : A →P[ℂ] ℂ` vanishing on the kernel of a surjective star
homomorphism `f : A → B` lifts uniquely (`PositiveContinuousLinearMap.eq_liftOfSurjective_iff`) to
a positive continuous linear functional `ω.liftOfSurjective f hf hker` on `B` of the same operator
norm (`PositiveContinuousLinearMap.opNorm_liftOfSurjective`).

## Positive functionals in the weak-* dual

For a functional `φ : WeakDual ℂ A` on a C⋆-algebra that is nonnegative on nonnegative elements,
this file records the norm facts about positive functionals in the form used on the weak-* dual.

* `WeakDual.toPositiveLinearMap`: bundles `φ` as a positive linear map `A →ₚ[ℂ] ℂ`.
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

/-- A positive contraction `e` bounds the value of a positive functional on the positive
square of `1 - e` by the norm of the functional minus the real part of its value at `e`. -/
theorem norm_map_star_one_sub_mul_one_sub_le {A : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →P[ℂ] ℂ) {e : A} (he : 0 ≤ e) (he₁ : ‖e‖ ≤ 1) :
    ‖f (star (1 - e) * (1 - e))‖ ≤ ‖(f : A →L[ℂ] ℂ)‖ - (f e).re := by
  have hnonneg : 0 ≤ 1 - e :=
    sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg e he).mp he₁)
  have hnorm : ‖1 - e‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hnonneg).mpr (sub_le_self _ he)
  have hle : f ((1 - e) * (1 - e)) ≤ f (1 - e) :=
    f.mono (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hnonneg hnorm)
  rw [← Complex.re_eq_norm.mpr (f.map_nonneg (star_mul_self_nonneg _)), hnonneg.star_eq]
  simpa only [map_sub, ← f.ofReal_opNorm_eq_map_one, Complex.sub_re, Complex.ofReal_re] using
    (Complex.le_def.mp hle).1

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

section StarOrdered

variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [Module ℂ A] [StarRing A]
  [StarOrderedRing A] [SelfAdjointDecompose A] [StarModule ℂ A] [IsScalarTower ℂ A A]
  {F : Type*} [FunLike F A ℂ] [LinearMapClass F ℂ A ℂ] [OrderHomClass F A ℂ]

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

end StarOrdered

section Order

/-- A positive map vanishing in real part on a nonnegative element vanishes on that element. -/
theorem map_eq_zero_of_re_eq_zero {A : Type*} [Preorder A] [Zero A]
    {F : Type*} [FunLike F A ℂ] [ZeroHomClass F A ℂ] [OrderHomClass F A ℂ]
    (f : F) {x : A} (hx : 0 ≤ x) (hre : (f x).re = 0) : f x = 0 :=
  Complex.ext hre (Complex.nonneg_iff.mp (map_nonneg f hx)).2.symm

end Order

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
theorem toContinuousLinearMap_ofClass_toPositiveLinearMap (φ : WeakDual ℂ A)
    (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    (PositiveContinuousLinearMap.ofClass (φ.toPositiveLinearMap hφ) : A →L[ℂ] ℂ) =
      toStrongDual φ := by
  ext a
  simp

/-- Two positive functionals define the same `PositiveLinearMap` if and only if they are equal. -/
@[simp]
theorem toPositiveLinearMap_inj {φ ψ : WeakDual ℂ A}
    {hφ : ∀ a, 0 ≤ a → 0 ≤ φ a} {hψ : ∀ a, 0 ≤ a → 0 ≤ ψ a} :
    φ.toPositiveLinearMap hφ = ψ.toPositiveLinearMap hψ ↔ φ = ψ :=
  ⟨fun h => DFunLike.ext _ _ fun a => by simpa using DFunLike.congr_fun h a,
    fun h => by subst h; rfl⟩

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
