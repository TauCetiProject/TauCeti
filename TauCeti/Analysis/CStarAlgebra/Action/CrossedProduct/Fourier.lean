/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Regular
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Discrete
import TauCeti.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Fourier coefficients of discrete regular crossed products

For a faithful representation `ρ`, coefficient evaluation extends to a contractive linear
map `fourierCoeff` from the concrete regular crossed product to `A`. The coefficients
recover all operator matrix entries and therefore determine an element uniquely. The
construction uses counting measure on an arbitrary discrete group, including uncountable
groups, and permits nonunital coefficients and degenerate faithful representations.

This supplies the coefficient maps independently of representation-independence of the
regular norm. The coefficient at the identity is not yet bundled as a conditional expectation.

The construction follows Dana Williams, *Crossed Products of C*-Algebras*, Chapter 7,
using `RegularCrossedProduct.of` and `LinearMap.extendOfNorm`.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace CStarAlgebra

namespace TauCeti.CStarAction.RegularCrossedProduct

variable {G A H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- Coefficient evaluation on the dense convolution algebra. -/
private def coefficientEval (g : G) : ConvolutionAlgebra α Measure.count →ₗ[ℂ] A where
  toFun f := f.ofConv g
  map_add' f h := by simp
  map_smul' c f := by simp

private theorem norm_coefficientEval_le (hρ : Function.Injective ρ) (g : G)
    (f : ConvolutionAlgebra α Measure.count) :
    ‖coefficientEval α g f‖ ≤ ‖of α ρ Measure.count f‖ := by
  exact (CovariantRepresentation.norm_apply_le_norm_integratedOperator_regular
    α ρ hρ f.ofConv g).trans_eq (norm_of α ρ Measure.count f).symm

/-- The Fourier coefficient at `g`, extending `f ↦ f g` continuously from compactly supported
coefficients to the concrete regular crossed product. -/
def fourierCoeff (_hρ : Function.Injective ρ) (g : G) :
    regularAlgebra α ρ Measure.count →L[ℂ] A :=
  (coefficientEval α g).extendOfNorm (Eₗ := regularAlgebra α ρ Measure.count)
    (LinearMap.ofClass (of α ρ Measure.count))

/-- Fourier coefficients of a compactly supported element are its original coefficients. -/
@[simp]
theorem fourierCoeff_of (hρ : Function.Injective ρ) (g : G)
    (f : ConvolutionAlgebra α Measure.count) :
    fourierCoeff α ρ hρ g (of α ρ Measure.count f) = f.ofConv g :=
  LinearMap.extendOfNorm_eq (denseRange_of α ρ Measure.count)
    ⟨1, fun f => by simpa only [one_mul, LinearMap.coe_ofClass] using
      norm_coefficientEval_le α ρ hρ g f⟩ f

/-- The norm of a Fourier coefficient is at most the regular crossed-product norm. -/
theorem norm_fourierCoeff_apply_le (hρ : Function.Injective ρ) (g : G)
    (x : regularAlgebra α ρ Measure.count) : ‖fourierCoeff α ρ hρ g x‖ ≤ ‖x‖ := by
  induction x using induction_on α ρ Measure.count with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih f =>
    rw [fourierCoeff_of]
    exact norm_coefficientEval_le α ρ hρ g f

/-- The coefficient of an adjoint is the action-twisted adjoint of the inverse coefficient. -/
@[simp]
theorem fourierCoeff_star (hρ : Function.Injective ρ) (g : G)
    (x : regularAlgebra α ρ Measure.count) :
    fourierCoeff α ρ hρ g (star x) = α g (star (fourierCoeff α ρ hρ g⁻¹ x)) := by
  have hc : Measure.modularCharacter g = 1 := by
    rw [modularCharacter_apply,
      Measure.modularCharacterFun_eq_haarScalarFactor (Measure.count : Measure G)]
    simp only [map_mul_right_eq_self, Measure.haarScalarFactor_self]
  have hstar : Continuous (star : regularAlgebra α ρ Measure.count →
      regularAlgebra α ρ Measure.count) := by
    apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, StarMemClass.coe_star, ContinuousLinearMap.star_eq_adjoint]
      using ContinuousLinearMap.adjoint.continuous.comp
        (continuous_subtype_val : Continuous fun y : regularAlgebra α ρ Measure.count =>
          (y : Lp H 2 (Measure.count : Measure G) →L[ℂ] Lp H 2 (Measure.count : Measure G)))
  induction x using induction_on α ρ Measure.count with
  | hp =>
    exact isClosed_eq ((fourierCoeff α ρ hρ g).continuous.comp hstar)
      ((map_continuous (α g)).comp
        (continuous_star.comp (fourierCoeff α ρ hρ g⁻¹).continuous))
  | ih f =>
    rw [← map_star, fourierCoeff_of, fourierCoeff_of,
      ConvolutionAlgebra.ofConv_star, twistedInvolution_apply, hc]
    simp only [NNReal.coe_one, Complex.ofReal_one, one_smul]

/-- The compact-support formula characterizes the Fourier-coefficient map among continuous
linear maps. -/
theorem fourierCoeff_unique (hρ : Function.Injective ρ) (g : G)
    (F : regularAlgebra α ρ Measure.count →L[ℂ] A)
    (hF : ∀ f, F (of α ρ Measure.count f) = f.ofConv g) : F = fourierCoeff α ρ hρ g := by
  ext x
  exact induction_on α ρ Measure.count x
    (isClosed_eq F.continuous (fourierCoeff α ρ hρ g).continuous)
    (fun f => (hF f).trans (fourierCoeff_of α ρ hρ g f).symm)

/-- Fourier coefficients recover every matrix entry of a concrete regular crossed-product
operator between singleton-supported vectors. -/
theorem inner_single_fourierCoeff (hρ : Function.Injective ρ)
    (x : regularAlgebra α ρ Measure.count) (r s : G) (w v : H) :
    ⟪indicatorConstLp 2 (measurableSet_singleton r) (by simp) w,
      (x : Lp H 2 Measure.count →L[ℂ] Lp H 2 Measure.count)
        (indicatorConstLp 2 (measurableSet_singleton s) (by simp) v)⟫_ℂ =
      ⟪w, ρ (α r⁻¹ (fourierCoeff α ρ hρ (r * s⁻¹) x)) v⟫_ℂ := by
  induction x using induction_on α ρ Measure.count with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    simpa only [coe_of, CovariantRepresentation.integratedStarAlgHom_apply, fourierCoeff_of]
      using CovariantRepresentation.inner_integratedOperator_regular_single α ρ f.ofConv r s w v

/-- An element with all Fourier coefficients zero is zero. -/
theorem eq_zero_of_fourierCoeff_eq_zero (hρ : Function.Injective ρ)
    (x : regularAlgebra α ρ Measure.count) (hx : ∀ g, fourierCoeff α ρ hρ g x = 0) : x = 0 := by
  have hsingle (s : G) (v : H) :
      (x : Lp H 2 (Measure.count : Measure G) →L[ℂ] Lp H 2 (Measure.count : Measure G))
        (indicatorConstLp 2 (measurableSet_singleton s) (by simp) v) = 0 := by
    refine Lp.eq_zero_of_inner_indicatorConstLp_singleton (𝕜 := ℂ) _ fun r w => ?_
    rw [inner_single_fourierCoeff α ρ hρ, hx]
    simp only [map_zero, zero_apply, inner_zero_right]
  have hadjoint (η : Lp H 2 (Measure.count : Measure G)) :
      (x : Lp H 2 (Measure.count : Measure G) →L[ℂ]
        Lp H 2 (Measure.count : Measure G)).adjoint η = 0 := by
    refine Lp.eq_zero_of_inner_indicatorConstLp_singleton (𝕜 := ℂ) _ fun s v => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, hsingle, inner_zero_left]
  apply Subtype.ext
  have ht : (x : Lp H 2 (Measure.count : Measure G) →L[ℂ]
      Lp H 2 (Measure.count : Measure G)).adjoint = 0 := by
    apply ContinuousLinearMap.ext
    intro η
    simpa only [zero_apply] using hadjoint η
  calc
    (x : Lp H 2 (Measure.count : Measure G) →L[ℂ] Lp H 2 (Measure.count : Measure G)) =
        (x : Lp H 2 (Measure.count : Measure G) →L[ℂ]
          Lp H 2 (Measure.count : Measure G)).adjoint.adjoint :=
      (ContinuousLinearMap.adjoint_adjoint _).symm
    _ = 0 := by rw [ht, map_zero]

/-- Fourier coefficients determine elements of the concrete regular crossed product. -/
@[ext]
theorem fourierCoeff_ext (hρ : Function.Injective ρ)
    {x y : regularAlgebra α ρ Measure.count}
    (h : ∀ g, fourierCoeff α ρ hρ g x = fourierCoeff α ρ hρ g y) : x = y := by
  apply sub_eq_zero.mp
  exact eq_zero_of_fourierCoeff_eq_zero α ρ hρ (x - y) fun g => by
    have hsub := (fourierCoeff α ρ hρ g).toLinearMap.map_sub x y
    exact hsub.trans (sub_eq_zero.mpr (h g))

end TauCeti.CStarAction.RegularCrossedProduct
