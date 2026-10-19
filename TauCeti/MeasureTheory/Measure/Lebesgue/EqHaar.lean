/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Haar measure under dilations and affine maps

The dimension root of outer volume scales by the absolute value of a real dilation
in a positive-dimensional real inner product space. The identity applies to arbitrary
sets and infinite outer volumes, and supplies the scaling law for volume inequalities.

An affine map of a finite-dimensional real normed space multiplies every additive Haar measure
by the absolute value of the determinant of its linear part
(`MeasureTheory.Measure.addHaar_image_affineMap`, and
`MeasureTheory.Measure.addHaar_image_affineEquiv` for affine equivalences), the affine form of
Mathlib's `MeasureTheory.Measure.addHaar_image_linearMap`.

A linear map into a finite-dimensional real normed space that is not surjective has almost every
fibre empty for every additive Haar measure on the codomain
(`LinearMap.ae_preimage_singleton_eq_empty`), since its range is a strict subspace.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Dimension-root volume scales linearly under every real dilation, including zero.
This identity holds for arbitrary sets and infinite outer volumes. -/
theorem volume_smul_rpow {A : Set E} (hn : Module.finrank ℝ E ≠ 0) (c : ℝ) :
    volume (c • A) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
      ENNReal.ofReal |c| * volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  rw [Measure.addHaar_smul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    abs_pow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.pow_rpow_inv_natCast (abs_nonneg c) hn]

end TauCeti

namespace MeasureTheory.Measure

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-- The image of a set under an affine map has Haar measure equal to the absolute value of the
determinant of the linear part times the measure of the set. -/
theorem addHaar_image_affineMap (f : F →ᵃ[ℝ] F) (s : Set F) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f.linear| * μ s := by
  have hf : f '' s = (fun y ↦ y + f 0) '' (f.linear '' s) := by
    rw [image_image]
    exact image_congr fun x _ ↦ by simpa using f.map_vadd 0 x
  rw [hf, image_add_right, measure_preimage_add_right, addHaar_image_linearMap]

/-- The image of a set under an affine equivalence has Haar measure equal to the absolute value of
the determinant of the linear part times the measure of the set. -/
theorem addHaar_image_affineEquiv (f : F ≃ᵃ[ℝ] F) (s : Set F) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f.linear : F →ₗ[ℝ] F)| * μ s :=
  addHaar_image_affineMap μ (f : F →ᵃ[ℝ] F) s

end MeasureTheory.Measure

namespace LinearMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A linear map that is not surjective has almost every fibre empty, for every additive Haar
measure on its finite-dimensional codomain. -/
theorem ae_preimage_singleton_eq_empty (μ : Measure F) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] F)
    (hL : ¬Function.Surjective L) :
    ∀ᵐ y ∂μ, L ⁻¹' {y} = ∅ := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1
    (Measure.addHaar_submodule μ _ (mt range_eq_top.mp hL))] with y hy
  exact eq_empty_of_forall_notMem fun x hx ↦ hy ⟨x, hx⟩

end LinearMap
