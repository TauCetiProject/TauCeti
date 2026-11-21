/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Analysis.Green.Comparison.Area.Basic

/-!
# Integrating top forms on a Riemann surface in a chart

A Riemann surface `X`, a complex manifold modelled on `ℂ`, carries its canonical orientation
`TauCeti.complexManifoldOrientation ℂ X`. Reindexed from `Fin (2 * finrank ℂ ℂ)` to `Fin 2`, the
degree of top forms on the underlying real surface, it is the orientation given by
`Manifold.OrientationLift.ofHasGroupoid` with model orientation `Complex.orientation`: every
holomorphic chart is oriented and `ℂ` carries its standard orientation, given by the basis `1, i`
(`TauCeti.reindex_complexManifoldOrientation_eq_mk_ofHasGroupoid`).

For this orientation the integral of a continuous top form with compact support inside the
preferred chart at `p` is the planar Lebesgue integral of its coefficient on the basis `1, i`
(`TauCeti.integralTopForm_reindex_complexManifoldOrientation_eq_integral`).

## Main results

* `TauCeti.reindex_complexManifoldOrientation_eq_mk_ofHasGroupoid`: the canonical orientation of
  a Riemann surface, indexed by `Fin 2`, is represented by the oriented holomorphic atlas.
* `TauCeti.integralTopForm_reindex_complexManifoldOrientation_eq_integral`: the integral of a top
  form supported in a chart is the planar integral of its coefficient.
-/

public section

open Complex MeasureTheory Set
open scoped Manifold TauCeti.ComplexManifold

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- The canonical orientation of a Riemann surface, reindexed to `Fin 2`, is represented by the
orientation lift of its holomorphic atlas with the standard orientation `Complex.orientation` of
the model. -/
theorem reindex_complexManifoldOrientation_eq_mk_ofHasGroupoid :
    (complexManifoldOrientation ℂ X).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)) =
      Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid Complex.orientation (by simp)) := by
  ext x
  rw [Manifold.Orientation.orientationAt_reindex,
    orientationAt_complexManifoldOrientation_eq_complexOrientation,
    Manifold.Orientation.orientationAt_mk, Manifold.OrientationLift.orientationAt_ofHasGroupoid,
    ← reindex_complexOrientation_complex]
  -- The tangent space at `x` is `ℂ`, and the two reindexings are along the same cast of `Fin`.
  rfl

/-- The integral of a continuous top form with compact support inside the preferred chart at `p`,
for the canonical orientation of the Riemann surface, is the planar integral of its coefficient on
the basis `1, i` over the target of the chart. -/
theorem integralTopForm_reindex_complexManifoldOrientation_eq_integral
    {φ : RoughForm 𝓘(ℝ, ℂ) X ℝ 2} (hφ : IsSmoothForm 𝓘(ℝ, ℂ) 0 φ)
    (hc : IsCompact (tsupport (α := ℂ [⋀^Fin 2]→L[ℝ] ℝ) φ))
    (p : X) (hs : tsupport (α := ℂ [⋀^Fin 2]→L[ℝ] ℝ) φ ⊆ (chartAt ℂ p).source) :
    integralTopForm ((complexManifoldOrientation ℂ X).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))) φ =
      ∫ z, (chartAt ℂ p).target.indicator (fun z ↦ φ.inChartAt p z ![1, I]) z := by
  have hσ : ∀ x : X, (Manifold.OrientationLift.ofHasGroupoid (I := 𝓘(ℝ, ℂ)) (M := X)
      Complex.orientation (by simp)).signAt p x = 1 := fun x ↦ by
    by_cases hx : x ∈ (chartAt ℂ p).source
    · rw [Manifold.OrientationLift.signAt_of_mem _ hx]
      exact Manifold.OrientationLift.ofHasGroupoid_sign _ _ _ _
    · exact Manifold.OrientationLift.signAt_of_notMem _ hx
  rw [reindex_complexManifoldOrientation_eq_mk_ofHasGroupoid,
    integralTopForm_eq_chartIntegral _ φ (hφ.integrableTopForm hc Complex.basisOneI) p
      (by simpa only [extChartAt_source] using hs),
    Manifold.OrientationLift.chartIntegral_eq_const_mul_unsigned _ φ Complex.basisOneI p 1
      fun x _ ↦ hσ x,
    Manifold.OrientationLift.ofHasGroupoid_modelOrientation, Complex.orientation,
    _root_.Orientation.signBasis_orientation, Complex.addHaar_basisOneI]
  simp only [Units.val_one, Int.cast_one, one_mul, RoughForm.signedInChartAt_one,
    Complex.coe_basisOneI, extChartAt_target, ModelWithCorners.range_eq_univ, inter_univ]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  by_cases hz : z ∈ (chartAt ℂ p).target
  · simp [indicator_of_mem hz]
  · simp [indicator_of_notMem hz]

end TauCeti
