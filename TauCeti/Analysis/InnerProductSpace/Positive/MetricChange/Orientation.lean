/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Composition
public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Orientation

/-!
# Orientations and canonical changes of metric

The canonical inverse-square-root transport from the fixed inner product to a positive metric
`h`, and its inverse, fix every orientation of the underlying finite-dimensional real vector
space, including either sign in dimension zero. Thus this transport does not exchange the sheets
of the orientation cover. The transport `metricChangeBetween h k` between two positive metrics
has positive determinant.

The orthogonal discrepancy between successive canonical metric changes and direct transport
also preserves orientation: it belongs to the special orthogonal group
`TauCeti.specialOrthogonalGroup E`. This is the comparison needed when using metric transports to
compare positively oriented frames; the transports themselves need not compose literally.

See Milnor and Stasheff, *Characteristic Classes*, §9, for orientations, and Bhatia,
*Positive Definite Matrices*, Chapter 1, for positive square roots.
-/

public section

open InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {h : E →L[ℝ] E →L[ℝ] ℝ}

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-- The canonical inverse-square-root transport has positive determinant. -/
theorem det_metricChangeTransport_pos (hH : IsStrictlyPositive h♯) :
    0 < h.metricChangeTransport.det :=
  (isStrictlyPositive_metricChangeTransport hH).det_pos

/-- Canonical transport between two positive metrics preserves orientation, even when their
Riesz operators do not commute. -/
theorem det_metricChangeBetween_pos (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) :
    0 < (h.metricChangeBetween k).det := by
  simp only [metricChangeBetween_def, ContinuousLinearMap.det, toLinearMap_mul, map_mul]
  exact mul_pos (mul_pos (det_metricChangeTransport_pos hH)
    (det_metricChangeTransport_pos
      (isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK)))
    hH.sqrt.det_pos

/-- The discrepancy between successive metric changes and direct transport is special
orthogonal. In particular it cannot reverse the orientation of a frame. -/
theorem metricChangeCompositionCorrection_mem_specialOrthogonalGroup
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) :
    Unitary.linearIsometryEquiv.symm (h.metricChangeCompositionCorrection k hH hK) ∈
      TauCeti.specialOrthogonalGroup E := by
  rw [TauCeti.mem_specialOrthogonalGroup_iff_det_pos,
    Unitary.coe_symm_linearIsometryEquiv_apply]
  have heq := congrArg ContinuousLinearMap.det
    (metricChangeBetween_mul_metricChangeTransport h k hH hK)
  simp only [ContinuousLinearMap.det, toLinearMap_mul, map_mul] at heq
  have hpos := mul_pos (det_metricChangeBetween_pos h k hH hK)
    (det_metricChangeTransport_pos hH)
  rw [heq] at hpos
  exact pos_of_mul_pos_right hpos (det_metricChangeTransport_pos hK).le

end ContinuousLinearMap

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

/-- The canonical change of positive metric fixes each orientation. No positive-rank
hypothesis is needed: both orientation signs are retained in dimension zero. -/
@[simp]
theorem map_metricChangeEquiv (o : Orientation ℝ E ι)
    (h : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) h))
    (hι : Fintype.card ι = Module.finrank ℝ E) :
    Orientation.map ι (h.metricChangeEquiv hH).toLinearEquiv o = o := by
  apply (o.map_eq_iff_det_pos _ hι).2
  rw [← ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    ← ContinuousLinearMap.det, ContinuousLinearMap.coe_metricChangeEquiv]
  exact ContinuousLinearMap.det_metricChangeTransport_pos hH

/-- The inverse metric change also fixes each orientation. -/
@[simp]
theorem map_metricChangeEquiv_symm (o : Orientation ℝ E ι)
    (h : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) h))
    (hι : Fintype.card ι = Module.finrank ℝ E) :
    Orientation.map ι (h.metricChangeEquiv hH).toLinearEquiv.symm o = o := by
  rw [← Orientation.map_symm, Equiv.symm_apply_eq]
  exact (map_metricChangeEquiv o h hH hι).symm

end Orientation
