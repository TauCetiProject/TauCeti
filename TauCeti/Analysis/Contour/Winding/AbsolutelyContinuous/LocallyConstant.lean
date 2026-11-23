/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Analysis.Contour.Winding.LocallyConstant

/-!
# Local constancy of winding numbers for absolutely continuous curves

The winding number of a closed absolutely continuous curve is locally constant off its trace,
and is consequently constant on each connected component of the trace complement. In particular,
around an off-curve point where the winding number of an absolutely continuous curve vanishes, it
vanishes on a whole ball that stays off the curve
(`AbsolutelyContinuousOnInterval.exists_ball_windingNumber_zero`): this is the local matching data
that Dixon's argument for the homology form of Cauchy's theorem uses.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti.Contour

/-- The winding number of a closed absolutely continuous curve is locally constant off its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.isLocallyConstant_windingNumber
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) :
    IsLocallyConstant (fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.val) := by
  exact hγ.continuousOn.isLocallyConstant_windingNumber_of_integer
    hγ.intervalIntegrable_deriv_of_finiteDimensional
    (fun _ hz ↦ hγ.exists_int_windingNumber hclosed hz)

/-- **The winding number vanishes on a ball around an off-curve null point.** For an absolutely
continuous curve `γ`, if the winding number about an off-curve point `w` is `0`, then it is `0`
throughout a ball around `w` that stays off the curve. The curve is automatically closed: the
endpoint-ratio identity `exp (2πi · n) = (γ b - w) / (γ a - w)` at the null point `w` gives
`γ a = γ b`. This is the local matching input for Dixon's argument: the off-curve set is open, so
the subtype-open set on which local constancy pins the winding number to `0` pushes forward, along
the open inclusion `Subtype.val`, to a `ℂ`-ball. -/
theorem _root_.AbsolutelyContinuousOnInterval.exists_ball_windingNumber_zero
    {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (hw_zero : windingNumber γ a b w = 0) :
    ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      (∀ t ∈ uIcc a b, γ t ≠ w') ∧ windingNumber γ a b w' = 0 := by
  have hw : w ∉ γ '' uIcc a b := by
    simpa only [mem_image, not_exists, not_and] using hoff
  -- A null winding number at an off-curve point forces the curve to be closed.
  have hclosed : γ a = γ b := by
    have h := hγ.exp_two_pi_I_mul_windingNumber hw
    rw [hw_zero, mul_zero, Complex.exp_zero, eq_comm,
      div_eq_one_iff_eq (sub_ne_zero.mpr (hoff a left_mem_uIcc))] at h
    exact (sub_left_inj.mp h).symm
  -- The off-curve set is open: it is the complement of the compact curve image.
  have hSopen : IsOpen {z : ℂ | z ∉ γ '' uIcc a b} :=
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).isClosed.isOpen_compl
  -- The winding number is locally constant off the curve, so it is `0` on a subtype-open set
  -- around `w`; push that set forward along the open inclusion to a `ℂ`-ball, every point of
  -- which is off the curve, being the value of a point of the subtype.
  obtain ⟨V, hV_open, hwV, hV_const⟩ :=
    (hγ.isLocallyConstant_windingNumber hclosed).exists_open ⟨w, hw⟩
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (hSopen.isOpenMap_subtypeVal V hV_open) w ⟨⟨w, hw⟩, hwV, rfl⟩
  refine ⟨ε, hε, fun w' hw' ↦ ?_⟩
  obtain ⟨p, hpV, rfl⟩ := hball hw'
  exact ⟨fun t ht heq ↦ p.property ⟨t, ht, heq⟩, (hV_const p hpV).trans hw_zero⟩

/-- The winding number of a closed absolutely continuous curve is constant on each connected
component of the complement of its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_mem_connectedComponentIn
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) {z w : ℂ}
    (hw : w ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) z) :
    windingNumber γ a b w = windingNumber γ a b z := by
  exact hγ.continuousOn.windingNumber_eq_of_mem_connectedComponentIn_of_integer
    hγ.intervalIntegrable_deriv_of_finiteDimensional
    (fun _ hz ↦ hγ.exists_int_windingNumber hclosed hz) hw

end TauCeti.Contour
