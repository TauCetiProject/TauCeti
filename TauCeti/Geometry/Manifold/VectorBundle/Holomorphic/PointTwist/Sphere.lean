/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Basic

/-!
# The affine coordinate as a section of a point twist on the Riemann sphere

On the Riemann sphere `OnePoint ℂ`, the affine coordinate `z` defines a holomorphic global section
of the point twist at `∞` of the trivial line bundle `Bundle.Trivial (OnePoint ℂ) ℂ`
(`TauCeti.contMDiff_pointTwistOfPole_affineChart`), whose zero set is `{0}`
(`TauCeti.pointTwistOfPole_affineChart_eq_zero_iff`). For comparison,
`OnePoint.not_mdifferentiable_section_twistCore_zero_of_coe` shows that `z` is not a holomorphic
section of the degree-zero bundle `OnePoint.twistCore 0`.
-/

public section

noncomputable section

open Bundle OnePoint Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

/-- On the Riemann sphere, the affine coordinate `z` is a holomorphic section of the twist of the
trivial line bundle at `∞`, with leading coefficient `1` at `∞`. -/
theorem contMDiff_pointTwistOfPole_affineChart :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) ω (fun z ↦ TotalSpace.mk' ℂ z
      (pointTwistOfPole ℂ (E := Bundle.Trivial (OnePoint ℂ) ℂ) (∞ : OnePoint ℂ)
        (fun z ↦ affineChart z) (fun _ ↦ 1) z)) := by
  refine contMDiff_pointTwistOfPole (fun z hz ↦ ?_) ?_ ?_
  · have h := contMDiffOn_of_mem_maximalAtlas
      (affineChart_mem_maximalAtlas (𝕜 := ℂ) (n := ω))
    exact ((contMDiffAt_section z).2 (h.contMDiffAt
      (affineChart.open_source.mem_nhds (by simpa using hz)))).contMDiffWithinAt
  · exact (contMDiffAt_section _).2 contMDiffAt_const
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      ((chartAt ℂ (∞ : OnePoint ℂ)).open_source.mem_nhds (mem_chart_source ℂ (∞ : OnePoint ℂ)))]
      with z hzi hz
    have hc0 := pointTwistCoord_ne_zero hz hzi
    rw [pointTwistCoord_apply, chartAt_infty, invChart_infty, sub_zero] at hc0 ⊢
    rw [smul_eq_mul, ← inv_invChart, mul_inv_cancel₀ hc0]

/-- The section `z` of the twist of the trivial line bundle at `∞` on the Riemann sphere vanishes
exactly at `0`. -/
theorem pointTwistOfPole_affineChart_eq_zero_iff {z : OnePoint ℂ} :
    pointTwistOfPole ℂ (E := Bundle.Trivial (OnePoint ℂ) ℂ) (∞ : OnePoint ℂ)
        (fun z ↦ affineChart z) (fun _ ↦ 1) z = 0 ↔ z = ((0 : ℂ) : OnePoint ℂ) := by
  induction z using OnePoint.rec with
  | infty =>
    rw [pointTwistOfPole_self]
    exact ⟨fun h ↦ absurd h (one_ne_zero (α := ℂ)), fun h ↦ absurd h (infty_ne_coe 0)⟩
  | coe w =>
    rw [pointTwistOfPole_of_ne ℂ (coe_ne_infty w), pointTwistMul_apply_of_ne (coe_ne_infty w),
      affineChart_coe]
    exact coe_eq_coe.symm

end TauCeti
