/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Smooth unit-sphere curves with prescribed tangent

Every vector orthogonal to a unit vector is the initial velocity of a smooth curve of
unit vectors. A parametrized great circle gives the construction, including zero velocity.
-/

public noncomputable section

open Metric
open scoped ContDiff InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every tangent vector to the unit sphere is realized by a smooth ambient curve
contained in that sphere. -/
theorem exists_contDiff_norm_eq_one_hasDerivAt {v w : E} (hv : ‖v‖ = 1)
    (hvw : ⟪v, w⟫_ℝ = 0) :
    ∃ c : ℝ → E, ContDiff ℝ ∞ c ∧ (∀ t, ‖c t‖ = 1) ∧ c 0 = v ∧ HasDerivAt c w 0 := by
  by_cases hw : w = 0
  · exact ⟨fun _ ↦ v, contDiff_const, fun _ ↦ hv, rfl, by simpa only [hw] using
      (hasDerivAt_const (0 : ℝ) v)⟩
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  let u := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hnorm]
  have hvu : ⟪v, u⟫_ℝ = 0 := by simp only [u, real_inner_smul_right, hvw, mul_zero]
  let c (t : ℝ) := Real.cos (‖w‖ * t) • v + Real.sin (‖w‖ * t) • u
  refine ⟨c, by fun_prop, ?_, by simp [c], ?_⟩
  · intro t
    exact norm_cos_smul_add_sin_smul
      ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩
      ⟨u, mem_sphere_zero_iff_norm.mpr hu⟩ hvu (‖w‖ * t)
  · have hphase : HasDerivAt (fun t : ℝ ↦ ‖w‖ * t) ‖w‖ 0 := by
      simpa only [mul_one] using (hasDerivAt_id' 0).const_mul ‖w‖
    have hd := (hphase.cos.smul_const v).fun_add (hphase.sin.smul_const u)
    simpa [c, u, smul_smul, hnorm] using hd

end TauCeti
