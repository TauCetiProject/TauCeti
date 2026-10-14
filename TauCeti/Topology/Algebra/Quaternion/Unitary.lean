/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
public import Mathlib.Analysis.Quaternion

/-!
# Unit Hamilton quaternions as a sphere

The unitary Hamilton quaternions are exactly the unit sphere in the four-dimensional real normed
space of quaternions. This gives a canonical homeomorphism between the two subtype presentations.

## Main definition

* `Quaternion.unitaryHomeomorphSphere` identifies the unitary Hamilton quaternions with their unit
  sphere.
-/

public section

open Metric
open scoped Quaternion

namespace Quaternion

/-- A Hamilton quaternion is unitary exactly when it belongs to the unit sphere. -/
@[simp 1100]
theorem mem_unitary_iff_mem_sphere_zero_one (q : ℍ[ℝ]) :
    q ∈ unitary ℍ[ℝ] ↔ q ∈ sphere (0 : ℍ[ℝ]) 1 := by
  rw [mem_unitary_iff_normSq_eq_one, mem_sphere, dist_zero_right,
    normSq_eq_norm_mul_self]
  constructor
  · intro h
    nlinarith [norm_nonneg q]
  · intro h
    rw [h]
    norm_num

/-- The unitary Hamilton quaternions are homeomorphic to the unit sphere in `ℍ`. -/
noncomputable def unitaryHomeomorphSphere :
    unitary ℍ[ℝ] ≃ₜ sphere (0 : ℍ[ℝ]) 1 :=
  Homeomorph.ofEqSubtypes (by
    funext q
    exact propext (mem_unitary_iff_mem_sphere_zero_one q))

/-- The homeomorphism from unitary quaternions to the unit sphere preserves the underlying
quaternion. -/
@[simp]
theorem coe_unitaryHomeomorphSphere_apply (q : unitary ℍ[ℝ]) :
    (unitaryHomeomorphSphere q : ℍ[ℝ]) = q := by
  rw [unitaryHomeomorphSphere]
  rfl

/-- The inverse homeomorphism from the unit sphere preserves the underlying quaternion. -/
@[simp]
theorem coe_unitaryHomeomorphSphere_symm_apply (q : sphere (0 : ℍ[ℝ]) 1) :
    (unitaryHomeomorphSphere.symm q : ℍ[ℝ]) = q := by
  rw [unitaryHomeomorphSphere]
  rfl

end Quaternion
