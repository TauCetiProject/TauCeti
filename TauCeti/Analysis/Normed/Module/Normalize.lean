/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Radial projection to the unit sphere

This file packages pointwise normalization of a continuous nowhere-zero map as a continuous map
to the unit sphere. It also defines the direction map `sphereDirection e`, which sends a nonzero
vector `x` to `‖x‖⁻¹ • x` and the origin to an assigned point `e` of the unit sphere.

## Main definitions

* `TauCeti.normalizeToSphere`: radial projection of a continuous nowhere-zero map.
* `TauCeti.sphereDirection`: the direction of a vector, with an assigned value at the origin.
-/

public section

noncomputable section

open Metric NormedSpace Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection sends a continuous nowhere-zero map into a real normed space continuously
to its unit sphere. -/
noncomputable def normalizeToSphere {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) : C(Y, sphere (0 : E) 1) where
  toFun y := ⟨normalize (f y), mem_sphere_zero_iff_norm.mpr (norm_normalize (h0 y))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [NormedSpace.normalize]
    exact ((continuous_norm.comp hf).inv₀
      (fun y => norm_ne_zero_iff.mpr (h0 y))).smul hf

/-- The underlying vector of `normalizeToSphere f hf h0 y` is the normalization of `f y`. -/
@[simp]
theorem coe_normalizeToSphere_apply {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) (y : Y) :
    ((normalizeToSphere f hf h0 y : sphere (0 : E) 1) : E) = normalize (f y) :=
  (rfl)

section Direction

open Classical in
/-- The direction of a vector on the unit sphere: `‖x‖⁻¹ • x` for a nonzero vector `x`, and the
assigned point `e` of the sphere at the origin. -/
def sphereDirection (e : sphere (0 : E) 1) (x : E) : sphere (0 : E) 1 :=
  ⟨if x = 0 then e else normalize x, by
    split_ifs with hx
    exacts [e.2, mem_sphere_zero_iff_norm.2 (norm_normalize hx)]⟩

variable (e : sphere (0 : E) 1) {x : E}

/-- The direction of the origin is the assigned point. -/
@[simp]
theorem sphereDirection_zero : sphereDirection e 0 = e := by
  simp [sphereDirection]

/-- The direction of a nonzero vector is its normalization. -/
theorem coe_sphereDirection_of_ne_zero (hx : x ≠ 0) :
    (sphereDirection e x : E) = normalize x := by
  simp [sphereDirection, hx]

/-- A vector is its norm times its direction. -/
@[simp]
theorem norm_smul_sphereDirection (x : E) : ‖x‖ • (sphereDirection e x : E) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [coe_sphereDirection_of_ne_zero e hx, norm_smul_normalize]

/-- A positive multiple of a point of the sphere has that point as its direction. -/
@[simp]
theorem sphereDirection_smul_of_pos {r : ℝ} (hr : 0 < r) (u : sphere (0 : E) 1) :
    sphereDirection e (r • (u : E)) = u := by
  have hu : (u : E) ≠ 0 := ne_zero_of_mem_sphere one_ne_zero u
  ext1
  rw [coe_sphereDirection_of_ne_zero e (smul_ne_zero hr.ne' hu), normalize_smul_of_pos hr,
    normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere u)]

/-- A point of the sphere is its own direction. -/
@[simp]
theorem sphereDirection_coe (u : sphere (0 : E) 1) : sphereDirection e (u : E) = u := by
  simpa using sphereDirection_smul_of_pos e one_pos u

end Direction

end TauCeti

end
