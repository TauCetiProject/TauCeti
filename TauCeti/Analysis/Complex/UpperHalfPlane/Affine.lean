/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Positive affine maps of the upper half-plane

A real affine map `z ↦ c * z + d` preserves the upper half-plane exactly when its slope `c` is
positive.  This file packages its value as an `UpperHalfPlane` point and records the coercion and
imaginary-part formulas used when applying analytic functions after such a change of variables.

## Main definitions

* `UpperHalfPlane.affine` -- the action of a positive real affine map on the upper half-plane.
-/

public section

open Complex Set UpperHalfPlane

namespace TauCeti

/-- A positive affine map of `ℂ` preserves the upper half-plane. -/
theorem affine_mem_upperHalfPlaneSet {c d : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) : (c : ℂ) * z + (d : ℂ) ∈ upperHalfPlaneSet := by
  simpa [upperHalfPlaneSet, mul_im] using mul_pos hc hz

/-- Apply a positive real affine map to a point of the upper half-plane. -/
def _root_.UpperHalfPlane.affine (z : UpperHalfPlane) (c d : ℝ) (hc : 0 < c) :
    UpperHalfPlane :=
  ⟨(c : ℂ) * z + (d : ℂ), affine_mem_upperHalfPlaneSet hc z.im_pos⟩

@[simp]
theorem _root_.UpperHalfPlane.coe_affine (z : UpperHalfPlane) (c d : ℝ) (hc : 0 < c) :
    (z.affine c d hc : ℂ) = (c : ℂ) * z + (d : ℂ) :=
  (rfl)

@[simp]
theorem _root_.UpperHalfPlane.im_affine (z : UpperHalfPlane) (c d : ℝ) (hc : 0 < c) :
    (z.affine c d hc).im = c * z.im := by
  simp [UpperHalfPlane.affine, mul_im]

end TauCeti

end
