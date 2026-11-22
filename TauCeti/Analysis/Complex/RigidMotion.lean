/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Rigid motions of the plane

The orientation-preserving isometries of the plane are the maps `z ↦ u z + a` with `u` on the
unit circle. Mathlib packages the rotations `z ↦ u z` as the linear isometries `rotation u`; this
file packages the rigid motions as affine isometry equivalences of `ℂ`, with their identity,
composition and inverse laws.

## Main declarations

* `Circle.rigidMotion u a : ℂ ≃ᵃⁱ[ℝ] ℂ`: the motion `z ↦ u z + a`.
* `Circle.linearIsometryEquiv_rigidMotion`: its linear part is `rotation u`, whose inverse is
  multiplication by `conj u` (`Circle.linearIsometryEquiv_rigidMotion_symm_apply`).
* `Circle.rigidMotion_one_zero`, `Circle.rigidMotion_trans_rigidMotion` and
  `Circle.rigidMotion_symm`: the identity, composition and inverse laws.
-/

public section

noncomputable section

namespace Circle

open scoped ComplexConjugate

/-- The rigid motion `z ↦ u z + a` of the plane, for `u` on the unit circle. -/
def rigidMotion (u : Circle) (a : ℂ) : ℂ ≃ᵃⁱ[ℝ] ℂ :=
  AffineIsometryEquiv.mk' (fun z ↦ (u : ℂ) * z + a) (rotation u) 0 fun z ↦ by simp

@[simp]
theorem rigidMotion_apply (u : Circle) (a z : ℂ) : u.rigidMotion a z = (u : ℂ) * z + a := (rfl)

/-- The linear part of the rigid motion `z ↦ u z + a` is the rotation by `u`. -/
@[simp]
theorem linearIsometryEquiv_rigidMotion (u : Circle) (a : ℂ) :
    (u.rigidMotion a).linearIsometryEquiv = rotation u := by
  simp [rigidMotion]

/-- The inverse of the linear part of the rigid motion `z ↦ u z + a` is multiplication by
`conj u = u⁻¹`. Simp normalizes the left-hand side through `linearIsometryEquiv_rigidMotion`, so
this is a rewriting lemma rather than a simp lemma. -/
theorem linearIsometryEquiv_rigidMotion_symm_apply (u : Circle) (a w : ℂ) :
    (u.rigidMotion a).linearIsometryEquiv.symm w = conj (u : ℂ) * w := by
  rw [linearIsometryEquiv_rigidMotion, rotation_symm, rotation_apply, coe_inv_eq_conj]

@[simp]
theorem rigidMotion_one_zero : rigidMotion 1 0 = AffineIsometryEquiv.refl ℝ ℂ := by
  ext z
  simp

/-- Performing `z ↦ u z + a` and then `z ↦ v z + b` is the motion `z ↦ u v z + (v a + b)`. -/
@[simp]
theorem rigidMotion_trans_rigidMotion (u v : Circle) (a b : ℂ) :
    (u.rigidMotion a).trans (v.rigidMotion b) = (u * v).rigidMotion (v * a + b) := by
  ext z
  simp only [AffineIsometryEquiv.coe_trans, Function.comp_apply, rigidMotion_apply, coe_mul]
  ring

/-- The inverse of the motion `z ↦ u z + a` is the motion `z ↦ u⁻¹ z - u⁻¹ a`. -/
@[simp]
theorem rigidMotion_symm (u : Circle) (a : ℂ) :
    (u.rigidMotion a).symm = u⁻¹.rigidMotion (-((u : ℂ)⁻¹ * a)) := by
  ext z
  rw [AffineIsometryEquiv.symm_apply_eq, rigidMotion_apply, rigidMotion_apply, coe_inv]
  field_simp [coe_ne_zero u]
  ring

end Circle
