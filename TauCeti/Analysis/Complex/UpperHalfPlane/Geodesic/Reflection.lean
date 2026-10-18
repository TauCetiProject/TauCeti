/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.HalfPlane

/-!
# Reflections in hyperbolic geodesics

Reflection in the imaginary axis sends `x + iy` to `-x + iy`.  Conjugating this isometry by the
projective Möbius action gives reflection in the oriented geodesic `geodesicLine g`.  The resulting
map fixes that line pointwise and exchanges its right and left half-planes.

These reflections are the orientation-reversing generators used to construct hyperbolic
reflection groups.  Products of adjacent reflections are orientation preserving and supply the
side-pairing transformations for triangle groups.

## Main declarations

* `TauCeti.UpperHalfPlane.imaginaryAxisReflection`: reflection in the imaginary axis.
* `TauCeti.UpperHalfPlane.geodesicReflection`: reflection in `geodesicLine g`, obtained by
  conjugating `imaginaryAxisReflection` by `g`.
* `TauCeti.UpperHalfPlane.geodesicReflection_apply_apply`: a geodesic reflection is an
  involution.
* `TauCeti.UpperHalfPlane.geodesicReflection_apply_eq_self_iff`: its fixed-point set is exactly
  the reflected geodesic.
* `TauCeti.UpperHalfPlane.geodesicReflection_image_rightHalfPlane` and
  `TauCeti.UpperHalfPlane.geodesicReflection_image_leftHalfPlane`: reflection exchanges the two
  sides of the geodesic.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 7.
* Svetlana Katok, *Fuchsian Groups*, §2.1.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

/-- Reflection in the imaginary axis of the upper half-plane, `x + iy ↦ -x + iy`, packaged as
an isometry. -/
def imaginaryAxisReflection : ℍ ≃ᵢ ℍ where
  toEquiv :=
    { toFun := fun z : ℍ ↦ UpperHalfPlane.mk ⟨-z.re, z.im⟩ z.im_pos
      invFun := fun z : ℍ ↦ UpperHalfPlane.mk ⟨-z.re, z.im⟩ z.im_pos
      left_inv := fun z ↦ by apply UpperHalfPlane.ext_re_im <;> simp
      right_inv := fun z ↦ by apply UpperHalfPlane.ext_re_im <;> simp }
  isometry_toFun := Isometry.of_dist_eq fun z w ↦ by
    rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq]
    congr 3
    rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, neg_sub_neg]
    congr 1
    ring

/-- Reflection in the imaginary axis negates the real part. -/
@[simp]
theorem imaginaryAxisReflection_re (z : ℍ) : (imaginaryAxisReflection z).re = -z.re :=
  (rfl)

/-- Reflection in the imaginary axis preserves the imaginary part. -/
@[simp]
theorem imaginaryAxisReflection_im (z : ℍ) : (imaginaryAxisReflection z).im = z.im :=
  (rfl)

/-- Reflection in the imaginary axis is an involution. -/
@[simp]
theorem imaginaryAxisReflection_apply_apply (z : ℍ) :
    imaginaryAxisReflection (imaginaryAxisReflection z) = z := by
  apply UpperHalfPlane.ext_re_im <;> simp

/-- A point is fixed by reflection in the imaginary axis exactly when it lies on that axis. -/
@[simp]
theorem imaginaryAxisReflection_apply_eq_self_iff (z : ℍ) :
    imaginaryAxisReflection z = z ↔ z.re = 0 := by
  constructor
  · intro h
    have := congrArg UpperHalfPlane.re h
    simp only [imaginaryAxisReflection_re] at this
    linarith
  · intro h
    apply UpperHalfPlane.ext_re_im
    · simp [h]
    · simp

/-- Reflection in the oriented geodesic `geodesicLine g`, obtained by transporting reflection in
the imaginary axis along the projective Möbius isometry `g`. -/
def geodesicReflection (g : PSL(2, ℝ)) : ℍ ≃ᵢ ℍ :=
  ((IsometryEquiv.constSMul g⁻¹).trans imaginaryAxisReflection).trans
    (IsometryEquiv.constSMul g)

/-- Reflection in `geodesicLine g` is conjugated imaginary-axis reflection. -/
theorem geodesicReflection_apply (g : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflection g z = g • imaginaryAxisReflection (g⁻¹ • z) :=
  (rfl)

/-- Reflection in a geodesic is an involution. -/
@[simp]
theorem geodesicReflection_apply_apply (g : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflection g (geodesicReflection g z) = z := by
  simp only [geodesicReflection_apply, inv_smul_smul, imaginaryAxisReflection_apply_apply,
    smul_inv_smul]

/-- A geodesic reflection is its own inverse. -/
@[simp]
theorem geodesicReflection_symm (g : PSL(2, ℝ)) :
    (geodesicReflection g).symm = geodesicReflection g := by
  apply IsometryEquiv.ext
  intro z
  apply (geodesicReflection g).injective
  rw [(geodesicReflection g).apply_symm_apply, geodesicReflection_apply_apply]

/-- Reflection in `geodesicLine g` fixes every point of its standard parametrisation. -/
@[simp]
theorem geodesicReflection_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) :
    geodesicReflection g (geodesicLine g t) = geodesicLine g t := by
  rw [geodesicReflection_apply, smul_geodesicLine]
  rw [inv_mul_cancel]
  have hbase : imaginaryAxisReflection (geodesicLine 1 t) = geodesicLine 1 t := by
    apply UpperHalfPlane.ext_re_im <;> simp [geodesicLine_one_apply]
  rw [hbase, smul_geodesicLine, mul_one]

/-- The fixed-point set of reflection in `geodesicLine g` is exactly that geodesic. -/
@[simp]
theorem geodesicReflection_apply_eq_self_iff (g : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflection g z = z ↔ z ∈ Set.range (geodesicLine g) := by
  constructor
  · intro h
    have h' := congrArg (fun w : ℍ ↦ g⁻¹ • w) h
    simp only [geodesicReflection_apply, inv_smul_smul] at h'
    rw [mem_range_geodesicLine_iff]
    exact (imaginaryAxisReflection_apply_eq_self_iff _).mp h'
  · intro hz
    rw [mem_range_geodesicLine_iff] at hz
    have hfix := (imaginaryAxisReflection_apply_eq_self_iff _).mpr hz
    rw [geodesicReflection_apply, hfix, smul_inv_smul]

/-- A point reflected across `geodesicLine g` lies in its left half-plane exactly when the
original point lies in its right half-plane. -/
theorem geodesicReflection_mem_leftHalfPlane_iff (g : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflection g z ∈ leftHalfPlane g ↔ z ∈ rightHalfPlane g := by
  rw [mem_leftHalfPlane_iff, geodesicReflection_apply, inv_smul_smul,
    imaginaryAxisReflection_re, mem_rightHalfPlane_iff]
  exact neg_lt_zero

/-- A point reflected across `geodesicLine g` lies in its right half-plane exactly when the
original point lies in its left half-plane. -/
theorem geodesicReflection_mem_rightHalfPlane_iff (g : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflection g z ∈ rightHalfPlane g ↔ z ∈ leftHalfPlane g := by
  rw [mem_rightHalfPlane_iff, geodesicReflection_apply, inv_smul_smul,
    imaginaryAxisReflection_re, mem_leftHalfPlane_iff]
  exact neg_pos

/-- Reflection in a geodesic maps its right half-plane onto its left half-plane. -/
@[simp]
theorem geodesicReflection_image_rightHalfPlane (g : PSL(2, ℝ)) :
    geodesicReflection g '' rightHalfPlane g = leftHalfPlane g := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (geodesicReflection_mem_leftHalfPlane_iff g w).2 hw
  · intro hz
    refine ⟨geodesicReflection g z, ?_, geodesicReflection_apply_apply g z⟩
    exact (geodesicReflection_mem_rightHalfPlane_iff g z).2 hz

/-- Reflection in a geodesic maps its left half-plane onto its right half-plane. -/
@[simp]
theorem geodesicReflection_image_leftHalfPlane (g : PSL(2, ℝ)) :
    geodesicReflection g '' leftHalfPlane g = rightHalfPlane g := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (geodesicReflection_mem_rightHalfPlane_iff g w).2 hw
  · intro hz
    refine ⟨geodesicReflection g z, ?_, geodesicReflection_apply_apply g z⟩
    exact (geodesicReflection_mem_leftHalfPlane_iff g z).2 hz

end TauCeti.UpperHalfPlane
