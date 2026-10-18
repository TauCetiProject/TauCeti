/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.HalfPlane
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Between

/-!
# Reflections in hyperbolic geodesics

Reflection in the imaginary axis sends `x + iy` to `-x + iy`; it is the action of Mathlib's
`UpperHalfPlane.J : GL (Fin 2) ℝ`.  Conjugating this isometry by the projective Möbius action
gives reflection in the oriented geodesic `geodesicLine g`.  The resulting map fixes that line
pointwise, exchanges its right and left half-planes, and depends only on the line as a set.

These reflections are the orientation-reversing generators used to construct hyperbolic
reflection groups.  Products of adjacent reflections are orientation preserving and supply the
side-pairing transformations for triangle groups.

## Main declarations

* `TauCeti.UpperHalfPlane.imaginaryAxisReflection`: reflection in the imaginary axis, the action
  of `UpperHalfPlane.J`.
* `TauCeti.UpperHalfPlane.geodesicReflection`: reflection in `geodesicLine g`, obtained by
  conjugating `imaginaryAxisReflection` by `g`.
* `TauCeti.UpperHalfPlane.geodesicReflection_apply_eq_smul`: it is the action of the conjugate
  `g J g⁻¹` in `PGL(2, ℝ)`.
* `TauCeti.UpperHalfPlane.smul_geodesicReflection`: moving a reflection by `h` gives the
  reflection in the moved geodesic.
* `TauCeti.UpperHalfPlane.geodesicReflection_eq_of_range_eq`: the reflection depends only on
  the geodesic line as a set.
* `TauCeti.UpperHalfPlane.geodesicReflection_geodesicReflection`: a geodesic reflection is an
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
an isometry. It is the action of Mathlib's orientation-reversing involution
`UpperHalfPlane.J : GL (Fin 2) ℝ` (`imaginaryAxisReflection_apply`). -/
def imaginaryAxisReflection : ℍ ≃ᵢ ℍ where
  toFun z := J • z
  invFun z := J • z
  left_inv z := by simp only [smul_smul, ← sq, J_sq, one_smul]
  right_inv z := by simp only [smul_smul, ← sq, J_sq, one_smul]
  isometry_toFun := Isometry.of_dist_eq fun z w ↦ by
    have him (z : ℍ) : (J • z).im = z.im := by
      rw [← UpperHalfPlane.coe_im, coe_J_smul, Complex.neg_im, Complex.conj_im, neg_neg,
        UpperHalfPlane.coe_im]
    rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq, coe_J_smul, coe_J_smul, dist_neg_neg,
      Complex.dist_conj_conj, him, him]

/-- Reflection in the imaginary axis is the action of `UpperHalfPlane.J`. -/
theorem imaginaryAxisReflection_apply (z : ℍ) : imaginaryAxisReflection z = J • z :=
  (rfl)

/-- Reflection in the imaginary axis negates the real part. -/
@[simp]
theorem imaginaryAxisReflection_re (z : ℍ) : (imaginaryAxisReflection z).re = -z.re := by
  rw [imaginaryAxisReflection_apply, ← UpperHalfPlane.coe_re, coe_J_smul, Complex.neg_re,
    Complex.conj_re, UpperHalfPlane.coe_re]

/-- Reflection in the imaginary axis preserves the imaginary part. -/
@[simp]
theorem imaginaryAxisReflection_im (z : ℍ) : (imaginaryAxisReflection z).im = z.im := by
  rw [imaginaryAxisReflection_apply, ← UpperHalfPlane.coe_im, coe_J_smul, Complex.neg_im,
    Complex.conj_im, neg_neg, UpperHalfPlane.coe_im]

/-- Reflection in the imaginary axis is an involution. -/
@[simp]
theorem imaginaryAxisReflection_imaginaryAxisReflection (z : ℍ) :
    imaginaryAxisReflection (imaginaryAxisReflection z) = z :=
  imaginaryAxisReflection.left_inv z

/-- Reflection in the imaginary axis is its own inverse. -/
@[simp]
theorem imaginaryAxisReflection_symm : imaginaryAxisReflection.symm = imaginaryAxisReflection :=
  (rfl)

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

/-- Reflection in the imaginary axis commutes with the involution `pslS : z ↦ -1/z`. -/
theorem imaginaryAxisReflection_pslS_smul (z : ℍ) :
    imaginaryAxisReflection (pslS • z) = pslS • imaginaryAxisReflection z := by
  apply UpperHalfPlane.coe_injective
  simp only [imaginaryAxisReflection_apply, coe_J_smul, pslS_smul, modular_S_smul,
    UpperHalfPlane.coe_mk, map_inv₀, map_neg, inv_neg, neg_neg]

/-- Reflection in the imaginary axis commutes with the dilations `z ↦ exp s * z`. -/
theorem imaginaryAxisReflection_dilation_smul (s : ℝ) (z : ℍ) :
    imaginaryAxisReflection (Matrix.SpecialLinearGroup.dilation s • z) =
      Matrix.SpecialLinearGroup.dilation s • imaginaryAxisReflection z := by
  apply UpperHalfPlane.coe_injective
  rw [imaginaryAxisReflection_apply, imaginaryAxisReflection_apply, coe_J_smul,
    coe_dilation_smul, coe_dilation_smul, coe_J_smul, map_mul, Complex.conj_ofReal, mul_neg]

/-- Reflection in the oriented geodesic `geodesicLine g`, obtained by transporting reflection in
the imaginary axis along the projective Möbius isometry `g`. -/
def geodesicReflection (g : PSL(2, ℝ)) : ℍ ≃ᵢ ℍ :=
  ((IsometryEquiv.constSMul g⁻¹).trans imaginaryAxisReflection).trans
    (IsometryEquiv.constSMul g)

/-- Reflection in `geodesicLine g` is conjugated imaginary-axis reflection. -/
theorem geodesicReflection_apply (g : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflection g z = g • imaginaryAxisReflection (g⁻¹ • z) :=
  (rfl)

/-- Reflection in `geodesicLine g` is the action of the element `g J g⁻¹` of `PGL(2, ℝ)`, the
conjugate of `UpperHalfPlane.J` by the image of `g`. Products of geodesic reflections are thus
computed in `PGL(2, ℝ)`. -/
theorem geodesicReflection_apply_eq_smul (g : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflection g z =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL g * Matrix.ProjGenLinGroup.mk J *
        (Matrix.ProjectiveSpecialLinearGroup.toPGL g)⁻¹) • z := by
  rw [mul_smul, mul_smul, ← map_inv, toPGL_smul, pglMk_smul, toPGL_smul, geodesicReflection_apply,
    imaginaryAxisReflection_apply]

/-- Reflection in the geodesic line of the identity is reflection in the imaginary axis. -/
@[simp]
theorem geodesicReflection_one : geodesicReflection 1 = imaginaryAxisReflection := by
  ext z
  rw [geodesicReflection_apply, inv_one, one_smul, one_smul]

/-- Moving a geodesic reflection by `h` gives the reflection in the moved geodesic `h * g`. -/
@[simp]
theorem smul_geodesicReflection (h g : PSL(2, ℝ)) (z : ℍ) :
    h • geodesicReflection g z = geodesicReflection (h * g) (h • z) := by
  rw [geodesicReflection_apply, geodesicReflection_apply, mul_inv_rev, mul_smul, mul_smul,
    inv_smul_smul]

/-- Reflection in a geodesic is an involution. -/
@[simp]
theorem geodesicReflection_geodesicReflection (g : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflection g (geodesicReflection g z) = z := by
  simp only [geodesicReflection_apply, inv_smul_smul,
    imaginaryAxisReflection_imaginaryAxisReflection, smul_inv_smul]

/-- A geodesic reflection is its own inverse. -/
@[simp]
theorem geodesicReflection_symm (g : PSL(2, ℝ)) :
    (geodesicReflection g).symm = geodesicReflection g := by
  apply IsometryEquiv.ext
  intro z
  apply (geodesicReflection g).injective
  rw [(geodesicReflection g).apply_symm_apply, geodesicReflection_geodesicReflection]

/-- Reversing the orientation of a geodesic line does not change the reflection in it. -/
@[simp]
theorem geodesicReflection_mul_pslS (g : PSL(2, ℝ)) :
    geodesicReflection (g * pslS) = geodesicReflection g := by
  ext z
  rw [geodesicReflection_apply, geodesicReflection_apply, mul_inv_rev, mul_smul, mul_smul,
    ← imaginaryAxisReflection_pslS_smul, smul_inv_smul]

/-- Shifting the parametrisation of a geodesic line does not change the reflection in it. -/
@[simp]
theorem geodesicReflection_mul_dilation (g : PSL(2, ℝ)) (s : ℝ) :
    geodesicReflection (g * ↑(Matrix.SpecialLinearGroup.dilation s)) = geodesicReflection g := by
  ext z
  rw [geodesicReflection_apply, geodesicReflection_apply, mul_inv_rev, mul_smul, mul_smul,
    pslMk_smul, ← imaginaryAxisReflection_dilation_smul, ← pslMk_smul, smul_inv_smul]

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

/-- Reflection in `geodesicLine g` fixes every point of its standard parametrisation. -/
@[simp]
theorem geodesicReflection_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) :
    geodesicReflection g (geodesicLine g t) = geodesicLine g t :=
  (geodesicReflection_apply_eq_self_iff g _).2 (Set.mem_range_self t)

/-- A geodesic reflection depends only on the geodesic line as a set, not on the representative
`g` (which also records an orientation and a base point). -/
theorem geodesicReflection_eq_of_range_eq {g h : PSL(2, ℝ)}
    (hgh : Set.range (geodesicLine g) = Set.range (geodesicLine h)) :
    geodesicReflection g = geodesicReflection h := by
  have key (k : PSL(2, ℝ)) {s t : ℝ} (hst : s ≠ t) :
      geodesicReflection (geodesicBetween (geodesicLine k s) (geodesicLine k t)) =
        geodesicReflection k := by
    rcases hst.lt_or_gt with hst | hst
    · rw [geodesicBetween_geodesicLine_of_lt k hst, geodesicReflection_mul_dilation]
    · rw [geodesicBetween_swap ((geodesicLine_injective k).ne hst.ne),
        geodesicReflection_mul_pslS, geodesicReflection_mul_dilation,
        geodesicBetween_geodesicLine_of_lt k hst, geodesicReflection_mul_dilation]
  obtain ⟨s, hs⟩ : geodesicLine g 0 ∈ Set.range (geodesicLine h) := hgh ▸ Set.mem_range_self 0
  obtain ⟨t, ht⟩ : geodesicLine g 1 ∈ Set.range (geodesicLine h) := hgh ▸ Set.mem_range_self 1
  have hst : s ≠ t := by
    rintro rfl
    exact zero_ne_one (geodesicLine_injective g (hs.symm.trans ht))
  rw [← key g zero_ne_one, ← hs, ← ht, key h hst]

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
  rw [← geodesicReflection_symm, IsometryEquiv.image_symm]
  ext z
  exact geodesicReflection_mem_rightHalfPlane_iff g z

/-- Reflection in a geodesic maps its left half-plane onto its right half-plane. -/
@[simp]
theorem geodesicReflection_image_leftHalfPlane (g : PSL(2, ℝ)) :
    geodesicReflection g '' leftHalfPlane g = rightHalfPlane g := by
  rw [← geodesicReflection_symm, IsometryEquiv.image_symm]
  ext z
  exact geodesicReflection_mem_leftHalfPlane_iff g z

end TauCeti.UpperHalfPlane
