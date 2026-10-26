/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.HalfPlane
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.FromTo
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.VertexAngle
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.ConjJ
import Mathlib.Analysis.Calculus.Deriv.Star
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Semicircle

/-!
# Reflections in hyperbolic geodesics

Reflection in the imaginary axis sends `x + iy` to `-x + iy`; it is the action of Mathlib's
`UpperHalfPlane.J : GL (Fin 2) ℝ`.  Conjugating this isometry by the projective Möbius action
gives reflection in the oriented geodesic `geodesicLine g`.  The resulting map fixes that line
pointwise, exchanges its right and left half-planes, and depends only on the line as a set.

These reflections are the orientation-reversing generators used to construct hyperbolic
reflection groups.  Products of adjacent reflections are orientation preserving and supply the
side-pairing transformations for triangle groups.

Conjugation by `J` is the automorphism `pslConjJ` of `PSL(2, ℝ)` (from
`TauCeti/Analysis/Complex/UpperHalfPlane/PSL/ConjJ.lean`), and `J` intertwines each `g` with
`pslConjJ g`. Hence the product of two geodesic reflections is the action of an element of
`PSL(2, ℝ)`, `geodesicReflectionComp g h`. Since the vertices of polygons may be ideal,
reflections are also extended to `ℍ ∪ ∂ℍ`, where `J` acts on `∂ℍ = ℝ ∪ {∞}` by `x ↦ -x`:
`extGeodesicReflection g` fixes the line of `g` with its ideal endpoints, reverses orientation
(the left side of the geodesic from `p` to `q` goes to the left side of the geodesic from the
image of `q` to the image of `p`), and preserves angles. Reflecting a point `c` to the left of a
line from `a` to `b` lands it to the left of the geodesic from `c` to `a` when the angle at `a`
is acute; this is the convexity condition for gluing a triangle to its mirror image.

## Main declarations

* `TauCeti.UpperHalfPlane.isometry_J_smul`: the action of `UpperHalfPlane.J` is an isometry.
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
* `TauCeti.UpperHalfPlane.extGeodesicReflection`: reflection in `geodesicLine g` on `ℍ ∪ ∂ℍ`.
* `TauCeti.UpperHalfPlane.extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_iff`: a
  geodesic reflection reverses orientation.
* `TauCeti.UpperHalfPlane.vertexAngle_extGeodesicReflection`: geodesic reflections preserve
  angles.
* `TauCeti.UpperHalfPlane.geodesicReflectionComp`: the product of two geodesic reflections, as an
  element of `PSL(2, ℝ)` (`geodesicReflectionComp_smul`), composing by
  `geodesicReflectionComp_mul_geodesicReflectionComp` and moving equivariantly by
  `mul_geodesicReflectionComp_mul_inv`.
* `TauCeti.UpperHalfPlane.isParabolic_geodesicReflectionComp_iff`: the product of the
  reflections in two lines with a common ideal endpoint is parabolic exactly when the lines are
  distinct; for vertical lines it is a translation (`geodesicReflectionComp_upperRightHom`).
* `TauCeti.UpperHalfPlane.extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_left` and
  `TauCeti.UpperHalfPlane.extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_right`:
  reflecting across a side with an acute angle at one end.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 7.
* Svetlana Katok, *Fuchsian Groups*, §2.1.
-/

public section

noncomputable section

open UpperHalfPlane
open Matrix.ProjectiveSpecialLinearGroup (IsParabolic isParabolic_conj_iff
  isParabolic_upperRightHom_iff upperRightHom upperRightHom_smul_coe)
open Matrix.SpecialLinearGroup (dilation)
open scoped MatrixGroups Pointwise OnePoint Real ComplexConjugate

namespace TauCeti.UpperHalfPlane

/-- The orientation-reversing involution `UpperHalfPlane.J : z ↦ -conj z` acts on `ℍ` by an
isometry. -/
theorem isometry_J_smul : Isometry (J • · : ℍ → ℍ) :=
  Isometry.of_dist_eq fun z w ↦ by
    rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq, coe_J_smul, coe_J_smul, dist_neg_neg,
      Complex.dist_conj_conj, J_smul_im, J_smul_im]

/-- Reflection in the imaginary axis of the upper half-plane, `x + iy ↦ -x + iy`, packaged as
an isometry. It is the action of Mathlib's orientation-reversing involution
`UpperHalfPlane.J : GL (Fin 2) ℝ` (`imaginaryAxisReflection_apply`). -/
def imaginaryAxisReflection : ℍ ≃ᵢ ℍ where
  toFun z := J • z
  invFun z := J • z
  left_inv z := by simp only [smul_smul, ← sq, J_sq, one_smul]
  right_inv z := by simp only [smul_smul, ← sq, J_sq, one_smul]
  isometry_toFun := isometry_J_smul

/-- Reflection in the imaginary axis is the action of `UpperHalfPlane.J`. -/
theorem imaginaryAxisReflection_apply (z : ℍ) : imaginaryAxisReflection z = J • z :=
  (rfl)

/-- Reflection in the imaginary axis negates the real part. -/
@[simp]
theorem imaginaryAxisReflection_re (z : ℍ) : (imaginaryAxisReflection z).re = -z.re :=
  J_smul_re z

/-- Reflection in the imaginary axis preserves the imaginary part. -/
@[simp]
theorem imaginaryAxisReflection_im (z : ℍ) : (imaginaryAxisReflection z).im = z.im :=
  J_smul_im z

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
  rcases exists_eq_mul_dilation_or_eq_mul_pslS_mul_dilation_of_range_eq hgh with
    ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
  simp only [geodesicReflection_mul_dilation, geodesicReflection_mul_pslS]

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

/-! ### Reflection in a geodesic on `ℍ ∪ ∂ℍ` -/

/-- Reflection in the geodesic line of `g`, extended to the ideal boundary: on `ℍ` it is
`geodesicReflection g`, and on `∂ℍ` it is the Möbius map `g J g⁻¹`, where
`J : x ↦ -x` is reflection in the imaginary axis. It fixes the line and its two ideal endpoints
(`IsGeodesicFromTo.extGeodesicReflection_left`) and exchanges the two sides of the line
(`extGeodesicReflection_mem_extLeftHalfPlane_mul_pslS_iff`). -/
def extGeodesicReflection (g : PSL(2, ℝ)) : ℍ ⊕ OnePoint ℝ → ℍ ⊕ OnePoint ℝ :=
  Sum.map (geodesicReflection g) fun ξ ↦ g • J • g⁻¹ • ξ

/-- On `ℍ`, the extended reflection is `geodesicReflection`. -/
@[simp]
theorem extGeodesicReflection_inl (g : PSL(2, ℝ)) (z : ℍ) :
    extGeodesicReflection g (.inl z) = .inl (geodesicReflection g z) :=
  (rfl)

/-- On the ideal boundary, the extended reflection is the Möbius map `g J g⁻¹`. -/
@[simp]
theorem extGeodesicReflection_inr (g : PSL(2, ℝ)) (ξ : OnePoint ℝ) :
    extGeodesicReflection g (.inr ξ) = .inr (g • J • g⁻¹ • ξ) :=
  (rfl)

/-- Reflection in the geodesic line of `g` is reflection in the imaginary axis conjugated by
`g`. -/
theorem extGeodesicReflection_apply (g : PSL(2, ℝ)) (p : ℍ ⊕ OnePoint ℝ) :
    extGeodesicReflection g p = g • extGeodesicReflection 1 (g⁻¹ • p) := by
  rcases p with z | ξ
  · simp [geodesicReflection_apply]
  · simp

/-- Moving a reflection by `h` gives the reflection in the moved geodesic. -/
theorem smul_extGeodesicReflection (h g : PSL(2, ℝ)) (p : ℍ ⊕ OnePoint ℝ) :
    h • extGeodesicReflection g p = extGeodesicReflection (h * g) (h • p) := by
  rw [extGeodesicReflection_apply, extGeodesicReflection_apply (h * g), mul_inv_rev, mul_smul,
    mul_smul, inv_smul_smul, smul_smul]

/-- Reflection in the imaginary axis intertwines `h` with its conjugate `pslConjJ h`. -/
theorem extGeodesicReflection_one_smul (h : PSL(2, ℝ)) (p : ℍ ⊕ OnePoint ℝ) :
    extGeodesicReflection 1 (h • p) = pslConjJ h • extGeodesicReflection 1 p := by
  rcases p with z | ξ
  · simp [imaginaryAxisReflection_apply, J_smul_smul]
  · simp [J_smul_smul_onePoint]

/-- Reflection in a geodesic is an involution of `ℍ ∪ ∂ℍ`. -/
@[simp]
theorem extGeodesicReflection_extGeodesicReflection (g : PSL(2, ℝ)) (p : ℍ ⊕ OnePoint ℝ) :
    extGeodesicReflection g (extGeodesicReflection g p) = p := by
  rcases p with z | ξ
  · simp
  · simp

/-- Reflection in a geodesic is injective. -/
theorem extGeodesicReflection_injective (g : PSL(2, ℝ)) :
    Function.Injective (extGeodesicReflection g) :=
  Function.LeftInverse.injective (extGeodesicReflection_extGeodesicReflection g)

/-- Reversing the orientation of a geodesic line does not change the reflection in it. -/
@[simp]
theorem extGeodesicReflection_mul_pslS (g : PSL(2, ℝ)) :
    extGeodesicReflection (g * pslS) = extGeodesicReflection g := by
  funext p
  rw [extGeodesicReflection_apply, extGeodesicReflection_apply g, mul_inv_rev, mul_smul,
    mul_smul, extGeodesicReflection_one_smul, pslS_inv, pslConjJ_pslS, smul_smul pslS,
    pslS_mul_self, one_smul]

/-- Shifting the parametrisation of a geodesic line does not change the reflection in it. -/
@[simp]
theorem extGeodesicReflection_mul_dilation (g : PSL(2, ℝ)) (s : ℝ) :
    extGeodesicReflection (g * ↑(Matrix.SpecialLinearGroup.dilation s)) =
      extGeodesicReflection g := by
  funext p
  rw [extGeodesicReflection_apply, extGeodesicReflection_apply g, mul_inv_rev, mul_smul,
    mul_smul, extGeodesicReflection_one_smul, map_inv, pslConjJ_dilation, smul_inv_smul]

/-- A geodesic reflection of `ℍ ∪ ∂ℍ` depends only on the geodesic line as a set. -/
theorem extGeodesicReflection_eq_of_range_eq {g h : PSL(2, ℝ)}
    (hgh : Set.range (geodesicLine g) = Set.range (geodesicLine h)) :
    extGeodesicReflection g = extGeodesicReflection h := by
  rcases exists_eq_mul_dilation_or_eq_mul_pslS_mul_dilation_of_range_eq hgh with
    ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
  simp only [extGeodesicReflection_mul_dilation, extGeodesicReflection_mul_pslS]

/-- Reflection in the line of `g` fixes the point that `g` runs from. -/
theorem IsGeodesicFromTo.extGeodesicReflection_left {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) : extGeodesicReflection g p = p := by
  rcases p with z | ξ
  · rw [extGeodesicReflection_inl, (geodesicReflection_apply_eq_self_iff g z).2 hg.left_mem_range]
  · rw [extGeodesicReflection_inr, ← hg.smul_zero_eq, inv_smul_smul, J_smul_coe, neg_zero]

/-- Reflection in the line of `g` fixes the point that `g` runs to. -/
theorem IsGeodesicFromTo.extGeodesicReflection_right {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) : extGeodesicReflection g q = q := by
  rcases q with w | η
  · rw [extGeodesicReflection_inl, (geodesicReflection_apply_eq_self_iff g w).2 hg.right_mem_range]
  · rw [extGeodesicReflection_inr, ← hg.smul_infty_eq, inv_smul_smul, J_smul_infty]

/-- Reflection in the imaginary axis carries its left side onto the left side of the reversed
axis. -/
private theorem extGeodesicReflection_one_mem_extLeftHalfPlane_pslS_iff (p : ℍ ⊕ OnePoint ℝ) :
    extGeodesicReflection 1 p ∈ extLeftHalfPlane pslS ↔ p ∈ extLeftHalfPlane 1 := by
  rcases p with z | ξ
  · simp only [extGeodesicReflection_inl, inl_mem_extLeftHalfPlane_iff,
      mem_leftHalfPlane_iff_sideForm_neg, sideForm_pslS, sideForm_one, geodesicReflection_one,
      coe_re, imaginaryAxisReflection_re, neg_neg]
  · induction ξ using OnePoint.rec with
    | infty =>
      simp only [extGeodesicReflection_inr, inv_one, one_smul, J_smul_infty,
        inr_mem_extLeftHalfPlane_iff]
      have h₁ := smul_zero_notMem_boundaryLeftHalfPlane pslS
      have h₂ := smul_infty_notMem_boundaryLeftHalfPlane 1
      rw [pslS_smul_zero] at h₁
      rw [one_smul] at h₂
      exact iff_of_false h₁ h₂
    | coe x =>
      simp only [extGeodesicReflection_inr, inv_one, one_smul, J_smul_coe,
        inr_mem_extLeftHalfPlane_iff, coe_mem_boundaryLeftHalfPlane_iff, sideForm_pslS,
        sideForm_one, Complex.ofReal_re, neg_neg]

/-- The geodesic line of the conjugate `pslConjJ g` is the reflection in the imaginary axis of
the geodesic line of `g`, with the same parametrisation. -/
theorem geodesicLine_pslConjJ (g : PSL(2, ℝ)) (t : ℝ) :
    geodesicLine (pslConjJ g) t = imaginaryAxisReflection (geodesicLine g t) := by
  rw [← mul_one g, ← smul_geodesicLine, imaginaryAxisReflection_apply, J_smul_smul, mul_one,
    ← imaginaryAxisReflection_apply,
    (imaginaryAxisReflection_apply_eq_self_iff _).2 (by simp [geodesicLine_one_apply]),
    smul_geodesicLine, mul_one]

/-- Reflection in the imaginary axis carries a geodesic line from `p` to `q` to a geodesic line
from the reflection of `p` to the reflection of `q`, conjugated by `J`. -/
private theorem IsGeodesicFromTo.extGeodesicReflection_one {k : PSL(2, ℝ)}
    {p q : ℍ ⊕ OnePoint ℝ} (hk : IsGeodesicFromTo k p q) :
    IsGeodesicFromTo (pslConjJ k) (extGeodesicReflection 1 p) (extGeodesicReflection 1 q) := by
  have hline (t : ℝ) : geodesicReflection 1 (geodesicLine k t) = geodesicLine (pslConjJ k) t := by
    rw [geodesicReflection_one, geodesicLine_pslConjJ]
  rcases p with z | ξ <;> rcases q with w | η <;>
    simp only [isGeodesicFromTo_inl_inl, isGeodesicFromTo_inl_inr, isGeodesicFromTo_inr_inl,
      isGeodesicFromTo_inr_inr, extGeodesicReflection_inl, extGeodesicReflection_inr, inv_one,
      one_smul] at hk ⊢
  · obtain ⟨s, t, hst, rfl, rfl⟩ := hk
    exact ⟨s, t, hst, (hline s).symm, (hline t).symm⟩
  · obtain ⟨⟨t, rfl⟩, rfl⟩ := hk
    exact ⟨⟨t, (hline t).symm⟩, by rw [J_smul_smul_onePoint, J_smul_infty]⟩
  · obtain ⟨rfl, ⟨t, rfl⟩⟩ := hk
    exact ⟨by rw [J_smul_smul_onePoint, J_smul_coe, neg_zero], ⟨t, (hline t).symm⟩⟩
  · obtain ⟨rfl, rfl⟩ := hk
    exact ⟨by rw [J_smul_smul_onePoint, J_smul_coe, neg_zero],
      by rw [J_smul_smul_onePoint, J_smul_infty]⟩

/-- Reflection in the imaginary axis carries the left side of `k` onto the left side of the
reversed conjugate line. -/
private theorem extGeodesicReflection_one_mem_extLeftHalfPlane_iff (k : PSL(2, ℝ))
    (r : ℍ ⊕ OnePoint ℝ) :
    extGeodesicReflection 1 r ∈ extLeftHalfPlane (pslConjJ k * pslS) ↔
      r ∈ extLeftHalfPlane k := by
  rw [← smul_extLeftHalfPlane, ← mul_one k, ← smul_extLeftHalfPlane, mul_one,
    Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem, ← map_inv,
    ← extGeodesicReflection_one_smul, extGeodesicReflection_one_mem_extLeftHalfPlane_pslS_iff]

/-- Reflection in a geodesic carries its left side onto the left side of the reversed line,
which is its right side. -/
theorem extGeodesicReflection_mem_extLeftHalfPlane_mul_pslS_iff (g : PSL(2, ℝ))
    (p : ℍ ⊕ OnePoint ℝ) :
    extGeodesicReflection g p ∈ extLeftHalfPlane (g * pslS) ↔ p ∈ extLeftHalfPlane g := by
  rw [extGeodesicReflection_apply, ← smul_extLeftHalfPlane, Set.smul_mem_smul_set_iff,
    ← mul_one g, ← smul_extLeftHalfPlane g 1, mul_one, Set.mem_smul_set_iff_inv_smul_mem,
    extGeodesicReflection_one_mem_extLeftHalfPlane_pslS_iff]

/-- **A geodesic reflection reverses orientation**: `r` is strictly to the left of the geodesic
from `p` to `q` exactly when its reflection is strictly to the left of the geodesic from the
reflection of `q` to the reflection of `p`. -/
theorem extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_iff (g : PSL(2, ℝ))
    {p q : ℍ ⊕ OnePoint ℝ} (hpq : p ≠ q) (r : ℍ ⊕ OnePoint ℝ) :
    extGeodesicReflection g r ∈ extLeftHalfPlane
        (geodesicFromTo (extGeodesicReflection g q) (extGeodesicReflection g p)) ↔
      r ∈ extLeftHalfPlane (geodesicFromTo p q) := by
  -- move to the frame where `g` is the imaginary axis
  have hpq' : g⁻¹ • p ≠ g⁻¹ • q := (MulAction.injective g⁻¹).ne hpq
  have hk := isGeodesicFromTo_geodesicFromTo hpq'
  have hk' := isGeodesicFromTo_mul_pslS_iff.2 hk.extGeodesicReflection_one
  have hne : extGeodesicReflection 1 (g⁻¹ • q) ≠ extGeodesicReflection 1 (g⁻¹ • p) :=
    (extGeodesicReflection_injective 1).ne hpq'.symm
  rw [extGeodesicReflection_apply g q, extGeodesicReflection_apply g p,
    extLeftHalfPlane_geodesicFromTo_smul g hne,
    hk'.extLeftHalfPlane_eq (isGeodesicFromTo_geodesicFromTo hne), extGeodesicReflection_apply,
    Set.smul_mem_smul_set_iff, extGeodesicReflection_one_mem_extLeftHalfPlane_iff,
    extLeftHalfPlane_geodesicFromTo_smul g⁻¹ hpq, Set.smul_mem_smul_set_iff]

/-- A point of `ℍ` is weakly to the left of the geodesic from `p` to `q` exactly when its mirror
image is weakly to the left of the geodesic from the mirror image of `q` to that of `p`. -/
theorem geodesicReflection_mem_closure_leftHalfPlane_geodesicFromTo_iff (g : PSL(2, ℝ))
    {p q : ℍ ⊕ OnePoint ℝ} (hpq : p ≠ q) (z : ℍ) :
    geodesicReflection g z ∈ closure (leftHalfPlane
        (geodesicFromTo (extGeodesicReflection g q) (extGeodesicReflection g p))) ↔
      z ∈ closure (leftHalfPlane (geodesicFromTo p q)) := by
  rw [mem_closure_leftHalfPlane_geodesicFromTo_iff
      ((extGeodesicReflection_injective g).ne hpq.symm),
    ← extGeodesicReflection_inl, extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_iff g
      hpq.symm, mem_closure_leftHalfPlane_geodesicFromTo_iff hpq]

/-! ### Angles -/

/-- Reflection in the imaginary axis conjugates velocities of geodesic lines:
the velocity of `pslConjJ g` is `-conj` of that of `g`. -/
theorem velocity_pslConjJ (g : PSL(2, ℝ)) (t : ℝ) :
    velocity (pslConjJ g) t = -(starRingEnd ℂ) (velocity g t) := by
  have h : (fun s : ℝ ↦ (geodesicLine (pslConjJ g) s : ℂ)) =
      fun s ↦ -star (geodesicLine g s : ℂ) := by
    funext s
    rw [geodesicLine_pslConjJ, imaginaryAxisReflection_apply, coe_J_smul, Complex.star_def]
  have h' : HasDerivAt (fun s : ℝ ↦ -star (geodesicLine g s : ℂ)) (-star (velocity g t)) t :=
    (HasDerivAt.star (hasDerivAt_coe_geodesicLine g t)).neg
  rw [← h, Complex.star_def] at h'
  exact (hasDerivAt_coe_geodesicLine (pslConjJ g) t).unique h'

/-- Reflection in the imaginary axis preserves angles between geodesic lines. -/
@[simp]
theorem geodesicAngle_pslConjJ (g₁ g₂ : PSL(2, ℝ)) :
    geodesicAngle (pslConjJ g₁) (pslConjJ g₂) = geodesicAngle g₁ g₂ := by
  rw [geodesicAngle_def, geodesicAngle_def, velocity_pslConjJ, velocity_pslConjJ,
    InnerProductGeometry.angle_neg_neg, ← Complex.conjLIE_apply, ← Complex.conjLIE_apply]
  exact Complex.conjLIE.toLinearIsometry.angle_map _ _

/-- The ray from the reflection of `A` towards the reflection of `q` is the reflection of the ray
from `A` towards `q`. -/
private theorem rayToward_geodesicReflection_one {A : ℍ} {q : ℍ ⊕ OnePoint ℝ}
    (hAq : .inl A ≠ q) :
    rayToward (geodesicReflection 1 A) (extGeodesicReflection 1 q) =
      pslConjJ (rayToward A q) := by
  have h₁ := (isGeodesicFromTo_rayToward hAq).extGeodesicReflection_one
  rw [extGeodesicReflection_inl] at h₁
  have hne : (.inl (geodesicReflection 1 A) : ℍ ⊕ OnePoint ℝ) ≠ extGeodesicReflection 1 q := by
    rw [← extGeodesicReflection_inl]
    exact (extGeodesicReflection_injective 1).ne hAq
  obtain ⟨s, hs⟩ := h₁.exists_eq_mul_dilation (isGeodesicFromTo_rayToward hne)
  have h₀ := geodesicLine_rayToward_zero (geodesicReflection 1 A) (extGeodesicReflection 1 q)
  rw [hs, geodesicLine_mul_dilation, add_zero] at h₀
  have h₁ : geodesicLine (pslConjJ (rayToward A q)) 0 = geodesicReflection 1 A := by
    rw [geodesicLine_pslConjJ, geodesicLine_rayToward_zero, geodesicReflection_one]
  have hs₀ : s = 0 := geodesicLine_injective _ (h₀.trans h₁.symm)
  rw [hs, hs₀, Matrix.SpecialLinearGroup.dilation_zero, QuotientGroup.mk_one, mul_one]

/-- Reflection in the imaginary axis preserves angles at vertices of `ℍ ∪ ∂ℍ`. -/
private theorem vertexAngle_extGeodesicReflection_one {p q r : ℍ ⊕ OnePoint ℝ} (hpq : p ≠ q)
    (hpr : p ≠ r) :
    vertexAngle (extGeodesicReflection 1 p) (extGeodesicReflection 1 q)
        (extGeodesicReflection 1 r) = vertexAngle p q r := by
  rcases p with A | ξ
  · rw [extGeodesicReflection_inl, vertexAngle_inl, vertexAngle_inl,
      rayToward_geodesicReflection_one hpq, rayToward_geodesicReflection_one hpr,
      geodesicAngle_pslConjJ]
  · rw [extGeodesicReflection_inr, vertexAngle_inr, vertexAngle_inr]

/-- **Geodesic reflections preserve angles** at vertices of `ℍ ∪ ∂ℍ`. -/
theorem vertexAngle_extGeodesicReflection (g : PSL(2, ℝ)) {p q r : ℍ ⊕ OnePoint ℝ}
    (hpq : p ≠ q) (hpr : p ≠ r) :
    vertexAngle (extGeodesicReflection g p) (extGeodesicReflection g q)
        (extGeodesicReflection g r) = vertexAngle p q r := by
  have hinj : Function.Injective fun x ↦ extGeodesicReflection 1 (g⁻¹ • x) :=
    (extGeodesicReflection_injective 1).comp (MulAction.injective g⁻¹)
  rw [extGeodesicReflection_apply g p, extGeodesicReflection_apply g q,
    extGeodesicReflection_apply g r, vertexAngle_smul g (hinj.ne hpq) (hinj.ne hpr),
    vertexAngle_extGeodesicReflection_one ((MulAction.injective g⁻¹).ne hpq)
      ((MulAction.injective g⁻¹).ne hpr), vertexAngle_smul g⁻¹ hpq hpr]

/-! ### Products of two reflections -/

/-- The product of the reflections in the geodesic lines of `g` and of `h`, first in that of `h`:
the orientation-preserving isometry `z ↦ geodesicReflection g (geodesicReflection h z)`, as an
element of `PSL(2, ℝ)` (`geodesicReflectionComp_smul`), which also acts on `ℍ ∪ ∂ℍ` as the
composite of the extended reflections. -/
def geodesicReflectionComp (g h : PSL(2, ℝ)) : PSL(2, ℝ) :=
  g * pslConjJ (g⁻¹ * h) * h⁻¹

/-- The product of two geodesic reflections acts on `ℍ ∪ ∂ℍ` as the composite of the
reflections. -/
theorem geodesicReflectionComp_smul_eq_extGeodesicReflection (g h : PSL(2, ℝ))
    (p : ℍ ⊕ OnePoint ℝ) :
    geodesicReflectionComp g h • p = extGeodesicReflection g (extGeodesicReflection h p) := by
  rw [extGeodesicReflection_apply g, extGeodesicReflection_apply h, smul_smul,
    extGeodesicReflection_one_smul, extGeodesicReflection_extGeodesicReflection, smul_smul,
    geodesicReflectionComp, mul_smul]

/-- The product of two geodesic reflections acts on `ℍ` as the composite of the reflections. -/
theorem geodesicReflectionComp_smul (g h : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflectionComp g h • z = geodesicReflection g (geodesicReflection h z) := by
  have h' := geodesicReflectionComp_smul_eq_extGeodesicReflection g h (.inl z)
  rwa [Sum.smul_inl, extGeodesicReflection_inl, extGeodesicReflection_inl, Sum.inl.injEq] at h'

/-- Reversing the order of two reflections inverts their product. -/
@[simp]
theorem geodesicReflectionComp_inv (g h : PSL(2, ℝ)) :
    (geodesicReflectionComp g h)⁻¹ = geodesicReflectionComp h g := by
  simp [geodesicReflectionComp, mul_assoc]

/-- The product of a reflection with itself is the identity. -/
@[simp]
theorem geodesicReflectionComp_self (g : PSL(2, ℝ)) : geodesicReflectionComp g g = 1 := by
  simp [geodesicReflectionComp]

/-- Products of reflections compose: the middle reflection cancels. -/
@[simp]
theorem geodesicReflectionComp_mul_geodesicReflectionComp (g h k : PSL(2, ℝ)) :
    geodesicReflectionComp g h * geodesicReflectionComp h k = geodesicReflectionComp g k := by
  simp [geodesicReflectionComp, mul_assoc]

/-- Conjugating a product of reflections by `k` gives the product of the reflections in the
moved geodesics. -/
theorem mul_geodesicReflectionComp_mul_inv (k g h : PSL(2, ℝ)) :
    k * geodesicReflectionComp g h * k⁻¹ = geodesicReflectionComp (k * g) (k * h) := by
  simp [geodesicReflectionComp, mul_assoc]

/-- Reversing the orientation of the first line does not change the product of reflections. -/
@[simp]
theorem geodesicReflectionComp_mul_pslS_left (g h : PSL(2, ℝ)) :
    geodesicReflectionComp (g * pslS) h = geodesicReflectionComp g h := by
  simp [geodesicReflectionComp, mul_assoc, -pslS_inv]

/-- Reversing the orientation of the second line does not change the product of reflections. -/
@[simp]
theorem geodesicReflectionComp_mul_pslS_right (g h : PSL(2, ℝ)) :
    geodesicReflectionComp g (h * pslS) = geodesicReflectionComp g h := by
  simp [geodesicReflectionComp, mul_assoc, -pslS_inv]

/-- Shifting the parametrisation of the first line does not change the product of reflections. -/
@[simp]
theorem geodesicReflectionComp_mul_dilation_left (g h : PSL(2, ℝ)) (s : ℝ) :
    geodesicReflectionComp (g * ↑(Matrix.SpecialLinearGroup.dilation s)) h =
      geodesicReflectionComp g h := by
  simp [geodesicReflectionComp, mul_assoc]

/-- Shifting the parametrisation of the second line does not change the product of
reflections. -/
@[simp]
theorem geodesicReflectionComp_mul_dilation_right (g h : PSL(2, ℝ)) (s : ℝ) :
    geodesicReflectionComp g (h * ↑(Matrix.SpecialLinearGroup.dilation s)) =
      geodesicReflectionComp g h := by
  simp [geodesicReflectionComp, mul_assoc]

/-! ### Two geodesic lines with a common ideal endpoint -/

/-- The product of the reflections in the vertical lines `Re z = a` and `Re z = b`, the geodesic
lines of the translations by `a` and by `b`, is the translation by `2 (a - b)`. -/
@[simp]
theorem geodesicReflectionComp_upperRightHom (a b : ℝ) :
    geodesicReflectionComp (upperRightHom a) (upperRightHom b) = upperRightHom (2 * (a - b)) := by
  simp only [geodesicReflectionComp, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul,
    pslConjJ_upperRightHom]
  congr 1
  ring

/-- **Reflections in two lines with a common ideal endpoint.** If the geodesic lines of `g` and
`h` have the same forward endpoint, the product of the reflections in them is parabolic exactly
when their backward endpoints differ, that is, when the lines are distinct. -/
theorem isParabolic_geodesicReflectionComp_iff {g h : PSL(2, ℝ)}
    (hgh : g • (∞ : OnePoint ℝ) = h • ∞) :
    IsParabolic (geodesicReflectionComp g h) ↔
      g • ((0 : ℝ) : OnePoint ℝ) ≠ h • ((0 : ℝ) : OnePoint ℝ) := by
  -- move the common endpoint to `∞`, where both lines are vertical
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq PSL(2, ℝ) (g • (∞ : OnePoint ℝ)) ∞
  obtain ⟨a, s, hs⟩ := exists_eq_upperRightHom_mul_dilation (g := k * g) (by rw [mul_smul, hk])
  obtain ⟨b, t, ht⟩ := exists_eq_upperRightHom_mul_dilation (g := k * h)
    (by rw [mul_smul, ← hgh, hk])
  have h₀ {x : PSL(2, ℝ)} {c u : ℝ} (hx : k * x = upperRightHom c * ↑(dilation u)) :
      x • ((0 : ℝ) : OnePoint ℝ) = k⁻¹ • (c : OnePoint ℝ) := by
    rw [eq_inv_smul_iff, ← mul_smul, hx, mul_smul, dilation_smul_zero, upperRightHom_smul_coe,
      zero_add]
  rw [← isParabolic_conj_iff k, mul_geodesicReflectionComp_mul_inv, hs, ht,
    geodesicReflectionComp_mul_dilation_left, geodesicReflectionComp_mul_dilation_right,
    geodesicReflectionComp_upperRightHom, isParabolic_upperRightHom_iff, h₀ hs, h₀ ht]
  simp [sub_eq_zero]

/-! ### Reflecting a vertex across a side with acute angles -/

/-- Reflection in the imaginary axis is `z ↦ -conj z` on points of `ℍ ∪ ∂ℍ` read as complex
numbers. -/
theorem toComplex_extGeodesicReflection_one (p : ℍ ⊕ OnePoint ℝ) :
    toComplex (extGeodesicReflection 1 p) = -conj (toComplex p) := by
  rcases p with z | ξ
  · rw [extGeodesicReflection_inl, geodesicReflection_one, toComplex_inl, toComplex_inl,
      imaginaryAxisReflection_apply, coe_J_smul]
  · induction ξ using OnePoint.rec with
    | infty => simp
    | coe x => simp

/-- In the frame where the reflecting line is the upward imaginary axis, running from `a` to `b`,
let `c` lie to its left and let the semicircle through `c` and `a` have centre `m`. If the angle
at `a` is acute, then `m < 0`. -/
private theorem center_neg_of_vertexAngle_lt {a b c : ℍ ⊕ OnePoint ℝ} {m ρ : ℝ}
    (hab : IsGeodesicFromTo 1 a b) (hcinf : c ≠ .inr ∞) (hainf : a ≠ .inr ∞)
    (hcre : (toComplex c).re < 0) (hare : (toComplex a).re = 0) (hρ : 0 < ρ)
    (hcm : Complex.normSq (toComplex c - m) = ρ ^ 2)
    (ham : Complex.normSq (toComplex a - m) = ρ ^ 2) (hangle : vertexAngle a c b < π / 2) :
    m < 0 := by
  rcases a with A | ξ
  · -- the acute angle at `A` is `arccos (-m / ρ)`
    have hray : rayToward A b = rayToward A (.inr ∞) := by
      rcases b with B | η
      · obtain ⟨s, t, hst, hs, ht⟩ := isGeodesicFromTo_inl_inl.1 hab
        rw [rayToward_inl, rayToward_inr_infty, ← hs, ← ht]
        refine geodesicBetween_eq_toPoint_of_re_eq ?_ ?_
        · simp [geodesicLine_one_apply]
        · simpa [geodesicLine_one_apply] using hst
      · obtain ⟨-, rfl⟩ := isGeodesicFromTo_inl_inr.1 hab
        rw [one_smul]
    have h := vertexAngle_infty_of_lt_re hρ hcinf hainf hcm ham (by rw [hare]; exact hcre)
    rw [vertexAngle_inl, hray, ← vertexAngle_inl, h, hare, Real.arccos_lt_pi_div_two,
      div_pos_iff_of_pos_right hρ] at hangle
    linarith
  · -- an ideal `a` is `0`, and the centre is `|c|² / (2 Re c)`
    have hξ := hab.smul_zero_eq
    rw [one_smul] at hξ
    subst hξ
    have hy := im_toComplex_nonneg c
    simp [Complex.normSq_apply] at ham hcm
    nlinarith

/-- In the frame where the reflecting line is the upward imaginary axis, running from `a` to `b`:
if `c` lies to its left and the angle at `a` is acute, then the mirror image of `c` lies strictly
to the left of the geodesic from `c` to `a`. -/
private theorem extGeodesicReflection_one_mem_extLeftHalfPlane {a b c : ℍ ⊕ OnePoint ℝ}
    (hab : IsGeodesicFromTo 1 a b) (hc : c ∈ extLeftHalfPlane 1)
    (hangle : vertexAngle a c b < π / 2) :
    extGeodesicReflection 1 c ∈ extLeftHalfPlane (geodesicFromTo c a) := by
  -- `c` is a point to the left of the imaginary axis, possibly ideal but not `∞`
  have hcinf : c ≠ .inr ∞ := by
    rintro rfl
    rw [inr_mem_extLeftHalfPlane_iff] at hc
    exact smul_infty_notMem_boundaryLeftHalfPlane 1 (by rwa [one_smul])
  have hcre : (toComplex c).re < 0 := by
    rwa [mem_extLeftHalfPlane_iff_sideForm_toComplex_neg hcinf, sideForm_one] at hc
  -- `a` lies on the imaginary axis
  have hainf : a ≠ .inr ∞ := by
    rintro rfl
    have h := hab.smul_zero_eq
    rw [one_smul] at h
    exact OnePoint.coe_ne_infty 0 h
  have hare : (toComplex a).re = 0 := by
    have h := hab.sideForm_toComplex_left hainf
    rwa [sideForm_one] at h
  have hca : c ≠ a := fun h ↦ by rw [h, hare] at hcre; exact hcre.false
  -- the geodesic from `c` to `a` is a semicircle with `∞` on its left
  have hh := isGeodesicFromTo_geodesicFromTo hca
  have hinf : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (geodesicFromTo c a) :=
    (hh.infty_mem_boundaryLeftHalfPlane_iff_re_lt hcinf hainf).2 (by rw [hare]; exact hcre)
  obtain ⟨m, ρ, κ, hρ, hκ, hform⟩ := exists_sideForm_eq_of_infty_mem_boundaryLeftHalfPlane hinf
  have hcm : Complex.normSq (toComplex c - m) = ρ ^ 2 := by
    have h := hh.sideForm_toComplex_left hcinf
    rw [hform, mul_eq_zero, sub_eq_zero] at h
    exact (h.resolve_left hκ.ne').symm
  have ham : Complex.normSq (toComplex a - m) = ρ ^ 2 := by
    have h := hh.sideForm_toComplex_right hainf
    rw [hform, mul_eq_zero, sub_eq_zero] at h
    exact (h.resolve_left hκ.ne').symm
  -- its centre is to the left of the imaginary axis
  have hm := center_neg_of_vertexAngle_lt hab hcinf hainf hcre hare hρ hcm ham hangle
  -- the mirror image of `c` is strictly outside the semicircle, so to its left
  have hE : extGeodesicReflection 1 c ≠ .inr ∞ := by
    intro h
    rw [← extGeodesicReflection_extGeodesicReflection 1 c, h, extGeodesicReflection_inr] at hcinf
    simp at hcinf
  rw [mem_extLeftHalfPlane_iff_sideForm_toComplex_neg hE, hform,
    toComplex_extGeodesicReflection_one]
  refine mul_neg_of_pos_of_neg hκ (sub_neg.2 ?_)
  rw [← hcm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith

/-- **Reflecting across a side with an acute angle.** Let the geodesic line of `g` run from `a`
to `b`, and let `c` lie strictly to its left. If the angle at `a` between the directions to `c`
and `b` is acute, then the mirror image of `c` in the line lies strictly to the left of the
geodesic from `c` to `a`. -/
theorem extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_left {g : PSL(2, ℝ)}
    {a b c : ℍ ⊕ OnePoint ℝ} (hab : IsGeodesicFromTo g a b) (hc : c ∈ extLeftHalfPlane g)
    (hangle : vertexAngle a c b < π / 2) :
    extGeodesicReflection g c ∈ extLeftHalfPlane (geodesicFromTo c a) := by
  -- move to the frame where the line is the upward imaginary axis
  have hab' := hab.smul g⁻¹
  rw [inv_mul_cancel] at hab'
  have hc' : g⁻¹ • c ∈ extLeftHalfPlane 1 := by
    rwa [← Set.smul_mem_smul_set_iff (a := g), smul_inv_smul, smul_extLeftHalfPlane, mul_one]
  have hac : a ≠ c := fun h ↦ hab.left_notMem_extLeftHalfPlane (h ▸ hc)
  have h := extGeodesicReflection_one_mem_extLeftHalfPlane hab' hc'
    (by rwa [vertexAngle_smul g⁻¹ hac hab.ne])
  rwa [← Set.smul_mem_smul_set_iff (a := g), ← extGeodesicReflection_apply,
    ← extLeftHalfPlane_geodesicFromTo_smul g ((MulAction.injective g⁻¹).ne hac.symm),
    smul_inv_smul, smul_inv_smul] at h

/-- **Reflecting across a side with an acute angle at its end.** Let the geodesic line of `g` run
from `a` to `b`, and let `c` lie strictly to its left. If the angle at `b` between the directions
to `a` and `c` is acute, then the mirror image of `c` in the line lies strictly to the left of
the geodesic from `b` to `c`. -/
theorem extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_right {g : PSL(2, ℝ)}
    {a b c : ℍ ⊕ OnePoint ℝ} (hab : IsGeodesicFromTo g a b) (hc : c ∈ extLeftHalfPlane g)
    (hangle : vertexAngle b a c < π / 2) :
    extGeodesicReflection g c ∈ extLeftHalfPlane (geodesicFromTo b c) := by
  -- apply the previous result to the reversed line and the mirror image of `c`
  have hba : IsGeodesicFromTo (g * pslS) b a := isGeodesicFromTo_mul_pslS_iff.2 hab
  have hc' : extGeodesicReflection g c ∈ extLeftHalfPlane (g * pslS) :=
    (extGeodesicReflection_mem_extLeftHalfPlane_mul_pslS_iff g c).2 hc
  have hbc : b ≠ c := fun h ↦ hab.right_notMem_extLeftHalfPlane (h ▸ hc)
  have hangle' : vertexAngle b (extGeodesicReflection g c) a < π / 2 := by
    have h := vertexAngle_extGeodesicReflection g hbc hab.ne.symm
    rw [hab.extGeodesicReflection_right, hab.extGeodesicReflection_left,
      vertexAngle_comm b a c] at h
    rwa [h]
  have h := extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_left hba hc' hangle'
  rw [extGeodesicReflection_mul_pslS, extGeodesicReflection_extGeodesicReflection] at h
  have hcb : extGeodesicReflection g c ≠ b := fun h' ↦
    hba.left_notMem_extLeftHalfPlane (h' ▸ hc')
  rwa [← extGeodesicReflection_mem_extLeftHalfPlane_geodesicFromTo_iff g hcb,
    hab.extGeodesicReflection_right, extGeodesicReflection_extGeodesicReflection] at h

end TauCeti.UpperHalfPlane
