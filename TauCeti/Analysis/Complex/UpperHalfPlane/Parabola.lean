/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.HalfPlane
import Mathlib.Analysis.Convex.Mul

/-!
# Parabolic coordinates on the upper half-plane

The map `x + iy ↦ x + i(x² + y²)` identifies the upper half-plane with the open region
above the parabola `v = u²`. Geodesic side forms become affine in these coordinates.
Consequently intersections of closed hyperbolic half-planes have convex images. These
coordinates allow Euclidean convex-set topology to be applied to hyperbolic polygons.

The coordinate change is elementary: circles with centre on the real axis have equations
`|z|² - 2c Re z + c² = r²`, which are linear in `Re z` and `|z|²`.
-/

public section

noncomputable section

open Set Topology UpperHalfPlane
open scoped MatrixGroups

namespace UpperHalfPlane

open TauCeti.UpperHalfPlane

/-- Parabolic coordinates: the real part is unchanged and the imaginary part becomes `|z|²`. -/
def parabolaMap (z : ℍ) : ℂ := ⟨z.re, Complex.normSq z⟩

@[simp] theorem parabolaMap_re (z : ℍ) : (parabolaMap z).re = z.re := (rfl)

@[simp] theorem parabolaMap_im (z : ℍ) : (parabolaMap z).im = Complex.normSq z := (rfl)

/-- Parabolic coordinates take values strictly above the parabola. -/
theorem sq_re_lt_im_parabolaMap (z : ℍ) : (parabolaMap z).re ^ 2 < (parabolaMap z).im := by
  have h : z.re ^ 2 < z.re * z.re + z.im * z.im := by
    nlinarith [sq_pos_of_pos z.im_pos]
  simpa only [parabolaMap_re, parabolaMap_im, Complex.normSq_apply, coe_re, coe_im] using h

/-- The upper half-plane as the open region above a parabola. -/
def parabolaHomeomorph : ℍ ≃ₜ {w : ℂ // w.re ^ 2 < w.im} where
  toFun z := ⟨parabolaMap z, sq_re_lt_im_parabolaMap z⟩
  invFun w := ⟨⟨w.val.re, Real.sqrt (w.val.im - w.val.re ^ 2)⟩,
    Real.sqrt_pos.2 (sub_pos.2 w.property)⟩
  left_inv z := by
    apply UpperHalfPlane.ext_re_im
    · rfl
    · simp only [parabolaMap_re, parabolaMap_im, Complex.normSq_apply, coe_re, coe_im,
        mk_im]
      have h : z.re * z.re + z.im * z.im - z.re ^ 2 = z.im ^ 2 := by ring
      rw [h, Real.sqrt_sq z.im_pos.le]
  right_inv w := by
    apply Subtype.ext
    apply Complex.ext
    · rfl
    · have hsq : Real.sqrt (w.val.im - w.val.re ^ 2) *
          Real.sqrt (w.val.im - w.val.re ^ 2) = w.val.im - w.val.re ^ 2 :=
        Real.mul_self_sqrt (sub_pos.2 w.property).le
      simp only [parabolaMap_im, Complex.normSq_apply]
      nlinarith only [hsq]
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold parabolaMap
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  continuous_invFun := by
    apply Continuous.upperHalfPlaneMk
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop

/-- The forward coordinate formula of the parabolic homeomorphism. -/
@[simp] theorem coe_parabolaHomeomorph_apply (z : ℍ) :
    (parabolaHomeomorph z : ℂ) = parabolaMap z := (rfl)

/-- The inverse parabolic coordinate formula. -/
@[simp] theorem coe_parabolaHomeomorph_symm_apply (w : {w : ℂ // w.re ^ 2 < w.im}) :
    (parabolaHomeomorph.symm w : ℂ) = ⟨w.val.re, Real.sqrt (w.val.im - w.val.re ^ 2)⟩ := (rfl)

/-- Parabolic coordinates give an open embedding into the complex plane. -/
theorem isOpenEmbedding_parabolaMap : IsOpenEmbedding parabolaMap := by
  exact IsOpenEmbedding.comp
    (isOpen_lt (Complex.continuous_re.pow 2) Complex.continuous_im).isOpenEmbedding_subtypeVal
    parabolaHomeomorph.isOpenEmbedding

/-- The image of parabolic coordinates is exactly the region above the parabola. -/
theorem range_parabolaMap : range parabolaMap = {w : ℂ | w.re ^ 2 < w.im} := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    exact sq_re_lt_im_parabolaMap z
  · intro hw
    exact ⟨parabolaHomeomorph.symm ⟨w, hw⟩,
      congrArg Subtype.val (parabolaHomeomorph.apply_symm_apply ⟨w, hw⟩)⟩

/-- The region above the parabola is convex. -/
theorem convex_range_parabolaMap : Convex ℝ (range parabolaMap) := by
  rw [range_parabolaMap]
  simpa using (even_two.convexOn_pow (𝕜 := ℝ)).convex_strict_epigraph.linear_preimage
    Complex.equivRealProdLm.toLinearMap

/-- A side form is affine in parabolic coordinates. -/
theorem sideForm_eq_of_parabolaMap_eq (g : PSL(2, ℝ)) {u z w : ℍ} {a b : ℝ}
    (hab : a + b = 1) (hu : parabolaMap u = a • parabolaMap z + b • parabolaMap w) :
    sideForm g u = a * sideForm g z + b * sideForm g w := by
  induction g using Quotient.inductionOn' with | h A =>
  have hre := congrArg Complex.re hu
  have him := congrArg Complex.im hu
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    smul_eq_mul, parabolaMap_re, parabolaMap_im] at hre him
  simp only [sideForm_mk, coe_re]
  rw [him, hre]
  linear_combination (A 0 0 * A 0 1) * hab

/-- Intersections of closed hyperbolic half-planes become Euclidean convex sets. The index
family may be infinite or empty. -/
theorem convex_parabolaMap_image_iInter_closure_leftHalfPlane {ι : Sort*} (g : ι → PSL(2, ℝ)) :
    Convex ℝ (parabolaMap '' ⋂ i, closure (leftHalfPlane (g i))) := by
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ a b ha hb hab
  obtain ⟨u, hu⟩ := convex_range_parabolaMap ⟨z, rfl⟩ ⟨w, rfl⟩ ha hb hab
  refine ⟨u, mem_iInter.2 (fun i ↦ ?_), hu⟩
  rw [mem_closure_leftHalfPlane_iff_sideForm_nonpos]
  have hz' := (mem_closure_leftHalfPlane_iff_sideForm_nonpos (g i) z).1 (mem_iInter.1 hz i)
  have hw' := (mem_closure_leftHalfPlane_iff_sideForm_nonpos (g i) w).1 (mem_iInter.1 hw i)
  rw [sideForm_eq_of_parabolaMap_eq (g i) hab hu]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hz') (mul_nonpos_of_nonneg_of_nonpos hb hw')

end UpperHalfPlane
