/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Mobius.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance

/-!
# The hyperbolic distance on `ℍ³` and the Möbius action

On hyperbolic three-space `UpperHalfSpace ℂ`, with the hyperbolic distance of
`TauCeti.UpperHalfSpace.instMetricSpace`, this file records that the Möbius action of
`SL(2, ℂ)` and `PSL(2, ℂ)` is isometric, and that the vertical half-plane over the real axis is a
copy of Mathlib's upper half-plane `ℍ`, with its distance and its action of `SL(2, ℝ)`. The
latter keeps the hyperbolic geometry of `ℍ³` compatible with the two-dimensional theory of
Fuchsian groups built on `UpperHalfPlane`.

## Main definitions

* `TauCeti.UpperHalfSpace.ofUpperHalfPlane`: the point `(x, y)` of `ℍ³` over the real axis
  corresponding to `x + i y ∈ ℍ`.

## Main results

* `IsIsometricSMul SL(2, ℂ) (UpperHalfSpace ℂ)` and `IsIsometricSMul PSL(2, ℂ) (UpperHalfSpace ℂ)`:
  the Möbius action is by isometries of the hyperbolic distance, so Mathlib's `isometry_smul` and
  `dist_smul` apply to it.
* `TauCeti.UpperHalfSpace.dist_ofUpperHalfPlane`: the slice `ofUpperHalfPlane` preserves
  distance, so it is an isometric embedding of `ℍ` into `ℍ³`.
* `TauCeti.UpperHalfSpace.ofUpperHalfPlane_smul`: the slice is equivariant for `SL(2, ℝ)`, acting
  on `ℍ³` through `SL(2, ℝ) → SL(2, ℂ)`.

## References

* A. F. Beardon, *The Geometry of Discrete Groups*, Springer GTM 91 (1983), Chapters 3 and 4
  (the Poincaré extension of a Möbius transformation is a hyperbolic isometry, and extends the
  action of `SL(2, ℝ)` on the upper half-plane).
* J. Elstrodt, F. Grunewald, J. Mennicke, *Groups Acting on Hyperbolic Space*, Springer (1998),
  Chapter 1.
-/

public section

open Matrix ComplexConjugate
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfSpace

/-- The Möbius action of `SL(2, ℂ)` on `ℍ³` is by isometries of the hyperbolic distance. -/
instance : IsIsometricSMul SL(2, ℂ) (UpperHalfSpace ℂ) where
  isometry_smul A := funext (slToIsom_apply A) ▸ IsometryClass.isometry (slToIsom A)

/-- The Möbius action of `PSL(2, ℂ)` on `ℍ³` is by isometries of the hyperbolic distance. -/
instance : IsIsometricSMul PSL(2, ℂ) (UpperHalfSpace ℂ) where
  isometry_smul g := funext (pslToIsom_apply g) ▸ IsometryClass.isometry (pslToIsom g)

/-- The point `(x, y)` of `ℍ³`, over the real axis, corresponding to `x + i y` in the upper
half-plane. -/
def ofUpperHalfPlane (z : ℍ) : UpperHalfSpace ℂ :=
  mk (WithLp.toLp 2 ((z.re : ℂ), z.im)) (by simpa using z.im_pos)

/-- The horizontal coordinate of `ofUpperHalfPlane z` is the real part of `z`. -/
@[simp]
theorem fst_ofUpperHalfPlane (z : ℍ) :
    (ofUpperHalfPlane z : WithLp 2 (ℂ × ℝ)).fst = z.re := by
  rw [ofUpperHalfPlane, coe_mk, WithLp.toLp_fst]

/-- The height of `ofUpperHalfPlane z` is the imaginary part of `z`. -/
@[simp]
theorem height_ofUpperHalfPlane (z : ℍ) : height (ofUpperHalfPlane z) = z.im := by
  rw [ofUpperHalfPlane, height_mk, WithLp.toLp_snd]

/-- The Euclidean distance of two points of the slice `ofUpperHalfPlane` is the distance of the
corresponding complex numbers. -/
theorem dist_coe_ofUpperHalfPlane (z w : ℍ) :
    dist (ofUpperHalfPlane z : WithLp 2 (ℂ × ℝ)) (ofUpperHalfPlane w) = dist (z : ℂ) w := by
  rw [WithLp.prod_dist_eq_of_L2, Complex.dist_eq_re_im (z : ℂ)]
  simp [Complex.dist_eq_re_im, Real.dist_eq, sq_abs, Real.sq_sqrt, sq_nonneg]

/-- On the slice over the real axis the hyperbolic distance of `ℍ³` is Mathlib's hyperbolic
distance on `ℍ`. -/
@[simp]
theorem dist_ofUpperHalfPlane (z w : ℍ) :
    dist (ofUpperHalfPlane z) (ofUpperHalfPlane w) = dist z w := by
  rw [dist_eq, UpperHalfPlane.dist_eq, dist_coe_ofUpperHalfPlane, height_ofUpperHalfPlane,
    height_ofUpperHalfPlane]

/-- The slice over the real axis is an isometric embedding of `ℍ` into `ℍ³`. -/
theorem isometry_ofUpperHalfPlane : Isometry ofUpperHalfPlane :=
  Isometry.of_dist_eq dist_ofUpperHalfPlane

/-- The slice over the real axis is equivariant for `SL(2, ℝ)`, which acts on `ℍ³` through
`SL(2, ℝ) → SL(2, ℂ)`. -/
theorem ofUpperHalfPlane_smul (g : SL(2, ℝ)) (z : ℍ) :
    ofUpperHalfPlane (g • z) = g.map Complex.ofRealHom • ofUpperHalfPlane z := by
  have hJ : denom (g.map Complex.ofRealHom) (ofUpperHalfPlane z) =
      Complex.normSq (g 1 0 * (z : ℂ) + g 1 1) := by
    simp only [denom_def, Fin.isValue, SpecialLinearGroup.map_apply_coe, map_apply,
      Complex.ofRealHom_eq_coe, fst_ofUpperHalfPlane, Complex.normSq_apply, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.add_im,
      Complex.mul_im, zero_mul, add_zero, height_ofUpperHalfPlane, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, add_right_inj]
    ring
  have hre : (g • z).re = ((g 0 0 * z.re + g 0 1) * (g 1 0 * z.re + g 1 1) +
      g 0 0 * g 1 0 * z.im ^ 2) / Complex.normSq (g 1 0 * (z : ℂ) + g 1 1) := by
    rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_specialLinearGroup_apply, Complex.div_re,
      ← add_div]
    simp only [Algebra.algebraMap_self, Fin.isValue, RingHom.id_apply, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, UpperHalfPlane.coe_re, Complex.ofReal_im,
      UpperHalfPlane.coe_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im, add_zero]
    ring
  refine ext_fst_height ?_ ?_
  · rw [fst_ofUpperHalfPlane, fst_smul, hJ, hre, height_ofUpperHalfPlane, fst_ofUpperHalfPlane]
    simp only [Fin.isValue, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_pow, SpecialLinearGroup.map_apply_coe, map_apply, Complex.ofRealHom_eq_coe,
      map_add, map_mul, Complex.conj_ofReal]
  · rw [height_ofUpperHalfPlane, height_smul, hJ, height_ofUpperHalfPlane,
      ← UpperHalfPlane.coe_im, UpperHalfPlane.coe_specialLinearGroup_apply, Complex.div_im,
      ← sub_div]
    congr 1
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact g.det_coe
    simp only [Algebra.algebraMap_self, Fin.isValue, RingHom.id_apply, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, UpperHalfPlane.coe_im, Complex.ofReal_im,
      UpperHalfPlane.coe_re, zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero]
    linear_combination z.im * hdet

end TauCeti.UpperHalfSpace
