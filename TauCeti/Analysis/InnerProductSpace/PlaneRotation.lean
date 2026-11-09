/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Rotations of an isometrically embedded complex plane

A linear isometry `ι : ℂ →ₗᵢ[ℝ] E` into a real inner product space distinguishes the plane `ι ℂ`
of `E`. Every point `c` of the unit circle rotates that plane by multiplication, `ι w ↦ ι (c w)`,
and this rotation extends to a linear isometry of `E` fixing the orthogonal complement of the
plane pointwise. These extensions form a homomorphism
`LinearIsometry.planeRotation ι : Circle →* E ≃ₗᵢ[ℝ] E`, the extension of Mathlib's `rotation` of
`ℂ` to `E`.

Explicitly, `planeRotation ι c x = x + ι ((c - 1) w)`, where `w = ⟪ι 1, x⟫ + ⟪ι i, x⟫ i` is the
complex coordinate of the orthogonal projection of `x` onto the plane. The rotation by `-1` is the
half-turn of the plane, the reflection across its orthogonal complement
(`LinearIsometry.planeRotation_neg_one`), and the rotation depends smoothly on the angle and the
point (`LinearIsometry.contMDiff_planeRotation`). Rotating the plane moves a great circle of the
unit sphere of `E` along itself; this is how knotted arcs are slid along a great circle.

## Main definitions

* `LinearIsometry.planeRotation ι`: the rotations of `E` in the plane `ι ℂ`.

## Main results

* `LinearIsometry.planeRotation_apply_map`: the rotation by `c` multiplies the plane by `c`.
* `LinearIsometry.planeRotation_apply_of_mem_orthogonal`: it fixes the orthogonal complement of
  the plane.
* `LinearIsometry.planeRotation_neg_one`: the rotation by `-1` is the reflection across that
  complement.
* `LinearIsometry.contMDiff_planeRotation`: the rotation is smooth in the angle and the point.
-/

public section

noncomputable section

namespace LinearIsometry

open Complex
open scoped RealInnerProductSpace Manifold ContDiff

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ι : ℂ →ₗᵢ[ℝ] E)

/-- The complex coordinate of the orthogonal projection onto the plane `ι ℂ`: the adjoint of `ι`,
written through the orthonormal pair `ι 1`, `ι i`. -/
private def planeCoord : E →L[ℝ] ℂ :=
  (innerSL ℝ (ι 1)).smulRight (1 : ℂ) + (innerSL ℝ (ι I)).smulRight I

private theorem planeCoord_apply (x : E) :
    planeCoord ι x = (⟪ι 1, x⟫ : ℂ) + (⟪ι I, x⟫ : ℂ) * I := by
  simp [planeCoord, Complex.real_smul]

private theorem planeCoord_map (w : ℂ) : planeCoord ι (ι w) = w := by
  rw [planeCoord_apply, ι.inner_map_map, ι.inner_map_map]
  apply Complex.ext <;> simp [Complex.inner]

/-- `planeCoord ι` is the adjoint of `ι`. -/
private theorem inner_map_left_eq (v : ℂ) (x : E) : ⟪ι v, x⟫ = ⟪v, planeCoord ι x⟫ := by
  have hv : v = v.re • (1 : ℂ) + v.im • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    planeCoord_apply, Complex.inner]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp
  ring

private theorem planeCoord_add_map (x : E) (d : ℂ) :
    planeCoord ι (x + ι d) = planeCoord ι x + d := by
  rw [map_add, planeCoord_map]

/-- The underlying map of the rotation by `c`. -/
private def rotFun (c : ℂ) (x : E) : E := x + ι ((c - 1) * planeCoord ι x)

private theorem planeCoord_rotFun (c : ℂ) (x : E) :
    planeCoord ι (rotFun ι c x) = c * planeCoord ι x := by
  rw [rotFun, planeCoord_add_map]
  ring

private theorem rotFun_rotFun (a b : ℂ) (x : E) :
    rotFun ι a (rotFun ι b x) = rotFun ι (a * b) x := by
  rw [rotFun, planeCoord_rotFun, rotFun, rotFun, add_assoc, ← map_add]
  congr 2
  ring

private theorem rotFun_one (x : E) : rotFun ι 1 x = x := by
  simp [rotFun]

private theorem norm_rotFun (c : Circle) (x : E) : ‖rotFun ι c x‖ = ‖x‖ := by
  set w := planeCoord ι x
  have hc : (c : ℂ).re ^ 2 + (c : ℂ).im ^ 2 = 1 := by
    have := Circle.normSq_coe c
    rw [Complex.normSq_apply] at this
    nlinarith [this]
  have hsq : ‖rotFun ι c x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [rotFun, norm_add_sq_real, real_inner_comm, inner_map_left_eq, ι.norm_map,
      Complex.inner, norm_mul, mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [map_mul, map_sub, map_one, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.conj_re,
      Complex.conj_im]
    linear_combination (w.re * w.re + w.im * w.im) * hc
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- The **rotations of `E` in the plane `ι ℂ`**: `planeRotation ι c` multiplies the plane `ι ℂ` by
the point `c` of the unit circle (`LinearIsometry.planeRotation_apply_map`) and fixes its
orthogonal complement pointwise (`LinearIsometry.planeRotation_apply_of_mem_orthogonal`). -/
def planeRotation : Circle →* E ≃ₗᵢ[ℝ] E where
  toFun c :=
    { toFun := rotFun ι c
      invFun := rotFun ι (c⁻¹ : Circle)
      map_add' x y := by
        simp only [rotFun, map_add, mul_add]
        abel
      map_smul' r x := by
        simp only [rotFun, map_smul, mul_smul_comm, smul_add, RingHom.id_apply]
      left_inv x := by
        rw [rotFun_rotFun, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, rotFun_one]
      right_inv x := by
        rw [rotFun_rotFun, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, rotFun_one]
      norm_map' := norm_rotFun ι c }
  map_one' := LinearIsometryEquiv.ext fun x => by
    simp [rotFun]
  map_mul' a b := LinearIsometryEquiv.ext fun x => by
    rw [LinearIsometryEquiv.coe_mul]
    exact (rotFun_rotFun ι a b x).symm

private theorem planeRotation_apply_eq (c : Circle) (x : E) :
    ι.planeRotation c x = x + ι ((c - 1) * planeCoord ι x) :=
  (rfl)

/-- **The rotation by `c` multiplies the plane `ι ℂ` by `c`.** -/
@[simp]
theorem planeRotation_apply_map (c : Circle) (w : ℂ) :
    ι.planeRotation c (ι w) = ι (c * w) := by
  rw [planeRotation_apply_eq, planeCoord_map, ← map_add]
  congr 1
  ring

/-- **The rotation fixes the orthogonal complement of the plane `ι ℂ`.** -/
@[simp]
theorem planeRotation_apply_of_mem_orthogonal (c : Circle) {x : E} (hx : x ∈ ι.rangeᗮ) :
    ι.planeRotation c x = x := by
  have h0 : planeCoord ι x = 0 := by
    rw [planeCoord_apply,
      Submodule.inner_right_of_mem_orthogonal (u := ι 1) (LinearMap.mem_range_self _ 1) hx,
      Submodule.inner_right_of_mem_orthogonal (u := ι I) (LinearMap.mem_range_self _ I) hx]
    simp
  rw [planeRotation_apply_eq, h0, mul_zero, map_zero, add_zero]

/-- **The rotation by `-1` is the half-turn of the plane `ι ℂ`**, the reflection across its
orthogonal complement. -/
theorem planeRotation_neg_one : ι.planeRotation (-1) = ι.rangeᗮ.reflection := by
  ext x
  -- Split `x` into its part `ι w` in the plane and a part `q` orthogonal to the plane.
  set w := planeCoord ι x
  have hq : x - ι w ∈ ι.rangeᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨v, rfl⟩
    rw [LinearIsometry.coe_toLinearMap, inner_sub_right, inner_map_left_eq, ι.inner_map_map,
      sub_self]
  have hx : x = ι w + (x - ι w) := by abel
  rw [hx, map_add, map_add, planeRotation_apply_map, planeRotation_apply_of_mem_orthogonal _ _ hq,
    reflection_orthogonal_range_apply, Submodule.reflection_mem_subspace_eq_self hq,
    Circle.coe_neg, Circle.coe_one, neg_one_mul, map_neg]

/-- **The rotation is smooth in the angle and the point**: the map `(c, x) ↦ planeRotation ι c x`
from `Circle × E` to `E` is analytic. -/
theorem contMDiff_planeRotation {m : ℕ∞ω} :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) m fun p : Circle × E => ι.planeRotation p.1 p.2 := by
  simp_rw [planeRotation_apply_eq]
  have hc : ContMDiff ((𝓡 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℂ) m fun p : Circle × E => (p.1 : ℂ) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  have hx : ContMDiff ((𝓡 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) m fun p : Circle × E => p.2 :=
    contMDiff_snd
  have hw : ContMDiff ((𝓡 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℂ) m fun p : Circle × E => planeCoord ι p.2 :=
    (planeCoord ι).contDiff.contMDiff.comp hx
  have hmul : ContMDiff ((𝓡 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℂ) m
      fun p : Circle × E => ((p.1 : ℂ) - 1) * planeCoord ι p.2 :=
    contDiff_mul.contMDiff.comp ((hc.sub contMDiff_const).prodMk_space hw)
  exact hx.add (ι.toContinuousLinearMap.contDiff.contMDiff.comp hmul)

end LinearIsometry
