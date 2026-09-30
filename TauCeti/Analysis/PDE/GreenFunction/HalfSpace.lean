/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The Green kernel of a Euclidean half-space

The method of images gives a Dirichlet Green kernel for the half-space on the positive side
of a hyperplane. Reflect the pole through the hyperplane and subtract its Newtonian kernel.
The reflected pole lies outside the half-space, so the correction is harmonic inside, while
the two kernels agree on the boundary. The construction works for any unit normal vector.
In dimension `n = 2`, the underlying `newtonianKernel` is degenerate; the Green-kernel
interpretation here is for `n = 1` or `n ≥ 3`.

The normalization follows Evans, *Partial Differential Equations*, Section 2.2.4.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Reflection through the hyperplane perpendicular to a unit normal `v` has this explicit
formula. -/
theorem reflection_orthogonal_singleton_apply {v : F} (hv : ‖v‖ = 1) (x : F) :
    (ℝ ∙ v)ᗮ.reflection x = x - (2 * ⟪v, x⟫_ℝ) • v := by
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub,
    hv, one_pow, div_one, two_smul, two_mul, add_smul]

/-- Reflection negates the component in the normal direction. -/
@[simp] theorem inner_reflection_orthogonal_singleton {v : F} (x : F) :
    ⟪v, (ℝ ∙ v)ᗮ.reflection x⟫_ℝ = -⟪v, x⟫_ℝ := by
  rw [← LinearIsometryEquiv.inner_map_map (ℝ ∙ v)ᗮ.reflection,
    Submodule.reflection_reflection,
    Submodule.reflection_orthogonalComplement_singleton_eq_neg, inner_neg_left]

/-- A point on the bounding hyperplane is fixed by reflection. -/
theorem reflection_orthogonal_singleton_eq_self_of_inner_eq_zero {v x : F}
    (hx : ⟪v, x⟫_ℝ = 0) : (ℝ ∙ v)ᗮ.reflection x = x := by
  exact Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hx)

/-- Reflection moves across a distance to the image point. -/
theorem norm_sub_reflection_orthogonal_singleton (v x y : F) :
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ = ‖(ℝ ∙ v)ᗮ.reflection y - x‖ := by
  calc
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ =
        ‖(ℝ ∙ v)ᗮ.reflection (y - (ℝ ∙ v)ᗮ.reflection x)‖ :=
      (((ℝ ∙ v)ᗮ.reflection).norm_map _).symm
    _ = ‖(ℝ ∙ v)ᗮ.reflection y - x‖ := by simp [map_sub]

/-- At the boundary, the pole and its image are equidistant from the variable point. -/
theorem norm_sub_reflection_orthogonal_singleton_eq_of_inner_eq_zero {v : F}
    (x : F) {y : F} (hy : ⟪v, y⟫_ℝ = 0) :
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ = ‖y - x‖ := by
  rw [norm_sub_reflection_orthogonal_singleton,
    reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hy]

end

/-- The method-of-images Dirichlet Green kernel for the half-space with unit inward normal
`v`, evaluated at the pole `x` and variable `y`. The Newtonian normalization gives a genuine
Green kernel for `n = 1` or `n ≥ 3`; at `n = 2` the Newtonian kernel is degenerate. -/
def halfSpaceGreenKernel (n : ℕ) (v x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  newtonianKernel n (y - x) - newtonianKernel n (y - (ℝ ∙ v)ᗮ.reflection x)

/-- The method-of-images formula for the half-space Green kernel. -/
theorem halfSpaceGreenKernel_def (v x y : E) :
    halfSpaceGreenKernel n v x y =
      newtonianKernel n (y - x) - newtonianKernel n (y - (ℝ ∙ v)ᗮ.reflection x) := by
  rw [halfSpaceGreenKernel]

/-- The image Green kernel is symmetric in its pole and variable. -/
theorem halfSpaceGreenKernel_comm (v x y : E) :
    halfSpaceGreenKernel n v x y = halfSpaceGreenKernel n v y x := by
  rw [halfSpaceGreenKernel_def, halfSpaceGreenKernel_def,
    newtonianKernel_sub_comm n y x]
  have hnorm : ‖y - (ℝ ∙ v)ᗮ.reflection x‖ = ‖x - (ℝ ∙ v)ᗮ.reflection y‖ := by
    rw [norm_sub_reflection_orthogonal_singleton, norm_sub_rev]
  simp only [newtonianKernel_def, hnorm]

/-- The Green kernel vanishes when its variable is on the bounding hyperplane. -/
@[simp] theorem halfSpaceGreenKernel_eq_zero_of_inner_eq_zero_right {v : E}
    (x : E) {y : E} (hy : ⟪v, y⟫_ℝ = 0) :
    halfSpaceGreenKernel n v x y = 0 := by
  rw [halfSpaceGreenKernel_def]
  have hnorm := norm_sub_reflection_orthogonal_singleton_eq_of_inner_eq_zero x hy
  rw [newtonianKernel_def, newtonianKernel_def, hnorm, sub_self]

/-- The Green kernel also vanishes when its pole lies on the bounding hyperplane. -/
@[simp] theorem halfSpaceGreenKernel_eq_zero_of_inner_eq_zero_left {v : E}
    {x : E} (hx : ⟪v, x⟫_ℝ = 0) (y : E) :
    halfSpaceGreenKernel n v x y = 0 := by
  rw [halfSpaceGreenKernel_def,
    reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hx, sub_self]

section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A point whose normal component differs from the negated component of `x` is not its
reflection. -/
theorem ne_reflection_orthogonal_singleton_of_inner_ne_neg {v x y : F}
    (hinner : ⟪v, y⟫_ℝ ≠ -⟪v, x⟫_ℝ) :
    y ≠ (ℝ ∙ v)ᗮ.reflection x := by
  intro h
  rw [h, inner_reflection_orthogonal_singleton] at hinner
  exact hinner rfl

/-- The squared distance to the image pole exceeds the squared distance to the pole by
four times the product of the two signed distances to the boundary. -/
theorem norm_sub_reflection_orthogonal_singleton_sq {v : F} (hv : ‖v‖ = 1) (x y : F) :
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ ^ 2 =
      ‖y - x‖ ^ 2 + 4 * ⟪v, x⟫_ℝ * ⟪v, y⟫_ℝ := by
  have heq : y - (ℝ ∙ v)ᗮ.reflection x =
      (y - x) + (2 * ⟪v, x⟫_ℝ) • v := by
    rw [reflection_orthogonal_singleton_apply hv]
    abel
  rw [heq, norm_add_sq_real, inner_smul_right, inner_sub_left, norm_smul, hv]
  simp only [mul_one, Real.norm_eq_abs, sq_abs]
  rw [real_inner_comm y v, real_inner_comm x v]
  ring

/-- Both points in the positive half-space are closer to each other than to the image pole. -/
theorem norm_sub_lt_norm_sub_reflection_orthogonal_singleton {v x y : F} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) :
    ‖y - x‖ < ‖y - (ℝ ∙ v)ᗮ.reflection x‖ := by
  have hsq := norm_sub_reflection_orthogonal_singleton_sq hv x y
  nlinarith [norm_nonneg (y - x), norm_nonneg (y - (ℝ ∙ v)ᗮ.reflection x),
    mul_pos hx hy]

end

/-- Outside dimension two, the half-space Green kernel is positive at distinct
interior points. -/
theorem halfSpaceGreenKernel_pos (hn : n ≠ 2) {v x y : E} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) (hxy : y ≠ x) :
    0 < halfSpaceGreenKernel n v x y := by
  have hlt := norm_sub_lt_norm_sub_reflection_orthogonal_singleton hv hx hy
  rw [halfSpaceGreenKernel_def]
  exact sub_pos.mpr (newtonianKernel_lt_newtonianKernel_of_norm_lt n hn
    (sub_ne_zero.mpr hxy) hlt)

/-- The Green kernel is harmonic away from its pole and the reflected pole. -/
theorem harmonicAt_halfSpaceGreenKernel {v x y : E} (hxy : y ≠ x)
    (hxy' : y ≠ (ℝ ∙ v)ᗮ.reflection x) :
    HarmonicAt (halfSpaceGreenKernel n v x) y := by
  exact (harmonicAt_newtonianKernel_sub n hxy).sub
    (harmonicAt_newtonianKernel_sub n hxy')

/-- The Green kernel is harmonic throughout the punctured positive half-space. -/
theorem harmonicOnNhd_halfSpaceGreenKernel {v x : E}
    (hx : 0 < ⟪v, x⟫_ℝ) :
    HarmonicOnNhd (halfSpaceGreenKernel n v x)
      ({y : E | 0 < ⟪v, y⟫_ℝ} \ {x}) := by
  intro y hy
  exact harmonicAt_halfSpaceGreenKernel (Set.mem_compl_singleton_iff.mp hy.2)
    (ne_reflection_orthogonal_singleton_of_inner_ne_neg (by
      intro h
      have hypos : 0 < ⟪v, y⟫_ℝ := hy.1
      linarith))

/-- The Green kernel is harmonic in its pole away from the variable point and its reflection. -/
theorem harmonicAt_halfSpaceGreenKernel_left {v x y : E}
    (hxy : x ≠ y) (hxy' : x ≠ (ℝ ∙ v)ᗮ.reflection y) :
    HarmonicAt (fun z => halfSpaceGreenKernel n v z y) x := by
  have hfun : (fun z => halfSpaceGreenKernel n v z y) = halfSpaceGreenKernel n v y := by
    funext z
    exact halfSpaceGreenKernel_comm v z y
  rw [hfun]
  exact harmonicAt_halfSpaceGreenKernel hxy hxy'

/-- The Poisson kernel for the half-space with unit inward normal `v`. Its boundary
normalization is `2 ⟪v,x⟫ / (n ωₙ ‖y-x‖ⁿ)`, where `ωₙ` is the volume of the unit ball. -/
def halfSpacePoissonKernel (n : ℕ) (v x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  2 * ⟪v, x⟫_ℝ *
    (((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
      ‖y - x‖ ^ (-(n : ℝ)))

/-- The defining formula for the half-space Poisson kernel. -/
theorem halfSpacePoissonKernel_def (v x y : E) :
    halfSpacePoissonKernel n v x y =
      2 * ⟪v, x⟫_ℝ *
        (((n : ℝ) * volume.real (ball (0 : E) 1))⁻¹ * ‖y - x‖ ^ (-(n : ℝ))) := by
  rw [halfSpacePoissonKernel]

/-- The usual quotient form of the half-space Poisson kernel. -/
theorem halfSpacePoissonKernel_eq_div (v x y : E) :
    halfSpacePoissonKernel n v x y =
      (2 * ⟪v, x⟫_ℝ) /
        ((n : ℝ) * volume.real (ball (0 : E) 1) * ‖y - x‖ ^ n) := by
  rw [halfSpacePoissonKernel_def, Real.rpow_neg (norm_nonneg _) _,
    Real.rpow_natCast]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The half-space Poisson kernel is positive for an interior pole and a distinct point. -/
theorem halfSpacePoissonKernel_pos {v x y : E}
    (hx : 0 < ⟪v, x⟫_ℝ) (hxy : y ≠ x) :
    0 < halfSpacePoissonKernel n v x y := by
  rw [halfSpacePoissonKernel_def]
  have hn : 0 < n := pos_of_ne_zero_euclideanSpace (sub_ne_zero.mpr hxy)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (mul_pos (by norm_num) hx)
    (mul_pos (inv_pos.mpr (mul_pos hnreal (volume_real_unitBall_pos n)))
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _))

/-- The Fréchet derivative of the half-space Green kernel away from its two poles. -/
theorem hasFDerivAt_halfSpaceGreenKernel (hn : n ≠ 2) {v x y : E}
    (hxy : y ≠ x) (hyref : y ≠ (ℝ ∙ v)ᗮ.reflection x) :
    HasFDerivAt (halfSpaceGreenKernel n v x)
      ((-(((n : ℝ) * volume.real (ball (0 : E) 1))⁻¹) *
          ‖y - x‖ ^ (-(n : ℝ))) • innerSL ℝ (y - x) -
        (-(((n : ℝ) * volume.real (ball (0 : E) 1))⁻¹) *
          ‖y - (ℝ ∙ v)ᗮ.reflection x‖ ^ (-(n : ℝ))) •
          innerSL ℝ (y - (ℝ ∙ v)ᗮ.reflection x)) y := by
  have hfun : halfSpaceGreenKernel n v x =
      (fun z => newtonianKernel n (z - x)) -
        (fun z => newtonianKernel n (z - (ℝ ∙ v)ᗮ.reflection x)) := by
    funext z
    exact halfSpaceGreenKernel_def v x z
  rw [hfun]
  exact (hasFDerivAt_newtonianKernel_sub n hn hxy).sub
    (hasFDerivAt_newtonianKernel_sub n hn hyref)

/-- On the boundary, the derivative in the negative normal direction of the Green kernel is
the negative Poisson kernel. -/
theorem fderiv_halfSpaceGreenKernel_normal (hn : n ≠ 2) {v x y : E}
    (hxy : y ≠ x) (hy : ⟪v, y⟫_ℝ = 0) :
    fderiv ℝ (halfSpaceGreenKernel n v x) y (-v) =
      -halfSpacePoissonKernel n v x y := by
  have hyref : y ≠ (ℝ ∙ v)ᗮ.reflection x := by
    by_cases hx : ⟪v, x⟫_ℝ = 0
    · rw [reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hx]
      exact hxy
    · exact ne_reflection_orthogonal_singleton_of_inner_ne_neg (by
        rw [hy]
        exact Ne.symm (neg_ne_zero.mpr hx))
  have hnorm := norm_sub_reflection_orthogonal_singleton_eq_of_inner_eq_zero x hy
  rw [(hasFDerivAt_halfSpaceGreenKernel hn hxy hyref).fderiv, sub_apply]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  rw [hnorm, halfSpacePoissonKernel_def]
  have hinner₁ : ⟪y - x, -v⟫_ℝ = ⟪v, x⟫_ℝ := by
    rw [inner_sub_left, inner_neg_right, inner_neg_right]
    linarith [real_inner_comm y v, real_inner_comm x v, hy]
  have hinner₂ : ⟪y - (ℝ ∙ v)ᗮ.reflection x, -v⟫_ℝ =
      -⟪v, x⟫_ℝ := by
    rw [inner_sub_left, inner_neg_right, inner_neg_right]
    linarith [real_inner_comm y v,
      real_inner_comm ((ℝ ∙ v)ᗮ.reflection x) v, hy,
      inner_reflection_orthogonal_singleton (v := v) x]
  rw [hinner₁, hinner₂]
  ring

end TauCeti

end
