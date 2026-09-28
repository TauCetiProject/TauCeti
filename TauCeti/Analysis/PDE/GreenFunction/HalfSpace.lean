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

/-- Reflection through the hyperplane perpendicular to a unit normal `v` has this explicit
formula. -/
theorem halfSpaceReflection_apply {v : E} (hv : ‖v‖ = 1) (x : E) :
    (ℝ ∙ v)ᗮ.reflection x = x - (2 * ⟪v, x⟫_ℝ) • v := by
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub, sub_right_inj,
    hv, one_pow, div_one]
  rw [two_smul, two_mul, add_smul]

/-- Reflection negates the component in the normal direction. -/
@[simp] theorem inner_halfSpaceReflection {v : E} (hv : ‖v‖ = 1) (x : E) :
    ⟪v, (ℝ ∙ v)ᗮ.reflection x⟫_ℝ = -⟪v, x⟫_ℝ := by
  rw [halfSpaceReflection_apply hv, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hv]
  simp
  ring

/-- A point on the bounding hyperplane is fixed by reflection. -/
theorem halfSpaceReflection_eq_self_of_inner_eq_zero {v x : E}
    (hx : ⟪v, x⟫_ℝ = 0) : (ℝ ∙ v)ᗮ.reflection x = x := by
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simpa only [real_inner_comm] using hx

/-- At the boundary, the pole and its image are equidistant from the variable point. -/
theorem norm_sub_halfSpaceReflection_eq_of_inner_eq_zero {v : E}
    (x : E) {y : E} (hy : ⟪v, y⟫_ℝ = 0) :
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ = ‖y - x‖ := by
  calc
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ =
        ‖(ℝ ∙ v)ᗮ.reflection (y - (ℝ ∙ v)ᗮ.reflection x)‖ :=
      (((ℝ ∙ v)ᗮ.reflection).norm_map _).symm
    _ = ‖y - x‖ := by
      simp [map_sub, halfSpaceReflection_eq_self_of_inner_eq_zero hy]

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
    calc
      ‖y - (ℝ ∙ v)ᗮ.reflection x‖ =
          ‖(ℝ ∙ v)ᗮ.reflection (y - (ℝ ∙ v)ᗮ.reflection x)‖ :=
        (((ℝ ∙ v)ᗮ.reflection).norm_map _).symm
      _ = ‖(ℝ ∙ v)ᗮ.reflection y - x‖ := by simp [map_sub]
      _ = ‖x - (ℝ ∙ v)ᗮ.reflection y‖ := norm_sub_rev _ _
  simp only [newtonianKernel_def, hnorm]

/-- The Green kernel vanishes when its variable is on the bounding hyperplane. -/
theorem halfSpaceGreenKernel_eq_zero_of_inner_eq_zero {v : E}
    (x : E) {y : E} (hy : ⟪v, y⟫_ℝ = 0) :
    halfSpaceGreenKernel n v x y = 0 := by
  rw [halfSpaceGreenKernel_def]
  have hnorm := norm_sub_halfSpaceReflection_eq_of_inner_eq_zero x hy
  rw [newtonianKernel_def, newtonianKernel_def, hnorm, sub_self]

/-- The Green kernel also vanishes when its pole lies on the bounding hyperplane. -/
theorem halfSpaceGreenKernel_eq_zero_of_inner_eq_zero_left {v : E}
    {x : E} (hx : ⟪v, x⟫_ℝ = 0) (y : E) :
    halfSpaceGreenKernel n v x y = 0 := by
  rw [halfSpaceGreenKernel_def, halfSpaceReflection_eq_self_of_inner_eq_zero hx, sub_self]

/-- The image pole of a point in the positive half-space lies outside that half-space. -/
theorem halfSpaceReflection_ne_of_inner_pos {v x y : E} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) :
    y ≠ (ℝ ∙ v)ᗮ.reflection x := by
  intro h
  rw [h, inner_halfSpaceReflection hv] at hy
  linarith

/-- The squared distance to the image pole exceeds the squared distance to the pole by
four times the product of the two signed distances to the boundary. -/
theorem norm_sub_halfSpaceReflection_sq {v : E} (hv : ‖v‖ = 1) (x y : E) :
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ ^ 2 =
      ‖y - x‖ ^ 2 + 4 * ⟪v, x⟫_ℝ * ⟪v, y⟫_ℝ := by
  have heq : y - (ℝ ∙ v)ᗮ.reflection x =
      (y - x) + (2 * ⟪v, x⟫_ℝ) • v := by
    rw [halfSpaceReflection_apply hv]
    abel
  rw [heq, norm_add_sq_real, inner_smul_right, inner_sub_left, norm_smul, hv]
  simp only [mul_one, Real.norm_eq_abs, sq_abs]
  rw [real_inner_comm y v, real_inner_comm x v]
  ring

/-- Both points in the positive half-space are closer to each other than to the image pole. -/
theorem norm_sub_lt_norm_sub_halfSpaceReflection {v x y : E} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) :
    ‖y - x‖ < ‖y - (ℝ ∙ v)ᗮ.reflection x‖ := by
  have hsq := norm_sub_halfSpaceReflection_sq hv x y
  nlinarith [norm_nonneg (y - x), norm_nonneg (y - (ℝ ∙ v)ᗮ.reflection x),
    mul_pos hx hy]

/-- For dimension at least three, the half-space Green kernel is positive at distinct
interior points. -/
theorem halfSpaceGreenKernel_pos (hn : 3 ≤ n) {v x y : E} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) (hxy : y ≠ x) :
    0 < halfSpaceGreenKernel n v x y := by
  have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hlt := norm_sub_lt_norm_sub_halfSpaceReflection hv hx hy
  have hexp : (2 : ℝ) - n < 0 := by
    have hnreal : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
    linarith
  have hrpow := Real.rpow_lt_rpow_of_neg hnorm hlt hexp
  have hcoef : 0 < ((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : E) 1))⁻¹ := by
    have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_pos.mpr (mul_pos (mul_pos (by linarith) (by linarith))
      (volume_real_unitBall_pos n))
  rw [halfSpaceGreenKernel_def, newtonianKernel_def, newtonianKernel_def]
  exact sub_pos.mpr (mul_lt_mul_of_pos_left hrpow hcoef)

/-- The Green kernel is harmonic in the half-space away from its pole. -/
theorem harmonicAt_halfSpaceGreenKernel {v x y : E} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) (hxy : y ≠ x) :
    HarmonicAt (halfSpaceGreenKernel n v x) y := by
  exact (harmonicAt_newtonianKernel_sub n hxy).sub
    (harmonicAt_newtonianKernel_sub n (halfSpaceReflection_ne_of_inner_pos hv hx hy))

/-- The Green kernel is harmonic throughout the punctured positive half-space. -/
theorem harmonicOnNhd_halfSpaceGreenKernel {v x : E} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) :
    HarmonicOnNhd (halfSpaceGreenKernel n v x)
      ({y : E | 0 < ⟪v, y⟫_ℝ} \ {x}) := by
  intro y hy
  exact harmonicAt_halfSpaceGreenKernel hv hx hy.1 (Set.mem_compl_singleton_iff.mp hy.2)

/-- The Green kernel is harmonic in its pole throughout the punctured half-space. -/
theorem harmonicAt_halfSpaceGreenKernel_left {v x y : E} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) (hxy : x ≠ y) :
    HarmonicAt (fun z => halfSpaceGreenKernel n v z y) x := by
  have hfun : (fun z => halfSpaceGreenKernel n v z y) = halfSpaceGreenKernel n v y := by
    funext z
    exact halfSpaceGreenKernel_comm v z y
  rw [hfun]
  exact harmonicAt_halfSpaceGreenKernel hv hy hx hxy

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
theorem halfSpacePoissonKernel_pos (hn : 0 < n) {v x y : E}
    (hx : 0 < ⟪v, x⟫_ℝ) (hxy : y ≠ x) :
    0 < halfSpacePoissonKernel n v x y := by
  rw [halfSpacePoissonKernel_def]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (mul_pos (by norm_num) hx)
    (mul_pos (inv_pos.mpr (mul_pos hnreal (volume_real_unitBall_pos n)))
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _))

/-- On the boundary, the outward unit normal derivative of the Green kernel is the
negative Poisson kernel. -/
theorem fderiv_halfSpaceGreenKernel_normal (hn : n ≠ 2) {v x y : E}
    (hv : ‖v‖ = 1) (hx : 0 < ⟪v, x⟫_ℝ) (hy : ⟪v, y⟫_ℝ = 0) :
    fderiv ℝ (halfSpaceGreenKernel n v x) y (-v) =
      -halfSpacePoissonKernel n v x y := by
  have hxy : y ≠ x := by
    intro h
    rw [h] at hy
    linarith
  have hyref : y ≠ (ℝ ∙ v)ᗮ.reflection x := by
    intro h
    rw [h, inner_halfSpaceReflection hv] at hy
    linarith
  have hnorm := norm_sub_halfSpaceReflection_eq_of_inner_eq_zero x hy
  have hderiv := ((hasFDerivAt_newtonianKernel_sub n hn hxy).sub
    (hasFDerivAt_newtonianKernel_sub n hn hyref)).fderiv
  have hfun : halfSpaceGreenKernel n v x =
      (fun z => newtonianKernel n (z - x)) -
        (fun z => newtonianKernel n (z - (ℝ ∙ v)ᗮ.reflection x)) := by
    funext z
    exact halfSpaceGreenKernel_def v x z
  rw [hfun, hderiv, sub_apply]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  rw [hnorm, halfSpacePoissonKernel_def]
  have hinner₁ : ⟪y - x, -v⟫_ℝ = ⟪v, x⟫_ℝ := by
    rw [inner_sub_left, inner_neg_right, inner_neg_right]
    nlinarith [real_inner_comm y v, real_inner_comm x v, hy]
  have hinner₂ : ⟪y - (ℝ ∙ v)ᗮ.reflection x, -v⟫_ℝ =
      -⟪v, x⟫_ℝ := by
    rw [inner_sub_left, inner_neg_right, inner_neg_right]
    nlinarith [real_inner_comm y v,
      real_inner_comm ((ℝ ∙ v)ᗮ.reflection x) v, hy,
      inner_halfSpaceReflection hv x]
  rw [hinner₁, hinner₂]
  ring

end TauCeti

end
