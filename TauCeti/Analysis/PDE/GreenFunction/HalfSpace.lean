/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import TauCeti.Analysis.InnerProductSpace.Reflection

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
local notation "U" => {w : EuclideanSpace ℝ (Fin n) // ‖w‖ = 1}

/-- The method-of-images Dirichlet Green kernel for the half-space with unit inward normal
`v`, evaluated at the pole `x` and variable `y`. The Newtonian normalization gives a genuine
Green kernel for `n = 1` or `n ≥ 3`; at `n = 2` the Newtonian kernel is degenerate. -/
def halfSpaceGreenKernel (n : ℕ) (v : {w : EuclideanSpace ℝ (Fin n) // ‖w‖ = 1})
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  newtonianKernel n (y - x) -
    newtonianKernel n (y - (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ.reflection x)

/-- The method-of-images formula for the half-space Green kernel. -/
theorem halfSpaceGreenKernel_def (v : U) (x y : E) :
    halfSpaceGreenKernel n v x y =
      newtonianKernel n (y - x) - newtonianKernel n (y - (ℝ ∙ (v : E))ᗮ.reflection x) := by
  rw [halfSpaceGreenKernel]

/-- The image Green kernel is symmetric in its pole and variable. -/
theorem halfSpaceGreenKernel_comm (v : U) (x y : E) :
    halfSpaceGreenKernel n v x y = halfSpaceGreenKernel n v y x := by
  rw [halfSpaceGreenKernel_def, halfSpaceGreenKernel_def,
    newtonianKernel_sub_comm n y x]
  have hnorm : ‖y - (ℝ ∙ (v : E))ᗮ.reflection x‖ = ‖x - (ℝ ∙ (v : E))ᗮ.reflection y‖ := by
    rw [norm_sub_reflection_orthogonal_singleton, norm_sub_rev]
  simp only [newtonianKernel_def, hnorm]

/-- The Green kernel vanishes when its variable is on the bounding hyperplane. -/
@[simp] theorem halfSpaceGreenKernel_eq_zero_of_inner_eq_zero_right {v : U}
    (x : E) {y : E} (hy : ⟪(v : E), y⟫_ℝ = 0) :
    halfSpaceGreenKernel n v x y = 0 := by
  rw [halfSpaceGreenKernel_def]
  have hnorm := norm_sub_reflection_orthogonal_singleton_eq_of_inner_eq_zero x hy
  rw [newtonianKernel_def, newtonianKernel_def, hnorm, sub_self]

/-- The Green kernel also vanishes when its pole lies on the bounding hyperplane. -/
@[simp] theorem halfSpaceGreenKernel_eq_zero_of_inner_eq_zero_left {v : U}
    {x : E} (hx : ⟪(v : E), x⟫_ℝ = 0) (y : E) :
    halfSpaceGreenKernel n v x y = 0 := by
  rw [halfSpaceGreenKernel_def,
    reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hx, sub_self]

/-- Outside dimension two, the half-space Green kernel is positive at distinct
interior points. -/
theorem halfSpaceGreenKernel_pos (hn : n ≠ 2) {v : U} {x y : E}
    (hx : 0 < ⟪(v : E), x⟫_ℝ) (hy : 0 < ⟪(v : E), y⟫_ℝ) (hxy : y ≠ x) :
    0 < halfSpaceGreenKernel n v x y := by
  have hlt := norm_sub_lt_norm_sub_reflection_orthogonal_singleton v.property hx hy
  rw [halfSpaceGreenKernel_def]
  exact sub_pos.mpr (newtonianKernel_lt_newtonianKernel_of_norm_lt n hn
    (sub_ne_zero.mpr hxy) hlt)

/-- The Green kernel is harmonic away from its pole and the reflected pole. -/
theorem harmonicAt_halfSpaceGreenKernel {v : U} {x y : E} (hxy : y ≠ x)
    (hxy' : y ≠ (ℝ ∙ (v : E))ᗮ.reflection x) :
    HarmonicAt (halfSpaceGreenKernel n v x) y := by
  exact (harmonicAt_newtonianKernel_sub n hxy).sub
    (harmonicAt_newtonianKernel_sub n hxy')

/-- The Green kernel is harmonic throughout the punctured positive half-space. -/
theorem harmonicOnNhd_halfSpaceGreenKernel {v : U} {x : E}
    (hx : 0 < ⟪(v : E), x⟫_ℝ) :
    HarmonicOnNhd (halfSpaceGreenKernel n v x)
      ({y : E | 0 < ⟪(v : E), y⟫_ℝ} \ {x}) := by
  intro y hy
  exact harmonicAt_halfSpaceGreenKernel (Set.mem_compl_singleton_iff.mp hy.2)
    (ne_reflection_orthogonal_singleton_of_inner_ne_neg (by
      intro h
      have hypos : 0 < ⟪(v : E), y⟫_ℝ := hy.1
      linarith))

/-- The Green kernel is harmonic in its pole away from the variable point and its reflection. -/
theorem harmonicAt_halfSpaceGreenKernel_left {v : U} {x y : E}
    (hxy : x ≠ y) (hxy' : x ≠ (ℝ ∙ (v : E))ᗮ.reflection y) :
    HarmonicAt (fun z => halfSpaceGreenKernel n v z y) x := by
  have hfun : (fun z => halfSpaceGreenKernel n v z y) = halfSpaceGreenKernel n v y := by
    funext z
    exact halfSpaceGreenKernel_comm v z y
  rw [hfun]
  exact harmonicAt_halfSpaceGreenKernel hxy hxy'

/-- The Poisson kernel for the half-space with unit inward normal `v`. Its boundary
normalization is `2 ⟪v,x⟫ / (n ωₙ ‖y-x‖ⁿ)`, where `ωₙ` is the volume of the unit ball. -/
def halfSpacePoissonKernel (n : ℕ)
    (v : {w : EuclideanSpace ℝ (Fin n) // ‖w‖ = 1})
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  2 * ⟪(v : EuclideanSpace ℝ (Fin n)), x⟫_ℝ *
    (((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
      ‖y - x‖ ^ (-(n : ℝ)))

/-- The defining formula for the half-space Poisson kernel. -/
theorem halfSpacePoissonKernel_def (v : {w : E // ‖w‖ = 1}) (x y : E) :
    halfSpacePoissonKernel n v x y =
      2 * ⟪(v : E), x⟫_ℝ *
        (((n : ℝ) * volume.real (ball (0 : E) 1))⁻¹ * ‖y - x‖ ^ (-(n : ℝ))) := by
  rw [halfSpacePoissonKernel]

/-- The usual quotient form of the half-space Poisson kernel. -/
theorem halfSpacePoissonKernel_eq_div (v : {w : E // ‖w‖ = 1}) (x y : E) :
    halfSpacePoissonKernel n v x y =
      (2 * ⟪(v : E), x⟫_ℝ) /
        ((n : ℝ) * volume.real (ball (0 : E) 1) * ‖y - x‖ ^ n) := by
  rw [halfSpacePoissonKernel_def, Real.rpow_neg (norm_nonneg _) _,
    Real.rpow_natCast]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The half-space Poisson kernel is positive for an interior pole and a distinct point. -/
theorem halfSpacePoissonKernel_pos {v : {w : E // ‖w‖ = 1}} {x y : E}
    (hx : 0 < ⟪(v : E), x⟫_ℝ) (hxy : y ≠ x) :
    0 < halfSpacePoissonKernel n v x y := by
  rw [halfSpacePoissonKernel_def]
  have hn : 0 < n := pos_of_ne_zero_euclideanSpace (sub_ne_zero.mpr hxy)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (mul_pos (by norm_num) hx)
    (mul_pos (inv_pos.mpr (mul_pos hnreal (volume_real_unitBall_pos n)))
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _))

/-- The Fréchet derivative of the half-space Green kernel away from its two poles. -/
theorem hasFDerivAt_halfSpaceGreenKernel (hn : n ≠ 2) {v : U} {x y : E}
    (hxy : y ≠ x) (hyref : y ≠ (ℝ ∙ (v : E))ᗮ.reflection x) :
    HasFDerivAt (halfSpaceGreenKernel n v x)
      ((-(((n : ℝ) * volume.real (ball (0 : E) 1))⁻¹) *
          ‖y - x‖ ^ (-(n : ℝ))) • innerSL ℝ (y - x) -
        (-(((n : ℝ) * volume.real (ball (0 : E) 1))⁻¹) *
          ‖y - (ℝ ∙ (v : E))ᗮ.reflection x‖ ^ (-(n : ℝ))) •
          innerSL ℝ (y - (ℝ ∙ (v : E))ᗮ.reflection x)) y := by
  have hfun : halfSpaceGreenKernel n v x =
      (fun z => newtonianKernel n (z - x)) -
        (fun z => newtonianKernel n (z - (ℝ ∙ (v : E))ᗮ.reflection x)) := by
    funext z
    exact halfSpaceGreenKernel_def v x z
  rw [hfun]
  exact (hasFDerivAt_newtonianKernel_sub n hn hxy).sub
    (hasFDerivAt_newtonianKernel_sub n hn hyref)

/-- On the boundary, the derivative in the negative normal direction of the Green kernel is
the negative Poisson kernel. -/
theorem fderiv_halfSpaceGreenKernel_normal (hn : n ≠ 2) {v : U} {x y : E}
    (hxy : y ≠ x) (hy : ⟪(v : E), y⟫_ℝ = 0) :
    fderiv ℝ (halfSpaceGreenKernel n v x) y (-(v : E)) =
      -halfSpacePoissonKernel n v x y := by
  have hyref : y ≠ (ℝ ∙ (v : E))ᗮ.reflection x := by
    by_cases hx : ⟪(v : E), x⟫_ℝ = 0
    · rw [reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hx]
      exact hxy
    · exact ne_reflection_orthogonal_singleton_of_inner_ne_neg (by
        rw [hy]
        exact Ne.symm (neg_ne_zero.mpr hx))
  have hnorm := norm_sub_reflection_orthogonal_singleton_eq_of_inner_eq_zero x hy
  rw [(hasFDerivAt_halfSpaceGreenKernel hn hxy hyref).fderiv, sub_apply]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  rw [hnorm, halfSpacePoissonKernel_def]
  have hinner₁ : ⟪y - x, -v⟫_ℝ = ⟪(v : E), x⟫_ℝ := by
    rw [inner_sub_left, inner_neg_right, inner_neg_right]
    linarith [real_inner_comm y v, real_inner_comm x v, hy]
  have hinner₂ : ⟪y - (ℝ ∙ (v : E))ᗮ.reflection x, -v⟫_ℝ =
      -⟪(v : E), x⟫_ℝ := by
    rw [inner_sub_left, inner_neg_right, inner_neg_right]
    linarith [real_inner_comm y v,
      real_inner_comm ((ℝ ∙ (v : E))ᗮ.reflection x) v, hy,
      inner_reflection_orthogonal_singleton (v := (v : E)) x]
  rw [hinner₁, hinner₂]
  ring

end TauCeti

end
