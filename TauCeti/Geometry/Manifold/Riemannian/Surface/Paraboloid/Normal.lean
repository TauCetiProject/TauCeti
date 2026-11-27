/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Paraboloid.Basic
public import TauCeti.Analysis.InnerProductSpace.Normalize

/-!
# The upward normal fields of the paraboloid

The Cartesian graph normal `N=(-2x₀,-2x₁,1)` has squared length `1+4‖x‖²`
and spans the graph normal space. Normalize it to obtain a smooth unit normal
at every point, including the vertex.

Adapted from Yangyang Li's formalization in ColdingMinicozziTheory:
[Cartesian graph and tensor work](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/ab114a15)
and [curvature follow-up](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/234e55b3).
-/

public noncomputable section

open scoped ContDiff InnerProductSpace

namespace TauCeti.Manifold

local notation "V₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The upward, unnormalized normal to the Cartesian graph. -/
def paraboloidNormal (x : V₂) : E₃ :=
  (-2 * x 0) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
    (-2 * x 1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
    EuclideanSpace.basisFun (Fin 3) ℝ 2

/-- The first coordinate of the upward graph normal. -/
@[simp]
theorem paraboloidNormal_apply_zero (x : V₂) : paraboloidNormal x 0 = -2 * x 0 := by
  simp [paraboloidNormal, EuclideanSpace.basisFun_apply]

/-- The second coordinate of the upward graph normal. -/
@[simp]
theorem paraboloidNormal_apply_one (x : V₂) : paraboloidNormal x 1 = -2 * x 1 := by
  simp [paraboloidNormal, EuclideanSpace.basisFun_apply]

/-- The height coordinate of the upward graph normal. -/
@[simp]
theorem paraboloidNormal_apply_two (x : V₂) : paraboloidNormal x 2 = 1 := by
  simp [paraboloidNormal, EuclideanSpace.basisFun_apply]

/-- The normal has squared length `1+4‖x‖²`, and is therefore never zero. -/
@[simp]
theorem norm_paraboloidNormal_sq (x : V₂) :
    ‖paraboloidNormal x‖ ^ 2 = 1 + 4 * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [paraboloidNormal, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  norm_num
  ring

/-- The upward graph normal never vanishes. -/
theorem paraboloidNormal_ne_zero (x : V₂) : paraboloidNormal x ≠ 0 := by
  intro h
  have hi := norm_paraboloidNormal_sq x
  rw [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hi
  nlinarith [sq_nonneg ‖x‖]

/-- The normal is orthogonal to every graph tangent. -/
@[simp]
theorem inner_paraboloidNormal_fderiv_paraboloidGraph (x w : V₂) :
    inner ℝ (paraboloidNormal x) (fderiv ℝ paraboloidGraph x w) = 0 := by
  simp only [paraboloidNormal, inner_add_left, real_inner_smul_left, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, fderiv_paraboloidGraph_apply_zero,
    fderiv_paraboloidGraph_apply_one, fderiv_paraboloidGraph_apply_two]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  ring

/-- The upward normal lies in the orthogonal complement of the range of the graph differential. -/
theorem paraboloidNormal_mem_orthogonal_range_fderiv_paraboloidGraph (x : V₂) :
    paraboloidNormal x ∈ (fderiv ℝ paraboloidGraph x).rangeᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨w, rfl⟩
  rw [real_inner_comm]
  exact inner_paraboloidNormal_fderiv_paraboloidGraph x w

/-- The upward graph normal is smooth at every order, including analytic order. -/
@[fun_prop]
theorem contDiff_paraboloidNormal {n : ℕ∞ω} : ContDiff ℝ n paraboloidNormal := by
  unfold paraboloidNormal
  have hp (i : Fin 2) : ContDiff ℝ n (fun x : V₂ ↦ x i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).contDiff
  exact (((contDiff_const.mul (hp 0)).smul contDiff_const).add
    ((contDiff_const.mul (hp 1)).smul contDiff_const)).add contDiff_const

/-- The upward normal spans the whole graph normal space at every Cartesian point. -/
theorem orthogonal_range_fderiv_paraboloidGraph_eq_span_paraboloidNormal (x : V₂) :
    (fderiv ℝ paraboloidGraph x).rangeᗮ = Submodule.span ℝ {paraboloidNormal x} := by
  have hdim := (fderiv ℝ paraboloidGraph x).range.finrank_add_finrank_orthogonal
  have hrank := LinearMap.finrank_range_of_inj (fderiv_paraboloidGraph_injective x)
  norm_num at hdim hrank
  exact eq_span_singleton_of_mem_of_finrank_eq_one (by omega)
    (paraboloidNormal_mem_orthogonal_range_fderiv_paraboloidGraph x) (paraboloidNormal_ne_zero x)

/-- The upward unit normal to the Cartesian paraboloid. -/
def paraboloidUnitNormal (x : V₂) : E₃ :=
  NormedSpace.normalize (paraboloidNormal x)

/-- The explicit expression for the upward unit normal. -/
theorem paraboloidUnitNormal_apply (x : V₂) :
    paraboloidUnitNormal x = (√(1 + 4 * ‖x‖ ^ 2))⁻¹ • paraboloidNormal x := by
  have hn : ‖paraboloidNormal x‖ = √(1 + 4 * ‖x‖ ^ 2) := by
    rw [← norm_paraboloidNormal_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [paraboloidUnitNormal, NormedSpace.normalize, hn]

/-- The upward Cartesian unit normal has length one. -/
@[simp]
theorem norm_paraboloidUnitNormal (x : V₂) : ‖paraboloidUnitNormal x‖ = 1 :=
  NormedSpace.norm_normalize (paraboloidNormal_ne_zero x)

/-- The upward unit normal is orthogonal to the differential of the graph. -/
@[simp]
theorem inner_paraboloidUnitNormal_fderiv_paraboloidGraph (x w : V₂) :
    ⟪paraboloidUnitNormal x, fderiv ℝ paraboloidGraph x w⟫_ℝ = 0 := by
  simp [paraboloidUnitNormal, NormedSpace.normalize, real_inner_smul_left]

/-- The upward unit normal is smooth at every order, including analytic order. -/
@[fun_prop]
theorem contDiff_paraboloidUnitNormal {n : ℕ∞ω} : ContDiff ℝ n paraboloidUnitNormal := by
  exact contDiff_iff_contDiffAt.2 fun x ↦
    (NormedSpace.contDiffAt_normalize (paraboloidNormal_ne_zero x)).comp x
      contDiff_paraboloidNormal.contDiffAt

end TauCeti.Manifold
