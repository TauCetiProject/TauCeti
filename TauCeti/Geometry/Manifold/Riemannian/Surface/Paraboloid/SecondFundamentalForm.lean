/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Paraboloid.Basic
public import TauCeti.Analysis.InnerProductSpace.SecondFundamentalForm
public import TauCeti.Analysis.InnerProductSpace.SquaredDistance

/-!
# The Cartesian second fundamental form of the paraboloid

This file computes `TauCeti.secondFundamentalForm ℝ paraboloidGraph` explicitly,
providing a Euclidean second fundamental form example valid also at the vertex.
The upward normal `N=(-2x₀,-2x₁,1)` has squared length `1+4‖x‖²`. The graph Hessian is
`(2⟪w,z⟫) • e₂`, hence its normal projection is `(2⟪w,z⟫/(1+4‖x‖²)) • N`.
The main results are `secondFundamentalForm_paraboloidGraph_apply` and
`orthogonal_range_fderiv_paraboloidGraph_eq_span_paraboloidNormal`.

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
theorem inner_paraboloidNormal_self (x : V₂) :
    inner ℝ (paraboloidNormal x) (paraboloidNormal x) = 1 + 4 * ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [paraboloidNormal, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  norm_num
  ring

/-- The upward graph normal never vanishes. -/
theorem paraboloidNormal_ne_zero (x : V₂) : paraboloidNormal x ≠ 0 := by
  intro h
  have hi := inner_paraboloidNormal_self x
  rw [h, inner_zero_left] at hi
  nlinarith [sq_nonneg ‖x‖]

/-- The normal is orthogonal to every graph tangent. -/
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

/-- The graph has second derivative `D²F(x)(w,z) = (2⟪w,z⟫) • e₂`, independent of `x`;
only the height coordinate is curved. -/
theorem fderiv_fderiv_paraboloidGraph_apply (x w z : V₂) :
    fderiv ℝ (fderiv ℝ paraboloidGraph) x w z =
      (2 * inner ℝ w z) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  let L := (LinearIsometry.piLpExtendByZero 2 ℝ ℝ
    (Fin.castLEEmb (by decide : 2 ≤ 3))).toContinuousLinearMap
  have hgraph : paraboloidGraph = (L : V₂ → E₃) + (fun y ↦ ‖y‖ ^ 2 •
      EuclideanSpace.basisFun (Fin 3) ℝ 2) := by
    funext y
    have he (j : Fin 2) := EuclideanSpace.piLpExtendByZero_castLEEmb_apply_castLE
      (n := 3) (by decide) y j
    ext i
    fin_cases i
    · simpa [L, EuclideanSpace.basisFun_apply] using (he 0).symm
    · simpa [L, EuclideanSpace.basisFun_apply] using (he 1).symm
    · simp [L, EuclideanSpace.basisFun_apply]
  rw [hgraph, TauCeti.fderiv_fderiv_add
    (w := fun y : V₂ ↦ ‖y‖ ^ 2 • EuclideanSpace.basisFun (Fin 3) ℝ 2)
    L.contDiff.contDiffAt (((contDiff_norm_sq ℝ).smul contDiff_const).contDiffAt)]
  simp [TauCeti.fderiv_fderiv_smul_const_apply (contDiff_norm_sq ℝ).contDiffAt,
    TauCeti.fderiv_fderiv_norm_sq_apply]

/-- Pairing with the graph normal recovers the ordinary height Hessian. -/
theorem inner_paraboloidNormal_secondFundamentalForm_paraboloidGraph (x w z : V₂) :
    inner ℝ (paraboloidNormal x) (TauCeti.secondFundamentalForm ℝ paraboloidGraph x w z) =
      2 * inner ℝ w z := by
  rw [TauCeti.inner_secondFundamentalForm_apply_of_mem_orthogonal
    (paraboloidNormal_mem_orthogonal_range_fderiv_paraboloidGraph x),
    fderiv_fderiv_paraboloidGraph_apply]
  simp only [paraboloidNormal, inner_add_left, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  norm_num

/-- The upward normal spans the whole graph normal space at every Cartesian point. -/
theorem orthogonal_range_fderiv_paraboloidGraph_eq_span_paraboloidNormal (x : V₂) :
    (fderiv ℝ paraboloidGraph x).rangeᗮ = Submodule.span ℝ {paraboloidNormal x} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
    (Submodule.span_le.mpr (by
      simpa using paraboloidNormal_mem_orthogonal_range_fderiv_paraboloidGraph x))
  have hdim := (fderiv ℝ paraboloidGraph x).range.finrank_add_finrank_orthogonal
  have hrank := LinearMap.finrank_range_of_inj (fderiv_paraboloidGraph_injective x)
  rw [finrank_span_singleton (paraboloidNormal_ne_zero x)]
  norm_num at hdim hrank
  omega

/-- The second fundamental form is
`B(w,z) = (2⟪w,z⟫ / (1 + 4‖x‖²)) • paraboloidNormal x` at every point, including the vertex. -/
theorem secondFundamentalForm_paraboloidGraph_apply (x w z : V₂) :
    TauCeti.secondFundamentalForm ℝ paraboloidGraph x w z =
      (2 * inner ℝ w z / (1 + 4 * ‖x‖ ^ 2)) • paraboloidNormal x := by
  have hm := TauCeti.secondFundamentalForm_apply_mem_orthogonal (𝕜 := ℝ) paraboloidGraph x w z
  rw [orthogonal_range_fderiv_paraboloidGraph_eq_span_paraboloidNormal] at hm
  have hp := Submodule.starProjection_eq_self_iff.mpr hm
  rw [Submodule.starProjection_singleton, ← real_inner_self_eq_norm_sq,
    inner_paraboloidNormal_self, inner_paraboloidNormal_secondFundamentalForm_paraboloidGraph] at hp
  exact hp.symm

end TauCeti.Manifold
