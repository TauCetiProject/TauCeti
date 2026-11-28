/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Paraboloid.Normal
public import TauCeti.Analysis.InnerProductSpace.SecondFundamentalForm
import TauCeti.Analysis.InnerProductSpace.Calculus

/-!
# The Cartesian second fundamental form of the paraboloid

This file computes `TauCeti.secondFundamentalForm ℝ paraboloidGraph` explicitly,
providing a Euclidean second fundamental form example valid also at the vertex.
The upward normal `N=(-2x₀,-2x₁,1)` has squared length `1+4‖x‖²`. The graph Hessian is
`(2⟪w,z⟫) • e₂`, hence its normal projection is `(2⟪w,z⟫/(1+4‖x‖²)) • N`.
The main result is `secondFundamentalForm_paraboloidGraph_apply`.

Adapted from Yangyang Li's formalization in ColdingMinicozziTheory:
[Cartesian graph and tensor work](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/ab114a15)
and [curvature follow-up](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/234e55b3).
-/

public noncomputable section

open scoped ContDiff InnerProductSpace

namespace TauCeti.Manifold

local notation "V₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The graph has second derivative `D²F(x)(w,z) = (2⟪w,z⟫) • e₂`, independent of `x`;
only the height coordinate is curved. -/
theorem fderiv_fderiv_paraboloidGraph_apply (x w z : V₂) :
    fderiv ℝ (fderiv ℝ paraboloidGraph) x w z =
      (2 * inner ℝ w z) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  let L := (LinearIsometry.piLpExtendByZero 2 ℝ ℝ
    (Fin.castLEEmb (by decide : 2 ≤ 3))).toContinuousLinearMap
  have hgraph : paraboloidGraph = (L : V₂ → E₃) + (fun y ↦ ‖y‖ ^ 2 •
      EuclideanSpace.basisFun (Fin 3) ℝ 2) := by
    -- The imported graph body is hidden; recover the decomposition from its coordinate API.
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
  simp [real_inner_smul_right, EuclideanSpace.basisFun_apply]

/-- The second fundamental form is
`B(w,z) = (2⟪w,z⟫ / (1 + 4‖x‖²)) • paraboloidNormal x` at every point, including the vertex. -/
theorem secondFundamentalForm_paraboloidGraph_apply (x w z : V₂) :
    TauCeti.secondFundamentalForm ℝ paraboloidGraph x w z =
      (2 * inner ℝ w z / (1 + 4 * ‖x‖ ^ 2)) • paraboloidNormal x := by
  have hm := TauCeti.secondFundamentalForm_apply_mem_orthogonal (𝕜 := ℝ) paraboloidGraph x w z
  rw [orthogonal_range_fderiv_paraboloidGraph_eq_span_paraboloidNormal] at hm
  have hp := Submodule.starProjection_eq_self_iff.mpr hm
  rw [Submodule.starProjection_singleton, norm_paraboloidNormal_sq,
    inner_paraboloidNormal_secondFundamentalForm_paraboloidGraph] at hp
  exact hp.symm

end TauCeti.Manifold
