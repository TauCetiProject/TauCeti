/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Weingarten.Basic

/-!
# Naturality of the Weingarten map, principal curvatures and mean curvature

An isometry `Φ : M → M'` of Riemannian manifolds with boundary maps `∂M` onto `∂M'` and carries
`T_q∂M` onto `T_{Φ q}∂M'`: tangent vectors `u ∈ T_q∂M` and `u' ∈ T_{Φ q}∂M'` correspond
(`TauCeti.BoundaryTangentCorr`) when `dι' u' = dΦ (dι u)`, that is, when `u'` is the image of `u`
under the boundary tangent map `TauCeti.boundaryTangentMap`
(`TauCeti.RiemannianIsometry.boundaryTangentCorr_boundaryTangentMap`). This file shows that `Φ`
preserves the extrinsic geometry of the boundary built on the second fundamental form:

* the Weingarten map: if `u` and `u'` correspond, so do `S_q u` and `S'_{Φ q} u'`
  (`TauCeti.RiemannianIsometry.boundaryWeingarten_map`), that is `(Φ|∂M)^* S' = S`;
* the principal curvatures and the mean curvature, `κ'(Φ q) = κ(q)` and `H'(Φ q) = H(q)`
  (`TauCeti.RiemannianIsometry.boundaryPrincipalCurvatures_map`,
  `TauCeti.RiemannianIsometry.boundaryMeanCurvature_map`).

The Weingarten map is determined by `h(S_q u, w) = II_q(u, w)`, and both the induced metric `h`
and the second fundamental form are natural (`TauCeti.RiemannianIsometry.boundaryInducedForm_map`,
`TauCeti.RiemannianIsometry.boundarySecondFundamentalForm_map`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {n : ℕ} {M M' : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [TopologicalSpace M'] [ChartedSpace (EuclideanHalfSpace (n + 1)) M']
  [IsManifold (𝓡∂ (n + 1)) 2 M']
  [RiemannianBundle (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)]

namespace RiemannianIsometry

variable (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M)

/-- **Naturality of the Weingarten map of the boundary.** If `u ∈ T_q∂M` corresponds under an
isometry `Φ` to `u' ∈ T_{Φ q}∂M'`, then `S_q u` corresponds to `S'_{Φ q} u'`:
`dι' (S'_{Φ q} u') = dΦ (dι (S_q u))`. -/
theorem boundaryWeingarten_map {u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    {u' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M')}
    (hu : BoundaryTangentCorr Φ q ⟨Φ q, Φ.apply_mem_boundary q.property⟩ u u') :
    BoundaryTangentCorr Φ q ⟨Φ q, Φ.apply_mem_boundary q.property⟩
      (boundaryWeingarten q u) (boundaryWeingarten _ u') := by
  have hL := Φ.boundaryTangentCorr_boundaryTangentMap q
  generalize boundaryTangentMap _ Φ.toDiffeomorph q _ _ = L at hL
  -- `S'_{Φ q} u' = L (S_q u)`: test against every `w' ∈ T_{Φ q}∂M'` with the induced metric.
  have h : boundaryWeingarten _ u' = L (boundaryWeingarten q u) := by
    rw [← sub_eq_zero]
    refine (boundaryInducedForm_nondegenerate _).1 _ fun w' ↦ ?_
    have hw := hL (L.symm w')
    rw [LinearEquiv.apply_symm_apply] at hw
    rw [map_sub, LinearMap.sub_apply, boundaryInducedForm_boundaryWeingarten,
      Φ.boundarySecondFundamentalForm_map q u _ u' w' hu hw, Φ.boundaryInducedForm_map q (hL _) hw,
      boundaryInducedForm_boundaryWeingarten, sub_self]
  rw [h]
  exact hL _

/-- **Naturality of the principal curvatures of the boundary**: an isometry `Φ` preserves them,
`κ'(Φ q) = κ(q)`. -/
@[simp]
theorem boundaryPrincipalCurvatures_map :
    boundaryPrincipalCurvatures (⟨Φ q, Φ.apply_mem_boundary q.property⟩ :
      (𝓡∂ (n + 1)).boundary M') = boundaryPrincipalCurvatures q := by
  have hL := Φ.boundaryTangentCorr_boundaryTangentMap q
  generalize boundaryTangentMap _ Φ.toDiffeomorph q _ _ = L at hL
  -- The images of the principal directions are eigenvectors of `S'` with the same eigenvalues.
  refine boundaryPrincipalCurvatures_eq_of_eigenbasis _ ((boundaryPrincipalBasis q).map L)
    (boundaryPrincipalCurvatures_antitone q) fun i ↦ ?_
  rw [Module.Basis.map_apply, coe_boundaryPrincipalBasis]
  refine injective_mfderiv_subtypeVal_boundary _ ?_
  rw [Φ.boundaryWeingarten_map q (hL _), boundaryWeingarten_boundaryPrincipalDirection, map_smul,
    map_smul, map_smul, hL]

/-- **Naturality of the mean curvature of the boundary**: an isometry `Φ` preserves it,
`H'(Φ q) = H(q)`. -/
@[simp]
theorem boundaryMeanCurvature_map :
    boundaryMeanCurvature (⟨Φ q, Φ.apply_mem_boundary q.property⟩ :
      (𝓡∂ (n + 1)).boundary M') = boundaryMeanCurvature q := by
  rw [boundaryMeanCurvature_eq_sum_div, boundaryMeanCurvature_eq_sum_div,
    boundaryPrincipalCurvatures_map]

end RiemannianIsometry

end TauCeti
