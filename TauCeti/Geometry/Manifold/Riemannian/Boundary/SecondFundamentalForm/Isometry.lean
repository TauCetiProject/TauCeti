/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita

/-!
# Naturality of the second fundamental form of the boundary

An isometry `Φ : M → M'` of Riemannian manifolds with boundary maps `∂M` onto `∂M'`, and it
preserves the second fundamental form of the boundary: if `u, w ∈ T_q∂M` and `u', w' ∈ T_{Φ q}∂M'`
correspond under `dΦ` (`TauCeti.BoundaryTangentCorr`), that is `dι' u' = dΦ (dι u)` and
`dι' w' = dΦ (dι w)`, then
`II'_{Φ q}(u', w') = II_q(u, w)`
(`TauCeti.RiemannianIsometry.boundarySecondFundamentalForm_map`). In other words
`(Φ|∂M)^* II' = II`. It also preserves the induced metric, `h'(u', w') = h(u, w)`
(`TauCeti.RiemannianIsometry.boundaryInducedForm_map`), and the corresponding vector `u'` of
`u ∈ T_q∂M` is its image under the boundary tangent map `TauCeti.boundaryTangentMap`
(`TauCeti.RiemannianIsometry.boundaryTangentCorr_boundaryTangentMap`).

The proof transports the description `II_q(u, w) = -⟨∇_{dι u} W, ν_out(q)⟩` of
`TauCeti.boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal`: a vector field `W'`
tangent to `∂M'` with `W'(Φ q) = dι' w'` pulls back to a vector field `W` tangent to `∂M` with
`W(q) = dι w` (`TauCeti.eventually_mpullback_mem_boundaryTangentSpace`), the Levi-Civita
connection is natural under isometries
(`TauCeti.IsLocalRiemannianIsometry.mfderiv_leviCivitaConnection_mpullback`), and so is the outward
unit normal (`TauCeti.RiemannianIsometry.mfderiv_outwardUnitNormal`).
-/

public section

noncomputable section

open Bundle Filter Manifold VectorField
open scoped Manifold ContDiff InnerProductSpace Topology

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

/-- **Naturality of the second fundamental form of the boundary.** Let `Φ : M → M'` be an isometry
of Riemannian manifolds with boundary and `q ∈ ∂M`. If `u, w ∈ T_q∂M` and
`u', w' ∈ T_{Φ q}∂M'` satisfy `dι' u' = dΦ (dι u)` and `dι' w' = dΦ (dι w)`, then
`II'_{Φ q}(u', w') = II_q(u, w)`. -/
theorem RiemannianIsometry.boundarySecondFundamentalForm_map
    (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    (u' w' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M'))
    (hu : BoundaryTangentCorr Φ q ⟨Φ q, Φ.apply_mem_boundary q.property⟩ u u')
    (hw : BoundaryTangentCorr Φ q ⟨Φ q, Φ.apply_mem_boundary q.property⟩ w w') :
    boundarySecondFundamentalForm ⟨Φ q, Φ.apply_mem_boundary q.property⟩ u' w' =
      boundarySecondFundamentalForm q u w := by
  have hΦ := Φ.isLocalRiemannianIsometry
  obtain ⟨W', hW', hW'q, hW't⟩ := exists_mdifferentiableAt_extension_mem_boundaryTangentSpace _ w'
  set W : (y : M) → TangentSpace (𝓡∂ (n + 1)) y := mpullback (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ W'
  have hW : MDiffAt (T% W) (q : M) := hΦ.mdifferentiableAt_mpullback hW'
  have hWq : W q = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w :=
    (hΦ.mpullback_apply_eq_iff W' _).2 (hW'q.trans hw)
  have hWt : ∀ᶠ p in 𝓝 q, W p ∈ boundaryTangentSpace p := by
    have h := fun hV ↦ eventually_mpullback_mem_boundaryTangentSpace (by simp) Φ.toDiffeomorph
      (q := q) (V := W') hV
    simp only [RiemannianIsometry.coe_toDiffeomorph] at h
    exact h hW't
  rw [boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal q u w hW hWq hWt,
    boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal _ u' w' hW' hW'q hW't,
    ← Φ.inner_mfderiv (q : M), hΦ.mfderiv_leviCivitaConnection_mpullback hW',
    Φ.mfderiv_outwardUnitNormal, hu]

namespace RiemannianIsometry

variable (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M)

omit [IsManifold (𝓡∂ (n + 1)) 2 M] [IsManifold (𝓡∂ (n + 1)) 2 M']
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)] in
/-- **Naturality of the induced metric of the boundary.** If `u, w ∈ T_q∂M` correspond under an
isometry `Φ` to `u', w' ∈ T_{Φ q}∂M'`, then `h'(u', w') = h(u, w)`. -/
theorem boundaryInducedForm_map {u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    {u' w' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M')}
    (hu : BoundaryTangentCorr Φ q ⟨Φ q, Φ.apply_mem_boundary q.property⟩ u u')
    (hw : BoundaryTangentCorr Φ q ⟨Φ q, Φ.apply_mem_boundary q.property⟩ w w') :
    boundaryInducedForm ⟨Φ q, Φ.apply_mem_boundary q.property⟩ u' w' =
      boundaryInducedForm q u w := by
  rw [boundaryInducedForm_apply, boundaryInducedForm_apply, hu, hw, Φ.inner_mfderiv]

omit [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)] in
/-- An isometry `Φ` carries `u ∈ T_q∂M` to the corresponding vector of `T_{Φ q}∂M'` given by the
boundary tangent map of its underlying diffeomorphism. -/
theorem boundaryTangentCorr_boundaryTangentMap (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    BoundaryTangentCorr Φ q ⟨Φ q, Φ.apply_mem_boundary q.property⟩ u
      (boundaryTangentMap (by simp) Φ.toDiffeomorph q ⟨Φ q, Φ.apply_mem_boundary q.property⟩ rfl
        u) :=
  TauCeti.boundaryTangentCorr_boundaryTangentMap _ Φ.toDiffeomorph q _ rfl u

end RiemannianIsometry

end TauCeti
