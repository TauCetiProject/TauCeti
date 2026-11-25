/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita

/-!
# Naturality of the second fundamental form of the boundary

An isometry `Φ : M → M'` of Riemannian manifolds with boundary maps `∂M` onto `∂M'`, and it
preserves the second fundamental form of the boundary: if `u, w ∈ T_q∂M` and `u', w' ∈ T_{Φ q}∂M'`
correspond under `dΦ`, that is `dι' u' = dΦ (dι u)` and `dι' w' = dΦ (dι w)`, then
`II'_{Φ q}(u', w') = II_q(u, w)`
(`TauCeti.RiemannianIsometry.boundarySecondFundamentalForm_apply`). In other words
`(Φ|∂M)^* II' = II`.

The proof transports the description `II_q(u, w) = -⟨∇_{dι u} W, ν_out(q)⟩` of
`TauCeti.boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal`: a vector field `W'`
tangent to `∂M'` with `W'(Φ q) = dι' w'` pulls back to a vector field `W` tangent to `∂M` with
`W(q) = dι w`, the Levi-Civita connection is natural under isometries
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
theorem RiemannianIsometry.boundarySecondFundamentalForm_apply
    (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    (u' w' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M'))
    (hu : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M' → M') ⟨Φ q, Φ.apply_mem_boundary q.property⟩ u' =
      mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u))
    (hw : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M' → M') ⟨Φ q, Φ.apply_mem_boundary q.property⟩ w' =
      mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w)) :
    boundarySecondFundamentalForm ⟨Φ q, Φ.apply_mem_boundary q.property⟩ u' w' =
      boundarySecondFundamentalForm q u w := by
  have hΦ := Φ.isLocalRiemannianIsometry
  obtain ⟨W', hW', hW'q, hW't⟩ := exists_mdifferentiableAt_extension_mem_boundaryTangentSpace _ w'
  set W : (y : M) → TangentSpace (𝓡∂ (n + 1)) y := mpullback (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ W'
  have hW : MDiffAt (T% W) (q : M) := hΦ.mdifferentiableAt_mpullback hW'
  have hWq : W q = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w := by
    apply hΦ.mfderiv_injective (q : M)
    rw [hΦ.mfderiv_apply_mpullback, ← hw]
    exact hW'q
  -- `W` is tangent to the boundary near `q`, since `dΦ` maps `T∂M` onto `T∂M'`.
  have hbd : Continuous fun p : (𝓡∂ (n + 1)).boundary M ↦
      (⟨Φ p, Φ.apply_mem_boundary p.property⟩ : (𝓡∂ (n + 1)).boundary M') :=
    (Φ.continuous.comp continuous_subtypeVal).subtype_mk _
  have hWt : ∀ᶠ p in 𝓝 q, W p ∈ boundaryTangentSpace p := by
    filter_upwards [hbd.continuousAt.eventually hW't] with p hp
    have hmap := map_mfderiv_boundaryTangentSpace (by simp) Φ.toDiffeomorph p
    simp only [RiemannianIsometry.coe_toDiffeomorph] at hmap
    rw [← hmap] at hp
    obtain ⟨v, hv, hv'⟩ := hp
    have hWp : W p = v := hΦ.mfderiv_injective (p : M) (by
      simp only [W]
      rw [hΦ.mfderiv_apply_mpullback]
      simpa using hv'.symm)
    rw [hWp]
    exact hv
  rw [boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal q u w hW hWq hWt,
    boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal _ u' w' hW' hW'q hW't,
    ← Φ.inner_mfderiv (q : M), hΦ.mfderiv_leviCivitaConnection_mpullback hW',
    Φ.mfderiv_outwardUnitNormal, hu]

end TauCeti
