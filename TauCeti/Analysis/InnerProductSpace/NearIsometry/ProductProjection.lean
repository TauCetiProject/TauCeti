/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NearIsometry.Basic
public import TauCeti.Algebra.MonoidAlgebra.Star
public import TauCeti.RepresentationTheory.ProdTensorAction
public import TauCeti.RepresentationTheory.Unitary

/-!
# Near isometries after projecting at two group factors

In a unitary representation of `G × H`, apply the group-algebra projectors at the two
factors to one map. The squared Hilbert–Schmidt loss for their joint action is bounded by
the sum of the separate losses measured on the original map. Thus separate loss estimates
suffice to control the near-isometry error on the common projected space.

The application to a product of good projectors follows
`New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_one_sub_piTensorElem_comp_sq_le` and
`New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp` in
`grh/src/New/Spanning/Unfolding/Moments.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Spanning/Unfolding/Moments.lean
-/

public section

open LinearMap Module TauCeti.MonoidAlgebra TauCeti.UnitarilyInvariantSeminorm
open scoped InnerProductSpace TensorProduct

namespace Representation

variable {𝕜 S T G H : Type*} [RCLike 𝕜] [Group G] [Group H]
  [NormedAddCommGroup S] [InnerProductSpace 𝕜 S] [FiniteDimensional 𝕜 S]
  [NormedAddCommGroup T] [InnerProductSpace 𝕜 T]

/-- A pair of self-adjoint group-algebra idempotents acts as an orthogonal projection in a
unitary representation of the product, with no centrality assumption on the two idempotents. -/
theorem isSymmetricProjection_asAlgebraHom_prodTensorBialgEquiv_symm_tmul
    (ρ : Representation 𝕜 (G × H) T)
    (hρ : ∀ g v w, ⟪ρ g v, ρ g w⟫_𝕜 = ⟪v, w⟫_𝕜)
    {a : MonoidAlgebra 𝕜 G} {b : MonoidAlgebra 𝕜 H}
    (ha : IsStarProjection a) (hb : IsStarProjection b) :
    (ρ.asAlgebraHom ((prodTensorBialgEquiv 𝕜).symm (a ⊗ₜ[𝕜] b))).IsSymmetricProjection := by
  have hp := isSymmetricProjection_asAlgebraHom (ρ.comp (MonoidHom.inl G H))
    (fun g ↦ hρ (MonoidHom.inl G H g)) (fun g ↦ by
      simpa only [ha.isSelfAdjoint.star_eq, inv_inv] using MonoidAlgebra.coeff_star a g⁻¹)
    ha.isIdempotentElem
  have hq := isSymmetricProjection_asAlgebraHom (ρ.comp (MonoidHom.inr G H))
    (fun g ↦ hρ (MonoidHom.inr G H g)) (fun g ↦ by
      simpa only [hb.isSelfAdjoint.star_eq, inv_inv] using MonoidAlgebra.coeff_star b g⁻¹)
    hb.isIdempotentElem
  have hidem := hp.isIdempotentElem.mul_of_commute (ρ.commute_asAlgebraHom_prod_inl_inr a b)
    hq.isIdempotentElem
  have hsym : (asAlgebraHom (ρ.comp (MonoidHom.inl G H)) a *
      asAlgebraHom (ρ.comp (MonoidHom.inr G H)) b).IsSymmetric := by
    intro x y
    rw [mul_apply_eq_comp, hp.isSymmetric, hq.isSymmetric,
      ← mul_apply_eq_comp, (ρ.commute_asAlgebraHom_prod_inl_inr a b).eq]
  rw [ρ.asAlgebraHom_prodTensorBialgEquiv_symm_tmul]
  exact ⟨hidem, hsym⟩

/-- The squared Frobenius seminorm discarded by a pure tensor is bounded by the sum discarded
by its two factors, provided the first factor acts as an orthogonal projection. -/
theorem sq_frobenius_one_sub_asAlgebraHom_prodTensorBialgEquiv_symm_tmul_comp_le
    (ρ : Representation 𝕜 (G × H) T) (P : S →ₗ[𝕜] T)
    (a : MonoidAlgebra 𝕜 G) (b : MonoidAlgebra 𝕜 H)
    (ha : (asAlgebraHom (ρ.comp (MonoidHom.inl G H)) a).IsSymmetricProjection) :
    frobenius 𝕜 S T ((1 - ρ.asAlgebraHom ((prodTensorBialgEquiv 𝕜).symm (a ⊗ₜ[𝕜] b))) ∘ₗ P) ^ 2 ≤
      frobenius 𝕜 S T ((1 - asAlgebraHom (ρ.comp (MonoidHom.inl G H)) a) ∘ₗ P) ^ 2 +
        frobenius 𝕜 S T ((1 - asAlgebraHom (ρ.comp (MonoidHom.inr G H)) b) ∘ₗ P) ^ 2 := by
  rw [ρ.asAlgebraHom_prodTensorBialgEquiv_symm_tmul]
  exact sq_frobenius_one_sub_mul_comp_le ha _ P

/-- Projecting by both factors increases the near-isometry error by at most the sum of the
individual squared losses per source dimension. -/
theorem isNearIsometry_prod_projectors [FiniteDimensional 𝕜 T]
    (ρ : Representation 𝕜 (G × H) T)
    (hρ : ∀ g v w, ⟪ρ g v, ρ g w⟫_𝕜 = ⟪v, w⟫_𝕜)
    {P : S →ₗ[𝕜] T} {ε δ₁ δ₂ : ℝ} (hP : P.IsNearIsometry ε)
    {a : MonoidAlgebra 𝕜 G} {b : MonoidAlgebra 𝕜 H}
    (ha : IsStarProjection a) (hb : IsStarProjection b)
    (h₁ : frobenius 𝕜 S T ((1 - asAlgebraHom (ρ.comp (MonoidHom.inl G H)) a) ∘ₗ P) ^ 2 ≤
      δ₁ * finrank 𝕜 S)
    (h₂ : frobenius 𝕜 S T ((1 - asAlgebraHom (ρ.comp (MonoidHom.inr G H)) b) ∘ₗ P) ^ 2 ≤
      δ₂ * finrank 𝕜 S) :
    (ρ.asAlgebraHom ((prodTensorBialgEquiv 𝕜).symm (a ⊗ₜ[𝕜] b)) ∘ₗ P).IsNearIsometry
      (ε + (δ₁ + δ₂)) := by
  have hp := isSymmetricProjection_asAlgebraHom (ρ.comp (MonoidHom.inl G H))
    (fun g ↦ hρ (MonoidHom.inl G H g)) (fun g ↦ by
      simpa only [ha.isSelfAdjoint.star_eq, inv_inv] using MonoidAlgebra.coeff_star a g⁻¹)
    ha.isIdempotentElem
  apply hP.comp_of_isSymmetricProjection
    (ρ.isSymmetricProjection_asAlgebraHom_prodTensorBialgEquiv_symm_tmul hρ ha hb)
  rw [add_mul]
  exact (ρ.sq_frobenius_one_sub_asAlgebraHom_prodTensorBialgEquiv_symm_tmul_comp_le P a b hp).trans
    (add_le_add h₁ h₂)

end Representation
