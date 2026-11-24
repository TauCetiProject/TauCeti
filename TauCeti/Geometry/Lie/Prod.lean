/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Functor
public import Mathlib.Algebra.Lie.Prod

/-!
# The Lie algebra of a product Lie group

For finite-dimensional real Lie groups, the two projection homomorphisms identify the native
Lie algebra of the product with the product of the native Lie algebras. The groups may have
arbitrary models with corners and independent model and carrier universes.

## Main results

* `TauCeti.Lie.prodLieEquiv`: the Lie-algebra equivalence induced by the two projections.
* `TauCeti.Lie.prodLieEquiv_apply`: its two components are the native Lie maps of the projections.
* `TauCeti.Lie.lieMap_fst_prodLieEquiv_symm` and
  `TauCeti.Lie.lieMap_snd_prodLieEquiv_symm`: the projections recover the two input derivations.
* `TauCeti.Lie.lieMap_inl_add_lieMap_inr` and `TauCeti.Lie.prodLieEquiv_symm_eq_add`: a derivation
  of the product is the sum of the images of its components under the inclusions of the factors.
* `TauCeti.Lie.lieMap_fst_lieMap_prod`, `TauCeti.Lie.lieMap_snd_lieMap_prod`, and
  `TauCeti.Lie.prodLieEquiv_lieMap_prod`: the projections and product equivalence split the Lie map
  of a paired homomorphism into the pair of Lie maps.
* `TauCeti.Lie.lieMap_noncommCoprod`: the Lie map of `(g, g') ↦ φ g * ψ g'` for commuting smooth
  homomorphisms `φ` and `ψ` is the sum of their Lie maps on the two components.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113, Cambridge University Press (2008), Chapter 3, §3.8, proof of
  Theorem 3.41, p.42, for the product Lie-algebra identification.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

private def evalModel : LeftInvariantDerivation I G ≃ₗ[ℝ] E :=
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  leftInvariantDerivationLinearIsometryEquivModelVectorSpace.toLinearEquiv

private theorem eval_fst (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    evalModel (lieMap (ContMDiffMonoidMorphism.fst (I := I) (I' := I')) D) =
      (evalModel D).1 := by
  have h := leftInvariantDerivationLinearIsometryEquivModelVectorSpace_lieMap
    (ContMDiffMonoidMorphism.fst (I := I) (I' := I')) D
  dsimp only at h
  rw [ContMDiffMonoidMorphism.coe_fst, mfderiv_fst] at h
  -- `evalModel` is the canonical isometry viewed as a linear equivalence. Its coercion and
  -- the tangent-space first projection reduce to the model-space functions in this goal.
  exact h

private theorem eval_snd (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    evalModel (lieMap (ContMDiffMonoidMorphism.snd (I := I) (I' := I')) D) =
      (evalModel D).2 := by
  have h := leftInvariantDerivationLinearIsometryEquivModelVectorSpace_lieMap
    (ContMDiffMonoidMorphism.snd (I := I) (I' := I')) D
  dsimp only at h
  rw [ContMDiffMonoidMorphism.coe_snd, mfderiv_snd] at h
  -- The isometry's `toLinearEquiv` coercion and the tangent-space second projection are
  -- definitionally the model-space functions appearing in the goal.
  exact h

private def prodLieHom : LeftInvariantDerivation (I.prod I') (G × G') →ₗ⁅ℝ⁆
    LeftInvariantDerivation I G × LeftInvariantDerivation I' G' :=
  (lieMap ContMDiffMonoidMorphism.fst).prod (lieMap ContMDiffMonoidMorphism.snd)

private theorem prodLieHom_injective :
    Function.Injective (prodLieHom (I := I) (I' := I') (G := G) (G' := G')) := by
  intro D F h
  apply evalModel.injective
  apply Prod.ext
  · have h1 := congrArg (fun P ↦ evalModel (I := I) (G := G) P.1) h
    simpa only [prodLieHom, LieHom.prod_apply, eval_fst] using h1
  · have h2 := congrArg (fun P ↦ evalModel (I := I') (G := G') P.2) h
    simpa only [prodLieHom, LieHom.prod_apply, eval_snd] using h2

private theorem prodLieHom_surjective :
    Function.Surjective (prodLieHom (I := I) (I' := I') (G := G) (G' := G')) := by
  rintro ⟨X, Y⟩
  let Z := (evalModel (I := I.prod I') (G := G × G')).symm
    (evalModel X, evalModel Y)
  refine ⟨Z, Prod.ext ?_ ?_⟩
  · apply (evalModel (I := I) (G := G)).injective
    simp only [prodLieHom, LieHom.prod_apply, eval_fst, Z, LinearEquiv.apply_symm_apply]
  · apply (evalModel (I := I') (G := G')).injective
    simp only [prodLieHom, LieHom.prod_apply, eval_snd, Z, LinearEquiv.apply_symm_apply]

/-- The native Lie algebra of a product is the product of the two native Lie algebras. -/
def prodLieEquiv : LeftInvariantDerivation (I.prod I') (G × G') ≃ₗ⁅ℝ⁆
    LeftInvariantDerivation I G × LeftInvariantDerivation I' G' :=
  LieEquiv.ofBijective prodLieHom ⟨prodLieHom_injective, prodLieHom_surjective⟩

/-- The product Lie equivalence acts by the two projection Lie maps. -/
@[simp]
theorem prodLieEquiv_apply (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    prodLieEquiv D =
      (lieMap ContMDiffMonoidMorphism.fst D, lieMap ContMDiffMonoidMorphism.snd D) := by
  rfl

/-- The first projection recovers the first component of the inverse product Lie equivalence. -/
@[simp]
theorem lieMap_fst_prodLieEquiv_symm
    (p : LeftInvariantDerivation I G × LeftInvariantDerivation I' G') :
    lieMap ContMDiffMonoidMorphism.fst (prodLieEquiv.symm p) = p.1 := by
  have h := congrArg Prod.fst
    ((prodLieEquiv (I := I) (I' := I') (G := G) (G' := G')).apply_symm_apply p)
  simpa only [prodLieEquiv_apply] using h

/-- The second projection recovers the second component of the inverse product Lie equivalence. -/
@[simp]
theorem lieMap_snd_prodLieEquiv_symm
    (p : LeftInvariantDerivation I G × LeftInvariantDerivation I' G') :
    lieMap ContMDiffMonoidMorphism.snd (prodLieEquiv.symm p) = p.2 := by
  have h := congrArg Prod.snd
    ((prodLieEquiv (I := I) (I' := I') (G := G) (G' := G')).apply_symm_apply p)
  simpa only [prodLieEquiv_apply] using h

/-- The first projection undoes the first inclusion on Lie algebras. -/
@[simp]
theorem lieMap_fst_lieMap_inl (X : LeftInvariantDerivation I G) :
    lieMap (ContMDiffMonoidMorphism.fst (I := I) (I' := I') (G := G) (G' := G'))
      (lieMap (ContMDiffMonoidMorphism.inl (I := I) (I' := I') (G := G) (G' := G')) X) = X := by
  rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.fst_comp_inl, lieMap_id,
    one_apply_eq_self]

/-- The first projection kills the second inclusion on Lie algebras. -/
@[simp]
theorem lieMap_fst_lieMap_inr (Y : LeftInvariantDerivation I' G') :
    lieMap (ContMDiffMonoidMorphism.fst (I := I) (I' := I') (G := G) (G' := G'))
      (lieMap (ContMDiffMonoidMorphism.inr (I := I) (I' := I') (G := G) (G' := G')) Y) = 0 := by
  rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.fst_comp_inr, lieMap_one,
    zero_apply]

/-- The second projection kills the first inclusion on Lie algebras. -/
@[simp]
theorem lieMap_snd_lieMap_inl (X : LeftInvariantDerivation I G) :
    lieMap (ContMDiffMonoidMorphism.snd (I := I) (I' := I') (G := G) (G' := G'))
      (lieMap (ContMDiffMonoidMorphism.inl (I := I) (I' := I') (G := G) (G' := G')) X) = 0 := by
  rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.snd_comp_inl, lieMap_one,
    zero_apply]

/-- The second projection undoes the second inclusion on Lie algebras. -/
@[simp]
theorem lieMap_snd_lieMap_inr (Y : LeftInvariantDerivation I' G') :
    lieMap (ContMDiffMonoidMorphism.snd (I := I) (I' := I') (G := G) (G' := G'))
      (lieMap (ContMDiffMonoidMorphism.inr (I := I) (I' := I') (G := G) (G' := G')) Y) = Y := by
  rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.snd_comp_inr, lieMap_id,
    one_apply_eq_self]

/-- A left-invariant derivation of a product is the sum of the images of its two components under
the inclusions of the factors. -/
theorem lieMap_inl_add_lieMap_inr (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    lieMap ContMDiffMonoidMorphism.inl (lieMap ContMDiffMonoidMorphism.fst D) +
      lieMap ContMDiffMonoidMorphism.inr (lieMap ContMDiffMonoidMorphism.snd D) = D := by
  refine EquivLike.injective (prodLieEquiv (I := I) (I' := I') (G := G) (G' := G')) ?_
  simp

/-- The inverse product Lie equivalence reconstructs a derivation as the sum of the Lie maps of
the two smooth factor inclusions. -/
theorem prodLieEquiv_symm_eq_add
    (p : LeftInvariantDerivation I G × LeftInvariantDerivation I' G') :
    prodLieEquiv.symm p =
      lieMap (ContMDiffMonoidMorphism.inl (I := I) (I' := I') (G' := G')) p.1 +
        lieMap (ContMDiffMonoidMorphism.inr (I := I) (I' := I') (G := G)) p.2 := by
  simpa using (lieMap_inl_add_lieMap_inr (prodLieEquiv.symm p)).symm

/-- The first projection of the Lie map of a paired smooth homomorphism is the first Lie map. -/
@[simp]
theorem lieMap_fst_lieMap_prod
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [LieGroup I'' ∞ G''] [FiniteDimensional ℝ E'']
    (φ : ContMDiffMonoidMorphism I'' I ∞ G'' G) (ψ : ContMDiffMonoidMorphism I'' I' ∞ G'' G')
    (D : LeftInvariantDerivation I'' G'') :
    lieMap ContMDiffMonoidMorphism.fst (lieMap (φ.prod ψ) D) = lieMap φ D :=
  lieMap_lieMap_of_comp_eq (ContMDiffMonoidMorphism.fst_comp_prod φ ψ) D

/-- The second projection of the Lie map of a paired smooth homomorphism is the second Lie map. -/
@[simp]
theorem lieMap_snd_lieMap_prod
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [LieGroup I'' ∞ G''] [FiniteDimensional ℝ E'']
    (φ : ContMDiffMonoidMorphism I'' I ∞ G'' G) (ψ : ContMDiffMonoidMorphism I'' I' ∞ G'' G')
    (D : LeftInvariantDerivation I'' G'') :
    lieMap ContMDiffMonoidMorphism.snd (lieMap (φ.prod ψ) D) = lieMap ψ D :=
  lieMap_lieMap_of_comp_eq (ContMDiffMonoidMorphism.snd_comp_prod φ ψ) D

/-- Under `prodLieEquiv`, the Lie map of a paired smooth homomorphism is the pair of Lie maps. -/
theorem prodLieEquiv_lieMap_prod
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [LieGroup I'' ∞ G''] [FiniteDimensional ℝ E'']
    (φ : ContMDiffMonoidMorphism I'' I ∞ G'' G) (ψ : ContMDiffMonoidMorphism I'' I' ∞ G'' G')
    (D : LeftInvariantDerivation I'' G'') :
    prodLieEquiv (lieMap (φ.prod ψ) D) = (lieMap φ D, lieMap ψ D) := by
  simp

/-- The Lie map of the product `(g, g') ↦ φ g * ψ g'` of two smooth homomorphisms with commuting
images is the sum of their Lie maps on the two components. -/
@[simp]
theorem lieMap_noncommCoprod
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G''] [LieGroup I'' ∞ G'']
    (φ : ContMDiffMonoidMorphism I I'' ∞ G G'') (ψ : ContMDiffMonoidMorphism I' I'' ∞ G' G'')
    (h : ∀ g g', Commute (φ g) (ψ g')) (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    lieMap (φ.noncommCoprod ψ h) D =
      lieMap φ (lieMap ContMDiffMonoidMorphism.fst D) +
        lieMap ψ (lieMap ContMDiffMonoidMorphism.snd D) := by
  conv_lhs => rw [← lieMap_inl_add_lieMap_inr D]
  rw [map_add]
  congr 1
  · rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.noncommCoprod_comp_inl]
  · rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.noncommCoprod_comp_inr]

end TauCeti.Lie
